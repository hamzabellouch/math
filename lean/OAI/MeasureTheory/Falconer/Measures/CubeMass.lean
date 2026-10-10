import OAI.MeasureTheory.Falconer.Angular.CubeCapacity
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-! # Finite Frostman measures from dyadic cube capacities -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem split_cube_budget {d : ℕ} (c : (Fin d → Bool) → ℝ)
    (hc : ∀ b, 0 ≤ c b) {m : ℝ} (hm : 0 ≤ m) (hmc : m ≤ ∑ b, c b) :
    ∃ v : (Fin d → Bool) → ℝ, (∀ b, 0 ≤ v b ∧ v b ≤ c b) ∧ ∑ b, v b = m := by
  classical
  let S := ∑ b, c b
  have hS : 0 ≤ S := Finset.sum_nonneg fun b _ => hc b
  by_cases hzero : S = 0
  · have hm0 : m = 0 := le_antisymm (hmc.trans_eq hzero) hm
    exact ⟨fun _ => 0,fun b => ⟨le_rfl,hc b⟩,by simp [hm0]⟩
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    have hfrac : m/S ≤ 1 := (div_le_one hpos).mpr hmc
    refine ⟨fun b => (m/S)*c b,fun b => ⟨mul_nonneg (div_nonneg hm hS) (hc b),?_⟩,?_⟩
    · simpa using mul_le_mul_of_nonneg_right hfrac (hc b)
    · rw [← Finset.mul_sum]
      exact div_mul_cancel₀ m hzero

theorem finite_cube_measure {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (hQ : 0 < Q.side) (K : ℕ)
    (m : ℝ) (hm : 0 ≤ m) (hcap : m ≤ cubeCapacity E s Q K) :
    ∃ μ : Measure (Space d), μ univ = ENNReal.ofReal m ∧
      μ (E ∩ Q.carrier)ᶜ = 0 ∧
      ∀ p : List (Fin d → Bool), p.length ≤ K →
        μ (Q.descendant p).carrier ≤ ENNReal.ofReal ((Q.descendant p).side^s) := by
  classical
  induction K generalizing Q m with
  | zero =>
    by_cases h : (E ∩ Q.carrier).Nonempty
    · obtain ⟨x,hx⟩ := h
      refine ⟨ENNReal.ofReal m • Measure.dirac x,by simp,?_,?_⟩
      · simp [Measure.smul_apply,hx]
      · intro p hp
        have hp0 : p = [] := by cases p <;> simp_all
        subst p
        have hb : m ≤ Q.side^s := hcap.trans (cubeOccupied_le E s Q hQ.le)
        simpa [Measure.smul_apply,Measure.dirac_apply' _ Q.measurable,hx.2] using
          ENNReal.ofReal_le_ofReal hb
    · have hm0 : m = 0 := by
        have hb : m ≤ 0 := by simpa [cubeCapacity,cubeOccupied,h] using hcap
        exact le_antisymm hb hm
      refine ⟨0,by simp [hm0],by simp,?_⟩
      intro p hp
      simp
  | succ K ih =>
    have hsum : m ≤ ∑ b : Fin d → Bool, cubeCapacity E s (Q.child b) K :=
      hcap.trans (min_le_right _ _)
    obtain ⟨v,hv,hvsum⟩ := split_cube_budget (fun b => cubeCapacity E s (Q.child b) K)
      (fun b => cubeCapacity_nonneg E s (Q.child b) (by change 0 ≤ Q.side/2; positivity) K) hm hsum
    have hex (b : Fin d → Bool) :=
      ih (Q.child b) (by change 0 < Q.side/2; positivity) (v b) (hv b).1 (hv b).2
    choose μ hmass hcarry hbounds using hex
    have hchild (b : Fin d → Bool) : μ b (Q.child b).carrierᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr inter_subset_right) (hcarry b)
    have hparent (b : Fin d → Bool) : μ b (E ∩ Q.carrier)ᶜ = 0 :=
      measure_mono_null
        (compl_subset_compl.mpr (inter_subset_inter_right E (Q.child_subset b))) (hcarry b)
    refine ⟨∑ b, μ b,?_,?_,?_⟩
    · simp only [Measure.finsetSum_apply,hmass]
      rw [← ofReal_finset_sum_nonneg _ _ (fun b _ => (hv b).1),hvsum]
    · simp only [Measure.finsetSum_apply,hparent,Finset.sum_const_zero]
    · intro p hp
      cases p with
      | nil =>
        apply (measure_mono (subset_univ _)).trans
        simp only [Measure.finsetSum_apply,hmass]
        rw [← ofReal_finset_sum_nonneg _ _ (fun b _ => (hv b).1),hvsum]
        exact ENNReal.ofReal_le_ofReal
          (hcap.trans ((cubeCapacity_le_occupied E s Q (K+1)).trans (cubeOccupied_le E s Q hQ.le)))
      | cons b p =>
        change (∑ c, μ c) ((Q.child b).descendant p).carrier ≤ _
        rw [Measure.finsetSum_apply,Finset.sum_eq_single b]
        · exact hbounds b p (by simpa using Nat.le_of_succ_le_succ hp)
        · intro c _ hcb
          apply measure_mono_null _ (hchild c)
          intro x hx hxc
          exact Set.disjoint_left.mp (Q.children_disjoint (Ne.symm hcb))
            ((Q.child b).descendant_subset p hx) hxc
        · simp

end Falconer

end OAI
