import OAI.Geometry.TranslativeCovering.PoissonBinned

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1

namespace ActivityBins
open Finset
open scoped BigOperators
noncomputable def count (B : ℝ) : ℕ := ⌊B/Real.log 2⌋₊+1

lemma exists_bin {I : Type u_1} [Fintype I] [Nonempty I] [DecidableEq I]
    (ν : I → ℝ) {B : ℝ} (_hB : 0 ≤ B) (hlow : ∀ i,Real.exp (-B) ≤ ν i)
    (hupp : ∀ i,ν i ≤ 1) :
    ∃ S : Finset I, S.Nonempty ∧ (Fintype.card I:ℝ) ≤ (count B:ℝ)*S.card ∧
      ∃ a : ℝ, 0 < a ∧ ∀ i ∈ S,a ≤ ν i ∧ ν i ≤ 2*a := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp (i : I) : 0 < ν i := (Real.exp_pos _).trans_le (hlow i)
  have hz (i : I) : 0 ≤ -Real.log (ν i) := neg_nonneg.mpr (Real.log_nonpos (hp i).le (hupp i))
  have hb (i : I) : -Real.log (ν i) ≤ B := by
    have h := Real.log_le_log (Real.exp_pos _) (hlow i)
    rw [Real.log_exp] at h
    linarith
  let k : I → Fin (count B) := fun i => ⟨⌊-Real.log (ν i)/Real.log 2⌋₊,by
    dsimp [count]
    exact Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (hb i) hlog.le))⟩
  have hQ : 0 < (count B:ℝ) := by dsimp [count]; positivity
  have : Nonempty (Fin (count B)) := ⟨⟨0,by dsimp [count]; omega⟩⟩
  obtain ⟨j,hj⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card (f := k)
    (b := (Fintype.card I:ℝ)/(count B:ℝ)) (by
      rw [Fintype.card_fin,nsmul_eq_mul,mul_div_cancel₀ _ hQ.ne'])
  let S := univ.filter (fun i => k i = j)
  have hc : (Fintype.card I:ℝ)/(count B:ℝ) ≤ (S.card:ℝ) := by
    simpa only [S,Fintype.card_subtype] using hj
  have hI : 0 < (Fintype.card I:ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨S,Finset.card_pos.mp (by exact_mod_cast (div_pos hI hQ).trans_le hc),
    by nlinarith [(div_le_iff₀ hQ).mp hc],Real.exp (-((j.val:ℝ)+1)*Real.log 2),Real.exp_pos _,?_⟩
  intro i hi
  have he : ⌊-Real.log (ν i)/Real.log 2⌋₊ = j.val := congrArg Fin.val ((mem_filter.mp hi).2)
  have hlo : (j.val:ℝ) ≤ -Real.log (ν i)/Real.log 2 := by
    rw [← he]
    exact Nat.floor_le (div_nonneg (hz i) hlog.le)
  have hhi : -Real.log (ν i)/Real.log 2 < (j.val:ℝ)+1 := by
    rw [← he]
    exact Nat.lt_floor_add_one _
  have hlo' := (le_div_iff₀ hlog).mp hlo
  have hhi' := (div_lt_iff₀ hlog).mp hhi
  constructor
  · rw [← Real.exp_log (hp i)]
    exact Real.exp_le_exp.mpr (by linarith)
  · have hh : ν i ≤ Real.exp (-(j.val:ℝ)*Real.log 2) := by
      rw [← Real.exp_log (hp i)]
      exact Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ Real.exp (-(j.val:ℝ)*Real.log 2) := hh
      _ = _ := by
        rw [show -(j.val:ℝ)*Real.log 2 = Real.log 2+(-((j.val:ℝ)+1)*Real.log 2) by ring,
          Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2)]

end ActivityBins

end OAI
