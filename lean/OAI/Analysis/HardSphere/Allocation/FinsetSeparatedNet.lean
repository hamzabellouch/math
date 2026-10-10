import Mathlib
import OAI.Analysis.HardSphere.PathBounds.LatticeExponentialSum

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma finset_separated_net {ι : Type*} [DecidableEq ι] (A : Finset ι) (d : ι → ι → ℝ)
    (hd : ∀ i j, d i j=d j i) (hdiag : ∀ i, d i i=0) {R : ℝ} (hR : 0<R) :
    ∃ B : Finset ι, B⊆A ∧ (∀ i∈B, ∀ j∈B, i≠j → R≤d i j) ∧
      ∀ i∈A, ∃ j∈B, d i j<R := by
  classical
  let P : Finset ι → Prop := fun B ↦ ∀ i∈B, ∀ j∈B, i≠j → R≤d i j
  let S := A.powerset.filter P
  have hS : S.Nonempty := ⟨∅,by simp [S,P]⟩
  obtain ⟨B,hBS,hmax⟩ := S.exists_max_image Finset.card hS
  have hBA : B⊆A := Finset.mem_powerset.mp (Finset.mem_filter.mp hBS).1
  have hBP : P B := (Finset.mem_filter.mp hBS).2
  refine ⟨B,hBA,hBP,?_⟩
  intro i hi
  by_contra hn
  have hall : ∀ j∈B, R≤d i j := by
    intro j hj
    by_contra hlt
    exact hn ⟨j,hj,lt_of_not_ge hlt⟩
  have hin : i∉B := by
    intro hiB
    have hh := hall i hiB
    rw [hdiag] at hh
    exact (not_le_of_gt hR) hh
  have hPi : P (insert i B) := by
    intro j hj k hk hjk
    rcases Finset.mem_insert.mp hj with hji | hjB
    · subst j
      rcases Finset.mem_insert.mp hk with hki | hkB
      · exact (hjk hki.symm).elim
      · exact hall k hkB
    · rcases Finset.mem_insert.mp hk with hki | hkB
      · subst k
        rw [hd j i]
        exact hall j hjB
      · exact hBP j hjB k hkB hjk
  have hmem : insert i B∈S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hBA),hPi⟩
  have hh := hmax (insert i B) hmem
  rw [Finset.card_insert_of_notMem hin] at hh
  omega

theorem unitGrid_separated_subset : ∃ Q : ℕ, 0<Q ∧
    ∀ (K : ℕ) (L : Length), L.val=(K:ℝ) → ∀ A : Finset (CubeCell K),
      ∃ B : Finset (CubeCell K), B⊆A ∧
        (∀ v∈B, ∀ w∈B, v≠w → 20≤torusDistance L (unitCenter L v) (unitCenter L w)) ∧
        (A.card:ℝ)≤(Q:ℝ)*(B.card:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := unitGrid_exponential_bound
  let Q : ℕ := ⌈Real.exp 20*C⌉₊+1
  have hQ : 0<Q := Nat.succ_pos _
  have hQB : Real.exp 20*C≤(Q:ℝ) := by
    exact (Nat.le_ceil _).trans (by dsimp [Q]; push_cast; linarith)
  refine ⟨Q,hQ,?_⟩
  intro K L hL A
  obtain ⟨B,hBA,hB,hcover⟩ := finset_separated_net A
    (fun v w ↦ torusDistance L (unitCenter L v) (unitCenter L w))
    (fun v w ↦ torusDistance_comm L _ _) (fun v ↦ by simp [torusDistance]) (by norm_num : (0:ℝ)<20)
  refine ⟨B,hBA,hB,?_⟩
  have hpoint (v : CubeCell K) (hv : v∈A) :
      1≤Real.exp 20*∑ w∈B, Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)) := by
    obtain ⟨w,hw,hd⟩ := hcover v hv
    calc
      _ ≤ Real.exp (20-torusDistance L (unitCenter L v) (unitCenter L w)) :=
        Real.one_le_exp (by linarith only [hd])
      _ = Real.exp 20*Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)) := by
        rw [sub_eq_add_neg,Real.exp_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f:=fun w : CubeCell K ↦ Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)))
          (fun _ _ ↦ (Real.exp_pos _).le) hw) (Real.exp_pos 20).le
  calc
    _ = ∑ _v∈A, (1:ℝ) := by simp
    _ ≤ ∑ v∈A, Real.exp 20*∑ w∈B, Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)) :=
      Finset.sum_le_sum hpoint
    _ = Real.exp 20*∑ w∈B, ∑ v∈A, Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ Real.exp 20*∑ _w∈B, C := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 20).le
      apply Finset.sum_le_sum
      intro w _
      exact (Finset.sum_le_univ_sum_of_nonneg (fun v : CubeCell K ↦ (Real.exp_pos (-torusDistance L (unitCenter L v) (unitCenter L w))).le)).trans (hbound K L hL _)
    _ = (Real.exp 20*C)*(B.card:ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hQB (Nat.cast_nonneg _)

end HardSphere

end

end OAI
