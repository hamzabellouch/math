import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {I : Type*} [DecidableEq I]

def alternatingSubsetSum (U : Finset I) (s : ℝ) (p : Finset I → ℝ) : ℝ :=
  ∑A ∈ U.powerset, (-1:ℝ)^(U.card-A.card)*s^A.card*p A

lemma alternatingSubsetSum_of_isolated (U : Finset I) {s : ℝ} (hs : s≠0)
    (p : Finset I → ℝ) (i : I) (hi : i∈U)
    (hp : ∀A ⊆ U.erase i, p (insert i A)=s⁻¹*p A) :
    alternatingSubsetSum U s p=0 := by
  have hUi : U=insert i (U.erase i) := (Finset.insert_erase hi).symm
  have hn : i∉U.erase i := Finset.notMem_erase i U
  unfold alternatingSubsetSum
  rw [hUi,Finset.sum_powerset_insert hn,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro A hA
  have hAU : A⊆U.erase i := Finset.mem_powerset.mp hA
  have hiA : i∉A := fun h => hn (hAU h)
  have hcard := Finset.card_le_card hAU
  rw [Finset.card_insert_of_notMem hiA,hp A hAU]
  have he : (insert i (U.erase i)).card-A.card =
      ((insert i (U.erase i)).card-(A.card+1))+1 := by
    rw [Finset.card_insert_of_notMem hn]
    omega
  rw [he,pow_succ,pow_succ]
  simp only [mul_assoc]
  field_simp
  ring

end BinaryCoordinateSweeps

end

end OAI
