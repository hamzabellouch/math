import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PaddedGroupWeight

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.TaggedPrimeGroups
open Finset Classical
variable {P : Type*} [Fintype P] [DecidableEq P]

lemma padded_weight_identity (W : P → ℝ) {m : ℕ} (x : Fin m → Option P) :
    weight (paddedGroupWeight W) x =
      ∏ p : P, if ∃ i, x i=some p then W p else 1 := by
  have he : weight (paddedGroupWeight W) x =
      ∏ p : Option P, if p ∈ support x then paddedGroupWeight W p else 1 := by
    rw [← prod_filter]
    simp only [weight,filter_mem_eq_inter,univ_inter]
  rw [he,Fintype.prod_option]
  simp only [paddedGroupWeight,ite_self,one_mul]
  apply prod_congr rfl
  intro p hp
  simp only [support,mem_image,mem_univ,true_and]

omit [Fintype P] [DecidableEq P] in
lemma padded_same_pair {Q : Type*} (U : P → Q → ℝ) (z : Option (P × Q)) :
    paddedShapeWeight U (z.map Prod.fst) (z.map Prod.snd) =
      z.elim 1 (fun z => U z.1 z.2) := by
  cases z <;> rfl
end OrdinaryCorrelations.TaggedPrimeGroups

end

end OAI
