import OAI.Algebra.AffineCancellation.ReesDerivation
import OAI.Algebra.AffineCancellation.GradedMap
import OAI.Algebra.AffineCancellation.DegenerationGrading

namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def weight (i : Fin 6) : ℤ := if i=0 then 1 else if i=1 then -1 else if i=2 ∨ i=3 then 0 else 2
def sourcePieces (e : ℤ) := weightedHomogeneousSubmodule ℂ weight e
instance sourceGrading : GradedAlgebra sourcePieces := inferInstanceAs (GradedAlgebra (weightedHomogeneousSubmodule ℂ weight))
lemma xp_homogeneous : IsWeightedHomogeneous weight xp 0 := by
  have h₁ : IsWeightedHomogeneous weight ((X 2 : Poly)^2) 0 := by
    convert (isWeightedHomogeneous_X ℂ weight 2).pow 2 using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₂ : IsWeightedHomogeneous weight ((X 3 : Poly)^3) 0 := by
    convert (isWeightedHomogeneous_X ℂ weight 3).pow 3 using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₃ : IsWeightedHomogeneous weight ((X 1 : Poly)^2*X 4) 0 := by
    convert ((isWeightedHomogeneous_X ℂ weight 1).pow 2).mul (isWeightedHomogeneous_X ℂ weight 4) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  exact (h₁.add h₂).add h₃
lemma relation_homogeneous : relation ∈ sourcePieces 2 := by
  have h₁ : IsWeightedHomogeneous weight (xp^2*X 4) 2 := by
    convert (xp_homogeneous.pow 2).mul (isWeightedHomogeneous_X ℂ weight 4) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₂ : IsWeightedHomogeneous weight (1+2*X 2*xp : Poly) 0 := by
    apply (isWeightedHomogeneous_one ℂ weight).add
    convert ((isWeightedHomogeneous_C weight (2:ℂ)).mul (isWeightedHomogeneous_X ℂ weight 2)).mul xp_homogeneous using 1 <;> try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₃ : IsWeightedHomogeneous weight ((1+2*X 2*xp)*X 5 : Poly) 2 := by
    convert h₂.mul (isWeightedHomogeneous_X ℂ weight 5) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₄ : IsWeightedHomogeneous weight (X 1^2*X 5^2 : Poly) 2 := by
    convert ((isWeightedHomogeneous_X ℂ weight 1).pow 2).mul ((isWeightedHomogeneous_X ℂ weight 5).pow 2) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₅ : IsWeightedHomogeneous weight (X 0^3*X 1*X 3 : Poly) 2 := by
    convert (((isWeightedHomogeneous_X ℂ weight 0).pow 3).mul (isWeightedHomogeneous_X ℂ weight 1)).mul (isWeightedHomogeneous_X ℂ weight 3) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  exact ((h₁.sub h₃).sub h₄).sub h₅
lemma kernel_homogeneous : (RingHom.ker π).IsHomogeneous sourcePieces := by
  change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {relation}))).IsHomogeneous _
  rw [Ideal.mk_ker]
  apply Ideal.homogeneous_span
  intro r hr
  obtain rfl := Set.mem_singleton_iff.mp hr
  exact ⟨2,relation_homogeneous⟩
def pieces : ℤ → Submodule ℂ B := QuotientGrading.pieces sourcePieces π
instance grading : GradedAlgebra pieces := QuotientGrading.grading _ _ (Ideal.Quotient.mkₐ_surjective ℂ _) kernel_homogeneous
abbrev laurentPieces (e : ℤ) : Submodule ℂ L := (AddMonoidAlgebra.grade A e).restrictScalars ℂ
instance laurentGrading : GradedAlgebra laurentPieces := { (AddMonoidAlgebra.grade.gradedAlgebra (R := A) (ι := ℤ)) with }
lemma laurentMonomial_mem (r : A) (e : ℤ) : LaurentPolynomial.C r*T e ∈ laurentPieces e := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact AddMonoidAlgebra.single_mem_grade e r
lemma embedding_graded (e : ℤ) (b : B) (hb : b ∈ pieces e) : embedding b ∈ laurentPieces e := by
  obtain ⟨p,hp,rfl⟩ := hb
  change embedding (π p) ∈ _
  rw [embedding_π]
  apply GradedMap.mvpolynomial (k := ℂ) (R := L) laurentPieces weight eval _ hp
  intro i
  fin_cases i <;> simp only [eval,aeval_X,values,weight]
  · simpa using laurentMonomial_mem 1 1
  · exact laurentMonomial_mem _ _
  · change c (aπ (X 1)) ∈ laurentPieces 0
    have h := laurentMonomial_mem (aπ (X 1)) 0
    rw [T_zero,mul_one] at h
    exact h
  · change c (aπ (X 2)) ∈ laurentPieces 0
    have h := laurentMonomial_mem (aπ (X 2)) 0
    rw [T_zero,mul_one] at h
    exact h
  · exact laurentMonomial_mem _ _
  · exact laurentMonomial_mem _ _
lemma red_graded (e : ℤ) (b : B) (hb : b ∈ pieces e) : red b ∈ Degeneration.pieces e := by
  obtain ⟨p,hp,rfl⟩ := hb
  change red (π p) ∈ _
  rw [red_π]
  apply GradedMap.mvpolynomial Degeneration.pieces weight redEval _ hp
  intro i
  fin_cases i <;> simp only [redEval,aeval_X,redValues,weight]
  · exact (Degeneration.pieces 1).zero_mem
  · exact Degeneration.X_mem 0
  · exact Degeneration.X_mem 1
  · exact Degeneration.X_mem 2
  · exact Degeneration.X_mem 3
  · exact Degeneration.X_mem 4
lemma red_monomial_mem (s : B) (r : A) (i : ℤ) (hs : embedding s=T i*c r) :
    red s ∈ Degeneration.pieces i := by
  apply red_graded
  apply GradedMap.reflect (k := ℂ) (R := B) (S := L) pieces laurentPieces embedding embedding_injective embedding_graded
  rw [hs,mul_comm (T i : L) (c r)]
  exact laurentMonomial_mem _ _
end ComplexCancellation.Rees

end

end OAI
