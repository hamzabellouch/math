import OAI.Algebra.AffineCancellation.Degeneration

namespace OAI

noncomputable section

namespace ComplexCancellation.Degeneration
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def weight (i : Fin 5) : ℤ := if i=0 then -1 else if i=1 ∨ i=2 then 0 else 2
def sourcePieces (e : ℤ) := weightedHomogeneousSubmodule ℂ weight e
instance sourceGrading : GradedAlgebra sourcePieces := inferInstanceAs (GradedAlgebra (weightedHomogeneousSubmodule ℂ weight))
lemma xp_homogeneous : IsWeightedHomogeneous weight xp 0 := by
  have h₁ : IsWeightedHomogeneous weight ((X 1 : P)^2) 0 := by
    convert (isWeightedHomogeneous_X ℂ weight 1).pow 2 using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₂ : IsWeightedHomogeneous weight ((X 2 : P)^3) 0 := by
    convert (isWeightedHomogeneous_X ℂ weight 2).pow 3 using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₃ : IsWeightedHomogeneous weight ((X 0 : P)^2*X 3) 0 := by
    convert ((isWeightedHomogeneous_X ℂ weight 0).pow 2).mul (isWeightedHomogeneous_X ℂ weight 3) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  exact (h₁.add h₂).add h₃
lemma relation_homogeneous : relation ∈ sourcePieces 2 := by
  have h₁ : IsWeightedHomogeneous weight (xp^2*X 3) 2 := by
    convert (xp_homogeneous.pow 2).mul (isWeightedHomogeneous_X ℂ weight 3) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₂ : IsWeightedHomogeneous weight (1+2*X 1*xp : P) 0 := by
    apply (isWeightedHomogeneous_one ℂ weight).add
    convert ((isWeightedHomogeneous_C weight (2:ℂ)).mul (isWeightedHomogeneous_X ℂ weight 1)).mul xp_homogeneous using 1 <;> try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₃ : IsWeightedHomogeneous weight ((1+2*X 1*xp)*X 4 : P) 2 := by
    convert h₂.mul (isWeightedHomogeneous_X ℂ weight 4) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₄ : IsWeightedHomogeneous weight (X 0^2*X 4^2 : P) 2 := by
    convert ((isWeightedHomogeneous_X ℂ weight 0).pow 2).mul ((isWeightedHomogeneous_X ℂ weight 4).pow 2) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  exact (h₁.sub h₃).sub h₄
lemma kernel_homogeneous : (RingHom.ker π).IsHomogeneous sourcePieces := by
  change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {relation}))).IsHomogeneous _
  rw [Ideal.mk_ker]
  apply Ideal.homogeneous_span
  intro r hr
  obtain rfl := Set.mem_singleton_iff.mp hr
  exact ⟨2,relation_homogeneous⟩
def pieces : ℤ → Submodule ℂ G := QuotientGrading.pieces sourcePieces π
instance grading : GradedAlgebra pieces := QuotientGrading.grading _ _ (Ideal.Quotient.mkₐ_surjective ℂ _) kernel_homogeneous
lemma X_mem (i : Fin 5) : π (X i) ∈ pieces (weight i) := ⟨X i,isWeightedHomogeneous_X ℂ weight i,rfl⟩
end ComplexCancellation.Degeneration

end

end OAI
