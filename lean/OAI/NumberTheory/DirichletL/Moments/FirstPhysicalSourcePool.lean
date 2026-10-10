import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy
open CenteredMomentFirstSectorTransform CenteredMomentFirstChildProfile
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeExpansion RayFourExpansion
local notation "O"=>ActualEisensteinCubic.O

theorem original_pool_restriction (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (S:Finset (Ideal O))(f:Ideal O→Ideal O→ℂ):
    (∑a∈residualPool C hC (supportedColumns S),∑b∈residualPool D hD (supportedColumns S),
      if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then f a b else 0)=
    ∑a:columns C C hC S,∑b:columns C D hD S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then f a b else 0:=by
  rw [Finset.sum_coe_sort (columns C C hC S)
    (fun a:Ideal O=>∑b:columns C D hD S,if IsCoprime a (b:Ideal O) then f a b else 0)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hca:IsCoprime C a
  · simp only [hca,true_and,ite_true]
    rw [Finset.sum_coe_sort _ (fun b:Ideal O=>if IsCoprime a b then f a b else 0),Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hcb:IsCoprime C b <;> simp [hcb]
  · simp [hca]

theorem actual_child_family (η:Character)(m:O)(hm:m≠0)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (ξ₁ ξ₂:RayCharacter):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let r:=activeConductor C D;
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D);
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀S:Finset (Ideal O),∀c:Ideal O→ℂ,∀t:ℝ,∀L:Ideal O,∀a:columns C C hC.1 S,
        divisorCoefficient L (element C C hC.1 S)
          (fun a=>coefficient η m 1 t c C a*leftCoefficient e r ρ (element C C hC.1 S a)) ξ₁ a=
          (if L∣(a:Ideal O) then c (C*a) else 0)*heightCoeff τ₁ t a) ∧
      (∀S:Finset (Ideal O),∀c:Ideal O→ℂ,∀t:ℝ,∀L:Ideal O,∀b:columns C D hD.1 S,
        divisorCoefficient L (element C D hD.1 S)
          (fun b=>coefficient η m 1 t c D b*rightCoefficient e r ρ (element C D hD.1 S b)) ξ₂ b=
          (if L∣(b:Ideal O) then c (D*b) else 0)*heightCoeff τ₂ t b):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=exists_first_divisor_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro S c t L a
    exact h₁ L a (column_supported C C hC.1 S a) (fun I=>c (C*I)) t
  · intro S c t L b
    exact h₂ L b (column_supported C D hD.1 S b) (fun I=>c (D*I)) t

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
