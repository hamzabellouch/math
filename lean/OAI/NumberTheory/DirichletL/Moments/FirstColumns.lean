import OAI.NumberTheory.DirichletL.Moments.FirstNormalization
import OAI.NumberTheory.DirichletL.Moments.FixedRay
import OAI.NumberTheory.DirichletL.Moments.ChildAssembly

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstColumns
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

def leftCoefficient (e r : O) (ρ : O → ℂ) (a : O) : ℂ :=
  idealRowHom (e*r) (Ideal.span {a})*ρ a

def rightCoefficient (e r : O) (ρ : O → ℂ) (b : O) : ℂ :=
  idealRowHom (e*r) (Ideal.span {b})*star (ρ b)

theorem first_phase_columns (e r a b : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hpb : ConcretePrimeRowBridge.goodLambda^2∣b-1) (hab : IsCoprime a b) :
    (idealRowHom e (Ideal.span {a})*star (idealRowHom e (Ideal.span {b}))*ρ e)*
      (idealRowHom (b*r) (Ideal.span {a})*star (idealRowHom (a*r) (Ideal.span {b}))*ρ (a*b)) =
      ρ e*sexticReciprocityPhase a b*leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero a ha)
  let : Fintype (CenteredMomentCommonSupport.Residue a) := Fintype.ofFinite _
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero b hb)
  let : Fintype (CenteredMomentCommonSupport.Residue b) := Fintype.ofFinite _
  have hp := supported_opposite_phase b a hb ha hpb hpa hab.symm
  rw [sexticReciprocityPhase_symm b a] at hp
  calc
    _ = ρ e*(idealRowHom b (Ideal.span {a})*star (idealRowHom a (Ideal.span {b})))*
        leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
      simp only [leftCoefficient,rightCoefficient,idealRowHom_argument_mul,hρ,star_mul,star_star]
      ring
    _ = _ := by rw [hp]

def firstPhaseTable (r s : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign (QuadraticGaussRay.residueQuotientFour r)
    (QuadraticGaussRay.residueQuotientFour s):ℂ)

theorem firstPhaseTable_mk (a b : O) :
    firstPhaseTable (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)=sexticReciprocityPhase a b := by
  simp only [firstPhaseTable,QuadraticGaussRay.residueQuotientFour_mk,sexticReciprocityPhase]

theorem firstPhaseTable_expansion (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a b=∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*rayCharacter χ a*rayCharacter ξ b := by
  have hh := pair_phase_expansion firstPhaseTable a b
  simpa only [supported_rayMask a ha,supported_rayMask b hb,one_mul,firstPhaseTable_mk] using hh

theorem firstPhaseTable_mass :
    (∑ χ : RayCharacter,∑ ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖)≤256 := by
  have hb : ∀ u v : RayRingˣ,‖firstPhaseTable u v‖≤1 := by
    intro u v
    unfold firstPhaseTable QuadraticAllOddCRT.quadraticRaySign
    split_ifs <;> norm_num
  simpa only [mul_one] using pairCoeff_sum_norm_le firstPhaseTable 1 hb

def firstExtension (e r : O) (ρ : O → ℂ) (a b : O) : ℂ :=
  ρ e*sexticReciprocityPhase a b*leftCoefficient e r ρ a*star (rightCoefficient e r ρ b)

theorem firstExtension_separated (e r a b : O) (ρ : O → ℂ)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    firstExtension e r ρ a b=ρ e*∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*(leftCoefficient e r ρ a*rayCharacter χ a)*
        star (rightCoefficient e r ρ b*rayCharacter (ξ⁻¹) b) := by
  unfold firstExtension
  rw [firstPhaseTable_expansion a b ha hb]
  simp only [Finset.mul_sum,Finset.sum_mul,star_mul,CenteredMomentChildAssembly.rayCharacter_inverse_star]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ξ hξ
  ring

end SevenEighths.CenteredMomentFirstColumns

end

end OAI
