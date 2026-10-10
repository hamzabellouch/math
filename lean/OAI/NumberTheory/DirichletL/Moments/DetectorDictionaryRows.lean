import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
import OAI.NumberTheory.DirichletL.Detector.DetectorMomentData

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ψ : Character) (m u : O) (reverse : Bool)
    (hrow : ∀n,elementCoeff ψ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (1*u) n)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then conj (idealCoeff ψ I) else idealCoeff ψ I)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hMm : M≤Ideal.span {m})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η m 1 u
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  rw [positiveSlotRow_eq_product η ψ m 1 u hrow _ _ _ _ P _ _ _ _ hX₁ hX₂ hP]
  simp only [norm_mul,norm_prod]
  rw [norm_of_oriented_coefficients χ ψ reverse hc false W₁ X₁ σ t hX₁,
    norm_of_oriented_coefficients χ ψ reverse hc false W₂ X₂ σ t hX₂]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [physical_slot_conj M H η m u hmLam hMm (V i) (b i) (P i) (external i) (hP i) (hη i),RCLike.norm_conj]

theorem momentData_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then
      conj (idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
      else idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
    (hMm : M≤Ideal.span {ProbeHighRowFamily.rowMaskElement})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η ProbeHighRowFamily.rowMaskElement 1 u.val
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  apply source_plain_pair_norm M H η χ
    ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u))
    ProbeHighRowFamily.rowMaskElement u.val reverse _ hc (dvd_mul_left _ _) hMm
    W₁ W₂ V b P external X₁ X₂ σ t hX₁ hX₂ hP hη
  intro n
  simpa only [ProbeHighRowFamily.momentData,ProbeHighRowFamily.momentElement,one_mul] using
    (ProbeHighRowFamily.momentData η).character_spec (ProbeHighRowFamily.momentElement u) n

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
