import Mathlib.RingTheory.Ideal.Quotient.Operations
import OAI.NumberTheory.SiegelZeros.Structure.RectangleGenerators

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace Result.Workers.W57
variable (K : Type*) [CommRing K]

def jetCoeff (n i : ℕ) (hi : i < n) : Jet K n →ₗ[K] K :=
  ((truncationIdeal K n).restrictScalars K).liftQ (PowerSeries.coeff i)
    (by
      intro f hf
      change PowerSeries.coeff i f = 0
      have hdiv : (PowerSeries.X : PowerSeries K)^n ∣ f :=
        Ideal.mem_span_singleton.mp hf
      exact PowerSeries.X_pow_dvd_iff.mp hdiv i hi)

@[simp] theorem jetCoeff_projection (n i : ℕ) (hi : i < n) (f : PowerSeries K) :
    jetCoeff K n i hi (jetProjection K n f) = PowerSeries.coeff i f := rfl

def jetResidue (n : ℕ) (hn : 0 < n) : Jet K n →+* K :=
  Ideal.Quotient.lift (truncationIdeal K n) PowerSeries.constantCoeff
    (by
      intro f hf
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact PowerSeries.X_pow_dvd_iff.mp (Ideal.mem_span_singleton.mp hf) 0 hn)

@[simp] theorem jetResidue_projection (n : ℕ) (hn : 0 < n) (f : PowerSeries K) :
    jetResidue K n hn (jetProjection K n f) = PowerSeries.coeff 0 f := by
  exact (PowerSeries.coeff_zero_eq_constantCoeff_apply f).symm

def rectangleCoeff (a b c i j k : ℕ) (hi : i<a) (hj : j<b) (hk : k<c) :
    RectangleJet K a b c →+ K :=
  (jetCoeff K c k hk).toAddMonoidHom.comp
    ((jetCoeff (Jet K c) b j hj).toAddMonoidHom.comp
      (jetCoeff (Jet (Jet K c) b) a i hi).toAddMonoidHom)

@[simp] theorem rectangleCoeff_projection (a b c i j k : ℕ)
    (hi : i<a) (hj : j<b) (hk : k<c) (f : Series₃ K) :
    rectangleCoeff K a b c i j k hi hj hk (rectangleProjection K a b c f) =
      PowerSeries.coeff k (PowerSeries.coeff j (PowerSeries.coeff i f)) := by
  simp only [rectangleCoeff, rectangleProjection, RingHom.comp_apply,
    AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    jetCoeff_projection, PowerSeries.coeff_map]

def rectangleResidue (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    RectangleJet K a b c →+* K :=
  (jetResidue K c hc).comp
    ((jetResidue (Jet K c) b hb).comp (jetResidue (Jet (Jet K c) b) a ha))

@[simp] theorem rectangleResidue_projection (a b c : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (f : Series₃ K) :
    rectangleResidue K a b c ha hb hc (rectangleProjection K a b c f) =
      PowerSeries.coeff 0 (PowerSeries.coeff 0 (PowerSeries.coeff 0 f)) := by
  simp only [rectangleResidue, rectangleProjection, RingHom.comp_apply,
    jetResidue_projection, PowerSeries.coeff_map]

variable {R : Type*} [CommRing R] [Algebra ℚ R]

variable [Algebra ℚ K] in
theorem rectangleCoeff_taylor (D₁ D₂ D₃ : Derivation ℚ R R) (ρ : R →+* K)
    (a b c i j k : ℕ) (hi : i<a) (hj : j<b) (hk : k<c) (f : R) :
    rectangleCoeff K a b c i j k hi hj hk
      (rectangularJetHom K D₁ D₂ D₃ ρ a b c f) =
      (1 / (k.factorial : ℚ)) • ((1 / (j.factorial : ℚ)) •
        ((1 / (i.factorial : ℚ)) • ρ (iter D₃ k (iter D₂ j (iter D₁ i f))))) := by
  simp only [rectangularJetHom, RingHom.comp_apply, rectangleCoeff_projection,
    PowerSeries.coeff_map, coeff_taylorHom₃, map_rat_smul]

@[simp] theorem rectangleResidue_taylor (D₁ D₂ D₃ : Derivation ℚ R R) (ρ : R →+* K)
    (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (f : R) :
    rectangleResidue K a b c ha hb hc (rectangularJetHom K D₁ D₂ D₃ ρ a b c f) =
      ρ f := by
  simp only [rectangularJetHom, RingHom.comp_apply, rectangleResidue_projection,
    PowerSeries.coeff_map, coeff_taylorHom₃, iter_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_smul]

def rectangleAugmentation (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    Ideal (RectangleJet K a b c) := RingHom.ker (rectangleResidue K a b c ha hb hc)

theorem ideal_le_augmentation_comap (D₁ D₂ D₃ : Derivation ℚ R R)
    (ρ : R →+* K) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (I : Ideal R) (hI : I ≤ RingHom.ker ρ) :
    I ≤ (rectangleAugmentation K a b c ha hb hc).comap
      (rectangularJetHom K D₁ D₂ D₃ ρ a b c) := by
  intro f hf
  change rectangleResidue K a b c ha hb hc
    (rectangularJetHom K D₁ D₂ D₃ ρ a b c f) = 0
  rw [rectangleResidue_taylor]
  exact hI hf

end Result.Workers.W57

end

end

end SiegelZeros

end OAI
