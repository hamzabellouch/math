import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.Structure.RectangleGenerators

namespace OAI

noncomputable section
namespace SiegelZeros.W23
open Result.Workers.W57

section Nilpotence
variable (K : Type*) [CommRing K]

def jetConstant (n : ℕ) : K →+* Jet K n :=
  (jetProjection K n).comp PowerSeries.C

theorem jet_coordinate_nilpotent (n : ℕ) :
    IsNilpotent (jetProjection K n PowerSeries.X) := by
  refine ⟨n, ?_⟩
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

theorem jet_nilpotent_sub_constant (n : ℕ) (f : PowerSeries K) :
    IsNilpotent (jetProjection K n f - jetConstant K n (PowerSeries.coeff 0 f)) := by
  have hdiv : PowerSeries.X ∣ f - PowerSeries.C (PowerSeries.coeff 0 f) := by
    apply PowerSeries.X_dvd_iff.mpr
    rw [map_sub, PowerSeries.constantCoeff_C,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, sub_self]
  obtain ⟨g, hg⟩ := hdiv
  change IsNilpotent (jetProjection K n f - jetProjection K n (PowerSeries.C _))
  rw [← map_sub, hg, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right (jet_coordinate_nilpotent K n)

theorem jet_nilpotent_transfer (n : ℕ) (f : PowerSeries K) (u : K)
    (h : IsNilpotent (PowerSeries.coeff 0 f - u)) :
    IsNilpotent (jetProjection K n f - jetConstant K n u) := by
  have h₀ := jet_nilpotent_sub_constant K n f
  have h₁ := h.map (jetConstant K n)
  rw [map_sub] at h₁
  have hsum := (Commute.all _ _).isNilpotent_add h₀ h₁
  convert hsum using 1
  ring

def rectangleConstant (a b c : ℕ) : K →+* RectangleJet K a b c :=
  (jetConstant (Jet (Jet K c) b) a).comp
    ((jetConstant (Jet K c) b).comp (jetConstant K c))

theorem rectangle_nilpotent_sub_constant (a b c : ℕ) (f : Series₃ K) :
    IsNilpotent (rectangleProjection K a b c f - rectangleConstant K a b c
      (PowerSeries.coeff 0 (PowerSeries.coeff 0 (PowerSeries.coeff 0 f)))) := by
  unfold rectangleProjection rectangleConstant
  simp only [RingHom.comp_apply]
  apply jet_nilpotent_transfer
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
  apply jet_nilpotent_transfer
  rw [PowerSeries.coeff_map]
  exact jet_nilpotent_sub_constant K c _

end Nilpotence

section Taylor
variable {R K L : Type*} [CommRing R] [CommRing K] [CommRing L]
  [Algebra ℚ R]

theorem rectangularJetHom_nilpotent_correction
    (D₁ D₂ D₃ : Derivation ℚ R R) (ρ : R →+* K) (a b c : ℕ) (f : R) :
    IsNilpotent (rectangularJetHom K D₁ D₂ D₃ ρ a b c f -
      rectangleConstant K a b c (ρ f)) := by
  have h := rectangle_nilpotent_sub_constant K a b c
    (PowerSeries.map (PowerSeries.map (PowerSeries.map ρ)) (taylorHom₃ D₁ D₂ D₃ f))
  simpa only [rectangularJetHom, RingHom.comp_apply, PowerSeries.coeff_map,
    coeff_taylorHom₃, iter_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, one_smul] using h

theorem rectangularJetHom_isUnit
    (D₁ D₂ D₃ : Derivation ℚ R R) (ρ : R →+* K) (a b c : ℕ) (f : R)
    (hf : IsUnit (ρ f)) : IsUnit (rectangularJetHom K D₁ D₂ D₃ ρ a b c f) := by
  have hn := rectangularJetHom_nilpotent_correction D₁ D₂ D₃ ρ a b c f
  have h := hn.isUnit_add_left_of_commute
    (hf.map (rectangleConstant K a b c)) (Commute.all _ _)
  simpa using h

def localizedRectangularJet (M : Submonoid R) [Algebra R L] [IsLocalization M L]
    (D₁ D₂ D₃ : Derivation ℚ R R) (ρ : R →+* K) (a b c : ℕ)
    (hρ : ∀ s : M, IsUnit (ρ s)) : L →+* RectangleJet K a b c :=
  IsLocalization.lift (S := L)
    (fun s : M => rectangularJetHom_isUnit D₁ D₂ D₃ ρ a b c s (hρ s))

@[simp] theorem localizedRectangularJet_algebraMap (M : Submonoid R)
    [Algebra R L] [IsLocalization M L] (D₁ D₂ D₃ : Derivation ℚ R R)
    (ρ : R →+* K) (a b c : ℕ) (hρ : ∀ s : M, IsUnit (ρ s)) (f : R) :
    localizedRectangularJet M D₁ D₂ D₃ ρ a b c hρ (algebraMap R L f) =
      rectangularJetHom K D₁ D₂ D₃ ρ a b c f :=
  IsLocalization.lift_eq _ f

variable [Algebra ℚ K]

theorem localized_generator_span_le_ker (M : Submonoid R)
    [Algebra R L] [IsLocalization M L] (D₁ D₂ D₃ : Derivation ℚ R R)
    (ρ : R →+* K) (a b c : ℕ) (hρ : ∀ s : M, IsUnit (ρ s))
    (generators : Set R)
    (hgen : ∀ f ∈ generators, ∀ i < a, ∀ j < b, ∀ k < c,
      ρ (iter D₃ k (iter D₂ j (iter D₁ i f))) = 0) :
    Ideal.span (algebraMap R L '' generators) ≤
      RingHom.ker (localizedRectangularJet M D₁ D₂ D₃ ρ a b c hρ) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨f, hf, rfl⟩
  apply RingHom.mem_ker.mpr
  rw [localizedRectangularJet_algebraMap]
  exact rectangularJetHom_eq_zero K D₁ D₂ D₃ ρ a b c f (hgen f hf)

def localizedGeneratorQuotient (M : Submonoid R)
    [Algebra R L] [IsLocalization M L] (D₁ D₂ D₃ : Derivation ℚ R R)
    (ρ : R →+* K) (a b c : ℕ) (hρ : ∀ s : M, IsUnit (ρ s))
    (generators : Set R)
    (hgen : ∀ f ∈ generators, ∀ i < a, ∀ j < b, ∀ k < c,
      ρ (iter D₃ k (iter D₂ j (iter D₁ i f))) = 0) :
    L ⧸ Ideal.span (algebraMap R L '' generators) →+* RectangleJet K a b c :=
  Ideal.Quotient.lift _ (localizedRectangularJet M D₁ D₂ D₃ ρ a b c hρ)
    (fun _ hf => RingHom.mem_ker.mp
      (localized_generator_span_le_ker M D₁ D₂ D₃ ρ a b c hρ generators hgen hf))

end Taylor
end SiegelZeros.W23

end

end OAI
