import OAI.NumberTheory.SiegelZeros.Differentials.SelectedCotangent
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.RectangularLocalization

namespace OAI

namespace SiegelZeros

noncomputable section
namespace W23
open Result.Workers.W57 WeightedTorusJets.W19 WeightedTorusJets.W18

variable {R K L : Type*} [CommRing R] [CommRing K] [CommRing L]
  [Algebra ℚ R] [Algebra ℚ K] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L]

def localRectangleIdeal (D : Fin 3 → Derivation ℚ R R)
    (t : Fin 3 → ℕ) (b : ℕ) (f : R) : Ideal L :=
  Ideal.span (algebraMap R L '' rectangleGenerators D t b f)

omit [Algebra ℚ L] [IsScalarTower ℚ R L] in
theorem localRectangleIdeal_le_ker (M : Submonoid R) [IsLocalization M L]
    (D : Fin 3 → Derivation ℚ R R)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap)
    (ρ : R →+* K) (t : Fin 3 → ℕ) (b : ℕ) (f : R)
    (hρ : ∀ s : M, IsUnit (ρ s))
    (hnext : ∀ u ∈ rectangleGenerators D t (b+1) f, ρ u = 0) :
    localRectangleIdeal (L := L) D t b f ≤ RingHom.ker
      (localizedRectangularJet M (D 0) (D 1) (D 2) ρ
        (t 0+1) (t 1+1) (t 2+1) hρ) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨g, hg, rfl⟩
  apply RingHom.mem_ker.mpr
  rw [localizedRectangularJet_algebraMap]
  exact rectangularJetHom_generator_eq_zero D hD ρ t b f g hnext hg

def sourceTaylorFactorization (M : Submonoid R) [IsLocalization M L]
    (D : Fin 3 → Derivation ℚ R R)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap)
    (ρ : R →+* K) (t : Fin 3 → ℕ) (b : ℕ) (f : R)
    (hρ : ∀ s : M, IsUnit (ρ s))
    (hnext : ∀ u ∈ rectangleGenerators D t (b+1) f, ρ u = 0) :
    L ⧸ localRectangleIdeal D t b f →+*
      RectangleJet K (t 0+1) (t 1+1) (t 2+1) :=
  Ideal.Quotient.lift _
    (localizedRectangularJet M (D 0) (D 1) (D 2) ρ (t 0+1) (t 1+1) (t 2+1) hρ)
    (fun _ hx => RingHom.mem_ker.mp (localRectangleIdeal_le_ker M D hD ρ t b f hρ hnext hx))

theorem iter_localizedDerivation_algebraMap (M : Submonoid R) [IsLocalization M L]
    (D : Derivation ℚ R R) (n : ℕ) (f : R) :
    iter (localizedDerivation (S := L) M D) n (algebraMap R L f) =
      algebraMap R L (iter D n f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ, ih, localizedDerivation_algebraMap, iter_succ]

theorem localizedRectangularJet_eq_localTaylor (M : Submonoid R)
    [IsLocalization M L] (D₁ D₂ D₃ : Derivation ℚ R R)
    (ρ : R →+* K) (a b c : ℕ) (hρ : ∀ s : M, IsUnit (ρ s)) :
    localizedRectangularJet (L := L) M D₁ D₂ D₃ ρ a b c hρ =
      rectangularJetHom K (localizedDerivation (S := L) M D₁)
        (localizedDerivation (S := L) M D₂) (localizedDerivation (S := L) M D₃)
        (IsLocalization.lift (S := L) hρ) a b c := by
  apply IsLocalization.ringHom_ext M
  ext f
  simp only [RingHom.comp_apply, localizedRectangularJet_algebraMap]
  unfold rectangularJetHom
  simp only [RingHom.comp_apply]
  congr 1
  ext i j k
  simp only [PowerSeries.coeff_map, coeff_taylorHom₃, map_rat_smul,
    iter_localizedDerivation_algebraMap, IsLocalization.lift_eq]

end W23

end

end SiegelZeros

end OAI
