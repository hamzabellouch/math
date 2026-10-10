import OAI.Combinatorics.BalancedRyser.Profiles.PoissonProfile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileVisibilityConcrete

namespace OAI

open MeasureTheory

namespace Balanced.NearCoverVisibility

theorem visible_excess_of_row_moments
    (P : Profile) (νD νC : Measure Profile)
    [IsFiniteMeasure νD] [IsFiniteMeasure νC] {k μ c δ : ℝ}
    (hμ : 0 < μ) (hδ : 0 < δ) (hc : c ≤ 1)
    (hmassD : νD.real Set.univ = k) (hmassC : νC.real Set.univ = c)
    (hincD : ∀ i j : ℕ, (∫ x : Profile, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hincC : (∫ x : Profile, x (0, 1) ∂νC) = P (0, 1))
    (hcorner : P (0, 0) = 0) (hPnonneg : ∀ j, 0 ≤ P (0, j))
    (hrow : HasSum (fun j : ℕ => P (0, j)) μ)
    (hmoment : HasSum (fun j : ℕ => (j : ℝ) * P (0, j)) (c * μ))
    (huncovered : δ ≤ ∑' i : ℕ, P (i, 0))
    (hf : Integrable (fun x : Profile => x (0, 1)) νC)
    (hsupport : ∀ᵐ x ∂νC, (∀ j, 0 ≤ x (0, j)) ∧
      Summable (fun j : ℕ => x (0, j)) ∧ (∑' j : ℕ, x (0, j)) = μ) :
    c < νD.real (deletionVisible P) + νC.real (coverVisible P) := by
  obtain ⟨hc1, hp01, _⟩ := PoissonProfile.row_rigidity
    (fun j => P (0, j)) μ c hμ hc hPnonneg hcorner hrow hmoment
  have hreal : νC.real Set.univ = 1 := hmassC.trans hc1
  have hprob : IsProbabilityMeasure νC := by
    apply isProbabilityMeasure_iff.mpr
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top νC Set.univ) ENNReal.one_ne_top).mp
    simpa only [measureReal_def, ENNReal.toReal_one] using hreal
  let : IsProbabilityMeasure νC := hprob
  have hupper : ∀ᵐ x ∂νC, x (0, 1) ≤ μ := by
    filter_upwards [hsupport] with x hx
    rw [← hx.2.2]
    exact le_hasSum hx.2.1.hasSum 1 (fun j _ => hx.1 j)
  rw [hc1]
  exact ProfileVisibility.visible_excess_of_cover_saturation P νD νC
    hmassD hincD hcorner (lt_of_lt_of_le hδ huncovered) hμ hf hupper
    (hincC.trans hp01)

def NearCoverClass (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) : ProfileClass :=
  fun F _ _ _ D C =>
    IsProfilePair k D C ∧
    CoversPoints C (uncoveredBy D) ∧
    δ * (Fintype.card F : ℝ) ^ 2 ≤ ((uncoveredBy C).card : ℝ) ∧
    deletionMultiplicityTV k D ≤ ε (Fintype.card F) ∧
    ((exceptionalOccupancyLines k (ε (Fintype.card F)) D).card : ℝ) ≤
      ε (Fintype.card F) * (Fintype.card F : ℝ)

theorem nearCoverClass_valid (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) :
    ProfileClassValid k (NearCoverClass k δ ε) := by
  intro F _ _ _ D C h
  exact h.1

theorem nearCoverClass_badCoreCover (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {D C : Finset (Line F)} (h : NearCoverClass k δ ε F D C) :
    BadCoreCover δ D := by
  exact ⟨C, h.1.2.1.symm, h.1.2.2, h.2.1, h.2.2.1⟩

theorem nearCoverClass_of_badCoreCover (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {D : Finset (Line F)} (hD : IsDeletionSet k D) (hbad : BadCoreCover δ D)
    (hTV : deletionMultiplicityTV k D ≤ ε (Fintype.card F))
    (hocc : ((exceptionalOccupancyLines k (ε (Fintype.card F)) D).card : ℝ) ≤
      ε (Fintype.card F) * (Fintype.card F : ℝ)) :
    ∃ C, NearCoverClass k δ ε F D C := by
  obtain ⟨C, hdisj, hcard, hcover, hmiss⟩ := hbad
  exact ⟨C, ⟨hD, hdisj.symm, hcard⟩, hcover, hmiss, hTV, hocc⟩

end Balanced.NearCoverVisibility

end OAI
