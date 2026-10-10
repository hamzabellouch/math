import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalH1

namespace OAI

/-!
# The Sobolev density input for conditional estimates

N. G. Meyers and J. Serrin, *H = W*, Proc. Natl. Acad. Sci. USA 51 (1964),
1055–1056, DOI 10.1073/pnas.51.6.1055, Theorem and the Lemma on p.1056.
We use only m=1, p=2 on the full Euclidean configuration space. The finite
spin index is handled componentwise. This is smooth approximation in the
value-and-weak-gradient norm; no compact support or Coulomb-form comparison
is included in the assumption.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

/-- Squared error in the actual value-and-gradient graph. -/
def h1GraphError {n : ℕ} (u v : Coulomb.H1Vector n) : ℝ :=
  (∑ s, ∫ x, ‖u.value s x - v.value s x‖ ^ 2) +
    ∑ s, ∑ a, ∫ x, ‖u.gradient s a x - v.gradient s a x‖ ^ 2

theorem h1GraphError_nonnegative {n : ℕ} (u v : Coulomb.H1Vector n) :
    0 ≤ h1GraphError u v := by
  unfold h1GraphError
  apply add_nonneg
  · exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  · exact Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

/-- The precise specialization of the published H=W theorem. -/
def PublishedSobolevSmoothDensity : Prop :=
  ∀ (n : ℕ) (u : Coulomb.H1Vector n) (ε : ℝ), 0 < ε →
    ∃ (f : SpinConfiguration n → Configuration n → ℂ)
      (hf : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (f s))
      (hL2 : ∀ s, MemLp (f s) 2)
      (hpartial : ∀ s a, MemLp
        (fun x => fderiv ℝ (f s) x (EuclideanSpace.single a 1)) 2),
      h1GraphError u (classicalH1State f (fun s => (hf s).of_le (by simp)) hL2 hpartial) < ε

/-- A convenient actual-H1 version, preserving the published input explicitly. -/
theorem exists_smooth_h1_approximation (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (u : Coulomb.H1Vector n) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ (⊤ : ℕ∞) (v.value s)) ∧
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) ∧
      h1GraphError u v < ε := by
  obtain ⟨f, hf, hL2, hpartial, he⟩ := hpublished n u ε hε
  exact ⟨classicalH1State f (fun s => (hf s).of_le (by simp)) hL2 hpartial,
    hf, fun _ _ _ => rfl, he⟩

end ContinuumCoulomb

end

end OAI
