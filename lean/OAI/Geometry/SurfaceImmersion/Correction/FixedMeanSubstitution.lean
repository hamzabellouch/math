import OAI.Geometry.SurfaceImmersion.Correction.UniformFiniteMean

namespace OAI

/-! Finite mean correction for one fixed operator with derivative loss.
The smallness threshold is uniform in the operator; no infinite-dimensional
inverse or convergence of a derivative-losing iteration is asserted. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def rescaledMean (η : ℝ) (A : (E → F) → E → F) (θ : ℝ) (f : E → F) : E → F :=
  (θ / η) • A f

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma rescaledMean_self {η : ℝ} (hη : η ≠ 0) (A : (E → F) → E → F) :
    rescaledMean η A η = A := by
  funext f
  simp only [rescaledMean, div_self hη, one_smul]

lemma rescaledMean_bounds {U : Set E} (hU : UniqueDiffOn ℝ U) {s : ℝ}
    {reference : E → F} {r η : ℝ} {L : ℕ} (hη : 0 < η)
    (A : (E → F) → E → F) (B K : ℕ → ℝ → ℝ)
    (hB : ∀ m C, 1 ≤ C → 1 ≤ B m C) (hK : ∀ m C, 1 ≤ C → 1 ≤ K m C)
    (hsm : ∀ f, ContDiffOn ℝ ∞ f U → InTrialBall U reference r f → ContDiffOn ℝ ∞ (A f) U)
    (hv : ∀ m C f, 1 ≤ C → ContDiffOn ℝ ∞ f U → InTrialBall U reference r f →
      WeightedBound U s (m + L) C f → WeightedBound U s m (η * B m C) (A f))
    (hd : ∀ m C D f g, 1 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      InTrialBall U reference r f → InTrialBall U reference r g →
      WeightedBound U s (m + L) C f → WeightedBound U s (m + L) C g →
      WeightedBound U s (m + L) D (f - g) →
      WeightedBound U s m (K m C * η * D) (A f - A g)) :
    MeanBounds U s reference r L (rescaledMean η A) B K := by
  refine ⟨hB, hK, ?_, ?_, ?_⟩
  · intro θ _ _ f hf hb
    exact (hsm f hf hb).const_smul (θ / η)
  · intro θ hθ _ m C f hC hf hb hbf
    have hh := (hv m C f hC hf hb hbf).const_smul hU (hsm f hf hb) (θ / η)
    change WeightedBound U s m _ (rescaledMean η A θ f) at hh
    convert hh using 1
    rw [abs_of_pos (div_pos hθ hη)]
    field_simp
  · intro θ hθ _ m C D f g hC hD hf hg hb hc hbf hbg hbd
    have hh := (hd m C D f g hC hD hf hg hb hc hbf hbg hbd).const_smul hU
      ((hsm f hf hb).sub (hsm g hg hc)) (θ / η)
    have he : (θ / η) • (A f - A g) = rescaledMean η A θ f - rescaledMean η A θ g :=
      smul_sub _ _ _
    change WeightedBound U s m _ ((θ / η) • (A f - A g)) at hh
    rw [he] at hh
    convert hh using 1
    rw [abs_of_pos (div_pos hθ hη)]
    field_simp

/-- The actual finite sequence depends only on the fixed mean operator. -/
def fixedTrial (H : E → F) (A : (E → F) → E → F) (j : ℕ) : E → F :=
  trial H (fun _ => A) 1 j

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma trial_rescaledMean {η : ℝ} (hη : η ≠ 0)
    (H : E → F) (A : (E → F) → E → F) (j : ℕ) :
    trial H (rescaledMean η A) η j = fixedTrial H A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change H - rescaledMean η A η (trial H (rescaledMean η A) η j) =
      H - A (fixedTrial H A j)
    rw [rescaledMean_self hη, ih]

/-- A fixed operator with an O(η) value bound and an O(η) finite-loss
Lipschitz bound admits any prescribed finite number of substitutions. -/
theorem fixed_mean_substitution {U : Set E} (hU : UniqueDiffOn ℝ U) {s : ℝ} (hs : 0 ≤ s)
    {reference H : E → F} {r0 r1 : ℝ} (hgap : r0 < r1) {L : ℕ}
    {B K : ℕ → ℝ → ℝ} (hB : ∀ m C, 1 ≤ C → 1 ≤ B m C)
    (hK : ∀ m C, 1 ≤ C → 1 ≤ K m C)
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (hH : ContDiffOn ℝ ∞ H U)
    (hH0 : ∀ p ∈ U, ‖H p - reference p‖ ≤ r0)
    (hbH : ∀ m, WeightedBound U s m (C m) H) (n : ℕ) :
    ∃ η0 : ℝ, 0 < η0 ∧ η0 ≤ 1 ∧ ∀ η, 0 < η → η ≤ η0 →
      ∀ A : (E → F) → E → F,
      (∀ f, ContDiffOn ℝ ∞ f U → InTrialBall U reference r1 f → ContDiffOn ℝ ∞ (A f) U) →
      (∀ m C f, 1 ≤ C → ContDiffOn ℝ ∞ f U → InTrialBall U reference r1 f →
        WeightedBound U s (m + L) C f → WeightedBound U s m (η * B m C) (A f)) →
      (∀ m C D f g, 1 ≤ C → 0 ≤ D →
        ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
        InTrialBall U reference r1 f → InTrialBall U reference r1 g →
        WeightedBound U s (m + L) C f → WeightedBound U s (m + L) C g →
        WeightedBound U s (m + L) D (f - g) →
        WeightedBound U s m (K m C * η * D) (A f - A g)) →
      ∀ j ≤ n, ContDiffOn ℝ ∞ (fixedTrial H A j) U ∧
        InTrialBall U reference r1 (fixedTrial H A j) ∧
        (∀ m, WeightedBound U s m (sizeBound L C B j m) (fixedTrial H A j)) ∧
        (∀ m, WeightedBound U s m (differenceBound L C B K j m * η ^ (j + 1))
          (fixedTrial H A j + A (fixedTrial H A j) - H)) := by
  obtain ⟨η0, h0, h1, hh⟩ := finite_substitution_uniform hU hs hgap hC hH hH0 hbH n
  refine ⟨η0, h0, h1, ?_⟩
  intro η hη hsmall A hsm hv hd j hj
  have hm := rescaledMean_bounds hU hη A B K hB hK hsm hv hd
  have hout := hh (rescaledMean η A) hm η hη hsmall j hj
  simpa only [trial_rescaledMean hη.ne', rescaledMean_self hη.ne'] using hout

end ClosedSurfaceR4.FiniteMean

end

end OAI
