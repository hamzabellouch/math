import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLocalMean

namespace OAI

/-! The local mean operator has explicit polynomial majorants in the
geometric profile and the current tensor norm. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

def polynomialMeanProfile (p : ℕ → ℕ) (C G : ℕ → ℝ) (m : ℕ) (A : ℝ) : ℝ :=
  C m*(G m+max 1 A)^(p m)

theorem polynomial_local_mean_majorants (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
    ∀ {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
      {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base},
      ∀ (_h : LocalBounds U V s r ρ R reference F ψ Q χ e)
        (d : Budgets U V s F ψ Q χ e),
      0 < s → s ≤ 1 → 0 < ρ → ∀ G : ℕ → ℝ, (∀ m, 1 ≤ G m) →
      (∀ m, ρ⁻¹ ≤ G m ∧ d.inv (m+q+2) ≤ G m ∧ d.forms (m+q+2) ≤ G m ∧
        d.psi (m+q+2) ≤ G m ∧ d.mode (m+q+2) ≤ G m ∧ d.normal (m+q+2) ≤ G m ∧
        d.chi m ≤ G m ∧ d.pull m ≤ G m) →
      ∀ δ : ℝ, 0 < δ → MeanBounds U s reference r (q+2)
        (meanTerm δ s F ψ Q χ e q) (polynomialMeanProfile p C G) (polynomialMeanProfile p C G) := by
  classical
  choose p C hC hmean using fun m => polynomial_local_mean_estimates q m
  refine ⟨p,C,hC,?_⟩
  intro U V s r ρ R reference F ψ Q χ e h d hs hs1 hρ G hG hbounds δ hδ
  have hmajor (m : ℕ) (A : ℝ) (_hA : 1 ≤ A) : 1 ≤ polynomialMeanProfile p C G m A := by
    apply one_le_mul_of_one_le_of_one_le (hC m)
    apply one_le_pow₀
    exact (hG m).trans (le_add_of_nonneg_right ((zero_le_one.trans (le_max_left 1 A))))
  have happly (m : ℕ) (A : ℝ) (hA : 1 ≤ A) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
      (f g : Base → Tensor) (D : ℝ) (hD : 0 ≤ D)
      (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
      (hfball : InTrialBall U reference r f) (hgball : InTrialBall U reference r g)
      (hfb : WeightedBound U s (m+(q+2)) A f) (hgb : WeightedBound U s (m+(q+2)) A g)
      (hdb : WeightedBound U s (m+(q+2)) D (f-g)) := by
    let B := G m+max 1 A
    have hBG : G m ≤ B := le_add_of_nonneg_right (zero_le_one.trans (le_max_left 1 A))
    have hBA : A ≤ B := (le_max_right 1 A).trans
      (le_add_of_nonneg_left (zero_le_one.trans (hG m)))
    have hB : 1 ≤ B := (hG m).trans hBG
    obtain ⟨hρG,hi,hforms,hψ,hmode,hnormal,hχ,hpull⟩ := hbounds m
    have horders : m+(q+2) = m+q+2 := by omega
    rw [horders] at hfb hgb hdb
    exact hmean m h d hs hs1 hρ B hB (hρG.trans hBG) (hi.trans hBG) (hforms.trans hBG)
      (hψ.trans hBG) (hmode.trans hBG) (hnormal.trans hBG) (hχ.trans hBG) (hpull.trans hBG)
      δ η hδ hη hη1 f g D hD hf hg hfball hgball (hfb.mono_const hBA) (hgb.mono_const hBA) hdb
  refine ⟨hmajor,hmajor,?_,?_,?_⟩
  · intro η hη hη1 f hf hfball
    exact h.mean_smooth hρ hf hfball δ q η
  · intro η hη hη1 m A f hA hf hfball hb
    have hz : WeightedBound U s (m+(q+2)) 0 (f-f) := by
      apply (weightedBound_zero U s (m+(q+2)) (F := Tensor)).congr
      intro x hx
      simp
    exact (happly m A hA η hη hη1 f f 0 le_rfl hf hf hfball hfball hb hb hz).1
  · intro η hη hη1 m A D f g hA hD hf hg hfball hgball hfb hgb hdb
    exact (happly m A hA η hη hη1 f g D hD hf hg hfball hgball hfb hgb hdb).2

end ClosedSurfaceR4.PhaseMean

end

end OAI
