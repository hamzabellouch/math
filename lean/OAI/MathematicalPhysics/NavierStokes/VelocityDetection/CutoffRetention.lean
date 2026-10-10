import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CutoffObservation
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.MovingCutoff

namespace OAI

noncomputable section
namespace VelocityDetection.MovingCutoff
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open SpatialCalculus

theorem capture_le_of_radius_doubled {R S t : ℝ} (hR : 0 < R) (hRS : 2 * R ≤ S)
    {ρ : ScalarField 2} {c d : ℝ → Coord 2} (hcd : c t = d t)
    (hρ : Integrable (ρ t)) (hρ0 : ∀ X, 0 ≤ ρ t X) :
    capture R c ρ t ≤ capture S d ρ t := by
  dsimp only [capture]
  rw [hcd]
  apply CutoffObservation.capture_monotone_at_change hρ hρ0
    (((Cutoff.contDiff_cutoff R).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
    (fun X => (Cutoff.cutoff_mem_Icc R (X - d t)).1)
    (fun X => (Cutoff.cutoff_mem_Icc R (X - d t)).2)
    (((Cutoff.contDiff_cutoff S).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
    (fun X => (Cutoff.cutoff_mem_Icc S (X - d t)).1)
    (fun X => (Cutoff.cutoff_mem_Icc S (X - d t)).2)
  intro X hX
  exact Cutoff.cutoff_one_on_support hR hRS hX

theorem retention_at_joints {ν : ℝ} (hν : 0 ≤ ν)
    {R τ : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hτ : ∀ n, τ n ≤ τ (n + 1))
    (hRnext : ∀ n, 2 * R n ≤ R (n + 1))
    {ρ : ScalarField 2} {c : ℕ → ℝ → Coord 2} {a : ℝ → Coord 2 → Coord 2}
    {g : ScalarField 2} {M : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hc : ∀ n, ContDiff ℝ 1 (c n))
    (hjoin : ∀ n, c n (τ (n + 1)) = c (n + 1) (τ (n + 1)))
    (hM : ∀ n, ContinuousOn M (Icc (τ n) (τ (n + 1))))
    (hM' : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → HasDerivAt M (∫ X, g t X) t)
    (ha : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) →
      ∀ i, ContDiff ℝ 1 (fun X => a t X i))
    (hg : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → Continuous (g t))
    (hdiv : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) →
      ∀ X, (∑ i, partialD i (fun Y => a t Y i) X) = 0)
    (heq : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → ∀ X,
      deriv (fun s => ρ s X) t + (∑ i, a t X i * partialD i (ρ t) X) =
        ν * laplacian (fun _ => ρ t) 0 X + g t X)
    (n : ℕ)
    (hplateau : ∀ k < n, ∀ t, t ∈ Ioo (τ k) (τ (k + 1)) → ∀ X,
      (∀ i, |X i - c k t i| ≤ R k) → a t X = deriv (c k) t)
    (hρint : ∀ n t, t ∈ Icc (τ n) (τ (n + 1)) → Integrable (ρ t))
    (hρ0 : ∀ n t, t ∈ Icc (τ n) (τ (n + 1)) → ∀ X, 0 ≤ ρ t X)
    (hmass : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → (∫ X, ρ t X) ≤ 1)
    (hsource : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → ∀ X,
      g t X ≠ 0 → ∀ i, |X i - c n t i| ≤ R n / 2) :
    M (τ n) - capture (R n) (c n) ρ (τ n) ≤
      M (τ 0) - capture (R 0) (c 0) ρ (τ 0) +
        ∑ k ∈ Finset.range n, (ν * 3000 / (R k) ^ 2) * (τ (k + 1) - τ k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun k hk => hplateau k (Nat.lt_succ_of_lt hk))
    have hstep := retention_on_interval (hR n) hν (hτ n) hρ (hc n) (hM n)
      (hM' n) (ha n) (hg n) (hdiv n) (heq n) (hplateau n (Nat.lt_succ_self n))
      (fun t ht => hρint n t ⟨ht.1.le, ht.2.le⟩)
      (fun t ht => hρ0 n t ⟨ht.1.le, ht.2.le⟩) (hmass n) (hsource n)
    have hchange := capture_le_of_radius_doubled (hR n) (hRnext n) (hjoin n)
      (hρint n _ ⟨hτ n, le_rfl⟩) (hρ0 n _ ⟨hτ n, le_rfl⟩)
    rw [Finset.sum_range_succ]
    linarith [ih']

theorem retention_le_series {ν : ℝ} (hν : 0 ≤ ν)
    {R τ : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hτ : ∀ n, τ n ≤ τ (n + 1))
    (hRnext : ∀ n, 2 * R n ≤ R (n + 1))
    {ρ : ScalarField 2} {c : ℕ → ℝ → Coord 2} {a : ℝ → Coord 2 → Coord 2}
    {g : ScalarField 2} {M : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hc : ∀ n, ContDiff ℝ 1 (c n))
    (hjoin : ∀ n, c n (τ (n + 1)) = c (n + 1) (τ (n + 1)))
    (hM : ∀ n, ContinuousOn M (Icc (τ n) (τ (n + 1))))
    (hM' : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → HasDerivAt M (∫ X, g t X) t)
    (ha : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) →
      ∀ i, ContDiff ℝ 1 (fun X => a t X i))
    (hg : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → Continuous (g t))
    (hdiv : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) →
      ∀ X, (∑ i, partialD i (fun Y => a t Y i) X) = 0)
    (heq : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → ∀ X,
      deriv (fun s => ρ s X) t + (∑ i, a t X i * partialD i (ρ t) X) =
        ν * laplacian (fun _ => ρ t) 0 X + g t X)
    {n : ℕ}
    (hplateau : ∀ k ≤ n, ∀ t, t ∈ Ioo (τ k) (τ (k + 1)) → ∀ X,
      (∀ i, |X i - c k t i| ≤ R k) → a t X = deriv (c k) t)
    (hρint : ∀ n t, t ∈ Icc (τ n) (τ (n + 1)) → Integrable (ρ t))
    (hρ0 : ∀ n t, t ∈ Icc (τ n) (τ (n + 1)) → ∀ X, 0 ≤ ρ t X)
    (hmass : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → (∫ X, ρ t X) ≤ 1)
    (hsource : ∀ n t, t ∈ Ioo (τ n) (τ (n + 1)) → ∀ X,
      g t X ≠ 0 → ∀ i, |X i - c n t i| ≤ R n / 2)
    (hsum : Summable (fun n => (ν * 3000 / (R n) ^ 2) * (τ (n + 1) - τ n)))
    {t : ℝ} (ht : t ∈ Icc (τ n) (τ (n + 1))) :
    M t - capture (R n) (c n) ρ t ≤
      M (τ 0) - capture (R 0) (c 0) ρ (τ 0) +
        ∑' k, (ν * 3000 / (R k) ^ 2) * (τ (k + 1) - τ k) := by
  have hsub : Ioo (τ n) t ⊆ Ioo (τ n) (τ (n + 1)) := by
    intro s hs
    exact ⟨hs.1, hs.2.trans_le ht.2⟩
  have hstep := retention_on_interval (hR n) hν ht.1 hρ (hc n)
    ((hM n).mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs => hM' n s (hsub hs)) (fun s hs => ha n s (hsub hs))
    (fun s hs => hg n s (hsub hs)) (fun s hs => hdiv n s (hsub hs))
    (fun s hs => heq n s (hsub hs)) (fun s hs => hplateau n le_rfl s (hsub hs))
    (fun s hs => hρint n s ⟨hs.1.le, hs.2.le.trans ht.2⟩)
    (fun s hs => hρ0 n s ⟨hs.1.le, hs.2.le.trans ht.2⟩)
    (fun s hs => hmass n s (hsub hs)) (fun s hs => hsource n s (hsub hs))
  have hstart := retention_at_joints hν hR hτ hRnext hρ hc hjoin hM hM'
    ha hg hdiv heq n (fun k hk => hplateau k hk.le) hρint hρ0 hmass hsource
  have htail (k : ℕ) : 0 ≤ (ν * 3000 / (R k) ^ 2) * (τ (k + 1) - τ k) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (hτ k))
  have hsum_le := hsum.sum_le_tsum (Finset.range (n + 1)) (fun k _ => htail k)
  rw [Finset.sum_range_succ] at hsum_le
  have htime : (ν * 3000 / (R n) ^ 2) * (t - τ n) ≤
      (ν * 3000 / (R n) ^ 2) * (τ (n + 1) - τ n) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 _) (by positivity)
  linarith

end VelocityDetection.MovingCutoff
end

end OAI
