import Mathlib.Tactic.NormNum
import OAI.Computability.BinPacking.Expanders.SpectralCut

namespace OAI

namespace BinPackingGames.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

theorem mean_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    mean (liftCloud (D := D) f) = mean f := by
  change mean (fun x : V × D => f x.1) = mean f
  rw [mean_prod]
  simp only [mean_const]

theorem energy_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    energy (liftCloud (D := D) f) = energy f :=
  mean_liftCloud (D := D) (fun v => f v ^ 2)

theorem mean_cloudMean [Fintype V] [Fintype D] (f : V × D → ℝ) :
    mean (cloudMean f) = mean f := (mean_prod f).symm

theorem energy_prod [Fintype V] [Fintype D] (f : V × D → ℝ) :
    energy f = mean (fun v => energy (fun d => f (v, d))) :=
  mean_prod (fun x => f x ^ 2)

theorem cloudMean_centered_zero [Fintype D] [Nonempty D]
    (f : V × D → ℝ) (v : V) : cloudMean (centered f) v = 0 := by
  change mean (fun d => f (v, d) - cloudMean f v) = 0
  rw [mean_sub, mean_const]
  exact sub_self _

theorem energy_centered_eq_sub [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) = energy f - energy (projection f) := by
  have hpoint (v : V) : energy (fun d => centered f (v, d)) =
      energy (fun d => f (v, d)) - (cloudMean f v) ^ 2 := by
    change energy (fun d => f (v, d) - cloudMean f v) = _
    rw [energy_sub_const]
    change energy (fun d => f (v, d)) - 2 * cloudMean f v * cloudMean f v +
      (cloudMean f v) ^ 2 = _
    ring
  have hproj : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  calc
    energy (centered f) = mean (fun v => energy (fun d => centered f (v, d))) :=
      energy_prod _
    _ = mean (fun v => energy (fun d => f (v, d)) - (cloudMean f v) ^ 2) := by
      congr 1
      funext v
      exact hpoint v
    _ = mean (fun v => energy (fun d => f (v, d))) -
        mean (fun v => (cloudMean f v) ^ 2) := mean_sub _ _
    _ = energy f - energy (projection f) := by
      rw [← energy_prod f, hproj]
      rfl

theorem projection_energy_decomposition [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy f = energy (projection f) + energy (centered f) := by
  rw [energy_centered_eq_sub]
  ring

theorem energy_projection_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (projection f) ≤ energy f := by
  have h := projection_energy_decomposition f
  have hn := energy_nonnegative (centered f)
  linarith

theorem energy_centered_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) ≤ energy f := by
  rw [energy_centered_eq_sub]
  exact sub_le_self _ (energy_nonnegative _)

theorem mean_sq_le_energy {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    mean f ^ 2 ≤ energy f := by
  have h := correlation_sq_le f (fun _ => 1)
  simpa [correlation, energy] using h

theorem averaging_energy_le [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) : energy (averagingOperator G f) ≤ energy f := by
  calc
    energy (averagingOperator G f) ≤ mean (averagingOperator G (fun v => f v ^ 2)) := by
      apply mean_mono
      intro v
      exact mean_sq_le_energy (fun d => f (G.rot (v, d)).1)
    _ = energy f := mean_operator G _

theorem cloudOperator_add [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f + g) = cloudOperator H f + cloudOperator H g := by
  funext x
  exact mean_add _ _

theorem cloudOperator_sub [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f - g) = cloudOperator H f - cloudOperator H g := by
  funext x
  exact mean_sub _ _

theorem cloudOperator_projection [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) : cloudOperator H (projection f) = projection f := by
  funext x
  change mean (fun _ : E => cloudMean f x.1) = cloudMean f x.1
  exact mean_const _

theorem cloudOperator_centered [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) :
    cloudOperator H (centered f) = cloudOperator H f - projection f := by
  unfold centered
  rw [cloudOperator_sub, cloudOperator_projection]

theorem graphPermutation_energy [Fintype V] [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) : energy (graphPermutation G f) = energy f :=
  mean_equiv G.rot (fun x => f x ^ 2)

theorem cloud_energy_le [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (f : V × D → ℝ) :
    energy (cloudOperator H f) ≤ energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => energy (fun d => f (v, d))) :=
      mean_mono (fun v => averaging_energy_le H _)
    _ = energy f := (energy_prod f).symm

theorem cloud_centered_contraction [Fintype V] [Fintype D] [Fintype E]
    (H : PortGraph D E) (lambda : ℝ) (hH : SpectralCertificate H lambda)
    (f : V × D → ℝ) (hzero : ∀ v, cloudMean f v = 0) :
    energy (cloudOperator H f) ≤ lambda ^ 2 * energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => lambda ^ 2 * energy (fun d => f (v, d))) :=
      mean_mono (fun v => hH.contraction _ (hzero v))
    _ = lambda ^ 2 * mean (fun v => energy (fun d => f (v, d))) := mean_mul_left _ _
    _ = lambda ^ 2 * energy f := by rw [← energy_prod f]

theorem cloud_residual_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (lambda : ℝ)
    (hH : SpectralCertificate H lambda) (f : V × D → ℝ) :
    energy (cloudOperator H f - projection f) ≤ lambda ^ 2 * energy f := by
  rw [← cloudOperator_centered H f]
  exact (cloud_centered_contraction H lambda hH (centered f)
    (cloudMean_centered_zero f)).trans
      (mul_le_mul_of_nonneg_left (energy_centered_le f) (sq_nonneg lambda))

theorem projection_graphPermutation_projection [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) :
    projection (graphPermutation G (projection f)) =
      liftCloud (averagingOperator G (cloudMean f)) := rfl

theorem projected_outer_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (projection (graphPermutation G (projection f))) ≤
      lambda ^ 2 * energy (projection f) := by
  have hzero : mean (cloudMean f) = 0 := (mean_cloudMean f).trans hf
  have hleft : energy (projection (graphPermutation G (projection f))) =
      energy (averagingOperator G (cloudMean f)) := by
    rw [projection_graphPermutation_projection]
    exact energy_liftCloud _
  have hright : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  rw [hleft, hright]
  exact hG.contraction _ hzero

theorem energy_add_three_le {A : Type*} [Fintype A] (a b c : A → ℝ) :
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := by
  calc
    energy (a + b + c) ≤ mean (fun x => 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)) := by
      apply mean_mono
      intro x
      change (a x + b x + c x) ^ 2 ≤ 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - c x), sq_nonneg (b x - c x)]
    _ = 3 * (energy a + energy b + energy c) := by
      rw [mean_mul_left, mean_add, mean_add]
      rfl

theorem zigzag_energy_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph D E) (lambdaG lambdaH : ℝ)
    (hG : SpectralCertificate G lambdaG) (hH : SpectralCertificate H lambdaH)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (zigzag G H) f) ≤
      3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
  let u := projection f
  let v := centered f
  let a := projection (graphPermutation G u)
  let b := cloudOperator H (graphPermutation G u) - a
  let c := cloudOperator H (graphPermutation G (cloudOperator H v))
  have hfactor : averagingOperator (zigzag G H) f = a + b + c := by
    rw [averagingOperator_zigzag]
    have hf' : f = u + v := by
      funext x
      change f x = projection f x + (f x - projection f x)
      ring
    have hbu : cloudOperator H u = u := cloudOperator_projection H f
    have hbf : cloudOperator H f = u + cloudOperator H v := by
      rw [hf', cloudOperator_add, hbu]
    rw [hbf]
    have hp : graphPermutation G (u + cloudOperator H v) =
        graphPermutation G u + graphPermutation G (cloudOperator H v) := rfl
    rw [hp, cloudOperator_add]
    change cloudOperator H (graphPermutation G u) + c =
      a + (cloudOperator H (graphPermutation G u) - a) + c
    funext x
    change cloudOperator H (graphPermutation G u) x + c x =
      a x + (cloudOperator H (graphPermutation G u) x - a x) + c x
    ring
  have ha : energy a ≤ lambdaG ^ 2 * energy u := projected_outer_bound G lambdaG hG f hf
  have hb : energy b ≤ lambdaH ^ 2 * energy u := by
    have h := cloud_residual_bound H lambdaH hH (graphPermutation G u)
    simpa only [graphPermutation_energy] using h
  have hc : energy c ≤ lambdaH ^ 2 * energy v := by
    calc
      energy c ≤ energy (graphPermutation G (cloudOperator H v)) := cloud_energy_le H _
      _ = energy (cloudOperator H v) := graphPermutation_energy G _
      _ ≤ lambdaH ^ 2 * energy v :=
        cloud_centered_contraction H lambdaH hH v (cloudMean_centered_zero f)
  rw [hfactor]
  calc
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := energy_add_three_le _ _ _
    _ ≤ 3 * (lambdaG ^ 2 * energy u + lambdaH ^ 2 * energy u + lambdaH ^ 2 * energy v) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hb) hc) (by norm_num)
    _ ≤ 3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
      have hdecomp : energy f = energy u + energy v := projection_energy_decomposition f
      rw [hdecomp]
      have hn := mul_nonneg (sq_nonneg lambdaG) (energy_nonnegative v)
      nlinarith

theorem square_certificate [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda) :
    SpectralCertificate (square G) (lambda ^ 2) where
  nonnegative := sq_nonneg lambda
  lt_one := by
    have hprod := mul_pos (sub_pos.mpr hG.lt_one)
      (show 0 < 1 + lambda by linarith [hG.nonnegative])
    nlinarith
  contraction f hf := by
    rw [averagingOperator_square]
    calc
      energy (averagingOperator G (averagingOperator G f)) ≤
          lambda ^ 2 * energy (averagingOperator G f) :=
        hG.contraction _ ((mean_operator G f).trans hf)
      _ ≤ lambda ^ 2 * (lambda ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (hG.contraction f hf) (sq_nonneg lambda)
      _ = (lambda ^ 2) ^ 2 * energy f := by ring

theorem square_zigzag_halfCertificate [Fintype V] [Fintype D] [Fintype E]
    [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph (D × D) E)
    (hG : SpectralCertificate G (1 / 2)) (hH : SpectralCertificate H (1 / 100)) :
    SpectralCertificate (zigzag (square G) H) (1 / 2) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := zigzag_energy_bound (square G) H ((1 / 2 : ℝ) ^ 2) (1 / 100)
      (square_certificate G (1 / 2) hG) hH f hf
    have hcoef : 3 * (((1 / 2 : ℝ) ^ 2) ^ 2 + (1 / 100) ^ 2) ≤ (1 / 2 : ℝ) ^ 2 := by
      norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end BinPackingGames.Foundations.PCP.ZigzagSpectral

end OAI
