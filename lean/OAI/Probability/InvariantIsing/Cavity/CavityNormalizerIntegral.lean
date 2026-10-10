import OAI.Probability.InvariantIsing.Cavity.CavityLogDetPotential
import OAI.Probability.InvariantIsing.Cavity.CavityFieldResidual

namespace OAI

/-! The finite root, positive-level and ordinary residual pieces of the
quadratic normalizer are the integral of D_p(r) R'(D_p(r)). -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityNormalizerDensity {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (p : OverlapPath) (r : ℝ) : ℝ :=
  deficit p r * cavityRDerivative rho lam hrho hsum (deficit p r)

lemma continuous_cavityNormalizerDensity {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (p : OverlapPath) :
    Continuous (cavityNormalizerDensity rho lam hrho hsum p) :=
  (continuous_deficit p).mul ((continuous_cavityRDerivative rho lam hrho hsum).comp
    (continuous_deficit p))

lemma integral_cavityNormalizer_gap {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {a b : ℝ} (hab : a < b)
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s)
    (hpos : 0 < deficit p b) (hmass : pathMeasure.real {s | p s ≤ a} ≠ 0) :
    (∫ r in a..b, cavityNormalizerDensity rho lam hrho hsum p r) =
      (cavityLogDetPotential rho lam hrho hsum (deficit p a) -
        cavityLogDetPotential rho lam hrho hsum (deficit p b)) /
          pathMeasure.real {s | p s ≤ a} := by
  let F := cavityLogDetPotential rho lam hrho hsum
  let ζ := pathMeasure.real {s | p s ≤ a}
  have hp (r : ℝ) (hr : r ∈ Icc a b) : 0 < deficit p r :=
    hpos.trans_le (deficit_antitone_argument p hr.2)
  have hc : ContinuousOn (fun r => F (deficit p r)) (Icc a b) := by
    intro r hr
    exact ((hasDerivAt_cavityLogDetPotential rho lam hrho hsum
      (hp r hr)).continuousAt.comp (continuous_deficit p).continuousAt).continuousWithinAt
  have hd : ∀ r ∈ Ioo a b, HasDerivAt (fun r => F (deficit p r))
      ((-ζ) * cavityNormalizerDensity rho lam hrho hsum p r) r := by
    intro r hr
    have hF := hasDerivAt_cavityLogDetPotential rho lam hrho hsum
      (hp r ⟨hr.1.le, hr.2.le⟩)
    have hD := hasDerivAt_deficit_on_gap p hgap hr
    convert! hF.comp r hD using 1
    dsimp only [ζ, cavityNormalizerDensity]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hc hd
    (((continuous_cavityNormalizerDensity rho lam hrho hsum p).intervalIntegrable a b).const_mul (-ζ))
  rw [intervalIntegral.integral_const_mul] at hf
  apply (eq_div_iff hmass).mpr
  change (∫ r in a..b, cavityNormalizerDensity rho lam hrho hsum p r) * ζ =
    F (deficit p a) - F (deficit p b)
  linarith

lemma integral_cavityNormalizer_root {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {q : ℝ} (hq : 0 ≤ q) (hbound : ∀ᵐ s ∂pathMeasure, q ≤ p s) :
    (∫ r in 0..q, cavityNormalizerDensity rho lam hrho hsum p r) =
      q * deficit p q * cavityRDerivative rho lam hrho hsum (deficit p q) := by
  calc
    _ = ∫ _r in 0..q, deficit p q * cavityRDerivative rho lam hrho hsum (deficit p q) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hq
      intro r hr
      dsimp only [cavityNormalizerDensity]
      rw [deficit_constant_below_ae_lower p hbound hr.2.le]
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring

lemma integral_cavityNormalizer_tail {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {top : ℝ} (htop : top ≤ 1)
    (hbound : ∀ᵐ s ∂pathMeasure, p s ≤ top) :
    (∫ r in top..1, cavityNormalizerDensity rho lam hrho hsum p r) =
      cavityLogDetPotential rho lam hrho hsum (deficit p top) := by
  let F := cavityLogDetPotential rho lam hrho hsum
  have he (r : ℝ) (hr : r ∈ Icc top 1) : deficit p r = 1 - r :=
    deficit_eq_one_sub_of_ae_le p (hbound.mono (fun _ hs => hs.trans hr.1))
  have hc : ContinuousOn (fun r => F (1 - r)) (Icc top 1) :=
    (continuousOn_cavityLogDetPotential rho lam hrho hsum).comp
      (continuous_const.sub continuous_id).continuousOn (fun _ hr => sub_nonneg.mpr hr.2)
  have hd : ∀ r ∈ Ioo top 1, HasDerivAt (fun r => F (1 - r))
      (-cavityNormalizerDensity rho lam hrho hsum p r) r := by
    intro r hr
    have hF := hasDerivAt_cavityLogDetPotential rho lam hrho hsum (sub_pos.mpr hr.2)
    have heq := he r ⟨hr.1.le, hr.2.le⟩
    convert! hF.comp r ((hasDerivAt_id r).const_sub 1) using 1
    dsimp only [cavityNormalizerDensity]
    rw [heq]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htop hc hd
    (((continuous_cavityNormalizerDensity rho lam hrho hsum p).intervalIntegrable top 1).neg)
  rw [intervalIntegral.integral_neg] at hf
  change -(∫ r in top..1, cavityNormalizerDensity rho lam hrho hsum p r) =
    F (1 - 1) - F (1 - top) at hf
  rw [sub_self, show F 0 = 0 from cavityLogDetPotential_zero rho lam hrho hsum] at hf
  rw [deficit_eq_one_sub_of_ae_le p hbound]
  linarith

private lemma cavity_integral_finite_partition {n : ℕ} (f : ℝ → ℝ) (hf : Continuous f)
    (q : Fin (n + 1) → ℝ) :
    (∫ r in 0..q 0, f r) +
      (∑ i : Fin n, ∫ r in q i.castSucc..q i.succ, f r) +
        (∫ r in q (Fin.last n)..1, f r) = ∫ r in 0..1, f r := by
  let G := fun x => ∫ r in 0..x, f r
  have hsub (a b : ℝ) : (∫ r in a..b, f r) = G b - G a := by
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
    dsimp only [G]
    linarith
  simp_rw [hsub]
  have h0 := Fin.sum_univ_succ (fun i => G (q i))
  have h1 := Fin.sum_univ_castSucc (fun i => G (q i))
  rw [Finset.sum_sub_distrib]
  linarith

/-- The exact finite-step normalizer integral, including both the common
root and the terminal residual of exponent one. -/
theorem finite_overlap_normalizer_integral {m n : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j r, r ∈ Ioo (cut j.castSucc) (cut j.succ) → p r = q j)
    (htop : q (Fin.last n) < 1) :
    (∫ r in 0..1, cavityNormalizerDensity rho lam hrho hsum p r) =
      q 0 * deficit p (q 0) * cavityRDerivative rho lam hrho hsum (deficit p (q 0)) +
      (∑ i : Fin n, (cavityLogDetPotential rho lam hrho hsum (deficit p (q i.castSucc)) -
        cavityLogDetPotential rho lam hrho hsum (deficit p (q i.succ))) / cut i.castSucc.succ) +
      cavityLogDetPotential rho lam hrho hsum (deficit p (q (Fin.last n))) := by
  have hb := finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp
  have hroot := integral_cavityNormalizer_root rho lam hrho hsum p
    (finite_overlap_value_mem_unit p cut hcut q hp 0).1 (hb.mono (fun _ h => h.1))
  have htail := integral_cavityNormalizer_tail rho lam hrho hsum p htop.le (hb.mono (fun _ h => h.2))
  have hgap (i : Fin n) : (∫ r in q i.castSucc..q i.succ,
      cavityNormalizerDensity rho lam hrho hsum p r) =
      (cavityLogDetPotential rho lam hrho hsum (deficit p (q i.castSucc)) -
        cavityLogDetPotential rho lam hrho hsum (deficit p (q i.succ))) / cut i.castSucc.succ := by
    have hm := finite_overlap_cumulative_mass p cut hcut hfirst hlast q hq hp i.castSucc
    have hc : 0 < cut i.castSucc.succ := by
      rw [← hfirst]
      exact hcut (Fin.succ_pos _)
    have he := integral_cavityNormalizer_gap rho lam hrho hsum p
      (hq (Fin.castSucc_lt_succ (i := i)))
      (finite_overlap_value_gap p cut hfirst hlast q hq.monotone hp i)
      (finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
        (hq.monotone (Fin.le_last _))) (by rw [hm]; exact hc.ne')
    rwa [hm] at he
  have h := cavity_integral_finite_partition _ (continuous_cavityNormalizerDensity rho lam hrho hsum p) q
  rw [hroot, htail] at h
  simp_rw [hgap] at h
  exact h.symm

end InvariantIsing

end

end OAI
