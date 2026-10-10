import OAI.Analysis.CircleDomains.Selection.WedgeEstimate
import OAI.Analysis.CircleDomains.Selection.StaircaseMean

namespace OAI

/-!
# Averaging the cutoff wedge estimate

Independent shifts reduce the leading wedge term to its original size.
The error from the common cutoff is linear in the grid spacing. Integrals
here use the square of shifts before normalization by its area `h²`.
-/

open MeasureTheory Set

namespace CircleDomainRigidity.FiniteTransfer

theorem integral_cutoff_wedge_le
    (u v c : ℝ × ℝ) {q p r s : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h)
    (hq : Continuous q) (hp : Continuous p) (hr : Continuous r) (hs : Continuous s)
    (hq0 : ∀ t ∈ Icc 0 h, 0 ≤ q t) (hp0 : ∀ t ∈ Icc 0 h, 0 ≤ p t)
    (hrh : ∀ t ∈ Icc 0 h, |r t| ≤ h) (hsh : ∀ t ∈ Icc 0 h, |s t| ≤ h)
    (hqmean : (∫ t in Icc 0 h, q t) = h)
    (hpmean : (∫ t in Icc 0 h, p t) = h) :
    (∫ z in Icc 0 h ×ˢ Icc 0 h,
      |planarWedge (q z.1 • u + r z.1 • c) (p z.2 • v + s z.2 • c)|
      ∂volume.prod volume) ≤
      h ^ 2 * |planarWedge u v| + h ^ 3 *
        (|planarWedge u c| + |planarWedge c v|) := by
  let A := |planarWedge u v|
  let B := |planarWedge u c|
  let C := |planarWedge c v|
  let D := Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h
  have hcompact : IsCompact D := isCompact_Icc.prod isCompact_Icc
  have hf : IntegrableOn (fun z : ℝ × ℝ =>
      |planarWedge (q z.1 • u + r z.1 • c) (p z.2 • v + s z.2 • c)|)
      D (volume.prod volume) := by
    apply ContinuousOn.integrableOn_compact hcompact
    unfold planarWedge
    fun_prop
  have hqp : IntegrableOn (fun z : ℝ × ℝ => (q z.1 * p z.2) * A)
      D (volume.prod volume) := by
    apply ContinuousOn.integrableOn_compact hcompact
    fun_prop
  have hq1 : IntegrableOn (fun z : ℝ × ℝ => (q z.1 * 1) * (h * B))
      D (volume.prod volume) := by
    apply ContinuousOn.integrableOn_compact hcompact
    fun_prop
  have h1p : IntegrableOn (fun z : ℝ × ℝ => (1 * p z.2) * (h * C))
      D (volume.prod volume) := by
    apply ContinuousOn.integrableOn_compact hcompact
    fun_prop
  have hbound := setIntegral_mono_on hf ((hqp.add hq1).add h1p) hcompact.measurableSet
    (fun z hz => (abs_planarWedge_cutoff_le u v c (hq0 _ hz.1)
      (hp0 _ hz.2) (hrh _ hz.1) (hsh _ hz.2)).trans_eq (by dsimp [A, B, C]; ring))
  have hone : (∫ t in Icc (0 : ℝ) h, (1 : ℝ)) = h := by
    simp [hh]
  have hqint : (∫ z in Icc 0 h ×ˢ Icc 0 h, q z.1 ∂volume.prod volume) = h * h := by
    simpa only [mul_one, hqmean, hone] using
      (setIntegral_prod_mul (μ := volume) (ν := volume)
        q (fun _ : ℝ => (1 : ℝ)) (Icc 0 h) (Icc 0 h))
  have hpint : (∫ z in Icc 0 h ×ˢ Icc 0 h, p z.2 ∂volume.prod volume) = h * h := by
    simpa only [one_mul, hpmean, hone] using
      (setIntegral_prod_mul (μ := volume) (ν := volume)
        (fun _ : ℝ => (1 : ℝ)) p (Icc 0 h) (Icc 0 h))
  calc
    _ ≤ (∫ z in D, (q z.1 * p z.2) * A + (q z.1 * 1) * (h * B) +
        (1 * p z.2) * (h * C) ∂volume.prod volume) := hbound
    _ = h ^ 2 * A + h ^ 3 * (B + C) := by
      have hadd := integral_add (hqp.add hq1) h1p
      have hadd' := integral_add hqp hq1
      simp only [Pi.add_apply] at hadd hadd'
      rw [hadd, hadd']
      simp only [D, integral_mul_const, setIntegral_prod_mul, hqmean, hpmean, hqint,
        one_mul, hpint]
      ring

end CircleDomainRigidity.FiniteTransfer

end OAI
