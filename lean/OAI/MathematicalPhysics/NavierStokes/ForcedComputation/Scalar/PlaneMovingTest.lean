import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneWeightedEvolution

namespace OAI

/-! Compact tests depending on time. This is the local transport identity
used to retain scalar mass inside each moving computation gate. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set MeasureTheory
open scoped ContDiff

theorem PlaneScalarSolution.moving_test_derivative
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    {φ φd : ℝ → Plane → ℝ}
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (hφd : ContDiff ℝ ∞ (Function.uncurry φd))
    (hdφ : ∀ t x, HasDerivAt (fun s => φ s x) (φd t x) t)
    {K : Set Plane} (hK : IsCompact K)
    (hsupp : ∀ t, Function.support (φ t) ⊆ K)
    (hdsupp : ∀ t, Function.support (φd t) ⊆ K)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => ∫ x, φ r x * w r x)
      ((∫ x, φd t x * w t x) +
        (∫ x, w t x * (ν * scalarLaplacian (φ t) x +
          fderiv ℝ (φ t) x (a t x))) + ∫ x, φ t x * h t x) t := by
  let A : ℝ := t / 2
  let B : ℝ := (t + T) / 2
  have hi : Icc A B ⊆ Ioo (0 : ℝ) T := by
    intro s hs
    dsimp [A, B] at hs
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  have htAB : t ∈ Ioo A B := by
    constructor <;> dsimp [A, B] <;> linarith [ht.1, ht.2]
  have hwc : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc A B ×ˢ univ) :=
    hw.smooth.mono (fun _ hs => ⟨Ioo_subset_Icc_self (hi hs.1), hs.2⟩)
  have hgen : ContDiffOn ℝ ∞ (fun p : ℝ × Plane =>
      scalarGenerator ν (a p.1) (w p.1) p.2 + h p.1 p.2) (Icc A B ×ˢ univ) :=
    ((hw.interior_generator ha).add hh.contDiffOn).mono (fun _ hs => ⟨hi hs.1, hs.2⟩)
  have hg : ContinuousOn (fun p : ℝ × Plane => φ p.1 p.2 * w p.1 p.2)
      (Icc A B ×ˢ univ) := (hφ.contDiffOn.mul hwc).continuousOn
  have hd : ContinuousOn (fun p : ℝ × Plane => φd p.1 p.2 * w p.1 p.2 +
      φ p.1 p.2 * (scalarGenerator ν (a p.1) (w p.1) p.2 + h p.1 p.2))
      (Icc A B ×ˢ univ) :=
    ((hφd.contDiffOn.mul hwc).add (hφ.contDiffOn.mul hgen)).continuousOn
  have he (s : ℝ) (hs : s ∈ Ioo A B) (x : Plane) :
      HasDerivAt (fun r => φ r x * w r x)
        (φd s x * w s x + φ s x *
          (scalarGenerator ν (a s) (w s) x + h s x)) s := by
    have hsT := hi (Ioo_subset_Icc_self hs)
    exact (hdφ s x).mul ((hw.equation s (Ioo_subset_Icc_self hsT) x).hasDerivAt
      (Icc_mem_nhds hsT.1 hsT.2))
  have hzero (r : ℝ) (x : Plane) (hx : x ∉ K) : φ r x = 0 ∧ φd r x = 0 := by
    constructor
    · by_contra hn
      exact hx (hsupp r hn)
    · by_contra hn
      exact hx (hdsupp r hn)
  have hs (r : ℝ) : Function.support (fun x => φ r x * w r x) ⊆ K := by
    intro x hx
    by_contra hn
    apply hx
    change φ r x * w r x = 0
    rw [(hzero r x hn).1, zero_mul]
  have hds : Function.support (fun x => φd t x * w t x + φ t x *
      (scalarGenerator ν (a t) (w t) x + h t x)) ⊆ K := by
    intro x hx
    by_contra hn
    apply hx
    change φd t x * w t x + φ t x *
      (scalarGenerator ν (a t) (w t) x + h t x) = 0
    rw [(hzero t x hn).1, (hzero t x hn).2, zero_mul, zero_mul, add_zero]
  have hD := compact_supported_integral_hasDerivAt hg hd he hK hs hds htAB
  have hφs : ContDiff ℝ ∞ (φ t) := hφ.comp (contDiff_const.prodMk contDiff_id)
  have hφds : ContDiff ℝ ∞ (φd t) := hφd.comp (contDiff_const.prodMk contDiff_id)
  have hwS := hw.slice_smooth (Ioo_subset_Icc_self ht)
  have haS : ContDiff ℝ ∞ (a t) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hhS : ContDiff ℝ ∞ (h t) := hh.comp (contDiff_const.prodMk contDiff_id)
  have hφc : HasCompactSupport (φ t) := HasCompactSupport.intro (K := K) hK (fun x hx => by
    by_contra hn
    exact hx (hsupp t hn))
  have hdc : HasCompactSupport (φd t) := HasCompactSupport.intro (K := K) hK (fun x hx => by
    by_contra hn
    exact hx (hdsupp t hn))
  have hgS : ContDiff ℝ ∞ (scalarGenerator ν (a t) (w t)) := by
    have hl : ContDiff ℝ ∞ (scalarLaplacian (w t)) := by
      unfold scalarLaplacian
      exact ContDiff.sum (fun j _ => spatialD_smooth j (spatialD_smooth j hwS))
    exact (contDiff_const.mul hl).sub
      ((hwS.fderiv_right (m := ∞) (by simp)).clm_apply haS)
  have hid : Integrable (fun x => φd t x * w t x) :=
    (hφds.mul hwS).continuous.integrable_of_hasCompactSupport hdc.mul_right
  have hig : Integrable (fun x => φ t x * scalarGenerator ν (a t) (w t) x) :=
    (hφs.mul hgS).continuous.integrable_of_hasCompactSupport hφc.mul_right
  have hih : Integrable (fun x => φ t x * h t x) :=
    (hφs.mul hhS).continuous.integrable_of_hasCompactSupport hφc.mul_right
  have hidg : Integrable (fun x => φd t x * w t x +
      φ t x * scalarGenerator ν (a t) (w t) x) := hid.add hig
  have hI : (∫ x, φd t x * w t x + φ t x *
      (scalarGenerator ν (a t) (w t) x + h t x)) =
      (∫ x, φd t x * w t x) + (∫ x, w t x *
        (ν * scalarLaplacian (φ t) x + fderiv ℝ (φ t) x (a t x))) +
        ∫ x, φ t x * h t x := by
    simp_rw [mul_add, ← add_assoc]
    rw [integral_add hidg hih, integral_add hid hig,
      integral_compact_generator hφs hwS haS hφc (hdiv t) ν]
    simp only [mul_add]
  exact hI ▸ hD

end ForcedComputation.VelocityDetector

end

end OAI
