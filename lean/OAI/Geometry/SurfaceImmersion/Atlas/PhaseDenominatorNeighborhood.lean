import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseNeighborhood

namespace OAI

/-! A compact-support denominator bound extends to an open phase domain
with a specified factor of two. The domain may depend on the immersion;
the numerical bounds do not. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma continuousAt_phaseNormal {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0) :
    ContinuousAt (fun y => secondQuadratic (realSecondTensor F y)
      (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)) x := by
  have hb := (contDiffAt_realSecondTensor hF x hD).continuousAt
  have hp := (continuous_phaseDerivative hφ).continuousAt (x := x)
  have hh : ContinuousAt (fun y : Base => (realSecondTensor F y,
      (-(phaseDerivative φ y).2,(phaseDerivative φ y).1))) x :=
    hb.prodMk (hp.snd.neg.prodMk hp.fst)
  have hc : ContinuousAt (fun z : (Fin 3 → RVec 4) × Base => secondQuadratic z.1 z.2)
      (realSecondTensor F x, (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)) :=
    (continuous_secondQuadratic (n := 4)).continuousAt
  exact hc.comp (f := fun y : Base => (realSecondTensor F y,
    (-(phaseDerivative φ y).2,(phaseDerivative φ y).1))) hh

lemma eventually_gram_reciprocal_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (x : Base) {B : ℝ} (hB : 0 < B)
    (hD : NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (h : ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) :
    ∀ᶠ y in 𝓝 x,
      ‖(NormalFrame.gramDet (coordDeriv dx F y) (coordDeriv dy F y))⁻¹‖ < 2*B := by
  have hc := ((continuous_gramDet_field hF).continuousAt (x := x)).inv₀ hD
  exact hc.norm.eventually (Iio_mem_nhds (lt_of_le_of_lt h (by linarith)))

lemma eventually_normal_reciprocal_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Base) {B : ℝ} (hB : 0 < B)
    (hD : NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (hn : secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1) ≠ 0)
    (h : ‖secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ B) :
    ∀ᶠ y in 𝓝 x, ‖secondQuadratic (realSecondTensor F y)
      (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)‖⁻¹ < 2*B := by
  have hc := (continuousAt_phaseNormal hF hφ x hD).norm.inv₀ (norm_ne_zero_iff.mpr hn)
  exact hc.eventually (Iio_mem_nhds (lt_of_le_of_lt h (by linarith)))

theorem phase_denominator_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Set Base) {B : ℝ} (hB : 0 < B)
    (hImm : ∀ x ∈ K, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ K, Good (realSecondTensor F x) (phaseDerivative φ x))
    (hgram : ∀ x ∈ K, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B)
    (hnormal : ∀ x ∈ K, ‖secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ B) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U,
      Function.Injective (fderiv ℝ F x) ∧ Good (realSecondTensor F x) (phaseDerivative φ x) ∧
      ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ 2*B ∧
      ‖secondQuadratic (realSecondTensor F x)
        (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ 2*B := by
  let S : Set Base := {x | Function.Injective (fderiv ℝ F x) ∧
    Good (realSecondTensor F x) (phaseDerivative φ x) ∧
    ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ 2*B ∧
    ‖secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ 2*B}
  refine ⟨interior S,isOpen_interior,?_,fun x hx => (show x ∈ S from interior_subset hx)⟩
  intro x hx
  have hD := gramDet_ne_zero_of_injective (fderiv ℝ F x) (hImm x hx)
  have hge := eventually_gram_reciprocal_bound hF x hB hD (hgram x hx)
  have hne := eventually_normal_reciprocal_bound hF hφ x hB hD (hgood x hx).2
    (hnormal x hx)
  have hb := (contDiffAt_realSecondTensor hF x hD).continuousAt
  have hp := (continuous_phaseDerivative hφ).continuousAt (x := x)
  have hgood' := good_eventually hb hp (hgood x hx)
  have hD' := (continuous_gramDet_field hF).continuousAt.eventually_ne hD
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hD',hgood',hge,hne] with y hyD hyg hyG hyN
  exact ⟨injective_of_gramDet_ne_zero _ hyD,hyg,hyG.le,hyN.le⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
