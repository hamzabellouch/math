import OAI.Geometry.Perimeter.Regularity.GraphChart

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def graphNormalVector (v : Euc n) (f : normalPlane v → ℝ) (y : normalPlane v) : Euc n :=
  v-((gradient f y : normalPlane v):Euc n)

def graphAreaFactor (v : Euc n) (f : normalPlane v → ℝ) (y : normalPlane v) : ℝ :=
  ‖graphNormalVector v f y‖

theorem graphDefining_gradient {v : Euc n} {f : normalPlane v → ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)))
    {x : Euc n} (hx : x∈graphCylinder v) :
    gradient (graphDefining v f) x=graphNormalVector v f (normalProjection v x) := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,(graphDefining_hasFDerivAt hf hx).fderiv]
  simp only [sub_apply,ContinuousLinearMap.comp_apply]
  change inner ℝ v z-fderiv ℝ f (normalProjection v x) (normalProjection v z)=
    inner ℝ (v-((gradient f (normalProjection v x) : normalPlane v):Euc n)) z
  rw [inner_sub_left,←(normalPlane v).inner_orthogonalProjectionOnto_eq_of_mem_left,inner_gradient_left]

theorem graphNormalVector_inner_normal {v : Euc n} (hv : ‖v‖=1)
    (f : normalPlane v → ℝ) (y : normalPlane v) : inner ℝ (graphNormalVector v f y) v=1 := by
  rw [graphNormalVector,inner_sub_left,real_inner_self_eq_norm_sq,hv,one_pow,
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (gradient f y).property,sub_zero]

theorem graphAreaFactor_sq {v : Euc n} (hv : ‖v‖=1)
    (f : normalPlane v → ℝ) (y : normalPlane v) : (graphAreaFactor v f y)^2=1+‖gradient f y‖^2 := by
  rw [graphAreaFactor,graphNormalVector,norm_sub_sq_real,hv,one_pow,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (gradient f y).property,
    mul_zero,sub_zero,Submodule.norm_coe]

theorem graphAreaFactor_pos {v : Euc n} (hv : ‖v‖=1)
    (f : normalPlane v → ℝ) (y : normalPlane v) : 0<graphAreaFactor v f y := by
  have hh := graphAreaFactor_sq hv f y
  have hn : 0≤graphAreaFactor v f y := norm_nonneg _
  nlinarith [sq_nonneg ‖gradient f y‖]

theorem graphAreaFactor_sqrt {v : Euc n} (hv : ‖v‖=1)
    (f : normalPlane v → ℝ) (y : normalPlane v) :
    graphAreaFactor v f y=Real.sqrt (1+‖gradient f y‖^2) := by
  rw [←graphAreaFactor_sq hv f y,Real.sqrt_sq (graphAreaFactor_pos hv f y).le]

theorem graph_approximateNormal (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {a : ℝ} (ha : 0≤a) (ha4 : a<1/4)
    (hs : FullSlab E v 8 a) {f : normalPlane v → ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)))
    (hiff : ∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
      ((y:Euc n)+t•v∈perimeterSupport E ↔ t=f y))
    {x : Euc n} (hx : x∈graphCylinder v) (hxS : x∈perimeterSupport E) :
    approximateNormal E x=(graphAreaFactor v f (normalProjection v x))⁻¹ •
      graphNormalVector v f (normalProjection v x) := by
  rw [graphDefining_approximateNormal hn hmin hv ha ha4 hs hf hiff hx hxS,
    graphDefining_gradient hf hx]
  rfl

theorem graph_normal_flux_positive (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {a : ℝ} (ha : 0≤a) (ha4 : a<1/4)
    (hs : FullSlab E v 8 a) {f : normalPlane v → ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)))
    (hiff : ∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
      ((y:Euc n)+t•v∈perimeterSupport E ↔ t=f y))
    {x : Euc n} (hx : x∈graphCylinder v) (hxS : x∈perimeterSupport E) :
    0 < inner ℝ (approximateNormal E x) v := by
  rw [graph_approximateNormal hn hmin hv ha ha4 hs hf hiff hx hxS,
    real_inner_smul_left,graphNormalVector_inner_normal hv,mul_one]
  exact inv_pos.mpr (graphAreaFactor_pos hv f _)

end RPISingularHarnack

end

end OAI
