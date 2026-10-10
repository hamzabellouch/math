import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.MfderivReModelTarget
import OAI.Geometry.SmoothYau.Geometry.LpProductFunctionMetric
import OAI.Geometry.SmoothYau.Smoothness.TorusAmbient
import OAI.Geometry.SmoothYau.Spectrum.SphericalSimpleEigenpairOpen
import OAI.Geometry.SmoothYau.Spectrum.UnitSphereProjection

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
abbrev ThreeManifold := Sphere 2 × Circle
abbrev ThreeProductModel := Euclidean 2 × Euclidean 1
abbrev ThreeModel := WithLp 2 ThreeProductModel
abbrev ThreeAmbient := WithLp 2 (Euclidean 3 × ℂ)
instance threeProductChartedSpace : ChartedSpace ThreeProductModel ThreeManifold :=
  prodChartedSpace (Euclidean 2) (Sphere 2) (Euclidean 1) Circle
instance threeProductIsManifold : IsManifold 𝓘(ℝ,ThreeProductModel) ∞ ThreeManifold := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (Sphere 2) Circle
abbrev threeModelEquiv : ThreeProductModel ≃L[ℝ] ThreeModel :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Euclidean 2) (Euclidean 1)).symm
instance threeChartedSpace : ChartedSpace ThreeModel ThreeManifold :=
  reModelChartedSpace threeModelEquiv
instance threeIsManifold : IsManifold 𝓘(ℝ,ThreeModel) ∞ ThreeManifold :=
  reModel_isManifold threeModelEquiv

def threeImmersion : ThreeManifold → ThreeAmbient :=
  productImmersion (fun x : Sphere 2 => (x : Euclidean 3)) (fun z : Circle => (z : ℂ))
lemma threeImmersion_product_smooth :
    ContMDiff 𝓘(ℝ,ThreeProductModel) 𝓘(ℝ,ThreeAmbient) ∞ threeImmersion := by
  rw [modelWithCornersSelf_prod]
  exact productImmersion_smooth sphere_two_immersion_smooth circle_immersion_smooth
lemma threeImmersion_smooth : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) ∞ threeImmersion :=
  contMDiff_reModel_source threeModelEquiv threeImmersion_product_smooth
lemma threeImmersion_injective (x : ThreeManifold) :
    Function.Injective (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion x) := by
  rw [mfderiv_reModel_source threeModelEquiv threeImmersion_product_smooth]
  change Function.Injective ((mfderiv 𝓘(ℝ,ThreeProductModel) 𝓘(ℝ,ThreeAmbient) threeImmersion x : ThreeProductModel → ThreeAmbient) ∘ (threeModelEquiv.symm : ThreeModel → ThreeProductModel))
  apply Function.Injective.comp
  · rw [modelWithCornersSelf_prod]
    exact productImmersion_injective_derivative sphere_two_immersion_smooth circle_immersion_smooth
      sphere_two_immersion_injective circle_immersion_injective x
  · exact threeModelEquiv.symm.injective

def threeBackgroundMetric : SmoothMetric ThreeModel ThreeManifold :=
  inducedMetric threeImmersion threeImmersion_smooth threeImmersion_injective

lemma threeModel_finrank : Module.finrank ℝ ThreeModel = 3 := by
  rw [(threeModelEquiv.symm.toLinearEquiv).finrank_eq]
  simp [ThreeProductModel,Euclidean]
end


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeModelNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeModelContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
instance circle_dimension_fact : Fact (Module.finrank ℝ ℂ = 1+1) := ⟨by simp⟩
def threeFrame (p : ThreeManifold) : ThreeModel →ₗᵢ[ℝ] ThreeAmbient :=
  lpProductIsometry (sphereFrame p.1) (unitSphereFrame (n:=1) p.2)
def threeChartMap (p : ThreeManifold) : ThreeModel → ThreeAmbient :=
  lpProductFunction (roundChart (p.1 : Euclidean 3) (sphereFrame p.1))
    (roundChart (p.2 : ℂ) (unitSphereFrame (n:=1) p.2))
lemma three_chart_symm (p : ThreeManifold) :
    threeImmersion ∘ (chartAt ThreeModel p).symm = threeChartMap p := by
  funext y
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · change ((chartAt (Euclidean 2) p.1).symm y.fst : Euclidean 3) = _
    exact congrFun (sphere_chart_symm p.1) y.fst
  · change ((chartAt (Euclidean 1) p.2).symm y.snd : ℂ) = _
    exact congrFun (unitSphere_chart_symm (n:=1) p.2) y.snd
lemma three_chart_center (p : ThreeManifold) : chartAt ThreeModel p p = 0 := by
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · exact sphere_chart_center p.1
  · exact unitSphere_chart_center (n:=1) p.2
lemma three_chart_target (p : ThreeManifold) : (chartAt ThreeModel p).target = univ := by
  change ( (chartAt ThreeProductModel p).trans threeModelEquiv.toHomeomorph.toOpenPartialHomeomorph ).target = _
  simp only [OpenPartialHomeomorph.trans_target,Homeomorph.toOpenPartialHomeomorph_target,
    univ_inter]
  have h : (chartAt ThreeProductModel p).target = univ := by
    change (chartAt (Euclidean 2) p.1).target ×ˢ (chartAt (Euclidean 1) p.2).target = univ
    have hc : (chartAt (Euclidean 1) p.2).target = univ := by
      change (stereographic' 1 (-p.2)).target = univ
      exact stereographic'_target (-p.2)
    rw [sphere_chart_target,hc,univ_prod_univ]
  rw [h,preimage_univ]
lemma three_coordinate_embedding (p : ThreeManifold) (y v : ThreeModel) :
    mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion
      ((chartAt ThreeModel p).symm y)
      (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) (chartAt ThreeModel p).symm y v) =
        fderiv ℝ (threeChartMap p) y v := by
  have hy : y ∈ (chartAt ThreeModel p).target := by rw [three_chart_target]; trivial
  have hh := mfderiv_comp y
    (threeImmersion_smooth.mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (n := ∞) p) hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L => L v) hh
  rw [mfderiv_eq_fderiv,three_chart_symm] at he
  exact he.symm
lemma three_metricCoefficients (p : ThreeManifold) (y : ThreeModel) (i j : CoordIndex ThreeModel) :
    metricCoefficients threeBackgroundMetric p y i j =
      inner ℝ (fderiv ℝ (threeChartMap p) y (Module.finBasis ℝ ThreeModel i))
        (fderiv ℝ (threeChartMap p) y (Module.finBasis ℝ ThreeModel j)) := by
  change (inner ℝ : ThreeAmbient → ThreeAmbient → ℝ) (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion ((chartAt ThreeModel p).symm y) (coordinateVector p y i)) (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion ((chartAt ThreeModel p).symm y) (coordinateVector p y j)) = _
  simp only [coordinateVector,three_coordinate_embedding]
lemma three_metricCoefficients_zero (p : ThreeManifold) :
    metricCoefficients threeBackgroundMetric p 0 = Matrix.gram ℝ (Module.finBasis ℝ ThreeModel) := by
  have hh : fderiv ℝ (threeChartMap p) 0 = (threeFrame p).toContinuousLinearMap :=
    (lpProductRoundChart_first (p.1:Euclidean 3) (p.2:ℂ) (sphereFrame p.1)
      (unitSphereFrame (n:=1) p.2)).fderiv
  ext i j
  rw [three_metricCoefficients,hh]
  exact (threeFrame p).inner_map_map _ _
lemma three_metricCoefficients_first (p : ThreeManifold) (i j : CoordIndex ThreeModel) :
    HasFDerivAt (fun y => metricCoefficients threeBackgroundMetric p y i j)
      (0 : ThreeModel →L[ℝ] ℝ) 0 := by
  simp_rw [three_metricCoefficients]
  exact lpProductRoundChart_metric_first _ _ _ _ (sphereFrame_orthogonal p.1)
    (unitSphereFrame_orthogonal p.2) _ _
lemma three_metricFirstCoefficient_zero (p : ThreeManifold) (j : CoordIndex ThreeModel) :
    metricFirstCoefficient threeBackgroundMetric p j 0 = 0 := by
  have hn : (metricCoefficients threeBackgroundMetric p 0).det ≠ 0 :=
    (metricCoefficients_det_pos threeBackgroundMetric p (by rw [three_chart_target]; trivial)).ne'
  have hh := fun i => (zero_jet_density_inverse (metricCoefficients threeBackgroundMetric p)
    (three_metricCoefficients_first p) hn i j).fderiv
  simp only [metricFirstCoefficient,hh,_root_.zero_apply,Finset.sum_const_zero,mul_zero]
theorem three_laplace_at_center (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (p : ThreeManifold) :
    laplaceBeltrami threeBackgroundMetric u p = ∑ i, ∑ j,
      (Matrix.gram ℝ (Module.finBasis ℝ ThreeModel))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (u ∘ (chartAt ThreeModel p).symm) y
        (Module.finBasis ℝ ThreeModel j)) 0 (Module.finBasis ℝ ThreeModel i) := by
  rw [laplaceBeltrami_inChart hu threeBackgroundMetric p p (mem_chart_source _ _),three_chart_center,
    localLaplacian_expansion hu threeBackgroundMetric p (by rw [three_chart_target]; trivial)]
  simp only [three_metricCoefficients_zero,three_metricFirstCoefficient_zero,
    zero_mul,Finset.sum_const_zero,add_zero]
end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff BoundedContinuousFunction ENNReal NNReal
variable {P : Type*} [TopologicalSpace P]
lemma three_simple_eigenpair_open (q : P → SmoothMetric ThreeModel ThreeManifold)
    (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
      (chartAt ThreeModel r).target) (a₀ : P)
    (lam : ℝ) (hlam : 0 < lam) (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami (q a₀) u x = lam*u x)
    (hsimple : ∀ v, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami (q a₀) v x = lam*v x) → ∃ c : ℝ, v = fun x => c*u x)
    (hreg : ∀ x, u x=0 → fderiv ℝ (u ∘ (chartAt ThreeModel x).symm)
      ((chartAt ThreeModel x) x) ≠ 0)
    {J : Type*} [Fintype J] (Q : J → Set (Fin 3 → ℝ)) (d : J → ℝ)
    (ψ : (Fin 3 → ℝ) → ThreeManifold) (hψ : Continuous ψ)
    (L : ℝ≥0∞) (hL : L < SignTests.signCertificate Q d (u ∘ ψ))
    {B D : ℝ} (hB : B < lam) (hD : lam < D) :
    ∀ᶠ a in 𝓝 a₀, ∃ e : ℝ, ∃ v : ThreeManifold → ℝ,
      B < e ∧ e < D ∧ ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ x, -laplaceBeltrami (q a) v x = e*v x) ∧
      (∀ x, v x=0 → fderiv ℝ (v ∘ (chartAt ThreeModel x).symm)
        ((chartAt ThreeModel x) x) ≠ 0) ∧
      L < SignTests.signCertificate Q d (v ∘ ψ) := by
  classical
  have hs : Module.finrank ℝ ThreeModel < 2*(2*(2:ℝ)) := by norm_num [threeModel_finrank]
  let A := (nonempty_compactMetricAtlas (q a₀) 2 hs).some
  let I := (nonempty_metricIntegralAtlas (E:=ThreeModel) (M:=ThreeManifold)).some
  let C : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  obtain ⟨α,hα1,hα⟩ := A.exists_parametrix_threshold C
  have hα0 : 0 < α := zero_lt_one.trans_le hα1
  obtain ⟨e,w,he,hw,hce,hcw,hpair⟩ := A.actual_simple_eigenpair_persistence I C α hα0
    (hα α le_rfl).1 (hα α le_rfl).2 lam (ne_of_gt (add_pos hα0 hlam))
    u hu hu0 hue hsimple q a₀ rfl (fun i => hq (A.p i))
  have hwr : ∀ᶠ a in 𝓝 a₀, ∀ x, A.realValue A.highIndex (w a) x=0 →
      fderiv ℝ (A.realValue A.highIndex (w a) ∘ (chartAt ThreeModel x).symm)
        ((chartAt ThreeModel x) x) ≠ 0 :=
    hcw.eventually (A.eventually_regular_realValue (w a₀) (by simpa only [hw] using hreg))
  let f (v : A.realH A.highIndex) : (Fin 3 → ℝ) → ℝ := A.realValue A.highIndex v ∘ ψ
  have hf : LowerSemicontinuous (fun v => SignTests.signCertificate Q d (f v)) := by
    apply SignTests.lowerSemicontinuous_signCertificate
    · intro v
      exact ((A.realRepresentative A.highIndex v).continuous.comp hψ).measurable
    · intro y
      exact (A.realRepresentative A.highIndex).continuous.eval_const (ψ y)
  have hwl : ∀ᶠ a in 𝓝 a₀, L < SignTests.signCertificate Q d (f (w a)) :=
    hcw.eventually (hf (w a₀) L (by simpa only [f,hw] using hL))
  have heb : ∀ᶠ a in 𝓝 a₀, B < e a := hce.eventually (lt_mem_nhds (he ▸ hB))
  have hed : ∀ᶠ a in 𝓝 a₀, e a < D := hce.eventually (gt_mem_nhds (he ▸ hD))
  filter_upwards [hpair,hwr,hwl,heb,hed] with a ha hr hl hb hd
  exact ⟨e a,A.realValue A.highIndex (w a),hb,hd,ha.1,ha.2.1,ha.2.2,hr,hl⟩
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
def fourToThree (q : FourManifold) : ThreeManifold := (q.1,q.2.1)
def fourToCircle (q : FourManifold) : Circle := q.2.2
lemma fourToThree_product_smooth : ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeProductModel) ∞ fourToThree := by
  unfold FourModel ThreeProductModel
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod,modelWithCornersSelf_prod]
  exact contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)
lemma fourToThree_smooth : ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) ∞ fourToThree :=
  contMDiff_reModel_target threeModelEquiv fourToThree_product_smooth
lemma fourToCircle_smooth : ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) ∞ fourToCircle := by
  unfold FourModel
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod]
  exact contMDiff_snd.comp contMDiff_snd
lemma mfderiv_fourToThree (q : FourManifold) (v : FourModel) :
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) fourToThree q v=threeModelEquiv (v.1,v.2.1) := by
  rw [mfderiv_reModel_target threeModelEquiv fourToThree_product_smooth]
  change threeModelEquiv ((mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeProductModel) fourToThree q : FourModel →L[ℝ] ThreeProductModel) v) = _
  congr 1
  unfold FourModel ThreeProductModel fourToThree
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod,modelWithCornersSelf_prod]
  change ((mfderiv _ _ (fun q : FourManifold => (Prod.fst q, (Prod.fst ∘ Prod.snd) q)) q) v) = _
  rw [mfderiv_prodMk mdifferentiableAt_fst (mdifferentiableAt_fst.comp _ mdifferentiableAt_snd)]
  rw [mfderiv_comp _ mdifferentiableAt_fst mdifferentiableAt_snd]
  rw [mfderiv_fst,mfderiv_snd,mfderiv_fst]
  rfl
lemma mfderiv_fourToCircle (q : FourManifold) (v : FourModel) :
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) fourToCircle q v=v.2.2 := by
  unfold FourModel fourToCircle
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod]
  change (mfderiv _ _ (Prod.snd ∘ Prod.snd) q) v = v.2.2
  rw [mfderiv_comp _ mdifferentiableAt_snd mdifferentiableAt_snd]
  rw [mfderiv_snd,mfderiv_snd]
  rfl
def circleRoundMetric : SmoothMetric (Euclidean 1) Circle :=
  inducedMetric (fun z : Circle => (z:ℂ)) circle_immersion_smooth circle_immersion_injective

end YauCounterexamples
end

end OAI
