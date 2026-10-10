import Mathlib
import OAI.Geometry.SmoothYau.Geometry.BlockDiagonalInverse
import OAI.Geometry.SmoothYau.NodalMeasure.SphericalNodalFinite
import OAI.Geometry.SmoothYau.Smoothness.FourLiftThreeSmul
import OAI.Geometry.SmoothYau.SphereMetric.ThreeFixedFormNorm

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
local instance fourChartThreeSmul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance fourChartFourSmul : ContinuousSMul ℝ FourModel := IsBoundedSMul.continuousSMul
local instance fourChartCircleSmul : ContinuousSMul ℝ (Euclidean 1) := IsBoundedSMul.continuousSMul
def fourSplitEquiv : FourModel ≃L[ℝ] ThreeModel × Euclidean 1 :=
  (ContinuousLinearEquiv.prodAssoc ℝ (Euclidean 2) (Euclidean 1) (Euclidean 1)).symm.trans
    (threeModelEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Euclidean 1)))
def fourProjThree : FourModel →L[ℝ] ThreeModel :=
  (ContinuousLinearMap.fst ℝ ThreeModel (Euclidean 1)).comp fourSplitEquiv.toContinuousLinearMap
def fourProjCircle : FourModel →L[ℝ] Euclidean 1 :=
  (ContinuousLinearMap.snd ℝ ThreeModel (Euclidean 1)).comp fourSplitEquiv.toContinuousLinearMap
lemma four_chart_target (p : FourManifold) : (chartAt FourModel p).target=univ := by
  change (chartAt (Euclidean 2) p.1).target ×ˢ
    ((chartAt (Euclidean 1) p.2.1).target ×ˢ (chartAt (Euclidean 1) p.2.2).target)=univ
  have hc (z : Circle) : (chartAt (Euclidean 1) z).target=univ := by
    change (stereographic' 1 (-z)).target=univ
    exact stereographic'_target (-z)
  rw [sphere_chart_target,hc,hc,univ_prod_univ,univ_prod_univ]
lemma four_chart_symm_three (p : FourManifold) (y : FourModel) :
    fourToThree ((chartAt FourModel p).symm y)=
      (chartAt ThreeModel (fourToThree p)).symm (fourProjThree y) := by rfl
lemma four_chart_symm_circle (p : FourManifold) (y : FourModel) :
    fourToCircle ((chartAt FourModel p).symm y)=
      (chartAt (Euclidean 1) (fourToCircle p)).symm (fourProjCircle y) := by rfl
lemma four_chart_three (p q : FourManifold) :
    fourProjThree (chartAt FourModel p q)=chartAt ThreeModel (fourToThree p) (fourToThree q) := by rfl
lemma four_chart_symm_smooth (p : FourManifold) :
    ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) ∞ (chartAt FourModel p).symm := by
  have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,FourModel)) (n:=∞) (x:=p)
  rwa [four_chart_target,contMDiffOn_univ] at h
lemma circle_chart_symm_smooth (p : Circle) :
    ContMDiff 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,Euclidean 1) ∞ (chartAt (Euclidean 1) p).symm := by
  have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,Euclidean 1)) (n:=∞) (x:=p)
  have ht : (chartAt (Euclidean 1) p).target=univ := by
    change (stereographic' 1 (-p)).target=univ
    exact stereographic'_target (-p)
  rwa [ht,contMDiffOn_univ] at h
lemma four_chart_deriv_three (p : FourManifold) (y v : FourModel) :
    fourProjThree (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v)=
      mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) (chartAt ThreeModel (fourToThree p)).symm
        (fourProjThree y) (fourProjThree v) := by
  have hs : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) ∞ (chartAt ThreeModel (fourToThree p)).symm := by
    have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,ThreeModel)) (n:=∞) (x:=fourToThree p)
    rwa [three_chart_target,contMDiffOn_univ] at h
  have h1 := mfderiv_comp y (fourToThree_smooth.mdifferentiable (by simp) _)
    ((four_chart_symm_smooth p).mdifferentiable (by simp) y)
  have he : fourToThree ∘ (chartAt FourModel p).symm =
      (chartAt ThreeModel (fourToThree p)).symm ∘ fourProjThree := funext (four_chart_symm_three p)
  rw [he,mfderiv_comp y (hs.mdifferentiable (by simp) _) fourProjThree.mdifferentiableAt] at h1
  have hh := congrArg (fun L => L v) h1
  change mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) (chartAt ThreeModel (fourToThree p)).symm
      (fourProjThree y) (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) fourProjThree y v) =
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) fourToThree ((chartAt FourModel p).symm y)
      (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v) at hh
  have hp : (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) fourProjThree y :
      FourModel →L[ℝ] ThreeModel) = fourProjThree :=
    (mfderiv_eq_fderiv (f := (fourProjThree : FourModel → ThreeModel)) (x := y)).trans
      fourProjThree.fderiv
  have hm := mfderiv_fourToThree ((chartAt FourModel p).symm y)
    (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v)
  exact hm.symm.trans (hh.symm.trans (congrArg
    (fun z : ThreeModel => mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel)
      (chartAt ThreeModel (fourToThree p)).symm (fourProjThree y) z)
    (congrArg (fun L : FourModel →L[ℝ] ThreeModel => L v) hp)))
lemma four_chart_deriv_circle (p : FourManifold) (y v : FourModel) :
    fourProjCircle (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v)=
      mfderiv 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,Euclidean 1) (chartAt (Euclidean 1) (fourToCircle p)).symm
        (fourProjCircle y) (fourProjCircle v) := by
  have h1 := mfderiv_comp y (fourToCircle_smooth.mdifferentiable (by simp) _)
    ((four_chart_symm_smooth p).mdifferentiable (by simp) y)
  have he : fourToCircle ∘ (chartAt FourModel p).symm =
      (chartAt (Euclidean 1) (fourToCircle p)).symm ∘ fourProjCircle := funext (four_chart_symm_circle p)
  rw [he,mfderiv_comp y ((circle_chart_symm_smooth _).mdifferentiable (by simp) _) fourProjCircle.mdifferentiableAt] at h1
  have hh := congrArg (fun L => L v) h1
  change mfderiv 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,Euclidean 1) (chartAt (Euclidean 1) (fourToCircle p)).symm
      (fourProjCircle y) (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) fourProjCircle y v) =
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) fourToCircle ((chartAt FourModel p).symm y)
      (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v) at hh
  have hp : (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) fourProjCircle y :
      FourModel →L[ℝ] Euclidean 1) = fourProjCircle :=
    (mfderiv_eq_fderiv (f := (fourProjCircle : FourModel → Euclidean 1)) (x := y)).trans
      fourProjCircle.fderiv
  have hm := mfderiv_fourToCircle ((chartAt FourModel p).symm y)
    (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y v)
  exact hm.symm.trans (hh.symm.trans (congrArg
    (fun z : Euclidean 1 => mfderiv 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,Euclidean 1)
      (chartAt (Euclidean 1) (fourToCircle p)).symm (fourProjCircle y) z)
    (congrArg (fun L : FourModel →L[ℝ] Euclidean 1 => L v) hp)))
lemma four_chartMetricForm (g : SmoothMetric ThreeModel ThreeManifold) (p : FourManifold)
    (y v w : FourModel) :
    chartMetricForm (fourProductMetric g) p y v w =
      chartMetricForm g (fourToThree p) (fourProjThree y) (fourProjThree v) (fourProjThree w)+
      chartMetricForm circleRoundMetric (fourToCircle p) (fourProjCircle y) (fourProjCircle v) (fourProjCircle w) := by
  rw [chartMetricForm_pairing,chartMetricForm_pairing,chartMetricForm_pairing]
  let D : FourModel →L[ℝ] FourModel :=
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) (chartAt FourModel p).symm y
  change fourProductInner g ((chartAt FourModel p).symm y) (D v) (D w) = _
  refine (fourProductInner_apply g ((chartAt FourModel p).symm y) (D v) (D w)).trans ?_
  change g.inner ((chartAt ThreeModel (fourToThree p)).symm (fourProjThree y))
      (fourProjThree (D v)) (fourProjThree (D w)) +
    circleRoundMetric.inner ((chartAt (Euclidean 1) (fourToCircle p)).symm (fourProjCircle y))
      (fourProjCircle (D v)) (fourProjCircle (D w)) = _
  exact congrArg₂ (fun a b : ℝ => a + b)
    (congrArg₂ (fun a b : ThreeModel =>
      g.inner ((chartAt ThreeModel (fourToThree p)).symm (fourProjThree y)) a b)
      (four_chart_deriv_three p y v) (four_chart_deriv_three p y w))
    (congrArg₂ (fun a b : Euclidean 1 =>
      circleRoundMetric.inner ((chartAt (Euclidean 1) (fourToCircle p)).symm (fourProjCircle y)) a b)
      (four_chart_deriv_circle p y v) (four_chart_deriv_circle p y w))
end


section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
local instance fourLapThreeSmul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance fourLapFourSmul : ContinuousSMul ℝ FourModel := IsBoundedSMul.continuousSMul
def fourSplitBasis : Module.Basis (CoordIndex ThreeModel ⊕ CoordIndex (Euclidean 1)) ℝ FourModel :=
  ((Module.finBasis ℝ ThreeModel).prod (Module.finBasis ℝ (Euclidean 1))).map fourSplitEquiv.symm.toLinearEquiv
lemma fourSplitBasis_inl (i : CoordIndex ThreeModel) :
    fourSplitEquiv (fourSplitBasis (.inl i))=(Module.finBasis ℝ ThreeModel i,0) := by
  simp [fourSplitBasis,Module.Basis.prod_apply]
lemma fourSplitBasis_inr (i : CoordIndex (Euclidean 1)) :
    fourSplitEquiv (fourSplitBasis (.inr i))=(0,Module.finBasis ℝ (Euclidean 1) i) := by
  simp [fourSplitBasis,Module.Basis.prod_apply]
lemma fourSplitBasis_Pa (i : CoordIndex ThreeModel) : fourProjThree (fourSplitBasis (.inl i))=Module.finBasis ℝ ThreeModel i :=
  congrArg Prod.fst (fourSplitBasis_inl i)
lemma fourSplitBasis_Pb (i : CoordIndex (Euclidean 1)) : fourProjThree (fourSplitBasis (.inr i))=0 :=
  congrArg Prod.fst (fourSplitBasis_inr i)
lemma fourSplitBasis_Qa (i : CoordIndex ThreeModel) : fourProjCircle (fourSplitBasis (.inl i))=0 :=
  congrArg Prod.snd (fourSplitBasis_inl i)
lemma fourSplitBasis_Qb (i : CoordIndex (Euclidean 1)) : fourProjCircle (fourSplitBasis (.inr i))=Module.finBasis ℝ (Euclidean 1) i :=
  congrArg Prod.snd (fourSplitBasis_inr i)
lemma four_metric_block (g : SmoothMetric ThreeModel ThreeManifold) (p : FourManifold) (y : FourModel) :
    bilinearCoordinateMatrix fourSplitBasis (chartMetricForm (fourProductMetric g) p y)=
      Matrix.fromBlocks (metricCoefficients g (fourToThree p) (fourProjThree y)) 0 0
        (metricCoefficients circleRoundMetric (fourToCircle p) (fourProjCircle y)) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j
  all_goals simp only [bilinearCoordinateMatrix,four_chartMetricForm,fourSplitBasis_Pa,
    fourSplitBasis_Pb,fourSplitBasis_Qa,fourSplitBasis_Qb,map_zero,_root_.zero_apply,add_zero,zero_add,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply]
  all_goals first | rfl | (rw [chartMetricForm_pairing]; rfl)
lemma metricCoefficients_differentiable_univ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (g : SmoothMetric E M) (p : M) (ht : (chartAt E p).target=univ) :
    Differentiable ℝ (metricCoefficients g p) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  have h := contDiffOn_metricCoefficient g p i j
  rw [ht,contDiffOn_univ] at h
  exact h.differentiable (by simp)
lemma laplaceBeltrami_four_lift (g : SmoothMetric ThreeModel ThreeManifold) (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (p : FourManifold) :
    laplaceBeltrami (fourProductMetric g) (u ∘ fourToThree) p=laplaceBeltrami g u (fourToThree p) := by
  rw [laplaceBeltrami_any_basis_univ _ _ (four_chart_target p) fourSplitBasis (hu.comp fourToThree_smooth)]
  simp_rw [four_metric_block]
  have hfun : (u ∘ fourToThree) ∘ (chartAt FourModel p).symm =
      (u ∘ (chartAt ThreeModel (fourToThree p)).symm) ∘ fourProjThree := by
    funext y
    simp only [Function.comp_apply,four_chart_symm_three]
  rw [hfun]
  have ht : (chartAt (Euclidean 1) (fourToCircle p)).target=univ := by
    change (stereographic' 1 (-fourToCircle p)).target=univ
    exact stereographic'_target _
  have hs : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) ∞ (chartAt ThreeModel (fourToThree p)).symm := by
    have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,ThreeModel)) (n:=∞) (x:=fourToThree p)
    rwa [three_chart_target,contMDiffOn_univ] at h
  rw [coordinateMetricLaplacian_split fourProjThree fourProjCircle
    (Module.finBasis ℝ ThreeModel) (Module.finBasis ℝ (Euclidean 1)) fourSplitBasis
    fourSplitBasis_Pa fourSplitBasis_Pb fourSplitBasis_Qa
    _ _ (metricCoefficients_differentiable_univ _ _ (three_chart_target _))
    (metricCoefficients_differentiable_univ _ _ ht)
    (fun y => metricCoefficients_det_pos _ _ (by rw [three_chart_target]; trivial))
    (fun y => metricCoefficients_det_pos _ _ (by rw [ht]; trivial))
    _ (contMDiff_iff_contDiff.mp (hu.comp hs))]
  rw [four_chart_three]
  rfl
lemma four_lift_regular (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (hr : ThreeRegular u) :
    ∀ p, (u ∘ fourToThree) p=0 →
      fderiv ℝ ((u ∘ fourToThree) ∘ (chartAt FourModel p).symm) (chartAt FourModel p p)≠0 := by
  intro p hp hh
  apply hr (fourToThree p) hp
  have hs : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) ∞ (chartAt ThreeModel (fourToThree p)).symm := by
    have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,ThreeModel)) (n:=∞) (x:=fourToThree p)
    rwa [three_chart_target,contMDiffOn_univ] at h
  have hfun : (u ∘ fourToThree) ∘ (chartAt FourModel p).symm =
      (u ∘ (chartAt ThreeModel (fourToThree p)).symm) ∘ fourProjThree := by
    funext y
    simp only [Function.comp_apply,four_chart_symm_three]
  rw [hfun,fderiv_comp _ ((contMDiff_iff_contDiff.mp (hu.comp hs)).differentiable (by simp) _)
    fourProjThree.differentiableAt,fourProjThree.fderiv,four_chart_three] at hh
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun L : FourModel →L[ℝ] ℝ => L (fourSplitEquiv.symm (v,0))) hh
  change fderiv ℝ (u ∘ (chartAt ThreeModel (fourToThree p)).symm)
    (chartAt ThreeModel (fourToThree p) (fourToThree p))
    (fourProjThree (fourSplitEquiv.symm (v,0))) = (0:ℝ) at h
  have hv : fourProjThree (fourSplitEquiv.symm (v,0))=v := by
    change (fourSplitEquiv (fourSplitEquiv.symm (v,0))).1=v
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [hv] at h
  exact h
end


open Set Filter Manifold Bundle Function Matrix BoxIntegral MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise ENNReal NNReal
local instance fourWaveThreeSmul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance fourWaveCircleSmul : ContinuousSMul ℝ (Euclidean 1) := IsBoundedSMul.continuousSMul
def fourTailHeadLinear : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) × ℝ where
  toFun x := (Fin.tail x,x 0)
  invFun x := Fin.cons x.2 x.1
  left_inv x := by ext i; exact Fin.cases rfl (fun j => rfl) i
  right_inv x := by rfl
  map_add' x y := rfl
  map_smul' t x := rfl
def fourTailHeadEquiv : (Fin 4 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) × ℝ := fourTailHeadLinear.toContinuousLinearEquiv
def fourCircleCoord : ℝ ≃L[ℝ] Euclidean 1 := ContinuousLinearEquiv.ofFinrankEq (by simp [Euclidean])
def fourWaveEquiv : (Fin 4 → ℝ) ≃L[ℝ] FourModel :=
  fourTailHeadEquiv.trans (((normalWaveEquiv.trans threeNormalEquiv).prodCongr fourCircleCoord).trans fourSplitEquiv.symm)
def fourProfileCenter : FourManifold := (threeProfileCenter.1,(threeProfileCenter.2,1))
lemma fourProfileCenter_three : fourToThree fourProfileCenter=threeProfileCenter := rfl
lemma fourWave_proj (x : Fin 4 → ℝ) :
    fourProjThree (fourWaveEquiv x)=threeNormalEquiv (normalWaveEquiv (Fin.tail x)) := by
  change (fourSplitEquiv (fourSplitEquiv.symm _)).1 = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl
lemma fourWave_lift (u : ThreeManifold → ℝ) :
    ((u ∘ fourToThree) ∘ (chartAt FourModel fourProfileCenter).symm) ∘ fourWaveEquiv =
      ((u ∘ threeNormalInv) ∘ normalWaveEquiv) ∘ Fin.tail := by
  funext x
  simp only [Function.comp_apply,four_chart_symm_three,fourWave_proj,fourProfileCenter_three,threeNormalInv]
lemma extrudeSet_tailhead (P : Set (Fin 3 → ℝ)) :
    SignTests.extrudeSet P = fourTailHeadEquiv ⁻¹' (P ×ˢ Ioo 0 1) := by
  ext x
  simp only [SignTests.extrudeSet,mem_preimage,SignTests.extrusionEquiv_apply,mem_prod]
  tauto
lemma extrudeSet_open {P : Set (Fin 3 → ℝ)} (hP : IsOpen P) : IsOpen (SignTests.extrudeSet P) := by
  rw [extrudeSet_tailhead]
  exact (hP.prod isOpen_Ioo).preimage fourTailHeadEquiv.continuous
lemma extrudeSet_convex {P : Set (Fin 3 → ℝ)} (hP : Convex ℝ P) : Convex ℝ (SignTests.extrudeSet P) := by
  rw [extrudeSet_tailhead]
  exact (hP.prod (convex_Ioo (0:ℝ) 1)).linear_preimage fourTailHeadEquiv.toLinearMap
lemma extrudeSet_disjoint {P Q : Set (Fin 3 → ℝ)} (h : Disjoint P Q) :
    Disjoint (SignTests.extrudeSet P) (SignTests.extrudeSet Q) := by
  rw [extrudeSet_tailhead,extrudeSet_tailhead]
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp h hx.1 hy.1
def fourWaveCompact (R : ℝ) : Set FourModel :=
  fourWaveEquiv '' (fourTailHeadEquiv.symm ''
    ((normalWaveEquiv.symm '' Metric.closedBall 0 (R/2)) ×ˢ Icc 0 1))
lemma fourWaveCompact_isCompact (R : ℝ) : IsCompact (fourWaveCompact R) :=
  ((((isCompact_closedBall (0:NormalWaveSpace) (R/2)).image normalWaveEquiv.symm.continuous).prod isCompact_Icc).image
    fourTailHeadEquiv.symm.continuous).image fourWaveEquiv.continuous
lemma fourWaveCompact_mem {R : ℝ} (x : Fin 4 → ℝ)
    (hx : normalWaveEquiv (Fin.tail x)∈Metric.closedBall 0 (R/2)) (hx0 : x 0∈Ioo 0 1) :
    fourWaveEquiv x∈fourWaveCompact R := by
  refine ⟨x,⟨fourTailHeadEquiv x,?_,fourTailHeadEquiv.symm_apply_apply x⟩,rfl⟩
  exact ⟨⟨normalWaveEquiv (Fin.tail x),hx,normalWaveEquiv.symm_apply_apply _⟩,hx0.1.le,hx0.2.le⟩
lemma four_signCertificate_bound (g : SmoothMetric FourModel FourManifold) (R : ℝ) :
    ∃ D : ℝ≥0, 0<D ∧ ∀ u : ThreeManifold → ℝ, Continuous u →
      ∀ (I : Box (Fin 3)), normalWaveEquiv '' Box.Icc I⊆Metric.closedBall 0 (R/2) →
      ∀ (partition : TaggedPrepartition I) (d : {J : Box (Fin 3) // J∈partition.boxes} → ℝ),
      (∀ j, 0<d j) → SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ threeNormalInv) ∘ normalWaveEquiv) ≤ (D:ℝ≥0∞)*nodalMeasure g 3 (u ∘ fourToThree) := by
  classical
  let K := fourWaveCompact R
  obtain ⟨C,hC,hCbound⟩ := nodalMeasure_coordinates_lower_bound g fourProfileCenter (fourWaveCompact_isCompact R)
    (by rw [four_chart_target]; exact subset_univ _)
  let L : ℝ≥0 := max ‖fourWaveEquiv.symm.toContinuousLinearMap‖₊ 1
  have hL : 0<L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlip : LipschitzWith L fourWaveEquiv.symm :=
    fourWaveEquiv.symm.toContinuousLinearMap.lipschitzWith.weaken (le_max_left _ _)
  refine ⟨96*L^3*C ^ 3,by positivity,?_⟩
  intro u hu I hI partition d hd
  let f := ((u ∘ fourToThree) ∘ (chartAt FourModel fourProfileCenter).symm) ∘ fourWaveEquiv
  have hf : Continuous f := ((hu.comp fourToThree_smooth.continuous).comp
    (four_chart_symm_smooth _).continuous).comp fourWaveEquiv.continuous
  let P := fun j : {J : Box (Fin 3) // J∈partition.boxes} => SignTests.extrudeSet (Box.Ioo j.val)
  let Z := (⋃ j, P j) ∩ {z | f z=0}
  have hsign : SignTests.signCertificate (fun j => Box.Ioo j.val) d
      ((u ∘ threeNormalInv) ∘ normalWaveEquiv) ≤ 96*Measure.hausdorffMeasure 3 Z := by
    have hh := SignTests.signCertificate_le_hausdorff_on_union P d hd
      (fun j => extrudeSet_open (isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)))
      (fun j => extrudeSet_convex (convex_pi (fun i _ => convex_Ioo _ _)))
      (fun j k hjk => extrudeSet_disjoint ((partition.toPrepartition.disjoint_coe_of_mem j.property k.property
        (fun hh => hjk (Subtype.ext hh))).mono j.val.Ioo_subset_coe k.val.Ioo_subset_coe))
      f hf.continuousOn
    have he : SignTests.signCertificate P d f = SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ threeNormalInv) ∘ normalWaveEquiv) := by
      dsimp [P,f]
      rw [fourWave_lift,SignTests.signCertificate_extrude]
    rw [he] at hh
    norm_num [Z] at hh ⊢
    exact hh
  have hZsub : Z ⊆ fourWaveEquiv.symm '' (K ∩ {y | (u ∘ fourToThree) ((chartAt FourModel fourProfileCenter).symm y)=0}) := by
    rintro x ⟨hx,hfx⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    have hp : Fin.tail x∈Box.Ioo j.val ∧ x 0∈Ioo 0 1 := by
      change x ∈ SignTests.extrudeSet (Box.Ioo j.val) at hj
      rw [extrudeSet_tailhead] at hj
      exact hj
    refine ⟨fourWaveEquiv x,⟨fourWaveCompact_mem x ?_ hp.2,hfx⟩,fourWaveEquiv.symm_apply_apply x⟩
    apply hI
    exact ⟨Fin.tail x,Box.coe_subset_Icc (partition.toPrepartition.le_of_mem j.property (j.val.Ioo_subset_coe hp.1)),rfl⟩
  have hmeasure : Measure.hausdorffMeasure 3 Z ≤ (L:ℝ≥0∞)^3*(C:ℝ≥0∞)^3*nodalMeasure g 3 (u ∘ fourToThree) := by
    calc
      _ ≤ Measure.hausdorffMeasure 3 (fourWaveEquiv.symm ''
        (K ∩ {y | (u ∘ fourToThree) ((chartAt FourModel fourProfileCenter).symm y)=0})) := measure_mono hZsub
      _ ≤ (L:ℝ≥0∞)^(3:ℝ)*Measure.hausdorffMeasure 3
        (K ∩ {y | (u ∘ fourToThree) ((chartAt FourModel fourProfileCenter).symm y)=0}) :=
          hlip.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤3) _
      _ ≤ (L:ℝ≥0∞)^(3:ℝ)*((C:ℝ≥0∞)^(3:ℝ)*nodalMeasure g 3 (u ∘ fourToThree)) :=
          mul_le_mul' le_rfl (hCbound _ 3 (by norm_num))
      _ = _ := by rw [show (3:ℝ)=(3:ℕ) by norm_num,ENNReal.rpow_natCast,ENNReal.rpow_natCast,mul_assoc]
  apply hsign.trans
  calc
    _ ≤ 96*((L:ℝ≥0∞)^3*(C:ℝ≥0∞)^3*nodalMeasure g 3 (u ∘ fourToThree)) := mul_le_mul' le_rfl hmeasure
    _ = _ := by simp only [ENNReal.coe_mul,ENNReal.coe_pow,ENNReal.coe_ofNat]; ring

end YauCounterexamples
end

end OAI
