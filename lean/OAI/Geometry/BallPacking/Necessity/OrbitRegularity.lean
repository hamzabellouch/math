import Mathlib
import OAI.Geometry.BallPacking.Necessity.FrozenResponse

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap _root_.OAI.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance htransHolderGroup (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ V α) := inferInstance
local instance htransHolderSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ V α) := inferInstance
local instance htransC1Group (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace V α) := inferInstance
local instance htransC1Space (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace V α) := inferInstance

 def diagonalShift (h : ℂ) : C(OffDiagonal ℂ,OffDiagonal ℂ) :=
  ⟨fun p => ⟨(p.val.1+h,p.val.2+h),fun he => p.property (add_right_cancel he)⟩,
    Continuous.subtype_mk (((continuous_fst.comp continuous_subtype_val).add continuous_const).prodMk
      ((continuous_snd.comp continuous_subtype_val).add continuous_const)) _⟩

 def holderShift (α : ℝ) (h : ℂ) : HolderSpace ℂ E α →L[ℝ] HolderSpace ℂ E α :=
  ((((BoundedContinuousFunction.compContinuousCLM E ℝ ⟨fun z => z+h,continuous_id.add continuous_const⟩).comp
      (holderValue α)).prod
    ((BoundedContinuousFunction.compContinuousCLM E ℝ (diagonalShift h)).comp
      (holderDifference α))).codRestrict (holderGraph ℂ E α) (by
        intro f p
        change holderValue α f (p.val.1+h)-holderValue α f (p.val.2+h)=
          (dist p.val.1 p.val.2)^α • holderDifference α f (diagonalShift h p)
        have hh := f.property (diagonalShift h p)
        change holderValue α f (p.val.1+h)-holderValue α f (p.val.2+h)=
          (dist (p.val.1+h) (p.val.2+h))^α • holderDifference α f (diagonalShift h p) at hh
        simpa only [dist_add_right] using hh))

 omit [CompleteSpace E] in
 @[simp] theorem holderShift_value (α : ℝ) (h : ℂ) (f : HolderSpace ℂ E α) (z : ℂ) :
    holderValue α (holderShift α h f) z=holderValue α f (z+h) := rfl

 omit [CompleteSpace E] in
 theorem holderShift_norm (α : ℝ) (h : ℂ) (f : HolderSpace ℂ E α) :
    ‖holderShift α h f‖≤‖f‖ := by
  change max ‖(holderValue α f).compContinuous _‖ ‖(holderDifference α f).compContinuous _‖≤ max ‖f.val.1‖ ‖f.val.2‖
  exact max_le_max (BoundedContinuousFunction.norm_compContinuous_le _ _) (BoundedContinuousFunction.norm_compContinuous_le _ _)

 def c1HolderShift (α : ℝ) (h : ℂ) : C1HolderSpace E α →L[ℝ] C1HolderSpace E α :=
  (((holderShift α h).comp (c1HolderValue α)).prod
    ((holderShift α h).comp (c1HolderDeriv α))).codRestrict (c1HolderGraph α) (by
      intro f
      apply c1HolderGraph_mem_of_hasFDerivAt
      intro z
      exact (c1Holder_hasFDerivAt α f (z+h)).comp z ((hasFDerivAt_id z).add_const h))

 @[simp] theorem c1HolderShift_value (α : ℝ) (h : ℂ) (f : C1HolderSpace E α) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderShift α h f)) z=
      holderValue α (c1HolderValue α f) (z+h) := rfl

 @[simp] theorem c1HolderShift_Deriv (α : ℝ) (h : ℂ) (f : C1HolderSpace E α) :
    c1HolderDeriv α (c1HolderShift α h f)=holderShift α h (c1HolderDeriv α f) := rfl

 theorem c1HolderShift_norm (α : ℝ) (h : ℂ) (f : C1HolderSpace E α) :
    ‖c1HolderShift α h f‖≤‖f‖ :=
  max_le_max (holderShift_norm α h _) (holderShift_norm α h _)

 theorem c1_shift_value_holder_bound (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α) (h k : ℂ) :
    ‖holderShift α h (c1HolderValue α f)-holderShift α k (c1HolderValue α f)‖≤
      ‖c1HolderDeriv α f‖*‖h-k‖ := by
  let v := holderValue α (c1HolderValue α f)
  let d := holderValue α (c1HolderDeriv α f)
  have hd (z : ℂ) : HasFDerivAt v (d z) z := c1Holder_hasFDerivAt α f z
  have hd0 (z : ℂ) : ‖d z‖≤‖c1HolderDeriv α f‖ :=
    ((holderValue α (c1HolderDeriv α f)).norm_coe_le_norm z).trans (holderValue_norm α _)
  have he (x y : ℂ) : ‖d x-d y‖≤‖c1HolderDeriv α f‖*(dist x y)^α :=
    holderSpace_estimate α hα _ x y
  apply (holder_norm_le_of_estimate α _ (by positivity) (by positivity) _ _).trans_eq (max_self _)
  · intro z
    change ‖v (z+h)-v (z+k)‖≤_
    have hh := (convex_univ : Convex ℝ (univ : Set ℂ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ => (hd x).hasFDerivWithinAt) (fun x _ => hd0 x) (mem_univ (z+k)) (mem_univ (z+h))
    simpa only [add_sub_add_left_eq_sub] using hh
  · intro x y
    let w : ℂ → E := fun z => v (x+z)-v (y+z)
    have hw (z : ℂ) : HasFDerivAt w (d (x+z)-d (y+z)) z :=
      ((hd (x+z)).comp z ((hasFDerivAt_id z).const_add x)).sub
        ((hd (y+z)).comp z ((hasFDerivAt_id z).const_add y))
    have hb (z : ℂ) : ‖d (x+z)-d (y+z)‖≤‖c1HolderDeriv α f‖*(dist x y)^α := by
      simpa only [dist_add_right] using he (x+z) (y+z)
    have hh := (convex_univ : Convex ℝ (univ : Set ℂ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hw z).hasFDerivWithinAt) (fun z _ => hb z) (mem_univ k) (mem_univ h)
    change ‖(v (x+h)-v (x+k))-(v (y+h)-v (y+k))‖≤_
    have heq : (v (x+h)-v (x+k))-(v (y+h)-v (y+k))=w h-w k := by dsimp [w]; abel
    rw [heq]
    convert hh using 1
    ring

 theorem c1_shift_value_continuous (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α) :
    Continuous (fun h : ℂ => holderShift α h (c1HolderValue α f)) := by
  apply (LipschitzWith.of_dist_le_mul (K := ⟨‖c1HolderDeriv α f‖,norm_nonneg _⟩) ?_).continuous
  intro h k
  simp only [dist_eq_norm]
  change ‖holderShift α h (c1HolderValue α f)-holderShift α k (c1HolderValue α f)‖≤
    ‖c1HolderDeriv α f‖*‖h-k‖
  exact c1_shift_value_holder_bound α hα f h k

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
local instance hdiffHolderGroup (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ V α) := inferInstance
local instance hdiffHolderSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ V α) := inferInstance

 def holderTranspose (α : ℝ) : HolderSpace ℂ (X →L[ℝ] E) α →L[ℝ] (X →L[ℝ] HolderSpace ℂ E α) :=
  (ContinuousLinearMap.compL ℝ X (HolderSpace ℂ X α) (HolderSpace ℂ E α)).flip
    (holderConstantCLM α) |>.comp (holderOperatorCLM α)

 omit [CompleteSpace E] in
 @[simp] theorem holderTranspose_value (α : ℝ) (D : HolderSpace ℂ (X →L[ℝ] E) α) (v : X) (z : ℂ) :
    holderValue α (holderTranspose α D v) z=holderValue α D z v := rfl

 omit [CompleteSpace E] in
 theorem holder_hasFDerivAt (α : ℝ) (hα : 0<α)
    (F : X → HolderSpace ℂ E α) (D : X → HolderSpace ℂ (X →L[ℝ] E) α)
    (hD : ∀ y z, HasFDerivAt (fun x => holderValue α (F x) z) (holderValue α (D y) z) y)
    (x : X) (hc : ContinuousAt D x) : HasFDerivAt F (holderTranspose α (D x)) x := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro c hcpos
  obtain ⟨ε,hε,hεc⟩ := Metric.mem_nhds_iff.mp (hc (Metric.ball_mem_nhds (D x) hcpos))
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  have hb (w : X) (hw : w∈Metric.ball x ε) : ‖D w-D x‖≤c := by
    simpa only [dist_eq_norm] using (show dist (D w) (D x)<c from hεc hw).le
  apply (holder_norm_le_of_estimate α _ (by positivity) (by positivity) _ _).trans_eq (max_self _)
  · intro z
    change ‖holderValue α (F y) z-holderValue α (F x) z-holderValue α (D x) z (y-x)‖≤_
    apply (convex_ball x ε).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun w _ => (hD w z).hasFDerivWithinAt) _ (Metric.mem_ball_self hε) hy
    intro w hw
    have hh := ((holderValue α (D w-D x)).norm_coe_le_norm z).trans (holderValue_norm α _)
    exact hh.trans (hb w hw)
  · intro z w
    have hh := (convex_ball x ε).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun t _ => ((hD t z).sub (hD t w)).hasFDerivWithinAt)
      (C := c*(dist z w)^α) (φ := holderValue α (D x) z-holderValue α (D x) w) ?_
      (Metric.mem_ball_self hε) hy
    · change ‖(holderValue α (F y) z-holderValue α (F x) z-holderValue α (D x) z (y-x))-
        (holderValue α (F y) w-holderValue α (F x) w-holderValue α (D x) w (y-x))‖≤_
      convert hh using 1
      · congr 1
        simp only [sub_apply,Pi.sub_apply]
        abel
      · ring
    · intro t ht
      have he := holderSpace_estimate α hα (D t-D x) z w
      have heq : (holderValue α (D t) z-holderValue α (D t) w)-
          (holderValue α (D x) z-holderValue α (D x) w)=
          holderValue α (D t-D x) z-holderValue α (D t-D x) w := by
        simp only [map_sub,BoundedContinuousFunction.sub_apply]
        abel
      rw [heq]
      exact he.trans (mul_le_mul_of_nonneg_right (hb t ht) (Real.rpow_nonneg (dist_nonneg) _))

 theorem holder_shift_value_hasFDerivAt (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α) (x : ℂ)
    (hc : ContinuousAt (fun h : ℂ => holderShift α h (c1HolderDeriv α f)) x) :
    HasFDerivAt (fun h : ℂ => holderShift α h (c1HolderValue α f))
      (holderTranspose α (holderShift α x (c1HolderDeriv α f))) x := by
  apply holder_hasFDerivAt α hα _ _ _ x hc
  intro y z
  exact (c1Holder_hasFDerivAt α f (z+y)).comp y ((hasFDerivAt_id y).const_add z)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance orbitHolderGroup (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ V α) := inferInstance
local instance orbitHolderSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ V α) := inferInstance
local instance orbitC1Group (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace V α) := inferInstance
local instance orbitC1Space (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace V α) := inferInstance

 theorem orbit_response_comp (α : ℝ) (k : ℕ) (f : C1HolderSpace E α) (x : ℂ)
    (Φ : ℂ × HolderSpace ℂ E α → C1HolderSpace E α)
    (hΦ : ContDiffAt ℝ ∞ Φ (x,holderShift α x (c1HolderValue α f)))
    (heq : (fun h => c1HolderShift α h f)=ᶠ[𝓝 x] fun h => Φ (h,holderShift α h (c1HolderValue α f)))
    (hG : ContDiffAt ℝ (k:ℕ∞ω) (fun h => holderShift α h (c1HolderValue α f)) x) :
    ContDiffAt ℝ (k:ℕ∞ω) (fun h => c1HolderShift α h f) x := by
  have hk : (k:ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤)
  exact ((hΦ.of_le hk).comp x (contDiffAt_id.prodMk hG)).congr_of_eventuallyEq heq

 theorem orbit_gain (α : ℝ) (f : C1HolderSpace E α) (k : ℕ) (x : ℂ)
    (hF : ContDiffAt ℝ (k:ℕ∞ω) (fun h => c1HolderShift α h f) x)
    (hDG : ∀ᶠ h in 𝓝 x, HasFDerivAt (fun h => holderShift α h (c1HolderValue α f))
      (holderTranspose α (holderShift α h (c1HolderDeriv α f))) h) :
    ContDiffAt ℝ (k+1) (fun h => holderShift α h (c1HolderValue α f)) x := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun h => holderTranspose α (holderShift α h (c1HolderDeriv α f)),?_,?_⟩
  · exact ⟨{h | HasFDerivAt (fun h => holderShift α h (c1HolderValue α f))
        (holderTranspose α (holderShift α h (c1HolderDeriv α f))) h},hDG,fun _ h => h⟩
  · have hdL : ContDiff ℝ (k:ℕ∞ω) (c1HolderDeriv (E := E) α) := ContinuousLinearMap.contDiff _
    have htL : ContDiff ℝ (k:ℕ∞ω) (holderTranspose (X := ℂ) (E := E) α) := ContinuousLinearMap.contDiff _
    exact htL.contDiffAt.comp x (hdL.contDiffAt.comp x hF)

 theorem c1_orbit_contDiff (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α)
    (U : Set ℂ) (hU : IsOpen U)
    (Φ : ℂ × HolderSpace ℂ E α → C1HolderSpace E α)
    (hΦ : ∀ h∈U, ContDiffAt ℝ ∞ Φ (h,holderShift α h (c1HolderValue α f)))
    (heq : ∀ h∈U, c1HolderShift α h f=Φ (h,holderShift α h (c1HolderValue α f))) :
    ∀ h∈U, ContDiffAt ℝ ∞ (fun h => c1HolderShift α h f) h := by
  let F := fun h : ℂ => c1HolderShift α h f
  let G := fun h : ℂ => holderShift α h (c1HolderValue α f)
  have he (h : ℂ) (hh : h∈U) : F=ᶠ[𝓝 h] fun x => Φ (x,G x) := by
    filter_upwards [hU.mem_nhds hh] with x hx
    exact heq x hx
  have hG0 : ContDiff ℝ 0 G := contDiff_zero.mpr (c1_shift_value_continuous α hα f)
  have hF0 : ∀ h∈U, ContDiffAt ℝ 0 F h := by
    intro h hh
    exact orbit_response_comp α 0 f h Φ (hΦ h hh) (he h hh) hG0.contDiffAt
  have hDG : ∀ h∈U, HasFDerivAt G (holderTranspose α (holderShift α h (c1HolderDeriv α f))) h := by
    intro h hh
    apply holder_shift_value_hasFDerivAt α hα f h
    exact (c1HolderDeriv (E := E) α).continuous.continuousAt.comp (hF0 h hh).continuousAt
  have hn : ∀ k : ℕ, ∀ h∈U, ContDiffAt ℝ k F h := by
    intro k
    induction k with
    | zero => exact hF0
    | succ k ih =>
      intro h hh
      have hkG := orbit_gain α f k h (ih h hh) (by
        filter_upwards [hU.mem_nhds hh] with x hx
        exact hDG x hx)
      exact orbit_response_comp α (k+1) f h Φ (hΦ h hh) (he h hh) hkG
  intro h hh
  exact contDiffAt_infty.mpr (fun k => hn k h hh)

 theorem c1_orbit_smooth_function (α : ℝ) (f : C1HolderSpace E α)
    (hf : ContDiffAt ℝ ∞ (fun h : ℂ => c1HolderShift α h f) 0) :
    ContDiff ℝ ∞ (holderValue α (c1HolderValue α f)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have he : ContDiffAt ℝ ∞ (fun h : ℂ => holderValue α (c1HolderValue α f) (z+h)) 0 :=
    (c1HolderEval (E := E) α z).contDiff.contDiffAt.comp 0 hf
  have hz : ContDiffAt ℝ ∞ (fun h : ℂ => h-z) z := contDiffAt_id.sub contDiffAt_const
  have he' : ContDiffAt ℝ ∞ (fun h : ℂ => holderValue α (c1HolderValue α f) (z+h)) (z-z) := by simpa only [sub_self] using he
  have hh := he'.comp (f := fun h : ℂ => h-z) z hz
  convert hh using 1
  funext x
  congr 1
  dsimp only [Function.comp_def]
  abel

 theorem c1_orbit_regular (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α)
    (U : Set ℂ) (hU : IsOpen U) (h0 : (0:ℂ)∈U)
    (Φ : ℂ × HolderSpace ℂ E α → C1HolderSpace E α)
    (hΦ : ∀ h∈U, ContDiffAt ℝ ∞ Φ (h,holderShift α h (c1HolderValue α f)))
    (heq : ∀ h∈U, c1HolderShift α h f=Φ (h,holderShift α h (c1HolderValue α f))) :
    ContDiff ℝ ∞ (holderValue α (c1HolderValue α f)) :=
  c1_orbit_smooth_function α f (c1_orbit_contDiff α hα f U hU Φ hΦ heq 0 h0)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance orbitHGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance orbitHSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance orbitCGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance orbitCSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance orbitCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance orbitCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 def affineSlope {n : ℕ} (a : Phase n) : ℂ →L[ℝ] Phase n :=
  ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Phase n →L[ℝ] Phase n).flip) a

 @[simp] theorem affineSlope_apply {n : ℕ} (a : Phase n) (z : ℂ) : affineSlope a z=z • a := rfl

 def orbitCoefficient {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3)) : HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  holderAffineFamily ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc ((c+p.1 • a,affineSlope a),p.2)

 theorem orbitCoefficient_contDiff {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (ha : a≠0) : ContDiff ℝ ∞ (orbitCoefficient f hf hc c a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hA (z : ℂ) : ‖a‖*‖z‖≤‖affineSlope a z‖ := by
    rw [affineSlope_apply,norm_smul,mul_comm]
  have hh := holderAffineFamily_contDiffAt ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc
    ((c+p.1 • a,affineSlope a),p.2) ‖a‖ (norm_pos_iff.mpr ha) hA
  have hp : ContDiff ℝ ∞ (fun p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3) =>
      ((c+p.1 • a,affineSlope a),p.2)) :=
    ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_const).prodMk contDiff_snd
  exact hh.comp p hp.contDiffAt

 theorem orbitCoefficient_value {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h z : ℂ) :
    holderValue ((1:ℝ)/3) (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v))) z=
      f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v (z+h)) := by
  change f (c+h • a+z • a+holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v) (z+h))=_
  congr 1
  unfold c1HolderAffineCurve
  rw [affineSlope_apply,add_smul]
  abel

 theorem orbitCoefficient_C1 {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h : ℂ) :
    ∃ H : C1HolderSpace (End n) ((1:ℝ)/3), c1HolderValue ((1:ℝ)/3) H=
      orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v)) :=
  ⟨c1HolderAffineCompose ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc
    (c+h • a) (affineSlope a) (c1HolderShift ((1:ℝ)/3) h v),rfl⟩

 theorem affineCoefficient_exterior {n : ℕ} (f : Phase n → End n) (hc : HasCompactSupport f)
    (c a : Phase n) (ha : a≠0) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) :
    ∃ R : ℝ, 0<R ∧ ∀ z : ℂ, R<‖z‖ → f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v z)=0 := by
  have hc' : HasCompactSupport (fun x => f x-(0:End n)) := by simpa only [sub_zero] using hc
  obtain ⟨R,hR,hh⟩ := affineC1_uniform_exterior f 0 hc' ((c,affineSlope a),v) ‖a‖ (norm_pos_iff.mpr ha) (by
    intro z
    rw [affineSlope_apply,norm_smul,mul_comm])
  refine ⟨R,hR,?_⟩
  exact hh ((c,affineSlope a),v) (by simp only [sub_self,norm_zero]; exact lt_min zero_lt_one (half_pos (norm_pos_iff.mpr ha)))

 theorem orbitCoefficient_support {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (ha : a≠0) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) :
    ∃ b : ContDiffBump (0:ℂ), ∀ h : ℂ, ‖h‖<1 → ∀ z : ℂ, b.rIn<‖z‖ →
      holderValue ((1:ℝ)/3) (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v))) z=0 := by
  obtain ⟨R,hR,hs⟩ := affineCoefficient_exterior f hc c a ha v
  let b : ContDiffBump (0:ℂ) := ⟨R+1,R+2,by linarith,by linarith⟩
  refine ⟨b,?_⟩
  intro h hh z hz
  rw [orbitCoefficient_value]
  apply hs
  have hn : ‖z‖≤‖z+h‖+‖h‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (z+h) h
  change R+1<‖z‖ at hz
  linarith

 theorem c1_shift_decay {n : ℕ} (v : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hl : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) (h : ℂ) :
    Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (c1HolderShift ((1:ℝ)/3) h v))) (cocompact ℂ) (𝓝 0) := by
  exact hl.comp ((Homeomorph.addRight h).isClosedEmbedding.tendsto_cocompact)

 theorem c1_shift_curl {n : ℕ} (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h z : ℂ) :
    holderValue ((1:ℝ)/3) (c1StandardCurl (c1HolderShift ((1:ℝ)/3) h v)) z=
      holderValue ((1:ℝ)/3) (c1StandardCurl v) (z+h) := rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance regularHGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance regularHSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance regularCGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance regularCSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance regularCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance regularCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

local instance AffineC1RegularityLocal1 (n : ℕ) : NormedAddCommGroup (HolderSpace ℂ (Phase n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal2 (n : ℕ) : NormedSpace ℝ (HolderSpace ℂ (Phase n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal3 (n : ℕ) : NormedAddCommGroup (HolderSpace ℂ (End n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal4 (n : ℕ) : NormedSpace ℝ (HolderSpace ℂ (End n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal5 (n : ℕ) : NormedAddCommGroup (C1HolderSpace (Phase n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal6 (n : ℕ) : NormedSpace ℝ (C1HolderSpace (Phase n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal7 (n : ℕ) (R : ℝ) : NormedAddCommGroup (CompactHolderSpace (Phase n) R) := inferInstance
local instance AffineC1RegularityLocal8 (n : ℕ) (R : ℝ) : NormedSpace ℝ (CompactHolderSpace (Phase n) R) := inferInstance

 def orbitResponse {n : ℕ} (b : ContDiffBump (0:ℂ))
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c a : Phase n)
    (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3)) : C1HolderSpace (Phase n) ((1:ℝ)/3) :=
  compactCRInverse b.rOut (frozenResponse b (orbitCoefficient f hf hc c a p,a))

 theorem orbitResponseDensity_contDiffAt {n : ℕ} (b : ContDiffBump (0:ℂ))
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c a : Phase n) (ha : a≠0)
    (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3))
    (hi : (cutoffFrozen b (orbitCoefficient f hf hc c a p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3) =>
      frozenResponse b (orbitCoefficient f hf hc c a p,a)) p := by
  exact frozenResponse_comp_contDiffAt b _ a p
    (orbitCoefficient_contDiff f hf hc c a ha).contDiffAt hi

 theorem orbitResponse_contDiffAt {n : ℕ} (b : ContDiffBump (0:ℂ))
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c a : Phase n) (ha : a≠0)
    (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3))
    (hi : (cutoffFrozen b (orbitCoefficient f hf hc c a p)).IsInvertible) :
    ContDiffAt ℝ ∞ (orbitResponse b f hf hc c a) p := by
  unfold orbitResponse
  have hC : ContDiff ℝ ∞ (compactCRInverse (E := Phase n) b.rOut) := ContinuousLinearMap.contDiff _
  exact hC.contDiffAt.comp p (orbitResponseDensity_contDiffAt b f hf hc c a ha p hi)

 theorem orbitResponse_identity {n : ℕ} (b : ContDiffBump (0:ℂ))
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h : ℂ)
    (hs : ∀ z, b.rIn<‖z‖ → holderValue ((1:ℝ)/3)
      (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v))) z=0)
    (hi : (cutoffFrozen b (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v)))).IsInvertible)
    (hcurl : ∀ z, holderValue ((1:ℝ)/3) (c1StandardCurl v) z=
      f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v z)
        (a+holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) v) z 1))
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) :
    c1HolderShift ((1:ℝ)/3) h v=
      orbitResponse b f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v)) := by
  apply c1_frozen_response (n := n) b _ a _ hs hi _ (c1_shift_decay v hlim h)
  intro z
  rw [c1_shift_curl v h z,orbitCoefficient_value f hf hc c a v h z,hcurl (z+h)]
  rfl

 

 theorem affine_c1_regular {n : ℕ}
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hK : ∀ x, Compatible (standardJ n+f x))
    (c a : Phase n) (ha : a≠0) (v : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hcurl : ∀ z, holderValue ((1:ℝ)/3) (c1StandardCurl v) z=
      f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v z)
        (a+holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) v) z 1))
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) :
    ContDiff ℝ ∞ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) := by
  obtain ⟨b,hb⟩ := orbitCoefficient_support f hf hc c a ha v
  have hi (h : ℂ) (hh : ‖h‖<1) :
      (cutoffFrozen b (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v)))).IsInvertible := by
    obtain ⟨H,hH⟩ := orbitCoefficient_C1 f hf hc c a v h
    rw [←hH]
    apply cutoffFrozen_invertible b H
    · simpa only [hH] using hb h hh
    · intro z
      rw [hH,orbitCoefficient_value]
      exact hK _
  apply c1_orbit_regular ((1:ℝ)/3) (by norm_num) v (Metric.ball 0 1) Metric.isOpen_ball
    (Metric.mem_ball_self (by norm_num)) (orbitResponse b f hf hc c a)
  · intro h hh
    exact orbitResponse_contDiffAt b f hf hc c a ha _ (hi h (by simpa using hh))
  · intro h hh
    have hh' : ‖h‖<1 := by simpa using hh
    exact orbitResponse_identity b f hf hc c a v h (hb h hh') (hi h hh') hcurl hlim

end HigherDimensionalBallPacking.Rigidity

end

end OAI
