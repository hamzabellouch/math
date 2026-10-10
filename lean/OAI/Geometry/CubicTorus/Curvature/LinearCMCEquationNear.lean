import Mathlib
import OAI.Geometry.CubicTorus.Estimates.HolderNear

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus
variable {E F G H I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup I] [NormedSpace ℝ I]

lemma HolderNear.common_four {f : E → F} {g : E → G} {h : E → H} {i : E → I} {x : E}
    (hf : HolderNear f x) (hg : HolderNear g x) (hh : HolderNear h x) (hi : HolderNear i x) :
    ∃ r α C : ℝ,0<r ∧ 0<α ∧ α≤1 ∧ 0≤C ∧
      ∀ y∈Metric.ball x r,∀ z∈Metric.ball x r,
        dist (f y) (f z)≤C*(dist y z)^α ∧ dist (g y) (g z)≤C*(dist y z)^α ∧
        dist (h y) (h z)≤C*(dist y z)^α ∧ dist (i y) (i z)≤C*(dist y z)^α := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf.prodMk (hg.prodMk (hh.prodMk hi))
  refine ⟨r,α,C,hr,hα,hα1,hC,?_⟩
  intro y hy z hz
  simpa only [Prod.dist_eq,max_le_iff] using hH y hy z hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.holderJet_two {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R))
    (hAJ : HolderJet 1 (fun y ↦ cmcJacobian (p y)) 0)
    (hBJ : HolderJet 1 B 0) (hgJ : HolderJet 1 g 0) : HolderJet 2 g 0 := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hcommon⟩ :=
    HolderNear.common_four hAJ.holderNear (HolderJet.holderNear hAJ.2)
      (HolderJet.holderNear hBJ.2) (HolderJet.holderNear hgJ.2)
  let s := min r R
  have hs : 0<s := lt_min hr hR
  have hsr : s≤r := min_le_left _ _
  have hsR : s≤R := min_le_right _ _
  have hcommon' (x : Plane) (hx : x∈Metric.ball (0 : Plane) s)
      (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) :=
    hcommon x ((Metric.ball_subset_ball hsr) hx) y ((Metric.ball_subset_ball hsr) hy)
  have hd (v : Plane) (hv : ‖v‖≤1) : HolderJet 1 (fun y ↦ fderiv ℝ g y v) 0 := by
    obtain ⟨t,L,β,ht,_,hL,hβ,hβ1,hc,hh⟩ :=
      (hw.mono (Metric.ball_subset_ball hsR)).directional_holder_C1 hg hp hpb hA hB hAc hBc hBb hs
        (hgc.mono (Metric.ball_subset_ball hsR)) hα hα1 hC hC hC hC
        (fun x hx y hy ↦ by simpa only [dist_eq_norm] using (hcommon' x hx y hy).1)
        (fun x hx y hy ↦ (hcommon' x hx y hy).2.1)
        (fun x hx y hy ↦ (hcommon' x hx y hy).2.2.1)
        (fun x hx y hy ↦ (hcommon' x hx y hy).2.2.2) v hv
    exact ⟨(hc 0 (Metric.mem_ball_self ht)).contDiffAt (Metric.ball_mem_nhds 0 ht),
      t,β,L,ht,hβ,hβ1,hL,hh⟩
  exact HolderJet.of_directionals hgJ.1
    (hd (EuclideanSpace.single 0 1) (by simp)) (hd (EuclideanSpace.single 1 1) (by simp))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma contDiff_local_vector_cutoff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} {η : Plane → ℝ} {S : Set Plane} {n : WithTop ℕ∞}
    (hS : IsOpen S) (hf : ContDiffOn ℝ n f S) (hη : ContDiff ℝ n η)
    (hs : tsupport η⊆S) : ContDiff ℝ n (fun y ↦ η y • f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.contDiffAt.smul ((hf y (hs hy)).contDiffAt (hS.mem_nhds (hs hy)))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma C2_gradient_contDiffOn {g : Plane → ℝ} {S : Set Plane}
    (hg : ContDiffOn ℝ 2 g S) (hS : IsOpen S) : ContDiffOn ℝ 1 (gradient g) S := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hg.fderiv_of_isOpen hS (by norm_num))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace CubicTorus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_C1_lipschitz {f : E → F} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ K : ℝ≥0,LipschitzWith K f := by
  obtain ⟨C,hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  refine ⟨Real.toNNReal C,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) fun x ↦ ?_⟩
  apply NNReal.coe_le_coe.mp
  exact (hC x).trans (Real.le_coe_toNNReal C)

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace CubicTorus

lemma HolderJet.extension {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : Plane → F} (hf : HolderJet (n+1) f 0) :
    ∃ (f' : Plane → F) (K : ℝ≥0) (M : ℝ),
      ContDiff ℝ (n+1) f' ∧ HasCompactSupport f' ∧ LipschitzWith K f' ∧
      (∀ y,‖f' y‖≤M) ∧ (∀ y,‖f' y‖≤‖f y‖) ∧
      f'=ᶠ[𝓝 0]f ∧ HolderJet (n+1) f' 0 := by
  obtain ⟨r,hr,hjets⟩ := Metric.mem_nhds_iff.mp hf.eventually
  have hfc : ContDiffOn ℝ (n+1) f (Metric.ball 0 r) := fun y hy ↦
    (hjets hy).contDiffAt.contDiffWithinAt
  let b : ContDiffBump (0 : Plane) := ⟨r/2,3*r/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 r := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f' : Plane → F := fun y ↦ b y • f y
  have hc : ContDiff ℝ (n+1) f' := contDiff_local_vector_cutoff Metric.isOpen_ball hfc b.contDiff hbs
  have hcs : HasCompactSupport f' := b.hasCompactSupport.smul_right
  obtain ⟨K,hK⟩ := compact_C1_lipschitz (hc.of_le (by norm_cast; omega)) hcs
  obtain ⟨M,hM⟩ := hcs.exists_bound_of_continuous hc.continuous
  have he : f'=ᶠ[𝓝 0]f := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (by linarith : 0<r/2)] with y hy
    dsimp only [f']
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_smul]
  refine ⟨f',K,M,hc,hcs,hK,hM,?_,he,hf.congr he.symm⟩
  intro y
  dsimp only [f']
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg b.nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) b.le_one

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def LinearCMCEquationNear (g : Plane → ℝ) (p B : Plane → Plane) : Prop :=
  ∃ R : ℝ,0<R ∧ LinearCMCEquation g p B (Metric.ball 0 R)

lemma LinearCMCEquationNear.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane}
    (hw : LinearCMCEquationNear g p B)
    (hg : g'=ᶠ[𝓝 0]g) (hp : p'=ᶠ[𝓝 0]p) (hB : B'=ᶠ[𝓝 0]B) : LinearCMCEquationNear g' p' B' := by
  obtain ⟨R,hR,hw⟩ := hw
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp (hg.and (hp.and hB))
  refine ⟨min r R,lt_min hr hR,?_⟩
  have hsub : Metric.ball (0 : Plane) (min r R)⊆Metric.ball 0 r := Metric.ball_subset_ball (min_le_left _ _)
  exact (hw.mono (Metric.ball_subset_ball (min_le_right _ _))).congr Metric.isOpen_ball
    (fun _ hy ↦ (he (hsub hy)).1) (fun _ hy ↦ (he (hsub hy)).2.1) (fun _ hy ↦ (he (hsub hy)).2.2)

lemma cmc_symbol_lipschitz {p : Plane → Plane} {K : ℝ≥0}
    (hp : LipschitzWith K p) (hpb : ∀ y,‖p y‖≤1) :
    ∃ L : ℝ≥0,LipschitzWith L (fun y ↦ cmcJacobian (p y)) := by
  obtain ⟨L,hL,hLip⟩ := cmcJacobian_uniform_lipschitz
  let L' : ℝ≥0 := ⟨L*(K:ℝ),mul_nonneg hL K.coe_nonneg⟩
  refine ⟨L',?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ L*dist (p x) (p y) := by simpa only [dist_eq_norm] using hLip (p x) (p y) (hpb x) (hpb y)
    _ ≤ L*((K:ℝ)*dist x y) := mul_le_mul_of_nonneg_left (hp.dist_le_mul x y) hL
    _ = _ := by change L*((K:ℝ)*dist x y)=L*(K:ℝ)*dist x y; ring

theorem LinearCMCEquationNear.holderJet_two {g : Plane → ℝ} {p B : Plane → Plane}
    (hw : LinearCMCEquationNear g p B) (hpb : ∀ y,‖p y‖≤1)
    (hgJ : HolderJet 1 g 0) (hpJ : HolderJet 1 p 0) (hBJ : HolderJet 1 B 0) : HolderJet 2 g 0 := by
  obtain ⟨g',K,Mg,hgc,_,hg,_,_,hge,hgJ'⟩ := hgJ.extension
  obtain ⟨p',Kp,Mp,hpc,_,hp,_,hpbd,hpe,hpJ'⟩ := hpJ.extension
  obtain ⟨B',KB,MB,hBc,_,hB,hBb,_,hBe,hBJ'⟩ := hBJ.extension
  have hpb' (y : Plane) : ‖p' y‖≤1 := (hpbd y).trans (hpb y)
  obtain ⟨LA,hA⟩ := cmc_symbol_lipschitz hp hpb'
  have hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p' y)) :=
    (cmcJacobian_contDiff.of_le (by simp)).comp hpc
  obtain ⟨R,hR,hw'⟩ := hw.congr hge hpe hBe
  have hh := hw'.holderJet_two hg hpc.continuous hpb' hA hB hAc hBc hBb hR hgc.contDiffOn
    (hpJ'.smooth_comp cmcJacobian_contDiff) hBJ' hgJ'
  exact hh.congr hge

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.classical_derivative {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R) (hgc : ContDiff ℝ 2 g)
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    LinearCMCEquation (fun y ↦ fderiv ℝ g y v) p
      (fun y ↦ fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))
      (Metric.ball 0 (R/4)) := by
  obtain ⟨u,U,hue,hug,hlin⟩ := hw.scalar_derivative hg hp hpb hA hB hAc hBc hBb hR
    (hgc.of_le (by norm_num)).contDiffOn v hv
  let d : Plane → ℝ := fun y ↦ fderiv ℝ g y v
  have hdc : ContDiff ℝ 1 d := (hgc.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hgradc : Continuous (gradient d) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hdc.continuous_fderiv (by simp))
  have hdu : PlaneWeakGradient (Metric.ball 0 (R/4)) d U :=
    hug.local_congr measurableSet_ball hue.symm (EventuallyEq.rfl)
  have hUeq := PlaneWeakGradient.unique Metric.isOpen_ball
    ((Lp.memLp U).locallyIntegrable (by norm_num)) hgradc.locallyIntegrable hdu (C1_weak_gradient hdc _)
  intro ψ hψ hc hs
  rw [← hlin ψ hψ hc hs]
  apply integral_congr_ae
  have he := (ae_restrict_iff' measurableSet_ball).mp hUeq
  filter_upwards [he] with y hy
  by_cases hys : y∈Metric.ball (0 : Plane) (R/4)
  · rw [hy hys]
  · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hys (hs h))]; rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def linearCMCSource (g : Plane → ℝ) (p B : Plane → Plane) (v : Plane) : Plane → Plane :=
  fun y ↦ fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y)

theorem LinearCMCEquationNear.derivative {g : Plane → ℝ} {p B : Plane → Plane}
    (hw : LinearCMCEquationNear g p B) (hpb : ∀ y,‖p y‖≤1)
    (hgJ : HolderJet 2 g 0) (hpJ : HolderJet 1 p 0) (hBJ : HolderJet 1 B 0)
    (v : Plane) (hv : ‖v‖≤1) :
    LinearCMCEquationNear (fun y ↦ fderiv ℝ g y v) p (linearCMCSource g p B v) := by
  obtain ⟨g',K,Mg,hgc,_,hg,_,_,hge,_⟩ := hgJ.extension
  obtain ⟨p',Kp,Mp,hpc,_,hp,_,hpbd,hpe,_⟩ := hpJ.extension
  obtain ⟨B',KB,MB,hBc,_,hB,hBb,_,hBe,_⟩ := hBJ.extension
  have hpb' (y : Plane) : ‖p' y‖≤1 := (hpbd y).trans (hpb y)
  obtain ⟨LA,hA⟩ := cmc_symbol_lipschitz hp hpb'
  have hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p' y)) :=
    (cmcJacobian_contDiff.of_le (by simp)).comp hpc
  obtain ⟨R,hR,hw'⟩ := hw.congr hge hpe hBe
  have hd' : LinearCMCEquationNear (fun y ↦ fderiv ℝ g' y v) p' (linearCMCSource g' p' B' v) :=
    ⟨R/4,by linarith,hw'.classical_derivative hg hpc.continuous hpb' hA hB hAc hBc hBb hR hgc v hv⟩
  have hde : (fun y ↦ fderiv ℝ g' y v)=ᶠ[𝓝 0](fun y ↦ fderiv ℝ g y v) :=
    hge.fderiv.mono fun _ hy ↦ congrArg (fun L : Plane →L[ℝ] ℝ ↦ L v) hy
  have hAe : (fun y ↦ cmcJacobian (p' y))=ᶠ[𝓝 0](fun y ↦ cmcJacobian (p y)) :=
    hpe.mono fun _ hy ↦ congrArg cmcJacobian hy
  have hSe : linearCMCSource g' p' B' v=ᶠ[𝓝 0]linearCMCSource g p B v := by
    filter_upwards [hBe.fderiv (𝕜 := ℝ),hAe.fderiv (𝕜 := ℝ),hge.fderiv (𝕜 := ℝ)] with y hBy hAy hgy
    have hG : gradient g' y=gradient g y := congrArg
      (fun L : Plane →L[ℝ] ℝ ↦ (InnerProductSpace.toDual ℝ Plane).symm L) hgy
    simp only [linearCMCSource,hBy,hAy,hG]
  exact hd'.congr hde.symm hpe.symm hSe.symm

lemma HolderJet.linearSource {n : ℕ} {g : Plane → ℝ} {p B : Plane → Plane}
    (hg : HolderJet (n+1) g 0) (hp : HolderJet (n+1) p 0) (hB : HolderJet (n+1) B 0)
    (v : Plane) : HolderJet n (linearCMCSource g p B v) 0 := by
  have hA := hp.smooth_comp cmcJacobian_contDiff
  exact (hB.2.clm_apply (HolderJet.const v)).sub
    ((hA.2.clm_apply (HolderJet.const v)).clm_apply hg.gradient)

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquationNear.schauder {n : ℕ} {g : Plane → ℝ} {p B : Plane → Plane}
    (hw : LinearCMCEquationNear g p B) (hpb : ∀ y,‖p y‖≤1)
    (hg : HolderJet 1 g 0) (hp : HolderJet (n+1) p 0) (hB : HolderJet (n+1) B 0) :
    HolderJet (n+2) g 0 := by
  induction n generalizing g B with
  | zero => exact hw.holderJet_two hpb hg hp hB
  | succ n ih =>
    have hg' : HolderJet (n+2) g 0 := ih hw hg hp.pred hB.pred
    have hd (v : Plane) (hv : ‖v‖≤1) : HolderJet (n+2) (fun y ↦ fderiv ℝ g y v) 0 := by
      have hgd : HolderJet 1 (fun y ↦ fderiv ℝ g y v) 0 := (hg'.directional v).of_le (by omega)
      have hp1 : HolderJet 1 p 0 := hp.of_le (by omega)
      have hB1 : HolderJet 1 B 0 := hB.of_le (by omega)
      have hw' := hw.derivative hpb (hg'.of_le (by omega)) hp1 hB1 v hv
      exact ih hw' hgd hp.pred (hg'.linearSource hp hB v)
    exact HolderJet.of_directionals hg.1
      (hd (EuclideanSpace.single 0 1) (by simp)) (hd (EuclideanSpace.single 1 1) (by simp))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem WeakCMCGraph.directional_holder_C1 {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R α C : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hα : 0<α) (hα1 : α≤1) (hC : 0≤C)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤C*(dist x y)^α)
    (v : Plane) (hv : ‖v‖≤1) :
    ∃ s L β : ℝ,0<s ∧ s≤R ∧ 0≤L ∧ 0<β ∧ β≤1 ∧
      ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ g y v) (Metric.ball 0 s) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (fderiv ℝ (fun z ↦ fderiv ℝ g z v) x) (fderiv ℝ (fun z ↦ fderiv ℝ g z v) y)≤L*(dist x y)^β := by
  obtain ⟨p,D,hp,hpb,hD,hpe,hpHolder⟩ := hw.holder_symbol_extension hg hK hR hgc hC hHolder
  obtain ⟨u,G,hue,hug,hlin⟩ := hw.scalar_linearized_equation hg hK hR hgc v hv
  have hsub : Metric.ball (0 : Plane) (R/4)⊆Metric.ball 0 (R/2) :=
    Metric.ball_subset_ball (by linarith)
  have hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (R/4) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0 := by
    intro ψ hψ hc hs
    rw [← hlin ψ hψ hc hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun y ↦ by
      dsimp only
      by_cases hy : y∈Metric.ball (0 : Plane) (R/4)
      · rw [hpe y (hsub hy)]
      · rw [fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy (hs hy'))]; rfl
  obtain ⟨G',s,L,β,hs,hsR,hL,hβ,hβ1,hGc,hGe,hGh⟩ :=
    cmc_linearized_holder_gradient hp hpb (by linarith : 0<R/4) hα hα1 hD
      (fun x hx y hy ↦ hpHolder x (hsub hx) y (hsub hy)) u G hug hd
  have hsR' : s≤R/4 := by linarith
  have hsub' : Metric.ball (0 : Plane) s⊆Metric.ball 0 (R/4) := Metric.ball_subset_ball hsR'
  have hsubR : Metric.ball (0 : Plane) s⊆Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hw' : PlaneWeakGradient (Metric.ball 0 s) (fun y ↦ fderiv ℝ g y v) G' :=
    ((hug.mono hsub').local_congr measurableSet_ball
      (ae_restrict_of_ae_restrict_of_subset hsub' hue.symm) hGe)
  have hfc : ContinuousOn (fun y ↦ fderiv ℝ g y v) (Metric.ball 0 s) :=
    ((hgc.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply continuousOn_const).mono hsubR
  exact ⟨s/4,L,β,by positivity,by linarith,hL,hβ,hβ1,
    hw'.holder_C1 hs hfc hGc hGh⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem WeakCMCGraph.holderJet_two {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R α C : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hα : 0<α) (hα1 : α≤1) (hC : 0≤C)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤C*(dist x y)^α) : HolderJet 2 g 0 := by
  have hd (v : Plane) (hv : ‖v‖≤1) : HolderJet 1 (fun y ↦ fderiv ℝ g y v) 0 := by
    obtain ⟨s,L,β,hs,_,hL,hβ,hβ1,hc,hh⟩ := hw.directional_holder_C1 hg hK hR hgc hα hα1 hC hHolder v hv
    exact ⟨(hc 0 (Metric.mem_ball_self hs)).contDiffAt (Metric.ball_mem_nhds 0 hs),
      s,β,L,hs,hβ,hβ1,hL,hh⟩
  exact HolderJet.of_directionals
    ((hgc 0 (Metric.mem_ball_self hR)).contDiffAt (Metric.ball_mem_nhds 0 hR))
    (hd (EuclideanSpace.single 0 1) (by simp)) (hd (EuclideanSpace.single 1 1) (by simp))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem WeakCMCGraph.directional_linear_near {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hgJ : HolderJet 2 g 0)
    (v : Plane) (hv : ‖v‖≤1) :
    LinearCMCEquationNear (fun y ↦ fderiv ℝ g y v) (gradient g) (fun _ ↦ 0) := by
  obtain ⟨d,Kd,Md,hdc,_,_,_,_,hde,_⟩ := (hgJ.directional v).extension
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp hde
  obtain ⟨u,G,hue,hug,hlin⟩ := hw.scalar_linearized_equation hg hK hR hgc v hv
  let s := min r (R/4)
  have hs : 0<s := lt_min hr (by linarith)
  have hsr : s≤r := min_le_left _ _
  have hsR : s≤R/4 := min_le_right _ _
  have hsub : Metric.ball (0 : Plane) s⊆Metric.ball 0 (R/4) := Metric.ball_subset_ball hsR
  have hdu : PlaneWeakGradient (Metric.ball 0 s) d G := by
    apply (hug.mono hsub).local_congr measurableSet_ball ?_ EventuallyEq.rfl
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hue,
      ae_restrict_mem measurableSet_ball] with y hy hyS
    exact (he ((Metric.ball_subset_ball hsr) hyS)).trans hy.symm
  have hgradc : Continuous (gradient d) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hdc.continuous_fderiv (by simp))
  have hGe := PlaneWeakGradient.unique Metric.isOpen_ball
    ((Lp.memLp G).locallyIntegrable (by norm_num)) hgradc.locallyIntegrable hdu (C1_weak_gradient hdc _)
  have hw' : LinearCMCEquationNear d (gradient g) (fun _ ↦ 0) := by
    refine ⟨s,hs,?_⟩
    intro ψ hψ hc hψs
    simp only [sub_zero]
    rw [← hlin ψ hψ hc (hψs.trans hsub)]
    apply integral_congr_ae
    have het := (ae_restrict_iff' measurableSet_ball).mp hGe
    filter_upwards [het] with y hy
    by_cases hys : y∈Metric.ball (0 : Plane) s
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hys (hψs h))]; rfl
  exact hw'.congr hde.symm EventuallyEq.rfl EventuallyEq.rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem WeakCMCGraph.holderJet_all {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R α C : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hα : 0<α) (hα1 : α≤1) (hC : 0≤C)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤C*(dist x y)^α) (n : ℕ) : HolderJet (n+2) g 0 := by
  have hbase := hw.holderJet_two hg hK hR hgc hα hα1 hC hHolder
  have hpb (y : Plane) : ‖gradient g y‖≤1 := by
    rw [plane_gradient_norm]
    exact (norm_fderiv_le_of_lipschitz ℝ hg).trans hK
  induction n with
  | zero => exact hbase
  | succ n ih =>
    have hd (v : Plane) (hv : ‖v‖≤1) : HolderJet (n+2) (fun y ↦ fderiv ℝ g y v) 0 :=
      (hw.directional_linear_near hg hK hR hgc hbase v hv).schauder hpb
        (hbase.directional v) ih.gradient (HolderJet.const 0)
    exact HolderJet.of_directionals hbase.1
      (hd (EuclideanSpace.single 0 1) (by simp)) (hd (EuclideanSpace.single 1 1) (by simp))

theorem WeakCMCGraph.smoothAt_zero {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hgJ : HolderJet 1 g 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) g 0 := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := HolderJet.holderNear hgJ.2
  let s := min r R
  have hs : 0<s := lt_min hr hR
  have hsr : s≤r := min_le_left _ _
  have hsR : s≤R := min_le_right _ _
  have hw' : WeakCMCGraph g H (Metric.ball 0 s) := fun ψ hψ hc ht ↦
    hw ψ hψ hc (ht.trans (Metric.ball_subset_ball hsR))
  apply contDiffAt_infty.mpr
  intro n
  exact (hw'.holderJet_all hg hK hs (hgc.mono (Metric.ball_subset_ball hsR)) hα hα1 hC
    (fun x hx y hy ↦ hH x ((Metric.ball_subset_ball hsr) hx) y ((Metric.ball_subset_ball hsr) hy)) n).contDiffAt.of_le
      (by norm_cast; omega)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem WeakCMCGraph.C2_smooth {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ}
    (hgc : ContDiffOn ℝ 2 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R) := by
  intro x hx
  have hxR : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  let r := (R-‖x‖)/2
  have hr : 0<r := by dsimp [r]; linarith
  have hrR : r+‖x‖≤R := by dsimp [r]; linarith
  let f : Plane → ℝ := fun z ↦ g (z+x)
  have hmap : MapsTo (fun z : Plane ↦ z+x) (Metric.ball 0 r) (Metric.ball 0 R) := by
    intro z hz
    have hz' : ‖z‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    rw [Metric.mem_ball,dist_zero_right]
    exact (norm_add_le z x).trans_lt (by linarith)
  have hfc : ContDiffOn ℝ 2 f (Metric.ball 0 r) :=
    hgc.comp (contDiff_id.add contDiff_const).contDiffOn hmap
  have hfL : LipschitzWith K f := LipschitzWith.of_dist_le_mul fun y z ↦ by
    simpa only [f,dist_add_right] using hg.dist_le_mul (y+x) (z+x)
  have hfw : WeakCMCGraph f H (Metric.ball 0 r) := by
    intro ψ hψ hc hs
    have he := hw.translated_test hrR hψ hs
    simpa only [f,gradient,fderiv_comp_add_right] using he
  have hfJ : HolderJet 1 f 0 := ContDiffAt.holderJet
    ((hfc.contDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hr))))
  have hfs := hfw.smoothAt_zero hfL hK hr (hfc.of_le (by norm_num)) hfJ
  have hf_at : ContDiffAt ℝ (⊤ : ℕ∞) f (x-x) := by simpa only [sub_self] using hfs
  have hc := hf_at.comp (f := fun z : Plane ↦ z-x) x
    ((contDiff_id.sub contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun z : Plane ↦ z-x)).contDiffAt)
  simpa only [f,Function.comp_def,sub_add_cancel] using hc.contDiffWithinAt

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeDivergence (F : Plane → Plane) (y : Plane) : ℝ :=
  (fderiv ℝ F y (EuclideanSpace.single 0 1)) 0+
  (fderiv ℝ F y (EuclideanSpace.single 1 1)) 1

lemma planeDivergence_continuous {F : Plane → Plane} (hF : ContDiff ℝ 1 F) :
    Continuous (planeDivergence F) := by
  have hd := hF.continuous_fderiv (by simp)
  exact ((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const))

lemma plane_component_fderiv {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) (y v : Plane) :
    fderiv ℝ (fun z ↦ F z i) y v=(fderiv ℝ F y v) i := by
  have hh := (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).hasFDerivAt.comp y
    ((hF.differentiable (by simp) y).hasFDerivAt)
  have he := hh.fderiv
  change fderiv ℝ (fun z ↦ F z i) y=_ at he
  rw [he]
  rfl

lemma plane_divergence_integration_by_parts {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ y,planeDivergence F y*ψ y)= -(∫ y,fderiv ℝ ψ y (F y)) := by
  have hcomp (i : Fin 2) : ContDiff ℝ 1 (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hi (i : Fin 2) : Integrable (fun y ↦ (fderiv ℝ F y (EuclideanSpace.single i 1)) i*ψ y) :=
    (((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).continuous.comp
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hj (i : Fin 2) : Integrable (fun y ↦ F y i*fderiv ℝ ψ y (EuclideanSpace.single i 1)) :=
    ((hcomp i).continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ _).mul_left
  have hpart (i : Fin 2) := C1_local_integration_by_parts isOpen_univ (hcomp i).continuous
    (hcomp i).contDiffOn hψ hc (subset_univ _) (EuclideanSpace.single i 1)
  simp_rw [plane_component_fderiv hF] at hpart
  have he (y : Plane) : fderiv ℝ ψ y (F y)=
      F y 0*fderiv ℝ ψ y (EuclideanSpace.single 0 1)+
      F y 1*fderiv ℝ ψ y (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [plane_decompose (F y)]
    simp
  simp_rw [planeDivergence,add_mul,he]
  rw [integral_add (hi 0) (hi 1),hpart 0,hpart 1,integral_add (hj 0) (hj 1)]
  ring

lemma classical_divergence_of_weak {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {S : Set Plane} (hS : IsOpen S) {H : ℝ}
    (hw : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ⊆S →
      (∫ y,fderiv ℝ ψ y (F y))=H*(∫ y,ψ y)) :
    ∀ y∈S,planeDivergence F y= -H := by
  have hd := (planeDivergence_continuous hF).add (continuous_const (y := H))
  have hae := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hd.locallyIntegrable.locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · have hae' : (fun y ↦ planeDivergence F y+H)=ᵐ[volume.restrict S] (fun _ ↦ (0:ℝ)) := by
      change ∀ᵐ y ∂volume.restrict S,planeDivergence F y+H=0
      rw [ae_restrict_iff' hS.measurableSet]
      exact hae
    have he := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hS hd.continuousOn continuousOn_const
    intro y hy
    exact eq_neg_of_add_eq_zero_left (he hy)
  · have hi : Integrable (fun y ↦ planeDivergence F y*ψ y) volume := ((planeDivergence_continuous hF).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
    have hj : Integrable (fun y ↦ H*ψ y) volume := (hψ.continuous.integrable_of_hasCompactSupport hc).const_mul H
    simp only [smul_eq_mul,Pi.add_apply,mul_add]
    simp_rw [mul_comm (ψ _) (planeDivergence F _),mul_comm (ψ _) H]
    rw [integral_add hi hj,plane_divergence_integration_by_parts hF (hψ.of_le (by simp)) hc,
      hw ψ hψ hc hs,integral_const_mul]
    ring

theorem WeakCMCGraph.classical {g : Plane → ℝ} {R H : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ 2 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∀ y∈Metric.ball (0 : Plane) (R/2),
      planeDivergence (fun z ↦ cmcFlux (gradient g z)) y= -H := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let F : Plane → Plane := fun y ↦ cmcFlux (b y • gradient g y)
  have hF : ContDiff ℝ 1 F := (cmcFlux_contDiff.of_le (by simp)).comp
    (contDiff_local_vector_cutoff Metric.isOpen_ball (C2_gradient_contDiffOn hg Metric.isOpen_ball)
      (b.contDiff (n := 1)) hbs)
  have he (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/2)) : F y=cmcFlux (gradient g y) := by
    have hb : b y=1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp [F,hb]
  have hw' : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (R/2) → (∫ y,fderiv ℝ ψ y (F y))=H*(∫ y,ψ y) := by
    intro ψ hψ hc hs
    rw [← hw ψ hψ hc (hs.trans (Metric.ball_subset_ball (by linarith)))]
    apply integral_congr_ae
    exact Eventually.of_forall fun y ↦ by
      dsimp only
      by_cases hy : y∈Metric.ball (0 : Plane) (R/2)
      · rw [he y hy]
      · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hy (hs hh))]
        rfl
  intro y hy
  have hloc : F=ᶠ[𝓝 y] (fun z ↦ cmcFlux (gradient g z)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    exact he z hz
  have hd : fderiv ℝ F y=fderiv ℝ (fun z ↦ cmcFlux (gradient g z)) y := hloc.fderiv_eq
  have hh := classical_divergence_of_weak hF Metric.isOpen_ball hw' y hy
  simpa only [planeDivergence,hd] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraphDerivative_contDiffOn {n : Cover} (hn : ‖n‖=1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (normalGraphDerivative n) (Metric.closedBall n (1/2)) := by
  have hi : ContDiffOn ℝ (⊤ : ℕ∞) (fun ν : Cover ↦ (⟪ν,n⟫)⁻¹)
      (Metric.closedBall n (1/2)) := by
    apply (contDiff_id.inner ℝ contDiff_const).contDiffOn.inv
    intro ν hν
    have hh : ‖n-ν‖≤1/2 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hν
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (transverse_inner_lower hn hh))
  exact hi.smul (((innerSL ℝ).contDiff.contDiffOn.clm_comp contDiffOn_const).neg)

lemma normalGraphDerivative_lipschitz {n : Cover} (hn : ‖n‖=1) :
    ∃ L : ℝ≥0, LipschitzOnWith L (normalGraphDerivative n) (Metric.closedBall n (1/2)) :=
  (normalGraphDerivative_contDiffOn hn).exists_lipschitzOnWith (by simp)
    (convex_closedBall n (1/2)) (isCompact_closedBall n (1/2))

theorem BoundaryNormalChart.graph_derivative_modulus {E : Set Torus} {c n : Cover}
    {r e C K ρ : ℝ} (hchart : BoundaryNormalChart E c n r e C K ρ)
    (hn : ‖n‖=1) (hsmall : C*e≤1/2) {g : Plane → ℝ}
    (hg : LipschitzWith (1/4) g) {U : Set Plane} (hU : IsOpen U)
    (hinside : ∀ y∈U, quotientMap c+quotientMap (normalGraph n g y)∈frontier (openRepresentative E) ∧
      ‖normalGraph n g y‖<r/128) :
    ∃ L : ℝ≥0, ∀ i : ℕ, ∀ x∈U, ∀ y∈U,
      dist x y≤ρ^i*(r/4) →
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤(L:ℝ)*K*e*(1/2:ℝ)^i := by
  obtain ⟨ν,hνc,hν,hmod⟩ := hchart
  obtain ⟨L,hL⟩ := normalGraphDerivative_lipschitz hn
  let f : Plane → Cover := fun y ↦ c+normalGraph n g y
  have hmap {y : Plane} (hy : y∈U) : f y∈
      quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c (r/128) := by
    refine ⟨?_,?_⟩
    · simpa only [f,mem_preimage,quotientMap_add] using (hinside y hy).1
    · simpa only [f,Metric.mem_ball,dist_eq_norm,add_sub_cancel_left] using (hinside y hy).2
  have hnub {y : Plane} (hy : y∈U) : ‖n-ν (f y)‖≤1/2 :=
    (hν (f y) (hmap hy)).2.1.trans hsmall
  have hmem {y : Plane} (hy : y∈U) : ν (f y)∈Metric.closedBall n (1/2) := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hnub hy
  have hder {y : Plane} (hy : y∈U) : fderiv ℝ g y=normalGraphDerivative n (ν (f y)) := by
    have hflat : BoundaryFlatAt (frontier (openRepresentative E))
        (quotientMap c+quotientMap (normalGraph n g y)) (ν (f y)) := by
      simpa only [f,quotientMap_add] using (hν (f y) (hmap hy)).2.2
    exact ((normalGraph_hasFDerivWithinAt_of_flat hn hg
      (fun z hz ↦ (hinside z hz).1) hflat
      (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2)
        (transverse_inner_lower hn (hnub hy))))).hasFDerivAt (hU.mem_nhds hy)).fderiv
  refine ⟨L,fun i x hx y hy hxy ↦ ?_⟩
  rw [hder hx,hder hy]
  have hdist : dist (f x) (f y)≤ρ^i*(r/2) := by
    have hh := (normalGraph_lipschitz hn hg).dist_le_mul x y
    have hnon : 0≤ρ^i*(r/4) := (dist_nonneg (x := x) (y := y)).trans hxy
    simp only [NNReal.coe_add,NNReal.coe_one,NNReal.coe_div,NNReal.coe_ofNat] at hh
    simp only [f,dist_add_left]
    nlinarith
  exact (hL.dist_le_mul _ (hmem hx) _ (hmem hy)).trans
    (by
      convert mul_le_mul_of_nonneg_left (hmod i (f x) (hmap hx) (f y) (hmap hy) hdist) L.coe_nonneg using 1
      ring)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_moving_C1_modulus {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ r₀ ρ : ℝ, 0<r₀ ∧ 0<ρ ∧ ρ≤1/16 ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1)=(z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖=1) →
      ∃ δ : ℝ, 0<δ ∧ ∀ c₀ : Cover, ‖c₀-cubeCenter‖≤1/16 →
        quotientMap c₀∈frontier (openRepresentative E) → ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖=1 →
        0<r → r≤r₀ → 0<e → e≤δ → r/e^2≤δ →
        (∫ x in Metric.closedBall (quotientMap c₀) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus))≤r^2*e^2 →
      ∃ (g : Plane → ℝ) (M : ℝ), 0≤M ∧ LipschitzWith (1/4) g ∧
        ContDiffOn ℝ 1 g (Metric.ball 0 (r/1024)) ∧
        (∀ y∈Metric.ball (0 : Plane) (r/1024),
          quotientMap c₀+quotientMap (normalGraph n₀ g y)∈frontier (openRepresentative E) ∧
          ‖normalGraph n₀ g y‖<r/512) ∧
        (∀ x∈quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          normalGraph n₀ g (normalPlaneCoordinates n₀ (x-c₀))=x-c₀) ∧
        (∀ i : ℕ, ∀ x∈Metric.ball (0 : Plane) (r/1024), ∀ y∈Metric.ball (0 : Plane) (r/1024),
          dist x y≤ρ^i*(r/4) → dist (fderiv ℝ g x) (fderiv ℝ g y)≤M*(1/2:ℝ)^i) := by
  obtain ⟨R,hR,hgraphs⟩ := isMinimizerAt_moving_C1_graph hV hE hmin hcenter
  obtain ⟨S,C,K,ρ,hS,hC,hK,hρ,hρs,hnormals⟩ := isMinimizerAt_moving_normal_modulus hV hE hmin hcenter
  refine ⟨min R S,ρ,lt_min hR hS,hρ,hρs,?_⟩
  intro μ hμ N hN hp hu
  obtain ⟨δG,hδG,hG⟩ := hgraphs μ hμ N hN hp hu
  obtain ⟨δN,hδN,hN'⟩ := hnormals μ hμ N hN hp hu
  let δ := min δG (min δN (1/(2*C)))
  refine ⟨δ,by dsimp [δ]; positivity,?_⟩
  intro c hc hbase n r e hn hr hrr he heδ hratio ht
  have hδG' : δ≤δG := min_le_left _ _
  have hδN' : δ≤δN := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨g,hg,hgc,hi,hcover⟩ := hG c hc hbase n r e hn hr
    (hrr.trans (min_le_left _ _)) he (heδ.trans hδG') (hratio.trans hδG') ht
  have hnchart : BoundaryNormalChart E c n r e C K ρ := hN' c hc n r e hn hr
    (hrr.trans (min_le_right _ _)) he (heδ.trans hδN') (hratio.trans hδN') ht
  have hsmall : C*e≤1/2 := by
    have hh := heδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0<2*C)).mp hh
    nlinarith
  obtain ⟨L,hL⟩ := hnchart.graph_derivative_modulus hn hsmall hg Metric.isOpen_ball
    (fun y hy ↦ ⟨(hi y hy).1,(hi y hy).2.trans_le (by linarith)⟩)
  exact ⟨g,(L:ℝ)*K*e,by positivity,hg,hgc,hi,hcover,hL⟩

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
