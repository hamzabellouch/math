import Mathlib
import OAI.Geometry.CubicTorus.Curvature.CMCFrameOperator

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_no_constant_normal_patch {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {U : Set Torus} (hU : IsOpen U) (hpatch : (frontier (openRepresentative E)∩U).Nonempty)
    (n : Cover) (hconst : ∀ a∈frontier (openRepresentative E)∩U,N (representative a)=n) : False := by
  have hunit (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) : ‖N x‖=1 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hN.continuous.norm continuous_const
      (fun k y => by rw [hp]) (fun _ _ => rfl) _ x hx
    filter_upwards [hae] with z hz
    rw [hz,z.2.property]
  obtain ⟨a,ha,haU⟩ := hpatch
  have hna := hconst a ⟨ha,haU⟩
  have hn : ‖n‖=1 := by
    rw [← hna]
    exact hunit (representative a) (by simpa only [quotientMap_representative] using ha)
  have hpar (b : Torus) (hb : b∈frontier (openRepresentative E)) :
      N (representative b)=n ∨ N (representative b)= -n := by
    let m := N (representative b)
    let d := ⟪n,m⟫
    let v := m-d • n
    have hvn : ⟪v,n⟫=0 := by
      simp only [v,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
      rw [real_inner_comm n m]
      exact sub_self _
    have hvm := isMinimizerAt_normal_unique_continuation hV hE hmin hconn hμ hN hp hae v
      hU ⟨a,ha,haU⟩ (fun c hc => by rw [hconst c hc,hvn]) b hb
    have hm : ‖m‖=1 := hunit (representative b) (by simpa only [quotientMap_representative] using hb)
    have hd : d^2=1 := by
      change ⟪m-d • n,m⟫=0 at hvm
      rw [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hm,one_pow] at hvm
      change 1-d*d=0 at hvm
      nlinarith
    have hdor : d=1 ∨ d= -1 := by
      have he : (d-1)*(d+1)=0 := by nlinarith
      rcases mul_eq_zero.mp he with h|h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hdor with hd1|hd1
    · left
      have hs : ‖m-n‖^2=0 := by
        rw [norm_sub_sq_real,hm,hn,real_inner_comm n m]
        change 1^2-2*d+1^2=0
        rw [hd1]; norm_num
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
    · right
      have hs : ‖m+n‖^2=0 := by
        rw [norm_add_sq_real,hm,hn,real_inner_comm n m]
        change 1^2+2*d+1^2=0
        rw [hd1]; norm_num
      exact eq_neg_iff_add_eq_zero.mpr (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
  have hc (b : Torus) (hb : b∈frontier (openRepresentative E)) : N (representative b)=n := by
    have hm : MapsTo (fun b : Torus => N (representative b)) (frontier (openRepresentative E))
        ({n,-n} : Set Cover) := by
      intro c hc
      simpa only [mem_insert_iff,mem_singleton_iff] using hpar c hc
    exact (hconn.constant_of_mapsTo (Set.toFinite ({n,-n} : Set Cover)).isDiscrete
      (continuous_periodic_descent hN.continuous hp).continuousOn hm hb ha).trans hna
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hac : ∀ᵐ z ∂(μ : Measure NormalBundle),(z.2 : Cover)=n := by
    filter_upwards [hbd,hae] with z hz he
    have hh := hc (quotientMap z.1) hz
    rw [periodic_representative hp] at hh
    exact he.symm.trans hh
  have hmpos : 0<(μ : Measure NormalBundle).real univ := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal,hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne
  have hf : AdmissibleField (fun _ : Cover => n) := ⟨contDiff_const,fun _ _ => rfl,fun _ => hn.le⟩
  have hflux := hμ.2 _ hf
  have hi : (∫ z,normalTest (fun _ : Cover => n) hf.1.continuous z ∂(μ : Measure NormalBundle))=
      (μ : Measure NormalBundle).real univ := by
    calc
      _=(∫ _ : NormalBundle,(1 : ℝ) ∂(μ : Measure NormalBundle)) := by
        apply integral_congr_ae
        filter_upwards [hac] with z hz
        simp only [normalTest,ContinuousMap.coe_mk,hz,real_inner_self_eq_norm_sq,hn,one_pow]
      _=_ := by simp
  have hd : divergence (fun _ : Cover => n)=fun _ => 0 := by funext x; simp [divergence]
  rw [hi,hd,integral_zero] at hflux
  exact hmpos.ne' hflux

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcSecant (p q : Plane) : Plane →L[ℝ] Plane :=
  ((cmcWeight p+cmcWeight q)/(2*cmcWeight p*cmcWeight q)) •
    ContinuousLinearMap.id ℝ Plane -
  (1/(2*cmcWeight p*cmcWeight q*(cmcWeight p+cmcWeight q))) •
    (innerSL ℝ (p+q)).smulRight (p+q)

lemma cmcSecant_apply (p q v : Plane) :
    cmcSecant p q v=((cmcWeight p+cmcWeight q)/(2*cmcWeight p*cmcWeight q)) • v -
      (⟪p+q,v⟫/(2*cmcWeight p*cmcWeight q*(cmcWeight p+cmcWeight q))) • (p+q) := by
  simp only [cmcSecant,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul,one_div_mul_eq_div]

lemma cmcSecant_exact (p q : Plane) : cmcSecant p q (q-p)=cmcFlux q-cmcFlux p := by
  have hp := cmcWeight_pos p
  have hq := cmcWeight_pos q
  have hs : cmcWeight p+cmcWeight q≠0 := ne_of_gt (add_pos hp hq)
  have he : ⟪p+q,q-p⟫=(cmcWeight q)^2-(cmcWeight p)^2 := by
    rw [inner_add_left,inner_sub_right,inner_sub_right,real_inner_comm p q,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,cmcWeight_sq,cmcWeight_sq]
    ring
  rw [cmcSecant_apply,he]
  apply PiLp.ext
  intro i
  simp only [cmcFlux,cmcWeight,PiLp.smul_apply,PiLp.sub_apply,PiLp.add_apply,smul_eq_mul]
  field_simp
  ring

lemma cmcSecant_symmetric (p q v w : Plane) : ⟪v,cmcSecant p q w⟫=⟪w,cmcSecant p q v⟫ := by
  simp only [cmcSecant_apply,inner_sub_right,real_inner_smul_right,real_inner_comm v (p+q),
    real_inner_comm w (p+q),real_inner_comm w v]
  ring

lemma cmcWeight_gt_norm (p : Plane) : ‖p‖<cmcWeight p := by
  have hp := cmcWeight_pos p
  have he := cmcWeight_sq p
  nlinarith [norm_nonneg p]

lemma cmcSecant_elliptic (p q : Plane) : ∃ ℓ>0,∀ v,ℓ*‖v‖^2≤⟪v,cmcSecant p q v⟫ := by
  let S := cmcWeight p+cmcWeight q
  let D := 2*cmcWeight p*cmcWeight q*S
  have hS : 0<S := add_pos (cmcWeight_pos p) (cmcWeight_pos q)
  have hD : 0<D := by dsimp [D]; have hp := cmcWeight_pos p; have hq := cmcWeight_pos q; positivity
  have hnorm : ‖p+q‖<S := (norm_add_le p q).trans_lt (add_lt_add (cmcWeight_gt_norm p) (cmcWeight_gt_norm q))
  have hn : 0<S^2-‖p+q‖^2 := by nlinarith [norm_nonneg (p+q)]
  refine ⟨(S^2-‖p+q‖^2)/D,div_pos hn hD,?_⟩
  intro v
  have hcs := real_inner_mul_inner_self_le (p+q) v
  simp only [real_inner_self_eq_norm_sq] at hcs
  rw [cmcSecant_apply,inner_sub_right,real_inner_smul_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm v (p+q)]
  have he : (cmcWeight p+cmcWeight q)/(2*cmcWeight p*cmcWeight q)=S^2/D := by
    dsimp [S,D]
    field_simp
  change (S^2-‖p+q‖^2)/D*‖v‖^2≤_
  rw [he]
  rw [real_inner_comm (p+q) v]
  change (S^2-‖p+q‖^2)/D*‖v‖^2≤S^2/D*‖v‖^2-⟪p+q,v⟫/D*⟪p+q,v⟫
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div,div_mul_eq_mul_div,← sub_div,
    div_le_div_iff_of_pos_right hD]
  nlinarith

lemma cmcSecant_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun z : Plane×Plane => cmcSecant z.1 z.2) := by
  have hp := cmcWeight_contDiff.comp (contDiff_fst : ContDiff ℝ (⊤ : ℕ∞) (Prod.fst : Plane×Plane → Plane))
  have hq := cmcWeight_contDiff.comp (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (Prod.snd : Plane×Plane → Plane))
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun z : Plane×Plane => 2*cmcWeight z.1*cmcWeight z.2) := (contDiff_const.mul hp).mul hq
  have hn (z : Plane×Plane) : 2*cmcWeight z.1*cmcWeight z.2≠0 := by
    have hh := cmcWeight_pos z.1; have hk := cmcWeight_pos z.2; positivity
  have hs (z : Plane×Plane) : cmcWeight z.1+cmcWeight z.2≠0 := ne_of_gt (add_pos (cmcWeight_pos _) (cmcWeight_pos _))
  unfold cmcSecant
  apply ((hp.add hq).div hd hn).smul contDiff_const |>.sub
  exact (contDiff_const.div (hd.mul (hp.add hq)) (fun z => mul_ne_zero (hn z) (hs z))).smul
    (((innerSL ℝ : Plane →L[ℝ] Plane →L[ℝ] ℝ).contDiff.comp (contDiff_fst.add contDiff_snd)).smulRight
      (contDiff_fst.add contDiff_snd))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_sub {f g : Plane → ℝ} (hf : PlaneSmooth f) (hg : PlaneSmooth g) (x : Plane) :
    gradient (fun y => g y-f y) x=gradient g x-gradient f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,inner_sub_left,inner_gradient_left,inner_gradient_left,
    fderiv_fun_sub (hg.differentiable (by simp) x) (hf.differentiable (by simp) x)]
  rfl

lemma cmcSecant_comp_contDiff {p q : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => cmcSecant (p x) (q x)) := by
  have hw₁ : ContDiff ℝ (⊤ : ℕ∞) (fun x => cmcWeight (p x)) := cmcWeight_contDiff.comp hp
  have hw₂ : ContDiff ℝ (⊤ : ℕ∞) (fun x => cmcWeight (q x)) := cmcWeight_contDiff.comp hq
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => 2*cmcWeight (p x)*cmcWeight (q x)) :=
    (contDiff_const.mul hw₁).mul hw₂
  have hn (x : Plane) : 2*cmcWeight (p x)*cmcWeight (q x)≠0 := by
    have hh := cmcWeight_pos (p x); have hk := cmcWeight_pos (q x); positivity
  have hs (x : Plane) : cmcWeight (p x)+cmcWeight (q x)≠0 :=
    ne_of_gt (add_pos (cmcWeight_pos _) (cmcWeight_pos _))
  unfold cmcSecant
  apply ((hw₁.add hw₂).div hd hn).smul contDiff_const |>.sub
  exact (contDiff_const.div (hd.mul (hw₁.add hw₂)) (fun x => mul_ne_zero (hn x) (hs x))).smul
    (((innerSL ℝ : Plane →L[ℝ] Plane →L[ℝ] ℝ).contDiff.comp (hp.add hq)).smulRight (hp.add hq))

lemma cmcSecant_graph_contDiff {f g : Plane → ℝ} (hf : PlaneSmooth f) (hg : PlaneSmooth g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => cmcSecant (gradient f x) (gradient g x)) := by
  exact cmcSecant_comp_contDiff (plane_gradient_contDiff hf) (plane_gradient_contDiff hg)

lemma cmcSecant_graph_flux {f g : Plane → ℝ} (hf : PlaneSmooth f) (hg : PlaneSmooth g) :
    (fun y => cmcSecant (gradient f y) (gradient g y) (gradient (fun z => g z-f z) y))=
      fun y => cmcFlux (gradient g y)-cmcFlux (gradient f y) := by
  funext y
  rw [plane_gradient_sub hf hg]
  exact cmcSecant_exact _ _

lemma cmcSecant_graph_divergence {f g : Plane → ℝ} (hf : PlaneSmooth f) (hg : PlaneSmooth g) (x : Plane) :
    planeElliptic (fun y => cmcSecant (gradient f y) (gradient g y)) (fun y => g y-f y) x=
      planeDivergence (fun y => cmcFlux (gradient g y)) x-
        planeDivergence (fun y => cmcFlux (gradient f y)) x := by
  unfold planeElliptic
  rw [cmcSecant_graph_flux hf hg]
  exact planeDivergence_sub (cmcFlux_contDiff.comp (plane_gradient_contDiff hg))
    (cmcFlux_contDiff.comp (plane_gradient_contDiff hf)) x

theorem cmcGraph_unique_continuation {f g : Plane → ℝ}
    (hf : PlaneSmooth f) (hg : PlaneSmooth g)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsPreconnected U)
    (heq : ∀ x∈U,planeDivergence (fun y => cmcFlux (gradient f y)) x=
      planeDivergence (fun y => cmcFlux (gradient g y)) x)
    (hpatch : (U∩interior {x | f x=g x}).Nonempty) : ∀ x∈U,f x=g x := by
  have hzero : ∀ x∈U,planeElliptic (fun y => cmcSecant (gradient f y) (gradient g y))
      (fun y => g y-f y) x=0 := by
    intro x hx
    rw [cmcSecant_graph_divergence hf hg,heq x hx,sub_self]
  have hzset : {x | f x=g x}={x | g x-f x=0} := by ext x; simp [sub_eq_zero,eq_comm]
  rw [hzset] at hpatch
  have hs : ∀ x v w,⟪v,cmcSecant (gradient f x) (gradient g x) w⟫=
      ⟪w,cmcSecant (gradient f x) (gradient g x) v⟫ := fun x v w => cmcSecant_symmetric _ _ v w
  have hell : ∀ x∈U,∃ ℓ>0,∀ v,ℓ*‖v‖^2≤⟪v,cmcSecant (gradient f x) (gradient g x) v⟫ :=
    fun x _ => cmcSecant_elliptic _ _
  have hh := planeElliptic_unique_continuation (cmcSecant_graph_contDiff hf hg) (hg.sub hf)
    hs hU hUc hell hzero hpatch
  exact fun x hx => (sub_eq_zero.mp (hh x hx)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_smooth_local_inverse {P : Plane → Plane}
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hP0 : P 0=0)
    (hinj : Function.Injective (fderiv ℝ P 0)) :
    ∃ q : Plane → Plane,∃ R>0,q 0=0 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) q (Metric.ball 0 R) ∧
      (∀ y∈Metric.ball 0 R,P (q y)=y) ∧
      ∀ᶠ y in 𝓝 (0 : Plane),q (P y)=y := by
  have hbij : Function.Bijective (fderiv ℝ P 0) :=
    ⟨hinj,(LinearMap.injective_iff_surjective (f := (fderiv ℝ P 0).toLinearMap)).mp hinj⟩
  let e : Plane ≃L[ℝ] Plane := (LinearEquiv.ofBijective (fderiv ℝ P 0).toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasFDerivAt P (e : Plane →L[ℝ] Plane) 0 := (hP.differentiable (by simp) 0).hasFDerivAt
  let h := hP.contDiffAt.toOpenPartialHomeomorph P hd (by simp)
  have hsource : (0 : Plane)∈h.source := hP.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have htarget : (0 : Plane)∈h.target := by
    simpa only [hP0] using hP.contDiffAt.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have hcoe : (h : Plane → Plane)=P := rfl
  have hq0 : h.symm (0 : Plane)=0 := by
    simpa only [hcoe,hP0] using h.left_inv hsource
  have hqcont : ContinuousAt h.symm (0 : Plane) :=
    h.continuousOn_invFun.continuousAt (h.open_target.mem_nhds htarget)
  have hunit : ∀ᶠ y in 𝓝 (0 : Plane),IsUnit (fderiv ℝ P y) := by
    have hevent := (hP.continuous_fderiv (by simp)).continuousAt.eventually e.nhds
    filter_upwards [hevent] with point hpoint
    obtain ⟨equiv,hequiv⟩ := hpoint
    rw [← hequiv]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr equiv.bijective
  have hunitq : ∀ᶠ y in 𝓝 (0 : Plane),IsUnit (fderiv ℝ P (h.symm y)) := by
    have ht : Tendsto h.symm (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by simpa [hq0] using hqcont.tendsto
    exact ht.eventually hunit
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (h.open_target.mem_nhds htarget) hunitq)
  refine ⟨h.symm,R,hR,hq0,?_,?_,?_⟩
  · intro y hy
    have hb := hball hy
    have hbj := ContinuousLinearMap.isUnit_iff_bijective.mp hb.2
    let ey : Plane ≃L[ℝ] Plane :=
      (LinearEquiv.ofBijective (fderiv ℝ P (h.symm y)).toLinearMap hbj).toContinuousLinearEquiv
    have hdy : HasFDerivAt h (ey : Plane →L[ℝ] Plane) (h.symm y) :=
      (hP.differentiable (by simp) _).hasFDerivAt
    exact (h.contDiffAt_symm hb.1 hdy (show ContDiffAt ℝ (⊤ : ℕ∞) h (h.symm y) from hP.contDiffAt)).contDiffWithinAt
  · intro y hy
    exact h.right_inv (hball hy).1
  · filter_upwards [h.open_source.mem_nhds hsource] with y hy
    exact h.left_inv hy

lemma normalPlane_decomposition {n : Cover} (hn : ‖n‖=1) (v : Cover) :
    normalPlaneEmbedding n (normalPlaneCoordinates n v)+⟪n,v⟫ • n=v := by
  have hz : ⟪n,v-⟪n,v⟫ • n⟫=0 := by
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,sub_self]
  have hh := normalPlaneEmbedding_coordinates_of_inner_zero hn hz
  rw [map_sub,map_smul,normalPlaneCoordinates_normal hn,smul_zero,sub_zero] at hh
  rw [hh]
  abel

lemma normalGraph_derivative_tangent {m : Cover} (hm : ‖m‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v : Plane) :
    ⟪graphSlopeNormal m (gradient g y),fderiv ℝ (normalGraph m g) y v⟫=0 := by
  have he : ⟪normalPlaneEmbedding m (gradient g y),m⟫=0 := by
    rw [real_inner_comm,normalPlaneEmbedding_inner hm]
  have hp : ⟪normalPlaneEmbedding m (gradient g y),normalPlaneEmbedding m v⟫=⟪gradient g y,v⟫ :=
    (normalPlaneLinearIsometry m).inner_map_map _ _
  rw [normalGraph_fderiv_apply hg,graphSlopeNormal_weight hm]
  simp only [real_inner_smul_left,inner_sub_left,inner_add_right,real_inner_smul_right,
    normalPlaneEmbedding_inner hm,real_inner_self_eq_norm_sq,hm,one_pow,he,hp]
  ring

theorem normalGraph_regraph {m n : Cover} (hm : ‖m‖=1) (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : g 0=0)
    (ht : ∀ v : Plane,⟪n,fderiv ℝ (normalGraph m g) 0 v⟫=0) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),normalGraph m g
        (normalPlaneCoordinates m (normalGraph n f y))=normalGraph n f y) ∧
      ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n f
        (normalPlaneCoordinates n (normalGraph m g y))=normalGraph m g y := by
  let G := normalGraph m g
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry m).contDiff.add (hg.smul contDiff_const)
  have hG0 : G 0=0 := by
    change (normalPlaneLinearIsometry m) 0+g 0 • m=0
    simp [hg0]
  let P : Plane → Plane := fun y => normalPlaneCoordinates n (G y)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (normalPlaneCoordinates n).contDiff.comp hG
  have hP0 : P 0=0 := by simp [P,hG0]
  have hder : fderiv ℝ P 0=(normalPlaneCoordinates n).comp (fderiv ℝ G 0) :=
    ((normalPlaneCoordinates n).hasFDerivAt.comp 0 (hG.differentiable (by simp) 0).hasFDerivAt).fderiv
  have hinj : Function.Injective (fderiv ℝ P 0) := by
    intro v w he
    have he' : fderiv ℝ G 0 v=fderiv ℝ G 0 w := by
      rw [hder] at he
      have hv := normalPlaneEmbedding_coordinates_of_inner_zero hn (ht v)
      have hw := normalPlaneEmbedding_coordinates_of_inner_zero hn (ht w)
      rw [← hv,← hw]
      exact congrArg (normalPlaneEmbedding n) he
    have hh := congrArg (normalPlaneCoordinates m) he'
    simpa only [G,normalGraph_fderiv_apply hg,map_add,map_smul,normalPlaneCoordinates_embedding,
      normalPlaneCoordinates_normal hm,smul_zero,add_zero] using hh
  obtain ⟨q,R,hR,hq0,hq,hpq,hqp⟩ := plane_smooth_local_inverse hP hP0 hinj
  let f₀ : Plane → ℝ := fun y => ⟪n,G (q y)⟫
  have hf₀ : ContDiffOn ℝ (⊤ : ℕ∞) f₀ (Metric.ball 0 R) :=
    contDiffOn_const.inner ℝ (hG.comp_contDiffOn hq)
  obtain ⟨f,hf,hff⟩ := smooth_graph_extension hR hf₀
  have hf0 : f 0=0 := by
    rw [hff (by simpa using half_pos hR)]
    simp [f₀,hq0,hG0]
  have heq : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n f y=G (q y) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (half_pos hR)] with y hy
    have hyR : y∈Metric.ball (0 : Plane) R := (Metric.ball_subset_ball (by linarith)) hy
    have hh := normalPlane_decomposition hn (G (q y))
    have hpq' : normalPlaneCoordinates n (G (q y))=y := hpq y hyR
    rw [hpq'] at hh
    simpa only [normalGraph,hff hy,f₀] using hh
  refine ⟨f,hf,hf0,?_,?_⟩
  · filter_upwards [heq] with y hy
    rw [hy,normalPlaneCoordinates_graph hm]
  · have htP : Tendsto P (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by simpa [hP0] using hP.continuous.continuousAt.tendsto (x := 0)
    filter_upwards [htP.eventually heq,hqp] with y hy hqy
    change normalGraph n f (P y)=G y
    rw [hy,hqy]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma unit_normal_graph_unique {n ν : Cover} (hn : ‖n‖=1) (hν : ‖ν‖=1)
    {p : Plane} (hpos : 0<⟪n,ν⟫)
    (ht : ∀ v : Plane,⟪ν,normalPlaneEmbedding n v+⟪p,v⟫ • n⟫=0) :
    ν=graphSlopeNormal n p := by
  let d : ℝ := ⟪n,ν⟫
  have hproj : normalPlaneCoordinates n ν= -d • p := by
    apply ext_inner_left ℝ
    intro v
    have hh := ht v
    rw [inner_add_right,real_inner_smul_right,real_inner_comm n ν] at hh
    rw [normalPlaneCoordinates,ContinuousLinearMap.adjoint_inner_right,real_inner_smul_right,
      real_inner_comm p v]
    change ⟪normalPlaneEmbedding n v,ν⟫ = -d*⟪p,v⟫
    rw [real_inner_comm ν (normalPlaneEmbedding n v)]
    dsimp [d] at *
    linarith
  have he : ν=d • (n-normalPlaneEmbedding n p) := by
    have hh := normalPlane_decomposition hn ν
    rw [hproj] at hh
    change (normalPlaneLinearIsometry n) (-d • p)+d • n=ν at hh
    rw [map_smul] at hh
    rw [← hh]
    change -d • normalPlaneEmbedding n p+d • n=d • (n-normalPlaneEmbedding n p)
    module
  have ha : ‖n-normalPlaneEmbedding n p‖≠0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (graphSlopeVector_norm_ge hn p))
  have hd : d=‖n-normalPlaneEmbedding n p‖⁻¹ := by
    have hh := congrArg norm he
    rw [hν,norm_smul,Real.norm_eq_abs,abs_of_pos hpos] at hh
    rw [← one_div]
    apply (eq_div_iff ha).mpr
    simpa only [one_div] using hh.symm
  rw [he,hd,graphSlopeNormal]

lemma normalGraph_zero {n : Cover} {f : Plane → ℝ} (hf0 : f 0=0) :
    normalGraph n f 0=0 := by
  change (normalPlaneLinearIsometry n) 0+f 0 • n=0
  simp [hf0]

lemma normalGraph_tendsto_zero {n : Cover} {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0=0) :
    Tendsto (normalGraph n f) (𝓝 (0 : Plane)) (𝓝 (0 : Cover)) := by
  have hc : Continuous (normalGraph n f) :=
    (normalPlaneLinearIsometry n).continuous.add (hf.continuous.smul continuous_const)
  simpa only [normalGraph_zero hf0] using hc.continuousAt.tendsto (x := 0)

theorem normalGraph_regraph_normal {m n x : Cover} (hm : ‖m‖=1) (hn : ‖n‖=1)
    {g f : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0=0) {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNx : N x=n)
    (hmatch : ∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph m g y)=σ • graphSlopeNormal m (gradient g y))
    (hgraph : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph m g
      (normalPlaneCoordinates m (normalGraph n f y))=normalGraph n f y) :
    ∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=graphSlopeNormal n (gradient f y) := by
  let P : Plane → Plane := fun y => normalPlaneCoordinates m (normalGraph n f y)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (normalPlaneCoordinates m).contDiff.comp
    ((normalPlaneLinearIsometry n).contDiff.add (hf.smul contDiff_const))
  have hP0 : P 0=0 := by simp only [P,normalGraph_zero hf0,map_zero]
  have htP : Tendsto P (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by
    simpa only [hP0] using hP.continuous.continuousAt.tendsto (x := 0)
  have hpos : ∀ᶠ y in 𝓝 (0 : Plane),0<⟪n,N (x+normalGraph n f y)⟫ := by
    have hc : Continuous (fun y => ⟪n,N (x+normalGraph n f y)⟫) :=
      continuous_const.inner (hN.continuous.comp
        (continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
          (hf.continuous.smul continuous_const))))
    have hz : 0<⟪n,N (x+normalGraph n f 0)⟫ := by
      rw [normalGraph_zero hf0,add_zero,hNx,real_inner_self_eq_norm_sq,hn,one_pow]
      norm_num
    exact hc.continuousAt.eventually (lt_mem_nhds hz)
  have hgraph' : ∀ᶠ y in 𝓝 (0 : Plane),∀ᶠ z in 𝓝 y,normalGraph m g (P z)=normalGraph n f z :=
    eventually_eventually_nhds.mpr hgraph
  filter_upwards [hgraph,hgraph',htP.eventually hmatch,hpos] with y hy he hm' hpos'
  have hmy : N (x+normalGraph n f y)=σ • graphSlopeNormal m (gradient g (P y)) := by
    rw [← hy]
    exact hm'
  refine unit_normal_graph_unique hn ?_ hpos' ?_
  · rw [hmy]
    rcases hσ with rfl|rfl <;> simp [graphSlopeNormal_unit hm]
  · intro v
    have he' : (fun z => normalGraph m g (P z)) =ᶠ[𝓝 y] normalGraph n f := he
    have hder := he'.fderiv_eq (𝕜 := ℝ)
    have hgD := (normalGraph_hasFDerivAt (n := m) (hg.differentiable (by simp) (P y)))
    have hPder := (hP.differentiable (by simp) y).hasFDerivAt
    change fderiv ℝ (normalGraph m g ∘ P) y=fderiv ℝ (normalGraph n f) y at hder
    rw [(hgD.comp y hPder).fderiv] at hder
    have hs := congrArg (fun L : Plane →L[ℝ] Cover => L v) hder
    have hs' : fderiv ℝ (normalGraph m g) (P y) (fderiv ℝ P y v)=
        fderiv ℝ (normalGraph n f) y v := by
      rw [hgD.fderiv]
      exact hs
    rw [← normalGraph_fderiv_apply hf,← hs',hmy,real_inner_smul_left,
      normalGraph_derivative_tangent hm hg,mul_zero]

lemma normalGraph_regraph_cover {m n : Cover} {g f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf0 : f 0=0) (hg0 : g 0=0)
    (hforward : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph m g
      (normalPlaneCoordinates m (normalGraph n f y))=normalGraph n f y)
    (hback : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n f
      (normalPlaneCoordinates n (normalGraph m g y))=normalGraph m g y) :
    ∀ᶠ v in 𝓝 (0 : Cover),
      (normalGraph m g (normalPlaneCoordinates m v)=v ↔
        normalGraph n f (normalPlaneCoordinates n v)=v) := by
  have htm : Tendsto (normalPlaneCoordinates m) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) :=
    (normalPlaneCoordinates m).continuous.tendsto' _ _ (map_zero _)
  have htn : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) :=
    (normalPlaneCoordinates n).continuous.tendsto' _ _ (map_zero _)
  have hgm : Tendsto (fun v : Cover => normalGraph m g (normalPlaneCoordinates m v))
      (𝓝 (0 : Cover)) (𝓝 (0 : Cover)) := (normalGraph_tendsto_zero hg hg0).comp htm
  have hfn : Tendsto (fun v : Cover => normalGraph n f (normalPlaneCoordinates n v))
      (𝓝 (0 : Cover)) (𝓝 (0 : Cover)) := (normalGraph_tendsto_zero hf hf0).comp htn
  filter_upwards [hgm.eventually (htm.eventually hback),
    hfn.eventually (htn.eventually hforward)] with v hb hf'
  constructor
  · intro hv
    simpa only [hv] using hb
  · intro hv
    simpa only [hv] using hf'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_tangent_CMC_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ k x,N (x+latticeVector k)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) {H : ℝ}
    (hgeom : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),
        N (x+normalGraph (N x) f y)=graphSlopeNormal (N x) (gradient f y) ∧
        quotientMap (x+normalGraph (N x) f y)∈frontier (openRepresentative E) ∧
        planeDivergence (fun z => cmcFlux (gradient f z)) y= -H) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph (N x) f (normalPlaneCoordinates (N x) v)=v := by
  obtain ⟨m,g,σ,hm,hg,hg0,hσ,hmatch,hcover⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hmin hμ hN hp hae x hx
  have hn : ‖N x‖=1 := (hgeom x hx).1.self_of_nhds
  have hcenter : N x=σ • graphSlopeNormal m (gradient g 0) := by
    simpa only [normalGraph_zero hg0,add_zero] using hmatch.self_of_nhds.1
  have ht (v : Plane) : ⟪N x,fderiv ℝ (normalGraph m g) 0 v⟫=0 := by
    rw [hcenter,real_inner_smul_left,normalGraph_derivative_tangent hm hg,mul_zero]
  obtain ⟨f,hf,hf0,hforward,hback⟩ := normalGraph_regraph hm hn hg hg0 ht
  have hnorm := normalGraph_regraph_normal hm hn hg hf hf0 hσ hN rfl
    (hmatch.mono fun y hy => hy.1) hforward
  have hnewcov := normalGraph_regraph_cover hf hg hf0 hg0 hforward hback
  have hP : Tendsto (fun y => normalPlaneCoordinates m (normalGraph (N x) f y))
      (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) :=
    ((normalPlaneCoordinates m).continuous.tendsto' _ _ (map_zero _)).comp
      (normalGraph_tendsto_zero hf hf0)
  have hnew : ∀ᶠ y in 𝓝 (0 : Plane),quotientMap (x+normalGraph (N x) f y)∈frontier (openRepresentative E) := by
    filter_upwards [hP.eventually hmatch,hforward] with y hy he
    have hh := hy.2
    rwa [he] at hh
  refine ⟨f,hf,hf0,?_,?_⟩
  · filter_upwards [hnorm,hnew,eventually_eventually_nhds.mpr hnorm] with y hy hyS hny
    refine ⟨hy,hyS,?_⟩
    have hd := graph_normal_extension_divergence x hn hf y (σ := 1) (Or.inl rfl) hN
      (hgeom _ hyS).1 (by simpa only [one_smul] using hny)
    rw [(hgeom _ hyS).2] at hd
    linarith
  · filter_upwards [hcover,hnewcov] with v hv hvc
    exact hv.trans hvc

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def relativeContainmentNeighborhood (S T : Set Torus) : Set Torus := interior (Sᶜ∪T)

lemma relativeContainmentNeighborhood_mem {S T : Set Torus} {a : Torus}
    (ha : a∈S) (hz : a∈relativeContainmentNeighborhood S T) : a∈T :=
  (interior_subset hz).resolve_left (fun hn => hn ha)

lemma quotient_graph_containment_germ {S T : Set Torus}
    {x : Cover} {G : Plane → Cover} {P : Cover →L[ℝ] Plane}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v)
    (hz : ∀ᶠ y in 𝓝 (0 : Plane),quotientMap (x+G y)∈T) :
    quotientMap x∈relativeContainmentNeighborhood S T := by
  have hP : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
  have hev : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → quotientMap (x+v)∈T := by
    filter_upwards [hcover,hP.eventually hz] with v hv hvz hS
    rwa [hv hS] at hvz
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (quotientMap x) hδ)
  intro a ha
  by_cases haS : a∈S
  · right
    rw [← quotientMap_image_ball x δ] at ha
    obtain ⟨z,hz,hza⟩ := ha
    have hz' : z-x∈Metric.ball (0 : Cover) δ := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hz
    simpa only [add_sub_cancel,hza] using hball hz' (by simpa only [add_sub_cancel,hza] using haS)
  · exact Or.inl haS

lemma preconnected_subset_of_closed_germ {S T : Set Torus}
    (hS : IsPreconnected S) (hD : IsClosed (S∩relativeContainmentNeighborhood S T))
    (hpatch : (S∩relativeContainmentNeighborhood S T).Nonempty) : S⊆T := by
  let Z := relativeContainmentNeighborhood S T
  have hZ : IsOpen Z := isOpen_interior
  have hsub : S⊆Z := by
    intro a ha
    by_contra hn
    have hcover : S⊆Z∪(S∩Z)ᶜ := by
      intro b hb
      by_cases hz : b∈Z
      · exact Or.inl hz
      · exact Or.inr (fun hd => hz hd.2)
    obtain ⟨b,hbS,hbZ,hbn⟩ := hS Z (S∩Z)ᶜ hZ hD.isOpen_compl hcover hpatch
      ⟨a,ha,fun hd => hn hd.2⟩
    exact hbn ⟨hbS,hbZ⟩
  exact fun a ha => relativeContainmentNeighborhood_mem ha (hsub ha)

lemma normalGraph_eq_height {n : Cover} (hn : ‖n‖=1) {f g : Plane → ℝ} {y : Plane}
    (he : normalGraph n f y=normalGraph n g y) : f y=g y := by
  simpa only [normalGraph_inner hn] using congrArg (fun v : Cover => ⟪n,v⟫) he

lemma normalGraph_boundary_height {n x : Cover} (hn : ‖n‖=1) {f g : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0=0) {S : Set Torus}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S ↔
      normalGraph n g (normalPlaneCoordinates n v)=v) :
    ∀ᶠ y in 𝓝 (0 : Plane),quotientMap (x+normalGraph n f y)∈S ↔ f y=g y := by
  filter_upwards [(normalGraph_tendsto_zero hf hf0).eventually hcover] with y hy
  rw [normalPlaneCoordinates_graph hn] at hy
  refine hy.trans ⟨fun h => (normalGraph_eq_height hn h).symm,?_⟩
  intro he
  simp only [normalGraph,he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

structure OrientedCMCCharts (S : Set Torus) (H : ℝ) (N : Cover → Cover) : Prop where
  normal_smooth : ContDiff ℝ (⊤ : ℕ∞) N
  normal_periodic : ∀ m x,N (x+latticeVector m)=N x
  chart : ∀ x : Cover,quotientMap x∈S → ‖N x‖=1 ∧
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),
        N (x+normalGraph (N x) f y)=graphSlopeNormal (N x) (gradient f y) ∧
        quotientMap (x+normalGraph (N x) f y)∈S ∧
        planeDivergence (fun z => cmcFlux (gradient f z)) y= -H) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S ↔
        normalGraph (N x) f (normalPlaneCoordinates (N x) v)=v

theorem isMinimizerAt_oriented_CMC_charts {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      OrientedCMCCharts (frontier (openRepresentative E)) H N := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hgeom,_⟩ :=
    Periodic.isMinimizerAt_tubular_normal_stability hV hE hmin
  refine ⟨μ,H,N,hμ,hae,hN,hp,?_⟩
  intro x hx
  exact ⟨(hgeom x hx).1.self_of_nhds,
    isMinimizerAt_tangent_CMC_chart hV hE hmin hμ hN hp hae hgeom x hx⟩

theorem OrientedCMCCharts.containment_germs_closed
    {S T : Set Torus} (hS : IsClosed S) (hT : IsClosed T)
    {H : ℝ} {N M : Cover → Cover}
    (hN : OrientedCMCCharts S H N) (hM : OrientedCMCCharts T H M) :
    IsClosed (S∩relativeContainmentNeighborhood S
      (T∩{a | N (representative a)=M (representative a)})) := by
  let A := T∩{a | N (representative a)=M (representative a)}
  let Z := relativeContainmentNeighborhood S A
  let D := S∩Z
  have hAc : IsClosed A := hT.inter (isClosed_eq
    (continuous_periodic_descent hN.normal_smooth.continuous hN.normal_periodic)
    (continuous_periodic_descent hM.normal_smooth.continuous hM.normal_periodic))
  have hDA : D⊆A := fun a ha => relativeContainmentNeighborhood_mem ha.1 ha.2
  apply isClosed_of_closure_subset
  intro a ha
  have haS : a∈S := closure_minimal inter_subset_left hS ha
  have haA : a∈A := closure_minimal hDA hAc ha
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hxS : quotientMap x∈S := by rwa [hxa]
  have hxT : quotientMap x∈T := by rw [hxa]; exact haA.1
  have hNM : N x=M x := haA.2
  obtain ⟨hn,f,hf,hf0,hfm,hfc⟩ := hN.chart x hxS
  obtain ⟨_,g,hg,hg0,hgm,hgc⟩ := hM.chart x hxT
  rw [← hNM] at hgm hgc
  let G := normalGraph (N x) f
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry (N x)).contDiff.add (hf.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  have hheight := normalGraph_boundary_height hn hf hf0 hgc
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((hfm.and hgm).and hheight)
  have hc : (0 : Plane)∈closure (φ ⁻¹' D) := quotient_graph_closure inter_subset_left
    (hfc.mono fun v hv => hv.mp) (by rwa [hxa])
  obtain ⟨y,hyD,hyd⟩ := Metric.mem_closure_iff.mp hc r hr
  have hyr : y∈Metric.ball (0 : Plane) r := by
    simpa only [Metric.mem_ball,dist_comm] using hyd
  have hO : IsOpen (φ ⁻¹' Z∩Metric.ball 0 r) :=
    (isOpen_interior.preimage hφ).inter Metric.isOpen_ball
  have hOeq : φ ⁻¹' Z∩Metric.ball 0 r⊆{z | f z=g z} := by
    intro z hz
    have hb := hball hz.2
    exact hb.2.mp (relativeContainmentNeighborhood_mem hb.1.1.2.1 hz.1).1
  have hpatch : (Metric.ball (0 : Plane) r∩interior {z | f z=g z}).Nonempty :=
    ⟨y,hyr,(hO.subset_interior_iff.mpr hOeq) ⟨hyD.2,hyr⟩⟩
  have heq := cmcGraph_unique_continuation hf hg Metric.isOpen_ball
    (convex_ball (0 : Plane) r).isPreconnected
    (fun z hz => (hball hz).1.1.2.2.trans (hball hz).1.2.2.2.symm) hpatch
  have he : f =ᶠ[𝓝 (0 : Plane)] g := Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) heq
  have heg : ∀ᶠ y in 𝓝 (0 : Plane),f =ᶠ[𝓝 y] g := eventually_eventually_nhds.mpr he
  refine ⟨haS,?_⟩
  rw [← hxa]
  apply quotient_graph_containment_germ (hfc.mono fun v hv => hv.mp)
  filter_upwards [hfm,hgm,he,heg] with z hz hk hez hezg
  have heG : normalGraph (N x) f z=normalGraph (N x) g z := by
    simp only [normalGraph,hez]
  refine ⟨?_,?_⟩
  · simpa only [heG] using hk.2.1
  · change N (representative (φ z))=M (representative (φ z))
    rw [periodic_representative hN.normal_periodic,periodic_representative hM.normal_periodic]
    change N (x+normalGraph (N x) f z)=M (x+normalGraph (N x) f z)
    rw [hz.1,heG,hk.1,(plane_gradient_eventuallyEq hezg).eq_of_nhds]

theorem OrientedCMCCharts.containment_of_patch
    {S T : Set Torus} (hS : IsClosed S) (hT : IsClosed T) (hSc : IsPreconnected S)
    {H : ℝ} {N M : Cover → Cover}
    (hN : OrientedCMCCharts S H N) (hM : OrientedCMCCharts T H M)
    {U : Set Torus} (hU : IsOpen U) (hpatch : (S∩U).Nonempty)
    (hu : S∩U⊆T∩{a | N (representative a)=M (representative a)}) :
    S⊆T∩{a | N (representative a)=M (representative a)} := by
  apply preconnected_subset_of_closed_germ hSc (hN.containment_germs_closed hS hT hM)
  obtain ⟨a,haS,haU⟩ := hpatch
  refine ⟨a,haS,?_⟩
  apply hU.subset_interior_iff.mpr ?_ haU
  intro b hb
  by_cases hbs : b∈S
  · exact Or.inr (hu ⟨hbs,hb⟩)
  · exact Or.inl hbs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem OrientedCMCCharts.curvature_eq_of_patch
    {S T : Set Torus} {H K : ℝ} {N M : Cover → Cover}
    (hN : OrientedCMCCharts S H N) (hM : OrientedCMCCharts T K M)
    {U : Set Torus} (hU : IsOpen U) (hpatch : (S∩U).Nonempty)
    (hu : S∩U⊆T∩{a | N (representative a)=M (representative a)}) : H=K := by
  obtain ⟨a,haS,haU⟩ := hpatch
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hxS : quotientMap x∈S := by rwa [hxa]
  have hxT : quotientMap x∈T := by rw [hxa]; exact (hu ⟨haS,haU⟩).1
  have hNM : N x=M x := (hu ⟨haS,haU⟩).2
  obtain ⟨hn,f,hf,hf0,hfm,_⟩ := hN.chart x hxS
  obtain ⟨_,g,hg,hg0,hgm,hgc⟩ := hM.chart x hxT
  rw [← hNM] at hgm hgc
  have hφ : Tendsto (fun y => quotientMap (x+normalGraph (N x) f y))
      (𝓝 (0 : Plane)) (𝓝 a) := by
    have ht : Tendsto (fun y : Plane => x+normalGraph (N x) f y)
        (𝓝 (0 : Plane)) (𝓝 x) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := x)).add (normalGraph_tendsto_zero hf hf0)
    simpa only [Function.comp_def,hxa] using (continuous_quotientMap.tendsto x).comp ht
  have hheight := normalGraph_boundary_height hn hf hf0 hgc
  have he : f =ᶠ[𝓝 (0 : Plane)] g := by
    filter_upwards [hfm,hheight,hφ.eventually (hU.mem_nhds haU)] with y hy he hu'
    exact he.mp (hu ⟨hy.2.1,hu'⟩).1
  have hflux : (fun y => cmcFlux (gradient f y))=ᶠ[𝓝 (0 : Plane)]
      (fun y => cmcFlux (gradient g y)) := by
    filter_upwards [plane_gradient_eventuallyEq he] with y hy
    rw [hy]
  have hd : planeDivergence (fun y => cmcFlux (gradient f y)) 0=
      planeDivergence (fun y => cmcFlux (gradient g y)) 0 := by
    simp only [planeDivergence,hflux.fderiv_eq]
  rw [hfm.self_of_nhds.2.2,hgm.self_of_nhds.2.2] at hd
  linarith

theorem OrientedCMCCharts.eq_of_patch
    {S T : Set Torus} (hS : IsClosed S) (hT : IsClosed T)
    (hSc : IsPreconnected S) (hTc : IsPreconnected T)
    {H K : ℝ} {N M : Cover → Cover}
    (hN : OrientedCMCCharts S H N) (hM : OrientedCMCCharts T K M)
    {U : Set Torus} (hU : IsOpen U) (hpatch : (S∩U).Nonempty)
    (hst : S∩U=T∩U)
    (hu : ∀ a∈S∩U,N (representative a)=M (representative a)) :
    S=T ∧ ∀ a∈S,N (representative a)=M (representative a) := by
  have hsub : S∩U⊆T∩{a | N (representative a)=M (representative a)} := by
    intro a ha
    exact ⟨(hst ▸ ha).1,hu a ha⟩
  have hHK := hN.curvature_eq_of_patch hM hU hpatch hsub
  subst K
  have hST := hN.containment_of_patch hS hT hSc hM hU hpatch hsub
  have hTS := hM.containment_of_patch hT hS hTc hN hU (hst ▸ hpatch) (by
    intro a ha
    have hh : a∈S∩U := hst.symm ▸ ha
    exact ⟨hh.1,(hu a hh).symm⟩)
  exact ⟨Subset.antisymm (fun a ha => (hST ha).1) (fun a ha => (hTS ha).1),fun a ha => (hST ha).2⟩

end CubicTorus

end
end

end OAI
