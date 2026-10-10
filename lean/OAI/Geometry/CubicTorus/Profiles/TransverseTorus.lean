import Mathlib
import OAI.Geometry.CubicTorus.Reflection.SiblingAxialProjection

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialProjection_axis {v : Cover} (hv : ‖v‖=1) : sibling_axialProjection v v=0 := by
  rw [sibling_axialProjection_apply,real_inner_self_eq_norm_sq,hv,one_pow,one_smul,sub_self]

lemma sibling_axialProjection_idempotent {v : Cover} (hv : ‖v‖=1) (x : Cover) :
    sibling_axialProjection v (sibling_axialProjection v x)=sibling_axialProjection v x := by
  rw [sibling_axialProjection_apply v x,map_sub,map_smul,axialProjection_axis hv,smul_zero,sub_zero]
  rfl

lemma axialProjection_transverse {v : Cover} (hv : ‖v‖=1) (x : Cover) :
    ⟪v,sibling_axialProjection v x⟫=0 := by
  rw [sibling_axialProjection_apply,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
    hv,one_pow,mul_one,sub_self]

lemma axialProjection_coordinates {v : Cover} (hv : ‖v‖=1) (x : Cover) :
    sibling_axialProjection v x=normalPlaneEmbedding v (normalPlaneCoordinates v x) := by
  have hh := normalPlaneCoordinates_reconstruct hv x
  rw [sibling_axialProjection_apply]
  exact (eq_sub_iff_add_eq.mpr hh).symm

lemma axialCylinder_preconnected {v c : Cover} (hv : ‖v‖=1) (hc : ⟪v,c⟫=0) (r : ℝ) :
    IsPreconnected (axialCylinder v c r) := by
  let S : Set (ℝ × Plane) := univ ×ˢ Metric.sphere (0 : Plane) r
  let F : ℝ × Plane → Cover := fun z ↦ c+z.1 • v+normalPlaneEmbedding v z.2
  have hF : Continuous F := (continuous_const.add (continuous_fst.smul continuous_const)).add
    ((normalPlaneLinearIsometry v).continuous.comp continuous_snd)
  have hS : IsPreconnected S := isPreconnected_univ.prod
    (isPreconnected_sphere (by rw [←Module.finrank_eq_rank]; norm_num [Plane,finrank_euclideanSpace_fin]) 0 r)
  have he : F '' S=axialCylinder v c r := by
    apply Subset.antisymm
    · rintro x ⟨⟨s,y⟩,hy,rfl⟩
      change ‖sibling_axialProjection v (c+s • v+normalPlaneEmbedding v y)-c‖=r
      rw [map_add,map_add,map_smul,axialProjection_fixed hc,axialProjection_axis hv,
        smul_zero,add_zero,axialProjection_fixed (normalPlaneEmbedding_inner hv y),
        add_sub_cancel_left,normalPlaneEmbedding_norm]
      simpa only [Metric.mem_sphere,dist_zero_right] using hy.2
    · intro x hx
      refine ⟨(⟪v,x-c⟫,normalPlaneCoordinates v (x-c)),⟨mem_univ _,?_⟩,?_⟩
      · rw [Metric.mem_sphere,dist_zero_right,←normalPlaneEmbedding_norm v,
          ←axialProjection_coordinates hv,map_sub,axialProjection_fixed hc]
        exact hx
      · dsimp only [F]
        have hh := normalPlaneCoordinates_reconstruct hv (x-c)
        calc
          _=c+(normalPlaneEmbedding v (normalPlaneCoordinates v (x-c))+⟪v,x-c⟫ • v) := by abel
          _=x := by rw [hh]; abel
  rw [←he]
  exact hS.image _ hF.continuousOn

theorem sibling_closed_cylindrical_set_contains_cylinder {S : Set Cover} (hS : IsClosed S)
    {N : Cover → Cover} (hN : Continuous N) {t : ℝ} {v : Cover} (hv : ‖v‖=1)
    (hu : ∀ a∈S,‖N a‖=1) (hz : ∀ a∈S,⟪v,N a⟫=0)
    (hloc : ∀ a∈S,∀ᶠ w in 𝓝 (0 : Cover),
      (a+w∈S ↔ a+w∈axialCylinder v (sibling_axialProjection v a-t • N a) |t|) ∧
      (a+w∈S → sibling_axialProjection v (a+w)-t • N (a+w)=sibling_axialProjection v a-t • N a))
    {a : Cover} (ha : a∈S) (b : Cover)
    (hb : b∈axialCylinder v (sibling_axialProjection v a-t • N a) |t|) :
    b∈S ∧ sibling_axialProjection v b-t • N b=sibling_axialProjection v a-t • N a := by
  let c := sibling_axialProjection v a-t • N a
  let P := axialCylinder v c |t|
  have hc : ⟪v,c⟫=0 := by
    dsimp only [c]
    rw [inner_sub_right,axialProjection_transverse hv,real_inner_smul_right,hz a ha,mul_zero,sub_zero]
  let : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp (axialCylinder_preconnected hv hc |t|)
  let T : Set P := {x | (x : Cover)∈S ∧ sibling_axialProjection v x-t • N x=c}
  have hTc : IsClosed T := (hS.preimage continuous_subtype_val).inter
    (isClosed_eq (((sibling_axialProjection v).continuous.comp continuous_subtype_val).sub
      ((hN.comp continuous_subtype_val).const_smul t)) continuous_const)
  have hTo : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have ht : Tendsto (fun y : P ↦ (y : Cover)-(x : Cover)) (𝓝 x) (𝓝 (0 : Cover)) := by
      have hc : Continuous (fun y : P ↦ (y : Cover)-(x : Cover)) := continuous_subtype_val.sub continuous_const
      simpa only [sub_self] using hc.tendsto x
    filter_upwards [ht.eventually (hloc x hx.1)] with y hy
    have hadd : (x : Cover)+((y : Cover)-(x : Cover))=(y : Cover) := by abel
    have hys : (y : Cover)∈S := by
      have hyiff : (y : Cover)∈S ↔ (y : Cover)∈axialCylinder v (sibling_axialProjection v x-t • N x) |t| := by
        simpa only [hadd] using hy.1
      apply hyiff.mpr
      rw [hx.2]
      exact y.property
    change (y : Cover)∈S ∧ sibling_axialProjection v y-t • N y=c
    refine ⟨hys,?_⟩
    have he := hy.2 (by simpa only [hadd] using hys)
    simpa only [hadd,hx.2] using he
  have haP : a∈P := by
    change ‖sibling_axialProjection v a-(sibling_axialProjection v a-t • N a)‖=|t|
    rw [sub_sub_cancel,norm_smul,hu a ha,mul_one,Real.norm_eq_abs]
  have hTu : T=univ := (show IsClopen T from ⟨hTc,hTo⟩).eq_univ ⟨⟨a,haP⟩,ha,rfl⟩
  have hmem : (⟨b,hb⟩ : P)∈T := by rw [hTu]; trivial
  exact hmem

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinate_axialProjection_lattice (i : Fin 3) (m : Fin 3 → ℤ) :
    sibling_axialProjection (EuclideanSpace.single i 1) (latticeVector m)=
      latticeVector (Function.update m i 0) := by
  ext j
  simp only [sibling_axialProjection_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.inner_single_left,PiLp.single_apply,latticeVector]
  by_cases h : j=i
  · subst j; simp
  · simp [h]

theorem periodic_complete_coordinate_cylinder_radius_lt_half
    {N : Cover → Cover} (hp : ∀ m x,N (x+latticeVector m)=N x)
    (i : Fin 3) {t : ℝ} {c : Cover}
    (hc : sibling_axialProjection (EuclideanSpace.single i 1) c=c)
    (hs : ∀ b∈axialCylinder (EuclideanSpace.single i 1) c |t|,
      sibling_axialProjection (EuclideanSpace.single i 1) b-t • N b=c) : |t|<1/2 := by
  by_contra! hh
  obtain ⟨j,k,hji,hki,hjk⟩ : ∃ j k : Fin 3,j≠i ∧ k≠i ∧ j≠k := by
    fin_cases i <;> decide
  let e : Cover := EuclideanSpace.single j 1
  let d : ℝ := Real.sqrt (t^2-1/4)
  let w : Cover := EuclideanSpace.single j (1/2)+EuclideanSpace.single k d
  have hd : d^2=t^2-1/4 := Real.sq_sqrt (by nlinarith [sq_abs t])
  have he : e=latticeVector (Pi.single j 1) := by
    ext l; simp [e,latticeVector,Pi.single_apply]
  have heunit : ‖e‖=1 := by simp [e]
  have hie : ⟪(EuclideanSpace.single i 1 : Cover),e⟫=0 := by
    simp [e,EuclideanSpace.inner_single_left,Ne.symm hji]
  have hiw : ⟪(EuclideanSpace.single i 1 : Cover),w⟫=0 := by
    simp [w,EuclideanSpace.inner_single_left,Ne.symm hji,Ne.symm hki]
  have hw : ‖w‖^2=t^2 := by
    have hinner : ⟪(EuclideanSpace.single j (1/2) : Cover),EuclideanSpace.single k d⟫=0 := by
      simp [EuclideanSpace.inner_single_left,hjk]
    rw [show w=EuclideanSpace.single j (1/2)+EuclideanSpace.single k d from rfl,norm_add_sq_real,hinner]
    simp only [PiLp.norm_single,Real.norm_eq_abs,sq_abs,mul_zero,add_zero]
    nlinarith [hd]
  have hweinner : ⟪w,e⟫=1/2 := by
    simp [w,e,inner_add_left,EuclideanSpace.inner_single_right,Ne.symm hjk]
  have hwe : ‖w-e‖^2=t^2 := by
    rw [norm_sub_sq_real,hw,heunit,hweinner]
    ring
  have hwn : ‖w‖=|t| := by nlinarith [norm_nonneg w,abs_nonneg t,sq_abs t]
  have hwen : ‖w-e‖=|t| := by nlinarith [norm_nonneg (w-e),abs_nonneg t,sq_abs t]
  have hb : c+w∈axialCylinder (EuclideanSpace.single i 1) c |t| := by
    change ‖sibling_axialProjection (EuclideanSpace.single i 1) (c+w)-c‖=|t|
    rw [map_add,hc,axialProjection_fixed hiw,add_sub_cancel_left,hwn]
  have hb' : c+w-e∈axialCylinder (EuclideanSpace.single i 1) c |t| := by
    change ‖sibling_axialProjection (EuclideanSpace.single i 1) (c+w-e)-c‖=|t|
    rw [map_sub,map_add,hc,axialProjection_fixed hiw,axialProjection_fixed hie]
    have hh : c+w-e-c=w-e := by abel
    rw [hh,hwen]
  have hn : N (c+w-e)=N (c+w) := by
    have hh := hp (Pi.single j 1) (c+w-e)
    rw [←he,sub_add_cancel] at hh
    exact hh.symm
  have h1 := hs _ hb
  have h2 := hs _ hb'
  rw [hn,map_sub,map_add,hc,axialProjection_fixed hiw,axialProjection_fixed hie] at h2
  rw [map_add,hc,axialProjection_fixed hiw] at h1
  have hz : e=0 := by
    linear_combination (norm := module) h1-h2
  have he0 := congrArg (fun x : Cover ↦ x j) hz
  simp [e] at he0

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem periodic_connected_coordinate_cylindrical_boundary {K : Set Torus}
    (hK : IsClosed K) (hc : IsPreconnected K) {N : Cover → Cover}
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (i : Fin 3) {t : ℝ}
    (hu : ∀ a : Cover,quotientMap a∈K → ‖N a‖=1)
    (hz : ∀ a : Cover,quotientMap a∈K → ⟪(EuclideanSpace.single i 1 : Cover),N a⟫=0)
    (hloc : ∀ a : Cover,quotientMap a∈K → ∀ᶠ w in 𝓝 (0 : Cover),
      (quotientMap (a+w)∈K ↔
        a+w∈axialCylinder (EuclideanSpace.single i 1)
          (sibling_axialProjection (EuclideanSpace.single i 1) a-t • N a) |t|) ∧
      (quotientMap (a+w)∈K → sibling_axialProjection (EuclideanSpace.single i 1) (a+w)-t • N (a+w)=
        sibling_axialProjection (EuclideanSpace.single i 1) a-t • N a))
    {a : Cover} (ha : quotientMap a∈K) :
    |t|<1/2 ∧ K=quotientMap '' axialCylinder (EuclideanSpace.single i 1)
      (sibling_axialProjection (EuclideanSpace.single i 1) a-t • N a) |t| := by
  let v : Cover := EuclideanSpace.single i 1
  let Q := sibling_axialProjection v
  let c := Q a-t • N a
  have hv : ‖v‖=1 := by simp [v]
  have hQc : Q c=c := by
    dsimp only [c,Q]
    rw [map_sub,map_smul,sibling_axialProjection_idempotent hv,axialProjection_fixed (hz a ha)]
  let S : Set Cover := quotientMap ⁻¹' K
  have hS : IsClosed S := hK.preimage continuous_quotientMap
  have hfull := sibling_closed_cylindrical_set_contains_cylinder hS hN hv hu hz hloc ha
  have hr : |t|<1/2 := periodic_complete_coordinate_cylinder_radius_lt_half hp i hQc
    (fun b hb ↦ (hfull b hb).2)
  refine ⟨hr,?_⟩
  apply Subset.antisymm
  · intro x hx
    let b := representative x
    have hb : quotientMap b∈K := by simpa only [b,quotientMap_representative] using hx
    let F : Cover → Torus := fun y ↦ quotientMap (Q y-t • N y)
    have hFp : ∀ m y,F (y+latticeVector m)=F y := by
      intro m y
      simp only [F,hp,map_add]
      rw [show Q y+Q (latticeVector m)-t • N y=(Q y-t • N y)+Q (latticeVector m) by abel]
      change quotientMap ((Q y-t • N y)+sibling_axialProjection (EuclideanSpace.single i 1) (latticeVector m))=_
      rw [coordinate_axialProjection_lattice,quotientMap_add,quotientMap_latticeVector,add_zero]
    have he : F b=F a := periodic_local_constant_on_preconnected hFp hc
      (fun y hy ↦ (hloc y hy).mono fun w hw hmem ↦ congrArg quotientMap (hw.2 hmem)) hb ha
    obtain ⟨m,hm⟩ := same_quotient_lattice he
    change Q b-t • N b=c+latticeVector m at hm
    have hmq := congrArg Q hm
    dsimp only [Q] at hmq
    rw [map_sub,map_smul,sibling_axialProjection_idempotent hv,
      axialProjection_fixed (hz b hb),map_add,hQc] at hmq
    let w := b-latticeVector m
    have hwc : Q w-c=t • N b := by
      dsimp only [w]
      rw [map_sub]
      linear_combination (norm := module) hmq
    have hw : w∈axialCylinder v c |t| := by
      change ‖Q w-c‖=|t|
      rw [hwc,norm_smul,Real.norm_eq_abs,hu b hb,mul_one]
    refine ⟨w,hw,?_⟩
    simp only [w,quotientMap_sub,quotientMap_latticeVector,sub_zero,b,quotientMap_representative]
  · rintro x ⟨b,hb,rfl⟩
    exact (hfull b hb).1

lemma isMinimizerAt_zero_component_multiplier_ne_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0) : H≠0 := by
  have hμO := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμO
  have hae' : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      ∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1 := by
    filter_upwards [hae,hbd] with z hn hm
    exact ⟨hn,(hb z.1 hm).1⟩
  have hpos := isMinimizerAt_connected_curvature_integral_pos hV hE hmin hc hμ hN hp hae'
  intro hzero
  have he : (∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
      ∂(μ : Measure NormalBundle))=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hbd] with z hzm
    rw [isMinimizerAt_zero_component_curvature hV hE hmin hμ hN hp hae hb hv hz hzm,hzero,zero_pow (by decide : 2≠0)]
    rfl
  exact hpos.ne' he

theorem isMinimizerAt_zero_axis_cylindrical_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (i : Fin 3)
    (hz : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → N x i=0) :
    0 < |H⁻¹| ∧ |H⁻¹| < 1/2 ∧ ∃ c : Cover,
      sibling_axialProjection (EuclideanSpace.single i 1) c=c ∧
      frontier (openRepresentative E)=quotientMap '' axialCylinder (EuclideanSpace.single i 1) c |H⁻¹| := by
  have hv : ‖(EuclideanSpace.single i 1 : Cover)‖=1 := by simp
  have hzi : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ⟪(EuclideanSpace.single i 1 : Cover),N x⟫=0 := by
    intro x hx
    simpa [EuclideanSpace.inner_single_left] using hz x hx
  have hH := isMinimizerAt_zero_component_multiplier_ne_zero hV hE hmin hc hμ hN hp hae hb hv hzi
  have hmpos : 0<(μ : Measure NormalBundle).real univ := by
    rw [Measure.real,←FiniteMeasure.ennreal_mass]
    change 0<(μ.mass : ℝ)
    rw [hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne
  have : NeZero (μ : Measure NormalBundle) := ⟨by intro hz; simp [hz,Measure.real] at hmpos⟩
  have hμO := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  obtain ⟨z,hzb⟩ := (normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμO).exists
  let x := quotientMap z.1
  have hx : x∈frontier (openRepresentative E) := hzb
  let a := representative x
  have ha : quotientMap a∈frontier (openRepresentative E) := by
    simpa only [a,quotientMap_representative] using hx
  obtain ⟨hr,he⟩ := periodic_connected_coordinate_cylindrical_boundary isClosed_frontier hc
    hN.continuous hp i (fun x hx ↦ (hb x hx).1.self_of_nhds) hzi
    (fun a ha ↦ isMinimizerAt_zero_component_local_cylinder hV hE hmin hμ hN hp hae hH hb hv hzi ha) ha
  refine ⟨abs_pos.mpr (inv_ne_zero hH),hr,_,?_,he⟩
  rw [map_sub,map_smul,sibling_axialProjection_idempotent hv,axialProjection_fixed (hzi a ha)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def transverseTorus (i : Fin 3) (x : Torus) : Torus :=
  WithLp.toLp 2 (fun j ↦ if j=i then 0 else x j)

@[simp] lemma transverseTorus_apply (i j : Fin 3) (x : Torus) :
    transverseTorus i x j=if j=i then 0 else x j := rfl

lemma continuous_transverseTorus (i : Fin 3) : Continuous (transverseTorus i) := by
  apply (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ AddCircle (1 : ℝ))).continuous_symm.comp
  apply continuous_pi
  intro j
  by_cases h : j=i
  · simp only [h,ite_true]; fun_prop
  · simp only [h,ite_false]; fun_prop

@[simp] lemma coordinate_axialProjection_apply (i j : Fin 3) (x : Cover) :
    sibling_axialProjection (EuclideanSpace.single i 1) x j=if j=i then 0 else x j := by
  simp only [sibling_axialProjection_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.inner_single_left,PiLp.single_apply]
  by_cases h : j=i
  · subst j; simp
  · simp [h]

lemma transverseTorus_quotientMap (i : Fin 3) (x : Cover) :
    transverseTorus i (quotientMap x)=quotientMap (sibling_axialProjection (EuclideanSpace.single i 1) x) := by
  ext j
  simp only [transverseTorus_apply,quotientMap,coordinate_axialProjection_apply]
  by_cases h : j=i <;> simp [h]

lemma transverseTorus_add (i : Fin 3) (x y : Torus) :
    transverseTorus i (x+y)=transverseTorus i x+transverseTorus i y := by
  ext j; by_cases h : j=i <;> simp [h]

lemma transverseTorus_sub (i : Fin 3) (x y : Torus) :
    transverseTorus i (x-y)=transverseTorus i x-transverseTorus i y := by
  ext j; by_cases h : j=i <;> simp [h]

lemma norm_transverseTorus_shortestLift (i : Fin 3) (x : Torus) :
    ‖transverseTorus i x‖=‖sibling_axialProjection (EuclideanSpace.single i 1) (shortestLift x)‖ := by
  conv_lhs => rw [←quotientMap_shortestLift x,transverseTorus_quotientMap]
  rw [norm_quotientMap_eq_of_half_cube]
  intro j
  rw [coordinate_axialProjection_apply]
  split_ifs
  · norm_num
  · exact shortestLift_half_cube x j

lemma quotientMap_image_coordinate_cylinder (i : Fin 3) {c : Cover}
    (hc : sibling_axialProjection (EuclideanSpace.single i 1) c=c) {r : ℝ} (hr : r≤1/2) :
    quotientMap '' axialCylinder (EuclideanSpace.single i 1) c r=
      {x : Torus | ‖transverseTorus i (x-quotientMap c)‖=r} := by
  let Q := sibling_axialProjection (EuclideanSpace.single i 1)
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change ‖transverseTorus i (quotientMap z-quotientMap c)‖=r
    rw [←quotientMap_sub,transverseTorus_quotientMap,map_sub,hc]
    rw [norm_quotientMap_eq_of_half_cube]
    · exact hz
    · intro j
      have hn : ‖Q z-c‖=r := hz
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (Q z-c) j).trans (hn.le.trans hr)
  · intro hx
    let w := shortestLift (x-quotientMap c)
    refine ⟨w+c,?_,?_⟩
    · change ‖Q (w+c)-c‖=r
      rw [map_add,hc,add_sub_cancel_right]
      rw [←norm_transverseTorus_shortestLift]
      exact hx
    · simp only [w,quotientMap_add,quotientMap_shortestLift,sub_add_cancel]

lemma torus_solid_cylinder_preconnected (i : Fin 3) (r : ℝ) :
    IsPreconnected {x : Torus | ‖transverseTorus i x‖<r} := by
  let Q := sibling_axialProjection (EuclideanSpace.single i 1)
  let S : Set Cover := Q ⁻¹' Metric.ball 0 r
  have hS : Convex ℝ S := (convex_ball (0 : Cover) r).linear_preimage Q.toLinearMap
  have he : quotientMap '' S={x : Torus | ‖transverseTorus i x‖<r} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      rw [mem_ofPred_eq,transverseTorus_quotientMap]
      exact (norm_quotientMap_le (Q z)).trans_lt (by simpa only [S,mem_preimage,Metric.mem_ball,dist_zero_right] using hz)
    · intro hx
      refine ⟨shortestLift x,?_,quotientMap_shortestLift x⟩
      change dist (Q (shortestLift x)) 0<r
      rw [dist_zero_right,←norm_transverseTorus_shortestLift]
      exact hx
  rw [←he]
  exact hS.isPreconnected.image _ continuous_quotientMap.continuousOn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem torus_cylinder_exterior_preconnected (i : Fin 3) {r : ℝ}
    (hr0 : 0≤r) (hr : r<1/2) :
    IsPreconnected {x : Torus | r<‖transverseTorus i x‖} := by
  let v : Cover := EuclideanSpace.single i 1
  let Q := sibling_axialProjection v
  have hv : ‖v‖=1 := by simp [v]
  let S := axialCylinder v 0 (1/2)
  let T : Set Torus := quotientMap '' S
  have hSc : IsPreconnected S := axialCylinder_preconnected hv (by simp) (1/2)
  have hTc : IsPreconnected T := hSc.image _ continuous_quotientMap.continuousOn
  have hTS : T⊆{x : Torus | r<‖transverseTorus i x‖} := by
    rintro x ⟨z,hz,rfl⟩
    change r<‖transverseTorus i (quotientMap z)‖
    rw [transverseTorus_quotientMap,norm_quotientMap_eq_of_half_cube]
    · have he : ‖Q z‖=1/2 := by simpa only [S,axialCylinder,mem_ofPred_eq,sub_zero] using hz
      exact hr.trans_le he.ge
    · intro j
      have he : ‖Q z‖=1/2 := by simpa only [S,axialCylinder,mem_ofPred_eq,sub_zero] using hz
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (Q z) j).trans he.le
  obtain ⟨j,hji⟩ : ∃ j : Fin 3,j≠i := by fin_cases i <;> decide
  let z₀ : Cover := EuclideanSpace.single j (1/2)
  have hz₀ : z₀∈S := by
    change ‖Q z₀-0‖=1/2
    have hzq : Q z₀=z₀ := axialProjection_fixed (by
      simp [v,z₀,EuclideanSpace.inner_single_left,Ne.symm hji])
    rw [hzq,sub_zero]
    simp [z₀]
  apply isPreconnected_of_forall (quotientMap z₀)
  intro x hx
  change r<‖transverseTorus i x‖ at hx
  let z := shortestLift x
  let q := Q z
  have hq : r<‖q‖ := by simpa only [q,Q,v,z,←norm_transverseTorus_shortestLift] using hx
  have hz : 0<‖q‖ := hr0.trans_lt hq
  let k : ℝ := (1/2)/‖q‖
  let w : Cover := z-q+k • q
  have hk : 0<k := div_pos (by norm_num) hz
  have hQw : Q w=k • q := by
    dsimp only [w,q]
    rw [map_add,map_sub,map_smul,sibling_axialProjection_idempotent hv,sub_self,zero_add]
  have hw : ‖Q w‖=1/2 := by
    rw [hQw,norm_smul,Real.norm_of_nonneg hk.le]
    dsimp only [k]
    field_simp
  have hwS : w∈S := by simpa only [S,axialCylinder,mem_ofPred_eq,sub_zero] using hw
  let f : ℝ → Torus := fun t ↦ quotientMap (z-q+((1-t)+t*k) • q)
  have hf : Continuous f := continuous_quotientMap.comp
    (continuous_const.add ((continuous_const.sub continuous_id |>.add
      (continuous_id.mul continuous_const)).smul continuous_const))
  have hf0 : f 0=x := by simp [f,z,quotientMap_shortestLift]
  have hf1 : f 1=quotientMap w := by simp [f,w]
  have hfS : f '' Icc 0 1 ⊆ {x : Torus | r<‖transverseTorus i x‖} := by
    rintro y ⟨t,ht,rfl⟩
    have ht0 : 0≤1-t := sub_nonneg.mpr ht.2
    have ha : 0≤(1-t)+t*k := add_nonneg ht0 (mul_nonneg ht.1 hk.le)
    have hQ : Q (z-q+((1-t)+t*k) • q)=((1-t)+t*k) • q := by
      dsimp only [q]
      rw [map_add,map_sub,map_smul,sibling_axialProjection_idempotent hv,sub_self,zero_add]
    have hc : ∀ j,|(((1-t)+t*k) • q) j|≤1/2 := by
      intro j
      have hqj : |q j|≤1/2 := by
        dsimp only [q,Q,v]
        rw [coordinate_axialProjection_apply]
        split_ifs
        · norm_num
        · exact shortestLift_half_cube x j
      have hwj : |(k • q) j|≤1/2 := by
        simpa only [hQw,Real.norm_eq_abs] using (PiLp.norm_apply_le (Q w) j).trans hw.le
      have he : (((1-t)+t*k) • q) j=(1-t)*q j+t*(k • q) j := by
        simp only [PiLp.smul_apply,smul_eq_mul]; ring
      rw [he]
      calc
        _≤|(1-t)*q j|+|t*(k • q) j| := abs_add_le _ _
        _=(1-t)*|q j|+t*|(k • q) j| := by rw [abs_mul,abs_mul,abs_of_nonneg ht0,abs_of_nonneg ht.1]
        _≤(1-t)*(1/2)+t*(1/2) := add_le_add (mul_le_mul_of_nonneg_left hqj ht0) (mul_le_mul_of_nonneg_left hwj ht.1)
        _=1/2 := by ring
    change r<‖transverseTorus i (quotientMap (z-q+((1-t)+t*k) • q))‖
    rw [transverseTorus_quotientMap,hQ,norm_quotientMap_eq_of_half_cube hc,
      norm_smul,Real.norm_of_nonneg ha]
    have hkq : k*‖q‖=1/2 := by dsimp only [k]; field_simp
    have hnonneg := mul_nonneg ht.1 (sub_nonneg.mpr hr.le)
    have hpos : 0<(1-t)*(‖q‖-r)+t*((1/2)-r) := by
      by_cases ht1 : t=1
      · simpa only [ht1,sub_self,zero_mul,one_mul,zero_add] using sub_pos.mpr hr
      · have htp : 0<1-t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
        exact add_pos_of_pos_of_nonneg (mul_pos htp (sub_pos.mpr hq)) hnonneg
    nlinarith
  refine ⟨T∪f '' Icc 0 1,union_subset hTS hfS,Or.inl ⟨z₀,hz₀,rfl⟩,
    Or.inr ⟨0,by norm_num,hf0⟩,?_⟩
  exact hTc.union (quotientMap w) ⟨w,hwS,rfl⟩ ⟨1,by norm_num,hf1⟩
    (isPreconnected_Icc.image _ hf.continuousOn)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_two_connected_phases {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {B D : Set Torus} (hBc : IsPreconnected B) (hDc : IsPreconnected D)
    (hBa : Disjoint B (frontier (openRepresentative E)))
    (hDa : Disjoint D (frontier (openRepresentative E)))
    (hpart : ∀ᵐ x ∂torusVolume,x∈B ∨ x∈D) :
    E =ᵐ[torusVolume] B ∨ E =ᵐ[torusVolume] Bᶜ := by
  let U := openRepresentative E
  have hB := preconnected_avoiding_frontier (isOpen_openRepresentative E) hBc hBa
  have hD := preconnected_avoiding_frontier (isOpen_openRepresentative E) hDc hDa
  have hEU := (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hne0 : ¬E =ᵐ[torusVolume] (∅ : Set Torus) := by
    intro h
    have hz := measure_congr h
    rw [measure_empty,hmin.2.1] at hz
    exact (ENNReal.ofReal_pos.mpr hV.1).ne' hz
  have hne1 : ¬E =ᵐ[torusVolume] (univ : Set Torus) := by
    intro h
    have ho := measure_congr h
    rw [torusVolume_univ,hmin.2.1] at ho
    have hv := congrArg ENNReal.toReal ho
    rw [ENNReal.toReal_ofReal hV.1.le,ENNReal.toReal_one] at hv
    linarith [hV.2]
  rcases hB with hB|hB <;> rcases hD with hD|hD
  · exfalso; apply hne1
    filter_upwards [hEU,hpart] with x hxu hx
    apply propext
    simp only [mem_univ,iff_true]
    exact hxu.mpr (hx.elim (fun hb ↦ hB hb) (fun hd ↦ hD hd))
  · left
    filter_upwards [hEU,hpart] with x hxu hx
    apply propext
    exact (Iff.of_eq hxu).trans ⟨fun hu ↦ hx.resolve_right (fun hd ↦ hD hd hu),fun hb ↦ hB hb⟩
  · right
    filter_upwards [hEU,hpart] with x hxu hx
    apply propext
    exact (Iff.of_eq hxu).trans ⟨fun hu hb ↦ hB hb hu,fun hb ↦ hD (hx.resolve_left hb)⟩
  · exfalso; apply hne0
    filter_upwards [hEU,hpart] with x hxu hx
    apply propext
    simp only [mem_empty_iff_false,iff_false]
    exact fun he ↦ hx.elim (fun hb ↦ hB hb (hxu.mp he)) (fun hd ↦ hD hd (hxu.mp he))

lemma torus_preconnected_sub_preimage {S : Set Torus} (hS : IsPreconnected S) (a : Torus) :
    IsPreconnected ((fun x : Torus ↦ x-a) ⁻¹' S) := by
  have he : (fun x : Torus ↦ x+a) '' S=(fun x : Torus ↦ x-a) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; simpa only [mem_preimage,add_sub_cancel_right] using hy
    · intro hx; exact ⟨x-a,hx,sub_add_cancel _ _⟩
  rw [←he]
  exact hS.image _ (continuous_id.add continuous_const).continuousOn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateTube (i : Fin 3) (a : Torus) (r : ℝ) : Set Torus :=
  {x | ‖transverseTorus i (x-a)‖<r}

lemma isOpen_coordinateTube (i : Fin 3) (a : Torus) (r : ℝ) :
    IsOpen (coordinateTube i a r) :=
  isOpen_lt (((continuous_transverseTorus i).comp (continuous_id.sub continuous_const)).norm) continuous_const

theorem isMinimizerAt_coordinate_cylinder_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) {c : Cover} (hc : sibling_axialProjection (EuclideanSpace.single i 1) c=c)
    {r : ℝ} (hr0 : 0≤r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' axialCylinder (EuclideanSpace.single i 1) c r) :
    E =ᵐ[torusVolume] coordinateTube i (quotientMap c) r ∨
      E =ᵐ[torusVolume] (coordinateTube i (quotientMap c) r)ᶜ := by
  let D : Set Torus := {x | r<‖transverseTorus i (x-quotientMap c)‖}
  have hbd' : frontier (openRepresentative E)={x | ‖transverseTorus i (x-quotientMap c)‖=r} :=
    hbd.trans (quotientMap_image_coordinate_cylinder i hc hr.le)
  apply isMinimizerAt_two_connected_phases hV hE hmin
    (torus_preconnected_sub_preimage (torus_solid_cylinder_preconnected i r) (quotientMap c))
    (torus_preconnected_sub_preimage (torus_cylinder_exterior_preconnected i hr0 hr) (quotientMap c))
  · rw [hbd']
    exact disjoint_left.mpr fun x hx hz ↦ (ne_of_lt hx) hz
  · rw [hbd']
    exact disjoint_left.mpr fun x hx hz ↦ (ne_of_gt hx) hz
  · have hnot : ∀ᵐ x ∂torusVolume,x∉frontier (openRepresentative E) := by
      rw [ae_iff]
      simp only [not_not]
      exact isMinimizerAt_volume_frontier_eq_zero hV hE hmin
    filter_upwards [hnot] with x hx
    rw [hbd'] at hx
    exact lt_or_gt_of_ne hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sibling_coverCoordinatePermute (e : Fin 3 ≃ Fin 3) : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm

lemma sibling_coverCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Cover) (i : Fin 3) :
    sibling_coverCoordinatePermute e x i=x (e i) := by
  rfl

lemma sibling_torusCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Torus) (i : Fin 3) :
    torusCoordinatePermute e x i=x (e i) := rfl

lemma coverCoordinatePermute_quotient (e : Fin 3 ≃ Fin 3) (x : Cover) :
    quotientMap (sibling_coverCoordinatePermute e x)=torusCoordinatePermute e (quotientMap x) := by
  ext i
  rfl

def coordinatePermutation (e : Fin 3 ≃ Fin 3) : LatticeIsometry where
  cover := sibling_coverCoordinatePermute e
  torus := torusCoordinatePermute e
  commute := coverCoordinatePermute_quotient e

lemma coverCoordinatePermute_symm (e : Fin 3 ≃ Fin 3) :
    (sibling_coverCoordinatePermute e).symm=sibling_coverCoordinatePermute e.symm := by
  ext x : 1
  apply (sibling_coverCoordinatePermute e).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp only [sibling_coverCoordinatePermute_apply,Equiv.symm_apply_apply]

lemma torusCoordinatePermute_symm (e : Fin 3 ≃ Fin 3) :
    (torusCoordinatePermute e).symm=torusCoordinatePermute e.symm := by
  ext x i
  rfl

theorem isMinimizerAt_coordinatePermutation {V : ℝ} {E : Set Torus}
    (hE : IsMinimizerAt V E) (e : Fin 3 ≃ Fin 3) :
    IsMinimizerAt V (torusCoordinatePermute e ⁻¹' E) :=
  (coordinatePermutation e).isMinimizerAt hE

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma transverseTorus_permute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (x : Torus) :
    transverseTorus i (torusCoordinatePermute e x)=torusCoordinatePermute e (transverseTorus (e i) x) := by
  ext j
  simp only [transverseTorus_apply,sibling_torusCoordinatePermute_apply,Equiv.apply_eq_iff_eq]

lemma norm_transverseTorus_zero_sq (x : Torus) :
    ‖transverseTorus 0 x‖^2=‖x 1‖^2+‖x 2‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_three]

lemma coordinateTube_zero_eq {r : ℝ} (hr : 0≤r) :
    coordinateTube 0 0 r=UpperComparison.centeredTube r := by
  ext x
  change ‖transverseTorus 0 (x-0)‖<r ↔ ‖x 1‖^2+‖x 2‖^2<r^2
  rw [sub_zero,←norm_transverseTorus_zero_sq,sq_lt_sq₀ (norm_nonneg _) hr]

lemma coordinateTube_eq_permutation_preimage (i : Fin 3) (r : ℝ) :
    coordinateTube i 0 r=torusCoordinatePermute (Equiv.swap 0 i) ⁻¹' coordinateTube 0 0 r := by
  ext x
  change ‖transverseTorus i (x-0)‖<r ↔ ‖transverseTorus 0 (torusCoordinatePermute (Equiv.swap 0 i) x-0)‖<r
  simp only [sub_zero,transverseTorus_permute,Equiv.swap_apply_left]
  have he := (coordinatePermutation (Equiv.swap 0 i)).torus.isometry.dist_eq (transverseTorus i x) 0
  rw [(coordinatePermutation (Equiv.swap 0 i)).map_zero,dist_zero_right,dist_zero_right] at he
  change ‖torusCoordinatePermute (Equiv.swap 0 i) (transverseTorus i x)‖=‖transverseTorus i x‖ at he
  rw [he]

lemma coordinateTube_eq_translate (i : Fin 3) (a : Torus) (r : ℝ) :
    coordinateTube i a r=(fun x : Torus ↦ x+(-a)) ⁻¹' coordinateTube i 0 r := by
  ext x; simp only [coordinateTube,mem_preimage,mem_ofPred_eq,sub_eq_add_neg,neg_zero,add_zero]

lemma coordinateTube_volume (i : Fin 3) (a : Torus) {r : ℝ} (hr0 : 0≤r) (hr : r≤1/2) :
    torusVolume (coordinateTube i a r)=ENNReal.ofReal (Real.pi*r^2) := by
  rw [coordinateTube_eq_translate,volume_translation (isOpen_coordinateTube i 0 r).measurableSet.nullMeasurableSet,
    coordinateTube_eq_permutation_preimage]
  have he := (coordinatePermutation (Equiv.swap 0 i)).measurePreserving.measure_preimage
      (isOpen_coordinateTube 0 0 r).measurableSet.nullMeasurableSet
  change torusVolume (torusCoordinatePermute (Equiv.swap 0 i) ⁻¹' coordinateTube 0 0 r)=torusVolume (coordinateTube 0 0 r) at he
  rw [he,coordinateTube_zero_eq hr0,UpperComparison.volume_centeredTube hr0 hr]

lemma coordinateTube_perimeter (i : Fin 3) (a : Torus) {r : ℝ} (hr0 : 0<r) (hr : r<1/2) :
    perimeter (coordinateTube i a r)=ENNReal.ofReal (2*Real.pi*r) := by
  rw [coordinateTube_eq_translate,perimeter_translation (isOpen_coordinateTube i 0 r).measurableSet.nullMeasurableSet,
    coordinateTube_eq_permutation_preimage]
  have he := (coordinatePermutation (Equiv.swap 0 i)).perimeter_eq
      (isOpen_coordinateTube 0 0 r).measurableSet.nullMeasurableSet
  change perimeter (torusCoordinatePermute (Equiv.swap 0 i) ⁻¹' coordinateTube 0 0 r)=perimeter (coordinateTube 0 0 r) at he
  rw [he,coordinateTube_zero_eq hr0.le,UpperComparison.centeredTube_eq_cubeTube_preimage hr0.le,
    perimeter_translation (UpperComparison.measurableSet_cubeTube r).nullMeasurableSet,
    UpperComparison.perimeter_cubeTube_eq hr0 hr]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma small_minimizer_coordinate_tube_phase {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) (i : Fin 3) {a : Torus} {r : ℝ}
    (hr0 : 0<r) (hr : r<1/2)
    (hph : E =ᵐ[torusVolume] coordinateTube i a r ∨ E =ᵐ[torusVolume] (coordinateTube i a r)ᶜ) :
    E =ᵐ[torusVolume] coordinateTube i a r := by
  rcases hph with h|h
  · exact h
  exfalso
  obtain ⟨F,hF,hFv,hFp⟩ := exists_bounded_competitor (V := V) ⟨hV.1.le,by linarith [hV.2]⟩
  have hP := (hmin.2.2 F hF hFv).trans hFp
  have hpbe : perimeter E=ENNReal.ofReal (2*Real.pi*r) :=
    (perimeter_congr_ae h).trans ((perimeter_compl
      (isOpen_coordinateTube i a r).measurableSet.nullMeasurableSet).trans
      (coordinateTube_perimeter i a hr0 hr))
  rw [hpbe] at hP
  have hP' : 2*Real.pi*r≤2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ)≤2)).mp
    simpa only [ENNReal.ofReal_ofNat] using hP
  have hv := congrArg ENNReal.toReal (measure_congr h)
  have hvb : torusVolume.real (coordinateTube i a r)=Real.pi*r^2 := by
    rw [Measure.real,coordinateTube_volume i a hr0.le hr.le,ENNReal.toReal_ofReal (by positivity)]
  change (torusVolume E).toReal=torusVolume.real (coordinateTube i a r)ᶜ at hv
  rw [hmin.2.1,ENNReal.toReal_ofReal hV.1.le,
    measureReal_compl (isOpen_coordinateTube i a r).measurableSet,hvb,
    Measure.real,torusVolume_univ,ENNReal.toReal_one] at hv
  have hh := mul_le_mul_of_nonneg_right hP' hr0.le
  nlinarith [hV.2]

lemma coordinateTube_isometric_canonical {V : ℝ} (_hV : 0≤V) (i : Fin 3) (a : Torus) :
    ∃ φ : Torus ≃ᵢ Torus,coordinateTube i a (Real.sqrt (V/Real.pi))=φ '' canonicalTube V := by
  let e := torusCoordinatePermute (Equiv.swap 0 i)
  let φ := e.symm.trans (IsometryEquiv.addRight a)
  refine ⟨φ,?_⟩
  rw [coordinateTube_eq_translate,coordinateTube_eq_permutation_preimage,
    coordinateTube_zero_eq (Real.sqrt_nonneg _)]
  change (fun x : Torus ↦ x+(-a)) ⁻¹' (e ⁻¹' canonicalTube V)=φ '' canonicalTube V
  ext x
  constructor
  · intro hx
    refine ⟨e (x+(-a)),hx,?_⟩
    change e.symm (e (x+(-a)))+a=x
    rw [e.symm_apply_apply,neg_add_cancel_right]
  · rintro ⟨y,hy,rfl⟩
    change e ((e.symm y+a)+(-a))∈canonicalTube V
    rw [add_neg_cancel_right,e.apply_symm_apply]
    exact hy

theorem isMinimizerAt_coordinate_cylinder_standard {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) {c : Cover} (hc : sibling_axialProjection (EuclideanSpace.single i 1) c=c)
    {r : ℝ} (hr0 : 0<r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' axialCylinder (EuclideanSpace.single i 1) c r) :
    4*Real.pi/81≤V ∧ V≤1/Real.pi ∧ CongruentAE E (canonicalTube V) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  have hae := small_minimizer_coordinate_tube_phase hV hmin i hr0 hr
    (isMinimizerAt_coordinate_cylinder_phase hV' hE hmin i hc hr0.le hr hbd)
  have hv := congrArg ENNReal.toReal (measure_congr hae)
  rw [hmin.2.1,coordinateTube_volume i (quotientMap c) hr0.le hr.le,
    ENNReal.toReal_ofReal hV.1.le,ENNReal.toReal_ofReal (by positivity)] at hv
  have hPe := (perimeter_congr_ae hae).trans (coordinateTube_perimeter i (quotientMap c) hr0 hr)
  have hP := isMinimizerAt_perimeter_le_candidateProfile hV' hmin
  have hP2 : 2*Real.pi*r≤2 := by
    rw [hPe] at hP
    have hc' : candidateProfile V≤2 := (min_le_right _ _).trans (min_le_right _ _)
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ)≤2)).mp
      (hP.trans (ENNReal.ofReal_le_ofReal hc'))
  obtain ⟨hs0,hs,hsv⟩ := UpperComparison.canonicalBall_radius_properties hV
  let s : ℝ := (3*V/(4*Real.pi))^(1/3 : ℝ)
  have hPb : 2*Real.pi*r≤4*Real.pi*s^2 := by
    rw [hPe] at hP
    have hc' : candidateProfile V≤(36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ) := by
      unfold candidateProfile
      rw [min_eq_left (by linarith [hV.2] : V≤1-V)]
      exact min_le_left _ _
    have hh := hP.trans (ENNReal.ofReal_le_ofReal hc')
    rw [←UpperComparison.ballArea_formula hV.1.le] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hrb : r≤2*s^2 := by nlinarith [Real.pi_pos]
  have hrsq := pow_le_pow_left₀ hr0.le hrb 2
  have hspos : 0<s^3 := by dsimp [s]; positivity
  have hfactor : 0 ≤ s^3*(3*s-1) := by nlinarith [Real.pi_pos]
  have hslo : 1/3 ≤ s := by
    have hh : 0≤3*s-1 := (mul_nonneg_iff_of_pos_left hspos).mp hfactor
    linarith
  refine ⟨?_,?_,?_⟩
  · have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1/3) hslo 3
    have hh := mul_le_mul_of_nonneg_right hcube (show 0≤Real.pi*4/3 by positivity)
    nlinarith [hsv]
  · apply (le_div_iff₀ Real.pi_pos).mpr
    have hh := sq_le_sq₀ (by positivity : 0≤Real.pi*r) (by norm_num : (0 : ℝ)≤1) |>.mpr (by linarith : Real.pi*r≤1)
    nlinarith [hv]
  · obtain ⟨φ,hφ⟩ := coordinateTube_isometric_canonical hV.1.le i (quotientMap c)
    have hrs : r=Real.sqrt (V/Real.pi) := by
      have hsq := Real.sq_sqrt (div_nonneg hV.1.le Real.pi_pos.le)
      have hh : r^2=V/Real.pi := (eq_div_iff Real.pi_pos.ne').mpr (by nlinarith [hv])
      nlinarith [Real.sqrt_nonneg (V/Real.pi)]
    refine ⟨φ,hae.trans ?_⟩
    rw [hrs,hφ]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace LatticeIsometry

end LatticeIsometry
end CubicTorus
end
end
end

end OAI
