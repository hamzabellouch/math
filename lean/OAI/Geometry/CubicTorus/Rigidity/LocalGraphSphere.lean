import Mathlib
import OAI.Geometry.CubicTorus.Estimates.TorusCoordinatePermute

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_graph_sphere_iff {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : Continuous g) (hg0 : g 0=0) {c : Cover} {R : ℝ}
    (hc : ⟪n,c⟫≠0)
    (hs : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n g y∈Metric.sphere c R) :
    ∀ᶠ v in 𝓝 (0 : Cover),
      (normalGraph n g (normalPlaneCoordinates n v)=v ↔ v∈Metric.sphere c R) := by
  have hct : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates n).continuous.tendsto (0 : Cover)
  have hnon : ∀ᶠ v in 𝓝 (0 : Cover),
      ⟪n,v⟫+g (normalPlaneCoordinates n v)-2*⟪n,c⟫≠0 := by
    have ht : ContinuousAt (fun v : Cover ↦ ⟪n,v⟫+g (normalPlaneCoordinates n v)-2*⟪n,c⟫) 0 := by fun_prop
    apply ht.eventually_ne
    simp only [inner_zero_right,map_zero,hg0,zero_add,zero_sub,neg_ne_zero,mul_ne_zero_iff]
    exact ⟨by norm_num,hc⟩
  filter_upwards [hct.eventually hs,hnon] with v hv hnv
  constructor
  · intro he
    rwa [← he]
  · intro hvs
    have he : ‖v-c‖^2-‖normalGraph n g (normalPlaneCoordinates n v)-c‖^2=0 := by
      rw [← dist_eq_norm,← dist_eq_norm,Metric.mem_sphere.mp hvs,Metric.mem_sphere.mp hv,sub_self]
    rw [normal_squared_distance_difference hn,mul_eq_zero] at he
    exact (normalGraph_coordinates_eq_iff hn g v).mpr
      ((sub_eq_zero.mp (he.resolve_right hnv)).symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem closed_spherical_set_contains_sphere {S : Set Cover} (hS : IsClosed S)
    {N : Cover → Cover} (hN : Continuous N) {t : ℝ}
    (hu : ∀ a∈S,‖N a‖=1)
    (hloc : ∀ a∈S,∀ᶠ v in 𝓝 (0 : Cover),
      (a+v∈S ↔ a+v∈Metric.sphere (a-t • N a) |t|) ∧
      (a+v∈S → (a+v)-t • N (a+v)=a-t • N a))
    {a : Cover} (ha : a∈S) (b : Cover) (hb : b∈Metric.sphere (a-t • N a) |t|) :
    b∈S ∧ b-t • N b=a-t • N a := by
  let c := a-t • N a
  let P : Set Cover := Metric.sphere c |t|
  have hPc : IsPreconnected P := isPreconnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [Cover,finrank_euclideanSpace_fin]) c |t|
  let : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hPc
  let T : Set P := {x | (x : Cover)∈S ∧ (x : Cover)-t • N x=c}
  have hTc : IsClosed T := (hS.preimage continuous_subtype_val).inter
    (isClosed_eq (continuous_subtype_val.sub ((hN.comp continuous_subtype_val).const_smul t)) continuous_const)
  have hTo : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have ht : Tendsto (fun y : P ↦ (y : Cover)-(x : Cover)) (𝓝 x) (𝓝 (0 : Cover)) := by
      have hc : Continuous (fun y : P ↦ (y : Cover)-(x : Cover)) := continuous_subtype_val.sub continuous_const
      simpa only [sub_self] using hc.tendsto x
    filter_upwards [ht.eventually (hloc x hx.1)] with y hy
    have hadd : (x : Cover)+((y : Cover)-(x : Cover))=(y : Cover) := by abel
    have hys : (y : Cover)∈S := by
      have hyiff : (y : Cover)∈S ↔ (y : Cover)∈Metric.sphere ((x : Cover)-t • N x) |t| := by
        simpa only [hadd] using hy.1
      apply hyiff.mpr
      rw [hx.2]
      exact y.property
    change (y : Cover)∈S ∧ (y : Cover)-t • N y=c
    refine ⟨hys,?_⟩
    have he := hy.2 (by simpa only [hadd] using hys)
    simpa only [hadd,hx.2] using he
  have haP : a∈P := by
    change dist a (a-t • N a)=|t|
    rw [dist_eq_norm,sub_sub_cancel,norm_smul,hu a ha,mul_one,Real.norm_eq_abs]
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

lemma norm_quotientMap_eq_of_half_cube {z : Cover} (hz : ∀ i,|z i|≤1/2) :
    ‖quotientMap z‖=‖z‖ := by
  rw [PiLp.norm_eq_of_L2,PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ‖(z i : AddCircle (1 : ℝ))‖^2=‖z i‖^2
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num : (1 : ℝ)≠0)).mpr
    (by simpa using hz i),Real.norm_eq_abs]

lemma shortestLift_half_cube (x : Torus) (i : Fin 3) : |shortestLift x i|≤1/2 := by
  have h := UpperComparison.representative_mem_cube (x+quotientMap cubeCenter) i
  change |representative (x+quotientMap cubeCenter) i-(1/2)|≤1/2
  exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

theorem smallBall_exterior_preconnected {r : ℝ} (hr0 : 0≤r) (hr : r<1/2) :
    IsPreconnected {x : Torus | r<‖x‖} := by
  let S : Set Cover := Metric.sphere 0 (1/2)
  let T : Set Torus := quotientMap '' S
  have hS : IsPreconnected S := isPreconnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num [Cover,finrank_euclideanSpace_fin]) 0 (1/2)
  have hT : IsPreconnected T := hS.image _ continuous_quotientMap.continuousOn
  have hTS : T⊆{x : Torus | r<‖x‖} := by
    rintro x ⟨z,hz,rfl⟩
    have hn : ‖z‖=1/2 := by simpa only [Metric.mem_sphere,dist_zero_right] using (show z∈Metric.sphere 0 (1/2) from hz)
    change r<‖quotientMap z‖
    rw [norm_quotientMap_eq_of_half_cube (fun i ↦ by
      simpa only [Real.norm_eq_abs,hn] using (PiLp.norm_apply_le z i))]
    simpa only [hn] using hr
  obtain ⟨z₀,hz₀⟩ := (NormedSpace.sphere_nonempty (x := (0 : Cover))).mpr (by norm_num : (0 : ℝ)≤1/2)
  apply isPreconnected_of_forall (quotientMap z₀)
  intro x hx
  change r<‖x‖ at hx
  have hx0 : x≠0 := by intro h; simp only [h,norm_zero] at hx; exact (not_lt_of_ge hr0) hx
  let z := shortestLift x
  have hz : 0<‖z‖ := by rw [norm_shortestLift]; exact norm_pos_iff.mpr hx0
  let k : ℝ := (1/2)/‖z‖
  let w : Cover := k • z
  have hk : 0<k := div_pos (by norm_num) hz
  have hw : ‖w‖=1/2 := by
    dsimp [w]; rw [norm_smul,Real.norm_of_nonneg hk.le]; dsimp [k]; field_simp
  have hwS : w∈S := by simpa only [S,Metric.mem_sphere,dist_zero_right] using hw
  let f : ℝ → Torus := fun t ↦ quotientMap (((1-t)+t*k) • z)
  have hf : Continuous f := continuous_quotientMap.comp
    ((continuous_const.sub continuous_id |>.add (continuous_id.mul continuous_const)).smul continuous_const)
  have hf0 : f 0=x := by simp [f,z,quotientMap_shortestLift]
  have hf1 : f 1=quotientMap w := by simp [f,w]
  have hfS : f '' Icc 0 1 ⊆ {x : Torus | r<‖x‖} := by
    rintro y ⟨t,ht,rfl⟩
    have ht0 : 0≤1-t := sub_nonneg.mpr ht.2
    have ha : 0≤(1-t)+t*k := add_nonneg ht0 (mul_nonneg ht.1 hk.le)
    have hc : ∀ i,|(((1-t)+t*k) • z) i|≤1/2 := by
      intro i
      have hzi := shortestLift_half_cube x i
      have hwi : |w i|≤1/2 := by simpa only [Real.norm_eq_abs,hw] using PiLp.norm_apply_le w i
      have he : (((1-t)+t*k) • z) i=(1-t)*z i+t*w i := by simp only [w,PiLp.smul_apply,smul_eq_mul]; ring
      rw [he]
      calc
        _≤|(1-t)*z i|+|t*w i| := abs_add_le _ _
        _=(1-t)*|z i|+t*|w i| := by rw [abs_mul,abs_mul,abs_of_nonneg ht0,abs_of_nonneg ht.1]
        _≤(1-t)*(1/2)+t*(1/2) := add_le_add (mul_le_mul_of_nonneg_left hzi ht0) (mul_le_mul_of_nonneg_left hwi ht.1)
        _=1/2 := by ring
    change r<‖quotientMap (((1-t)+t*k) • z)‖
    rw [norm_quotientMap_eq_of_half_cube hc,norm_smul,Real.norm_of_nonneg ha]
    have hkz : k*‖z‖=1/2 := by dsimp [k]; field_simp
    have hxz : r<‖z‖ := by simpa only [z,norm_shortestLift] using hx
    have hh := mul_nonneg ht0 (sub_nonneg.mpr hxz.le)
    have hh' := mul_nonneg ht.1 (sub_nonneg.mpr hr.le)
    have hh'' : 0<(1-t)*(‖z‖-r)+t*((1/2)-r) := by
      by_cases ht1 : t=1
      · simpa only [ht1,sub_self,zero_mul,one_mul,zero_add] using sub_pos.mpr hr
      · have htp : 0<1-t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
        exact add_pos_of_pos_of_nonneg (mul_pos htp (sub_pos.mpr hxz)) hh'
    nlinarith
  refine ⟨T∪f '' Icc 0 1,union_subset hTS hfS,Or.inl ⟨z₀,hz₀,rfl⟩,
    Or.inr ⟨0,by norm_num,hf0⟩,?_⟩
  exact hT.union (quotientMap w) ⟨w,hwS,rfl⟩ ⟨1,by norm_num,hf1⟩
    (isPreconnected_Icc.image _ hf.continuousOn)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_umbilic_local_sphere {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hH : H≠0)
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hd : ∀ x,quotientMap x∈frontier (openRepresentative E) → divergence N x=H)
    (hq : ∀ x,quotientMap x∈frontier (openRepresentative E) →
      H^2=2*coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)))
    (a : Cover) (ha : quotientMap a∈frontier (openRepresentative E)) :
    ∀ᶠ v in 𝓝 (0 : Cover),
      (quotientMap (a+v)∈frontier (openRepresentative E) ↔
        a+v∈Metric.sphere (a-(2/H) • N a) |2/H|) ∧
      (quotientMap (a+v)∈frontier (openRepresentative E) →
        (a+v)-(2/H) • N (a+v)=a-(2/H) • N a) := by
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm,hcov⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hmin hμ hN hp hae a ha
  have hx0 : normalGraph n f 0=0 := by
    simp only [normalGraph,hf0,zero_smul,add_zero]
    exact norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
  have hNa : N a=σ • graphSlopeNormal n (gradient f 0) := by
    simpa only [hx0,add_zero] using hm.self_of_nhds.1
  have hJ : -σ*H≠0 := by rcases hσ with rfl|rfl <;> simpa using hH
  have hrati : 2/(-σ*H)= -(2/H)*σ := by
    rcases hσ with rfl|rfl <;> simp
    ring
  have habs : |2/(-σ*H)|=|2/H| := by
    rw [hrati,abs_mul,abs_neg]
    rcases hσ with rfl|rfl <;> norm_num
  have hgraph : ∀ᶠ y in 𝓝 (0 : Plane),
      planeDivergence (fun z ↦ cmcFlux (gradient f z)) y= -σ*H ∧
      (-σ*H)^2=2*graphSquaredSecondFundamentalForm f y := by
    filter_upwards [hm,hm.eventually_nhds] with y hy hym
    have hdiv := graph_normal_extension_divergence a hn hf y hσ hN
      (hu _ hy.2) (hym.mono fun z hz ↦ hz.1)
    have hcurv := graph_normal_extension_curvature a hn hf y hσ hN
      (hu _ hy.2) (hym.mono fun z hz ↦ hz.1)
    rw [hd _ hy.2] at hdiv
    have heq := hq _ hy.2
    rw [hcurv] at heq
    rcases hσ with rfl|rfl <;> constructor <;> nlinarith
  obtain ⟨r,hr,hgr⟩ := Metric.mem_nhds_iff.mp hgraph
  have hc := graph_umbilic_CMC_center hn hf hr hJ
    (fun y hy ↦ (hgr hy).1) (fun y hy ↦ (hgr hy).2)
  let c : Cover := (2/(-σ*H)) • graphSlopeNormal n (gradient f 0)
  have hcs : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n f y∈Metric.sphere c |2/H| := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) hr] with y hy
    have he := hc y hy
    rw [hx0,zero_add] at he
    rw [Metric.mem_sphere,dist_eq_norm]
    dsimp only [c]
    rw [← he]
    simp only [sub_add_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,
      graphSlopeNormal_unit hn,mul_one,habs]
  have hcn : ⟪n,c⟫≠0 := by
    have hnN : ⟪n,graphSlopeNormal n (gradient f 0)⟫=(cmcWeight (gradient f 0))⁻¹ := by
      rw [graphSlopeNormal_weight hn,real_inner_smul_right,inner_sub_right,
        real_inner_self_eq_norm_sq,hn,one_pow,normalPlaneEmbedding_inner hn,sub_zero,mul_one]
    change ⟪n,(2/(-σ*H)) • graphSlopeNormal n (gradient f 0)⟫≠0
    rw [real_inner_smul_right,hnN]
    exact mul_ne_zero (div_ne_zero (by norm_num) hJ) (inv_ne_zero (cmcWeight_pos _).ne')
  have hce : c= -(2/H) • N a := by
    rw [hNa,smul_smul]
    change (2/(-σ*H)) • _= _
    rw [hrati]
  have hloc := local_graph_sphere_iff hn hf.continuous hf0 hcn hcs
  have hct : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates n).continuous.tendsto (0 : Cover)
  filter_upwards [hcov,hloc,hct.eventually hm,
    hct.eventually (Metric.ball_mem_nhds (0 : Plane) hr)] with v hv hl hm' hy
  constructor
  · rw [hv,hl,Metric.mem_sphere,Metric.mem_sphere,dist_eq_norm,dist_eq_norm,hce]
    rw [show a+v-(a-(2/H) • N a)=v - -(2/H) • N a by module]
  · intro hb
    have hvg := hv.mp hb
    have he := hc _ hy
    rw [hx0,zero_add,hvg,hrati] at he
    rw [hvg] at hm'
    rw [hm'.1,hNa,smul_smul,smul_smul]
    calc
      _=a+(v+(-(2/H)*σ) • graphSlopeNormal n (gradient f (normalPlaneCoordinates n v))) := by module
      _=a+(-(2/H)*σ) • graphSlopeNormal n (gradient f 0) := by rw [he]
      _=_ := by module

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem periodic_local_constant_on_preconnected {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x)
    {K : Set Torus} (hK : IsPreconnected K)
    (hloc : ∀ a : Cover,quotientMap a∈K →
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (a+v)∈K → F (a+v)=F a)
    {a b : Cover} (ha : quotientMap a∈K) (hb : quotientMap b∈K) : F a=F b := by
  let G : K → Y := fun x ↦ F (representative x)
  have hG : IsLocallyConstant G := by
    apply (IsLocallyConstant.iff_eventually_eq G).mpr
    intro x
    let u := representative (x : Torus)
    have hu : quotientMap u∈K := by simpa only [u,quotientMap_representative] using x.property
    obtain ⟨r,hr,hrr⟩ := Metric.mem_nhds_iff.mp (hloc u hu)
    have hnear : ∀ᶠ y : K in 𝓝 x,(y : Torus)∈Metric.ball (quotientMap u) r := by
      apply continuous_subtype_val.continuousAt.eventually
      simpa only [u,quotientMap_representative] using (show ∀ᶠ y : Torus in 𝓝 (x : Torus), y∈Metric.ball (x : Torus) r from Metric.ball_mem_nhds (x : Torus) hr)
    filter_upwards [hnear] with y hy
    rw [← quotientMap_image_ball u r] at hy
    obtain ⟨w,hw,hwy⟩ := hy
    have hwu : w-u∈Metric.ball (0 : Cover) r := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hw
    have hadd : u+(w-u)=w := by abel
    have he := hrr hwu (by simpa only [hadd,hwy] using y.property)
    rw [hadd] at he
    change F (representative (y : Torus))=F u
    rw [← hwy,periodic_representative hp]
    exact he
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  have he := (⟨G,hG⟩ : LocallyConstant K Y).apply_eq_of_preconnectedSpace (⟨quotientMap a,ha⟩ : K) (⟨quotientMap b,hb⟩ : K)
  change F (representative (quotientMap a))=F (representative (quotientMap b)) at he
  simpa only [periodic_representative hp] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem periodic_complete_sphere_radius_lt_half {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x) {t : ℝ} {c : Cover}
    (hs : ∀ b∈Metric.sphere c |t|,b-t • N b=c) : |t|<1/2 := by
  by_contra! hh
  let m : Fin 3 → ℤ := Pi.single 0 1
  let e : Cover := latticeVector m
  let d : ℝ := Real.sqrt (t^2-1/4)
  have hd : d^2=t^2-1/4 := Real.sq_sqrt (by nlinarith [sq_abs t])
  let w : Cover := EuclideanSpace.single 0 (1/2)+EuclideanSpace.single 1 d
  have he (i : Fin 3) : e i=if i=0 then 1 else 0 := by
    simp [e,m,latticeVector,Pi.single_apply]
  have hw : ‖w‖^2=t^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
    simp only [w,PiLp.add_apply,PiLp.single_apply]
    norm_num [show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide]
    nlinarith [hd]
  have hwe : ‖w-e‖^2=t^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
    simp only [PiLp.sub_apply,he,w,PiLp.add_apply,PiLp.single_apply]
    norm_num [show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide]
    nlinarith [hd]
  have hw' : ‖w‖=|t| := by nlinarith [norm_nonneg w,abs_nonneg t,sq_abs t]
  have hwe' : ‖w-e‖=|t| := by nlinarith [norm_nonneg (w-e),abs_nonneg t,sq_abs t]
  have hb : c+w∈Metric.sphere c |t| := by
    rw [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left,hw']
  have hbe : c+w-e∈Metric.sphere c |t| := by
    rw [Metric.mem_sphere,dist_eq_norm,show c+w-e-c=w-e by abel,hwe']
  have h1 := hs _ hb
  have h2 := hs _ hbe
  have hn : N (c+w-e)=N (c+w) := by
    have hh := hp m (c+w-e)
    change N (c+w-e+e)=N (c+w-e) at hh
    simpa only [sub_add_cancel] using hh.symm
  rw [hn] at h2
  have hz : e=0 := by
    have hsub := congrArg (fun x : Cover ↦ x-(c+w-t • N (c+w))) h2
    have hh : (c+w-e-t • N (c+w))-(c+w-t • N (c+w))= -e := by module
    rw [hh,h1,sub_self,neg_eq_zero] at hsub
    exact hsub
  have he0 := congrArg (fun v : Cover ↦ v 0) hz
  simp [he] at he0

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem periodic_connected_spherical_boundary {K : Set Torus}
    (hK : IsClosed K) (hc : IsPreconnected K)
    {N : Cover → Cover} (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) {t : ℝ}
    (hu : ∀ a : Cover,quotientMap a∈K → ‖N a‖=1)
    (hloc : ∀ a : Cover,quotientMap a∈K → ∀ᶠ v in 𝓝 (0 : Cover),
      (quotientMap (a+v)∈K ↔ a+v∈Metric.sphere (a-t • N a) |t|) ∧
      (quotientMap (a+v)∈K → (a+v)-t • N (a+v)=a-t • N a))
    {a : Cover} (ha : quotientMap a∈K) :
    |t|<1/2 ∧ K=quotientMap '' Metric.sphere (a-t • N a) |t| := by
  let S : Set Cover := quotientMap ⁻¹' K
  have hS : IsClosed S := hK.preimage continuous_quotientMap
  have hfull := closed_spherical_set_contains_sphere hS hN hu hloc ha
  have hr : |t|<1/2 := periodic_complete_sphere_radius_lt_half hp
    (fun b hb ↦ (hfull b hb).2)
  refine ⟨hr,?_⟩
  apply Subset.antisymm
  · intro x hx
    let b := representative x
    have hb : quotientMap b∈K := by simpa only [b,quotientMap_representative] using hx
    let F : Cover → Torus := fun y ↦ quotientMap (y-t • N y)
    have hFp : ∀ m y,F (y+latticeVector m)=F y := by
      intro m y
      simp only [F,hp]
      rw [show y+latticeVector m-t • N y=(y-t • N y)+latticeVector m by abel,
        quotientMap_add,quotientMap_latticeVector,add_zero]
    have he : F b=F a := periodic_local_constant_on_preconnected hFp hc
      (fun y hy ↦ (hloc y hy).mono fun v hv hmem ↦ congrArg quotientMap (hv.2 hmem)) hb ha
    obtain ⟨m,hm⟩ := same_quotient_lattice he
    let w := b-latticeVector m
    have hw : w∈Metric.sphere (a-t • N a) |t| := by
      have hwc : w-(a-t • N a)=t • N b := by
        change b-t • N b=(a-t • N a)+latticeVector m at hm
        dsimp only [w]
        calc
          _=(b-t • N b)-((a-t • N a)+latticeVector m)+t • N b := by module
          _=_ := by rw [hm,sub_self,zero_add]
      rw [Metric.mem_sphere,dist_eq_norm,hwc,norm_smul,hu b hb,Real.norm_eq_abs,mul_one]
    refine ⟨w,hw,?_⟩
    simp only [w,quotientMap_sub,quotientMap_latticeVector,sub_zero,b,quotientMap_representative]
  · rintro x ⟨b,hb,rfl⟩
    exact (hfull b hb).1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_mean_square_equality_spherical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1))
    {H : ℝ} (hH : H≠0)
    (hd : ∀ᵐ z ∂(μ : Measure NormalBundle),divergence N z.1=H)
    (heq : (∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
      ∂(μ : Measure NormalBundle))=H^2*isoperimetricProfile V) :
    0 < |2/H| ∧ |2/H|<1/2 ∧ ∃ c : Cover,
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c |2/H| := by
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hmass : (μ : Measure NormalBundle).real univ=2*isoperimetricProfile V := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)=_
    rw [hμ.1,isoperimetricProfile_eq_of_isMinimizerAt hmin]
    ring
  let q : NormalBundle → ℝ := fun z ↦ coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
  have hqi : Integrable q (μ : Measure NormalBundle) :=
    integrable_normal_base (normal_curvature_continuous hN) μ
  have hnon : ∀ᵐ z ∂(μ : Measure NormalBundle),0≤2*q z-H^2 := by
    filter_upwards [hbd,hae,hd] with z hzb hzu hdz
    have hh := isMinimizerAt_mean_curvature_bound hV hE hmin hμ hN hp
      (hae.mono fun _ h ↦ h.1) z.1 hzb hzu.2
    rw [hdz] at hh
    exact sub_nonneg.mpr hh
  have hint : (∫ z,2*q z-H^2 ∂(μ : Measure NormalBundle))=0 := by
    rw [integral_sub (hqi.const_mul 2) (integrable_const _),integral_const_mul,
      integral_const,smul_eq_mul,hmass]
    change 2*(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
      ∂(μ : Measure NormalBundle))-(2*isoperimetricProfile V)*H^2=0
    rw [heq]; ring
  have hqae := (integral_eq_zero_iff_of_nonneg_ae hnon
    ((hqi.const_mul 2).sub (integrable_const _))).mp hint
  have hunit : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ‖N x‖=1 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hN.continuous.norm
      continuous_const (fun m x ↦ by rw [hp]) (fun _ _ ↦ rfl)
    filter_upwards [hae] with z hzn
    rw [hzn.1,z.2.property]
  let R := regularizedNormal N
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := regularizedNormal_contDiff hN
  have hRp : ∀ m x,R (x+latticeVector m)=R x := regularizedNormal_periodic hp
  have heR : ∀ᵐ z ∂(μ : Measure NormalBundle),R=ᶠ[𝓝 (z.1 : Cover)]N := by
    filter_upwards [hae] with z hzn
    exact regularizedNormal_eventuallyEq hzn.2
  have hRa : ∀ᵐ z ∂(μ : Measure NormalBundle),R z.1=(z.2 : Cover) := by
    filter_upwards [hae,heR] with z hzn hze
    exact hze.eq_of_nhds.trans hzn.1
  have hRu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖R y‖=1 := by
    intro x hx
    exact regularizedNormal_unit_near hN.continuous (by rw [hunit x hx]; norm_num)
  have hRd : ∀ x,quotientMap x∈frontier (openRepresentative E) → divergence R x=H := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (continuous_divergence hR) continuous_const
      (fun m x ↦ divergence_periodic hRp m x) (fun _ _ ↦ rfl)
    filter_upwards [hd,heR] with z hdz hze
    rw [divergence_eq_coverTrace,hze.fderiv_eq,← divergence_eq_coverTrace]
    exact hdz
  have hRq : ∀ x,quotientMap x∈frontier (openRepresentative E) →
      H^2=2*coverTrace ((fderiv ℝ R x).comp (fderiv ℝ R x)) := by
    have hh : ∀ x,quotientMap x∈frontier (openRepresentative E) →
        2*coverTrace ((fderiv ℝ R x).comp (fderiv ℝ R x))=H^2 := by
      apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
        ((normal_curvature_continuous hR).const_mul 2) continuous_const
        (fun m x ↦ by simp only [fderiv_periodic hRp]) (fun _ _ ↦ rfl)
      filter_upwards [hqae,heR] with z hqz hze
      rw [hze.fderiv_eq]
      exact sub_eq_zero.mp hqz
    exact fun x hx ↦ (hh x hx).symm
  have hloc := isMinimizerAt_umbilic_local_sphere hV hE hmin hμ hR hRp hRa hH hRu hRd hRq
  have hmpos : 0<(μ : Measure NormalBundle).real univ := by
    rw [hmass]; exact mul_pos (by norm_num) (isoperimetricProfile_pos hV)
  have : NeZero (μ : Measure NormalBundle) := ⟨by intro hz; simp [hz,Measure.real] at hmpos⟩
  obtain ⟨z,hz⟩ := hbd.exists
  obtain ⟨hr,hset⟩ := periodic_connected_spherical_boundary isClosed_frontier hc
    hR.continuous hRp (fun x hx ↦ (hRu x hx).self_of_nhds) hloc hz
  exact ⟨abs_pos.mpr (div_ne_zero (by norm_num) hH),hr,z.1-(2/H) • R z.1,hset⟩

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus.Reduction

lemma second_deriv_sub_affine {D : ℝ → ℝ} {x a b : ℝ}
    (hD : ContDiffAt ℝ 2 D x) :
    deriv (deriv (fun W ↦ D W-(a*W+b))) x=deriv (deriv D) x := by
  have he : deriv (fun W ↦ D W-(a*W+b)) =ᶠ[𝓝 x] (fun W ↦ deriv D W-a) := by
    filter_upwards [hD.eventually (by norm_num)] with W hW
    change deriv (D-(fun W ↦ a*W+b)) W=deriv D W-a
    rw [deriv_sub (hW.differentiableAt (by norm_num)) (by fun_prop)]
    simp
  rw [he.deriv_eq,deriv_sub_const]

theorem UpperSupport.power_affine_jet_nonneg {I C : ℝ → ℝ} {x a b : ℝ}
    (hs : UpperSupport I C x) (hI : ∀ y,0≤I y) (hp : 0<I x)
    (he : ∀ᶠ y in 𝓝 x,I y^(3/2 : ℝ)=a*y+b) :
    0≤2*C x*deriv (deriv C) x+(deriv C x)^2 := by
  have hCx : 0<C x := hs.contact ▸ hp
  let D : ℝ → ℝ := fun W ↦ C W^(3/2 : ℝ)
  have hD : ContDiffAt ℝ 2 D x := hs.smooth.rpow_const_of_ne hCx.ne'
  have hmin : IsLocalMin (fun W ↦ D W-(a*W+b)) x := by
    have hx := he.self_of_nhds
    filter_upwards [he,hs.above] with W hWe hWa
    change C x^(3/2 : ℝ)-(a*x+b)≤C W^(3/2 : ℝ)-(a*W+b)
    rw [hs.contact,hx,sub_self,← hWe]
    exact sub_nonneg.mpr (Real.rpow_le_rpow (hI W) hWa (by norm_num))
  have hnn := second_deriv_nonneg_of_local_min hmin
    (hD.continuousAt.sub (by fun_prop))
  rw [second_deriv_sub_affine hD] at hnn
  change 0≤deriv (deriv (fun W ↦ C W^(3/2 : ℝ))) x at hnn
  rw [second_deriv_three_halves hs.smooth hCx] at hnn
  have hcoef : 0<(3/4 : ℝ)*C x^(-1/2 : ℝ) := by positivity
  exact (mul_nonneg_iff_of_pos_left hcoef).mp hnn

end CubicTorus.Reduction

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_power_affine_spherical {V : ℝ} (hV : V∈Ioo 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) {a b : ℝ}
    (he : ∀ᶠ W in 𝓝 V,isoperimetricProfile W^(3/2 : ℝ)=a*W+b) :
    ∃ (c : Cover) (r : ℝ),0<r ∧ r<1/2 ∧
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c r := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  obtain ⟨μ,H,N,C,hμ,hN,hp,hn,hCMC,hs,hd,hdd⟩ :=
    isMinimizerAt_exact_profile_hessian hV' hE hmin
  have hH : 0<H := (connected_CMC_strict_sign hV' hE hmin hc hμ hCMC).1 hV.2
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV' hE hmin).symm
  have hdiv := weakCMC_normal_extension hCMC hN hp hn
  have hpoint : ∀ᵐ z ∂(μ : Measure NormalBundle),H^2≤
      2*coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) := by
    filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU,
      hn,hdiv] with z hz hnz hHz
    rw [← hHz]
    exact isMinimizerAt_mean_curvature_bound hV' hE hmin hμ hN hp
      (hn.mono fun _ h ↦ h.1) z.1 hz hnz.2
  have hint := integral_mono_ae (integrable_const (H^2))
    ((integrable_normal_base (normal_curvature_continuous hN) μ).const_mul 2) hpoint
  rw [integral_const,integral_const_mul,smul_eq_mul] at hint
  have hmass : (μ : Measure NormalBundle).real univ=2*isoperimetricProfile V := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)=_
    rw [hμ.1,isoperimetricProfile_eq_of_isMinimizerAt hmin]
    ring
  rw [hmass] at hint
  have hjet := hs.power_affine_jet_nonneg isoperimetricProfile_nonneg
    (isoperimetricProfile_pos hV') he
  rw [hs.contact,hd] at hjet
  have hge := mul_nonneg (isoperimetricProfile_nonneg V) hjet
  have hQ : (∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
      ∂(μ : Measure NormalBundle))=H^2*isoperimetricProfile V := by
    nlinarith [hdd]
  obtain ⟨hr,hr',c,hc'⟩ := isMinimizerAt_mean_square_equality_spherical hV' hE hmin hc
    hμ hN hp hn hH.ne' hdiv hQ
  exact ⟨c,|2/H|,hr,hr',hc'⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotientMap_image_small_sphere (c : Cover) {r : ℝ} (hr : r≤1/2) :
    quotientMap '' Metric.sphere c r=Metric.sphere (quotientMap c) r := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    have he : ‖z-c‖=r := by simpa only [Metric.mem_sphere,dist_eq_norm] using hz
    change dist (quotientMap z) (quotientMap c)=r
    rw [dist_eq_norm,← quotientMap_sub,norm_quotientMap_eq_of_half_cube]
    · exact he
    · intro i
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (z-c) i).trans (he.le.trans hr)
  · intro hx
    refine ⟨shortestLift (x-quotientMap c)+c,?_,?_⟩
    · simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_right,norm_shortestLift] using hx
    · rw [quotientMap_add,quotientMap_shortestLift,sub_add_cancel]

lemma torus_ball_preconnected (c : Torus) (r : ℝ) : IsPreconnected (Metric.ball c r) := by
  rw [← quotientMap_representative c,← quotientMap_image_ball]
  exact (convex_ball (representative c) r).isPreconnected.image _ continuous_quotientMap.continuousOn

lemma torus_smallBall_exterior_preconnected (c : Torus) {r : ℝ} (hr0 : 0≤r) (hr : r<1/2) :
    IsPreconnected {x : Torus | r<dist x c} := by
  have he : (fun x : Torus ↦ x+c) '' {x : Torus | r<‖x‖}={x : Torus | r<dist x c} := by
    ext y
    simp only [mem_image,mem_ofPred_eq]
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa only [dist_eq_norm,add_sub_cancel_right] using hx
    · intro hy
      exact ⟨y-c,by simpa only [dist_eq_norm] using hy,sub_add_cancel _ _⟩
  rw [← he]
  exact (smallBall_exterior_preconnected hr0 hr).image _ (continuous_id.add continuous_const).continuousOn

lemma preconnected_avoiding_frontier {X : Type*} [TopologicalSpace X]
    {U S : Set X} (hU : IsOpen U) (hS : IsPreconnected S) (havoid : Disjoint S (frontier U)) :
    S⊆U ∨ S⊆Uᶜ := by
  have hcov : S⊆U∪(closure U)ᶜ := by
    intro x hx
    by_cases hxu : x∈U
    · exact Or.inl hxu
    · right
      intro hxc
      exact disjoint_left.mp havoid hx (by rw [hU.frontier_eq]; exact ⟨hxc,hxu⟩)
  rcases hS.subset_or_subset hU isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left subset_closure) hcov with h|h
  · exact Or.inl h
  · exact Or.inr (h.trans (compl_subset_compl.mpr subset_closure))

theorem isMinimizerAt_spherical_boundary_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {c : Cover} {r : ℝ} (hr0 : 0<r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' Metric.sphere c r) :
    E =ᵐ[torusVolume] Metric.ball (quotientMap c) r ∨
      E =ᵐ[torusVolume] (Metric.ball (quotientMap c) r)ᶜ := by
  let U := openRepresentative E
  let a := quotientMap c
  let B := Metric.ball a r
  let D := {x : Torus | r<dist x a}
  have hbd' : frontier U=Metric.sphere a r := hbd.trans (quotientMap_image_small_sphere c hr.le)
  have hBa : Disjoint B (frontier U) := by
    rw [hbd']; exact disjoint_left.mpr fun x hx hz ↦ (ne_of_lt hx) hz
  have hDa : Disjoint D (frontier U) := by
    rw [hbd']; exact disjoint_left.mpr fun x hx hz ↦ (ne_of_gt hx) hz
  have hB := preconnected_avoiding_frontier (isOpen_openRepresentative E)
    (torus_ball_preconnected a r) hBa
  have hD := preconnected_avoiding_frontier (isOpen_openRepresentative E)
    (torus_smallBall_exterior_preconnected a hr0.le hr) hDa
  have hnot : ∀ᵐ x ∂torusVolume,x∉frontier U := by
    rw [ae_iff]
    simp only [not_not]
    change torusVolume (frontier U)=0
    exact isMinimizerAt_volume_frontier_eq_zero hV hE hmin
  have hpart : ∀ᵐ x ∂torusVolume,x∈B ∨ x∈D := by
    filter_upwards [hnot] with x hx
    rw [hbd'] at hx
    exact lt_or_gt_of_ne hx
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
    change (x∈E)=(x∈B)
    apply propext
    exact (Iff.of_eq hxu).trans ⟨fun hu ↦ hx.resolve_right (fun hd ↦ hD hd hu),fun hb ↦ hB hb⟩
  · right
    filter_upwards [hEU,hpart] with x hxu hx
    change (x∈E)=(x∈Bᶜ)
    apply propext
    exact (Iff.of_eq hxu).trans ⟨fun hu hb ↦ hB hb hu,fun hb ↦ hD (hx.resolve_left hb)⟩
  · exfalso; apply hne0
    filter_upwards [hEU,hpart] with x hxu hx
    apply propext
    simp only [mem_empty_iff_false,iff_false]
    exact fun he ↦ hx.elim (fun hb ↦ hB hb (hxu.mp he)) (fun hd ↦ hD hd (hxu.mp he))

theorem Periodic.isMinimizerAt_power_affine_ball_or_complement {V : ℝ}
    (hV : V∈Ioo 0 (1/2)) {E : Set Torus} (hE : MeasurableSet E)
    (hmin : IsMinimizerAt V E) (hc : IsPreconnected (frontier (openRepresentative E)))
    {a b : ℝ} (he : ∀ᶠ W in 𝓝 V,isoperimetricProfile W^(3/2 : ℝ)=a*W+b) :
    ∃ c : Torus,∃ r : ℝ,0<r ∧ r<1/2 ∧
      (E =ᵐ[torusVolume] Metric.ball c r ∨ E =ᵐ[torusVolume] (Metric.ball c r)ᶜ) := by
  obtain ⟨c,r,hr,hr',hbd⟩ := isMinimizerAt_power_affine_spherical hV hE hmin hc he
  exact ⟨quotientMap c,r,hr,hr',isMinimizerAt_spherical_boundary_phase
    ⟨hV.1,by linarith [hV.2]⟩ hE hmin hr hr' hbd⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma metricBall_eq_translate (c : Torus) (r : ℝ) :
    Metric.ball c r=(fun x : Torus ↦ x+(-c)) ⁻¹' Metric.ball 0 r := by
  ext x
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,sub_zero,← sub_eq_add_neg]

lemma metricBall_volume (c : Torus) {r : ℝ} (hr0 : 0≤r) (hr : r≤1/2) :
    torusVolume (Metric.ball c r)=ENNReal.ofReal (r^3*(Real.pi*4/3)) := by
  rw [metricBall_eq_translate,volume_translation Metric.isOpen_ball.measurableSet.nullMeasurableSet,
    UpperComparison.volume_centeredBall hr0 hr]

lemma metricBall_perimeter (c : Torus) {r : ℝ} (hr0 : 0<r) (hr : r<1/2) :
    perimeter (Metric.ball c r)=ENNReal.ofReal (4*Real.pi*r^2) := by
  rw [metricBall_eq_translate,perimeter_translation Metric.isOpen_ball.measurableSet.nullMeasurableSet,
    UpperComparison.centeredBall_eq_cubeBall_preimage,
    perimeter_translation (UpperComparison.measurableSet_cubeBall r).nullMeasurableSet]
  exact perimeter_cubeBall_eq hr0 hr

lemma small_minimizer_ball_phase {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) {c : Torus} {r : ℝ}
    (hr0 : 0<r) (hr : r<1/2)
    (hph : E =ᵐ[torusVolume] Metric.ball c r ∨ E =ᵐ[torusVolume] (Metric.ball c r)ᶜ) :
    E =ᵐ[torusVolume] Metric.ball c r := by
  rcases hph with h|h
  · exact h
  exfalso
  obtain ⟨F,hF,hFv,hFp⟩ := exists_bounded_competitor (V := V) ⟨hV.1.le,by linarith [hV.2]⟩
  have hP := (hmin.2.2 F hF hFv).trans hFp
  have hpbe : perimeter E=ENNReal.ofReal (4*Real.pi*r^2) :=
    (perimeter_congr_ae h).trans ((perimeter_compl
      (Metric.isOpen_ball.measurableSet.nullMeasurableSet : NullMeasurableSet (Metric.ball c r) torusVolume)).trans
      (metricBall_perimeter c hr0 hr))
  rw [hpbe] at hP
  have hP' : 4*Real.pi*r^2≤2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ)≤2)).mp
    simpa only [ENNReal.ofReal_ofNat] using hP
  have hv := congrArg ENNReal.toReal (measure_congr h)
  have hvb : torusVolume.real (Metric.ball c r)=r^3*(Real.pi*4/3) := by
    rw [Measure.real,metricBall_volume c hr0.le hr.le,ENNReal.toReal_ofReal (by positivity)]
  change (torusVolume E).toReal=torusVolume.real (Metric.ball c r)ᶜ at hv
  rw [hmin.2.1,ENNReal.toReal_ofReal hV.1.le,measureReal_compl Metric.isOpen_ball.measurableSet,
    hvb,Measure.real,torusVolume_univ,ENNReal.toReal_one] at hv
  have hh := mul_le_mul_of_nonneg_right hP' hr0.le
  nlinarith only [hv,hh,hV.2,hr]

theorem isMinimizerAt_spherical_standard_ball {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {c : Cover} {r : ℝ} (hr0 : 0<r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' Metric.sphere c r) :
    V≤4*Real.pi/81 ∧ CongruentAE E (canonicalBall V) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  have hae := small_minimizer_ball_phase hV hmin hr0 hr
    (isMinimizerAt_spherical_boundary_phase hV' hE hmin hr0 hr hbd)
  have hv := congrArg ENNReal.toReal (measure_congr hae)
  rw [hmin.2.1,metricBall_volume (quotientMap c) hr0.le hr.le,
    ENNReal.toReal_ofReal hV.1.le,ENNReal.toReal_ofReal (by positivity)] at hv
  obtain ⟨hs0,hs,hsv⟩ := UpperComparison.canonicalBall_radius_properties hV
  have hrs : r=(3*V/(4*Real.pi))^(1/3 : ℝ) := by
    have he : r^3=((3*V/(4*Real.pi))^(1/3 : ℝ))^3 := by
      nlinarith [Real.pi_pos]
    exact (show Odd (3 : ℕ) by decide).strictMono_pow.injective he
  have hP := isMinimizerAt_perimeter_le_candidateProfile hV' hmin
  have hP' : 4*Real.pi*r^2≤2*Real.sqrt (Real.pi*V) := by
    rw [perimeter_congr_ae hae,metricBall_perimeter (quotientMap c) hr0 hr] at hP
    have hc : candidateProfile V≤2*Real.sqrt (Real.pi*V) := by
      unfold candidateProfile
      rw [min_eq_left (by linarith [hV.2] : V≤1-V)]
      exact (min_le_right _ _).trans (min_le_left _ _)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      (hP.trans (ENNReal.ofReal_le_ofReal hc))
  have hrthird : r≤1/3 := by
    have hh := sq_le_sq₀ (by positivity : 0≤4*Real.pi*r^2) (by positivity : 0≤2*Real.sqrt (Real.pi*V)) |>.mpr hP'
    have hsq := Real.sq_sqrt (show 0≤Real.pi*V from mul_nonneg Real.pi_pos.le hV.1.le)
    have hfactor : 0<16*Real.pi^2*r^3 := by positivity
    have hsq' : (4*Real.pi*r^2)^2≤4*Real.pi*V := by nlinarith only [hh,hsq]
    rw [hv] at hsq'
    have hprod : (16*Real.pi^2*r^3)*(3*r-1)≤0 := by nlinarith only [hsq']
    have hh' : 3*r-1≤0 := by
      by_contra h
      exact (not_lt_of_ge hprod) (mul_pos hfactor (lt_of_not_ge h))
    linarith
  refine ⟨?_,?_⟩
  · have hc := pow_le_pow_left₀ hr0.le hrthird 3
    have hp := mul_le_mul_of_nonneg_right hc (show 0≤Real.pi*4/3 by positivity)
    nlinarith [hv]
  · refine ⟨IsometryEquiv.addRight (quotientMap c),hae.trans ?_⟩
    apply Filter.Eventually.of_forall
    intro x
    apply propext
    change x∈Metric.ball (quotientMap c) r ↔ x∈(IsometryEquiv.addRight (quotientMap c)) '' Metric.ball 0 ((3*V/(4*Real.pi))^(1/3 : ℝ))
    rw [← hrs]
    constructor
    · intro hx
      refine ⟨x-quotientMap c,?_,by simp⟩
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hx
    · rintro ⟨y,hy,rfl⟩
      simpa only [IsometryEquiv.addRight_apply,Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,sub_zero] using hy

end CubicTorus
end
end
end

end OAI
