import Mathlib
import OAI.Geometry.CubicTorus.Reflection.MinimizerAxialCenter

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem periodic_complete_cylinder_radius_lt_half {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) {H : ℝ} {c : Cover}
    (hs : ∀ b∈euclideanCylinder (EuclideanSpace.single i 1) c |H⁻¹|,
      axialCenter (EuclideanSpace.single i 1) H N b=c) : |H⁻¹|<1/2 := by
  by_contra! hh
  obtain ⟨j,k,hji,hki,hjk⟩ := fin_three_other_coordinates i
  let v : Cover := EuclideanSpace.single i 1
  let m : Fin 3 → ℤ := Pi.single j 1
  let e : Cover := EuclideanSpace.single j 1
  have hel : latticeVector m=e := by ext q; simp [m,e,latticeVector,Pi.single_apply]
  let d : ℝ := Real.sqrt ((H⁻¹)^2-1/4)
  have hd : d^2=(H⁻¹)^2-1/4 := Real.sq_sqrt (by nlinarith [sq_abs H⁻¹])
  let w : Cover := (1/2 : ℝ) • e+d • EuclideanSpace.single k 1
  have hij : ⟪v,e⟫=0 := by simp [v,e,EuclideanSpace.inner_single_left,Ne.symm hji]
  have hik : ⟪v,(EuclideanSpace.single k 1 : Cover)⟫=0 := by
    simp [v,EuclideanSpace.inner_single_left,Ne.symm hki]
  have hew : ⟪e,(EuclideanSpace.single k 1 : Cover)⟫=0 := by
    simp [e,EuclideanSpace.inner_single_left,hjk]
  have hwv : ⟪v,w⟫=0 := by simp only [w,inner_add_right,real_inner_smul_right,hij,hik,mul_zero,add_zero]
  have hen : ‖e‖=1 := coordinateAxis_norm j
  have hwev : ⟪v,w-e⟫=0 := by rw [inner_sub_right,hwv,hij,sub_self]
  have hwsq : ‖w‖^2=(H⁻¹)^2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,hen,PiLp.norm_single,norm_one,mul_one,
      inner_smul_left,inner_smul_right,hew,mul_zero,add_zero]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ)<1/2),sq_abs]
    nlinarith [hd]
  have hwesq : ‖w-e‖^2=(H⁻¹)^2 := by
    have heq : w-e=(-1/2 : ℝ) • e+d • EuclideanSpace.single k 1 := by dsimp [w]; module
    rw [heq,norm_add_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,hen,PiLp.norm_single,norm_one,mul_one,
      inner_smul_left,inner_smul_right,hew,mul_zero,add_zero]
    norm_num only [sq_abs]
    nlinarith [hd]
  have hw : ‖w‖=|H⁻¹| := by nlinarith [norm_nonneg w,abs_nonneg H⁻¹,sq_abs H⁻¹]
  have hwe : ‖w-e‖=|H⁻¹| := by nlinarith [norm_nonneg (w-e),abs_nonneg H⁻¹,sq_abs H⁻¹]
  have hb : c+w∈euclideanCylinder v c |H⁻¹| := by
    change ‖axialProjection v (c+w-c)‖=|H⁻¹|
    rw [add_sub_cancel_left,axialProjection_tangent hwv,hw]
  have hbe : c+w-e∈euclideanCylinder v c |H⁻¹| := by
    change ‖axialProjection v (c+w-e-c)‖=|H⁻¹|
    rw [show c+w-e-c=w-e by abel,axialProjection_tangent hwev,hwe]
  have h1 := hs _ hb
  have h2 := hs _ hbe
  have hn : N (c+w-e)=N (c+w) := by
    have h := hp m (c+w-e)
    rw [hel,sub_add_cancel] at h
    exact h.symm
  change axialProjection v (c+w)-H⁻¹ • N (c+w)=c at h1
  change axialProjection v (c+w-e)-H⁻¹ • N (c+w-e)=c at h2
  rw [map_sub,axialProjection_tangent hij,hn] at h2
  have he0 : e=0 := by
    have hh' : (axialProjection v (c+w)-H⁻¹ • N (c+w))-e=c := by
      calc
        _=axialProjection v (c+w)-e-H⁻¹ • N (c+w) := by abel
        _=c := h2
    rw [h1,sub_eq_self] at hh'
    exact hh'
  have hn0 := congrArg norm he0
  simp [e] at hn0

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem periodic_connected_cylindrical_boundary {K : Set Torus}
    (hK : IsClosed K) (hc : IsPreconnected K)
    {N : Cover → Cover} (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) (H : ℝ)
    (hu : ∀ a : Cover,quotientMap a∈K → ‖N a‖=1)
    (hz : ∀ a : Cover,quotientMap a∈K → ⟪(EuclideanSpace.single i 1 : Cover),N a⟫=0)
    (hloc : ∀ a : Cover,quotientMap a∈K → ∀ᶠ z in 𝓝 a,
      (quotientMap z∈K ↔ z∈euclideanCylinder (EuclideanSpace.single i 1)
        (axialCenter (EuclideanSpace.single i 1) H N a) |H⁻¹|) ∧
      (quotientMap z∈K → axialCenter (EuclideanSpace.single i 1) H N z=
        axialCenter (EuclideanSpace.single i 1) H N a))
    {a : Cover} (ha : quotientMap a∈K) :
    |H⁻¹|<1/2 ∧ K=quotientMap '' euclideanCylinder (EuclideanSpace.single i 1)
      (axialCenter (EuclideanSpace.single i 1) H N a) |H⁻¹| := by
  let v : Cover := EuclideanSpace.single i 1
  have hv : ‖v‖=1 := coordinateAxis_norm i
  let c := axialCenter v H N a
  let S : Set Cover := quotientMap ⁻¹' K
  have hS : IsClosed S := hK.preimage continuous_quotientMap
  have hfull := closed_cylindrical_set_contains_cylinder hS hN hv H hu hz hloc ha
  have hr := periodic_complete_cylinder_radius_lt_half hp i (fun b hb => (hfull b hb).2)
  refine ⟨hr,?_⟩
  apply Subset.antisymm
  · intro x hx
    let b := representative x
    have hb : quotientMap b∈K := by simpa only [b,quotientMap_representative] using hx
    let F : Cover → Torus := fun y => quotientMap (axialCenter v H N y)
    have hFp : ∀ m y,F (y+latticeVector m)=F y := axialCenter_axis_periodic hp i H
    have hFl : ∀ y : Cover,quotientMap y∈K →
        ∀ᶠ w in 𝓝 (0 : Cover),quotientMap (y+w)∈K → F (y+w)=F y := by
      intro y hy
      have ht : Tendsto (fun w : Cover => y+w) (𝓝 0) (𝓝 y) := by
        have ht : Continuous (fun w : Cover => y+w) := continuous_const.add continuous_id
        simpa only [add_zero] using ht.tendsto (0 : Cover)
      filter_upwards [ht.eventually (hloc y hy)] with w hw hmem
      exact congrArg quotientMap (hw.2 hmem)
    have he : F b=F a := periodic_local_constant_on_preconnected hFp hc hFl hb ha
    obtain ⟨m,hm⟩ := same_quotient_lattice he
    have hcb : axialCenter v H N b=c+latticeVector m := hm
    let w := b-latticeVector m
    have hwt : axialProjection v (w-c)=H⁻¹ • N b := by
      have hpC : axialProjection v (axialCenter v H N b)=axialCenter v H N b :=
        axialProjection_tangent (axialCenter_transverse hv H (hz b hb))
      have hpc : axialProjection v c=c :=
        axialProjection_tangent (axialCenter_transverse hv H (hz a ha))
      have hpm : axialProjection v (latticeVector m)=latticeVector m := by
        have ht := congrArg (axialProjection v) hcb
        rw [hpC,map_add,hpc,hcb] at ht
        exact (add_left_cancel ht).symm
      change axialProjection v (b-latticeVector m-c)=_
      rw [map_sub,map_sub,hpm,hpc]
      change axialProjection v b-H⁻¹ • N b=c+latticeVector m at hcb
      calc
        _=(axialProjection v b-H⁻¹ • N b)-(c+latticeVector m)+H⁻¹ • N b := by module
        _=_ := by rw [hcb,sub_self,zero_add]
    have hw : w∈euclideanCylinder v c |H⁻¹| := by
      change ‖axialProjection v (w-c)‖=|H⁻¹|
      rw [hwt,norm_smul,hu b hb,Real.norm_eq_abs,mul_one]
    refine ⟨w,hw,?_⟩
    simp only [w,b,quotientMap_sub,quotientMap_latticeVector,sub_zero,quotientMap_representative]
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

theorem isMinimizerAt_axial_curvature_ne_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {H : ℝ} (hgeom : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) : H≠0 := by
  intro hH
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmE).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hu : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) := by
    filter_upwards [hae,hbd] with z hn hb
    exact ⟨hn,(hgeom _ hb).1⟩
  have hpos := isMinimizerAt_connected_curvature_integral_pos hV hE hmE hc hμ hN hp hu
  have he : (∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
      ∂(μ : Measure NormalBundle))=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hbd] with z hb
    have ht (w : Cover) : ⟪N z.1,fderiv ℝ N z.1 w⟫=0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left,
        smooth_unit_normal_derivative (hN.differentiable (by simp) _) (hgeom _ hb).1,inner_zero_left]
    have hh := normal_trace_square_invariance ((hgeom _ hb).1.self_of_nhds) ht
      (B := (0 : Cover →L[ℝ] Cover)) (by simp) (by
        intro w hw
        rw [isMinimizerAt_axial_shape hV hE hmE hμ hN hp hae hv hz hgeom _ hb w hw,hH,zero_smul]
        rfl)
    simpa only [ContinuousLinearMap.zero_comp,coverTrace_zero,Pi.zero_apply] using hh
  rw [he] at hpos
  exact lt_irrefl _ hpos

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_zero_coordinate_cylindrical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (i : Fin 3) (hz : ∀ a∈frontier (openRepresentative E),N (representative a) i=0) :
    ∃ (c : Cover) (r : ℝ),0<r ∧ r<1/2 ∧
      frontier (openRepresentative E)=quotientMap '' euclideanCylinder (EuclideanSpace.single i 1) c r := by
  obtain ⟨ν,H,M,hν,hM,hpM,haM,hgeom,hs⟩ := Periodic.isMinimizerAt_tubular_normal_stability hV hE hmE
  have he (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) : N x=M x := by
    exact isMinimizerAt_normal_local_eq hV hV hE hE hmE hmE isOpen_univ rfl hμ hν hN hM hp hpM hae haM x ⟨hx,mem_univ _⟩
  have hzM (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      ⟪(EuclideanSpace.single i 1 : Cover),M x⟫=0 := by
    rw [← he x hx,EuclideanSpace.inner_single_left,map_one,one_mul]
    have hh := hz (quotientMap x) hx
    simpa only [periodic_representative hp] using hh
  have hH : H≠0 := isMinimizerAt_axial_curvature_ne_zero hV hE hmE hc hν hM hpM haM (coordinateAxis_norm i) hzM hgeom
  have hloc := isMinimizerAt_axial_local_cylinder hV hE hmE hν hM hpM haM (coordinateAxis_norm i) hzM hH hgeom
  have hnon : (frontier (openRepresentative E)).Nonempty := by
    by_contra hn
    have hem : frontier (openRepresentative E)=∅ := not_nonempty_iff_eq_empty.mp hn
    have hpre : IsPreconnected (univ : Set Torus) := by
      rw [← Set.image_univ_of_surjective quotientMap_surjective]
      exact isPreconnected_univ.image quotientMap continuous_quotientMap.continuousOn
    have : PreconnectedSpace Torus := ⟨hpre⟩
    have haeU := isMinimizerAt_openRepresentative_ae hV hE hmE
    have hv := (measure_congr haeU).trans hmE.2.1
    rcases frontier_eq_empty_iff.mp hem with h|h
    · rw [h,measure_empty] at hv
      exact (ENNReal.ofReal_pos.mpr hV.1).ne' hv.symm
    · rw [h,torusVolume_univ] at hv
      have hh := congrArg ENNReal.toReal hv
      rw [ENNReal.toReal_one,ENNReal.toReal_ofReal hV.1.le] at hh
      linarith [hV.2]
  obtain ⟨a,ha⟩ := hnon
  have ha' : quotientMap (representative a)∈frontier (openRepresentative E) := by rwa [quotientMap_representative]
  obtain ⟨hr,hbd⟩ := periodic_connected_cylindrical_boundary isClosed_frontier hc hM.continuous hpM i H
    (fun x hx => (hgeom x hx).1.self_of_nhds) hzM hloc ha'
  exact ⟨axialCenter (EuclideanSpace.single i 1) H M (representative a),|H⁻¹|,
    abs_pos.mpr (inv_ne_zero hH),hr,hbd⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def torusAxialProjection (i : Fin 3) (x : Torus) : Torus :=
  WithLp.toLp 2 (fun j => if j=i then 0 else x j)

@[simp] lemma torusAxialProjection_apply (i : Fin 3) (x : Torus) (j : Fin 3) :
    torusAxialProjection i x j=if j=i then 0 else x j := rfl

lemma torusAxialProjection_continuous (i : Fin 3) : Continuous (torusAxialProjection i) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).comp
  apply continuous_pi
  intro j
  by_cases h : j=i
  · simp only [h,ite_true]; exact continuous_const
  · simp only [ite_eq_right h]; exact PiLp.continuous_apply 2 (fun _ : Fin 3 => AddCircle (1 : ℝ)) j

@[simp] lemma torusAxialProjection_zero (i : Fin 3) : torusAxialProjection i 0=0 := by ext j; simp

lemma torusAxialProjection_sub (i : Fin 3) (x y : Torus) :
    torusAxialProjection i (x-y)=torusAxialProjection i x-torusAxialProjection i y := by
  ext j
  by_cases h : j=i <;> simp [h]

lemma quotientMap_axialProjection (i : Fin 3) (x : Cover) :
    quotientMap (axialProjection (EuclideanSpace.single i 1) x)=torusAxialProjection i (quotientMap x) := by
  ext j
  simp only [quotientMap,PiLp.toLp_apply,axialProjection_axis_apply,torusAxialProjection_apply]
  split_ifs <;> simp

lemma norm_transverse_shortestLift (i : Fin 3) (x : Torus) :
    ‖axialProjection (EuclideanSpace.single i 1) (shortestLift x)‖=‖torusAxialProjection i x‖ := by
  have hh : ‖quotientMap (axialProjection (EuclideanSpace.single i 1) (shortestLift x))‖=
      ‖axialProjection (EuclideanSpace.single i 1) (shortestLift x)‖ := by
    apply norm_quotientMap_eq_of_half_cube
    intro j
    rw [axialProjection_axis_apply]
    split_ifs
    · norm_num
    · exact shortestLift_half_cube x j
  rw [quotientMap_axialProjection,quotientMap_shortestLift] at hh
  exact hh.symm

lemma quotientMap_image_small_cylinder (i : Fin 3) (c : Cover) {r : ℝ} (hr : r≤1/2) :
    quotientMap '' euclideanCylinder (EuclideanSpace.single i 1) c r=
      {x : Torus | ‖torusAxialProjection i (x-quotientMap c)‖=r} := by
  apply Subset.antisymm
  · rintro x ⟨z,hz,rfl⟩
    change ‖axialProjection (EuclideanSpace.single i 1) (z-c)‖=r at hz
    change ‖torusAxialProjection i (quotientMap z-quotientMap c)‖=r
    rw [← quotientMap_sub,← quotientMap_axialProjection,
      norm_quotientMap_eq_of_half_cube (fun j => by
        have h := PiLp.norm_apply_le (axialProjection (EuclideanSpace.single i 1) (z-c)) j
        rw [hz] at h
        exact h.trans hr),hz]
  · intro x hx
    refine ⟨c+shortestLift (x-quotientMap c),?_,?_⟩
    · change ‖axialProjection (EuclideanSpace.single i 1) (c+shortestLift (x-quotientMap c)-c)‖=r
      rw [add_sub_cancel_left,norm_transverse_shortestLift]
      exact hx
    · rw [quotientMap_add,quotientMap_shortestLift,add_sub_cancel]

def axialTube (i : Fin 3) (c : Torus) (r : ℝ) : Set Torus :=
  {x | ‖torusAxialProjection i (x-c)‖<r}

def axialTubeExterior (i : Fin 3) (c : Torus) (r : ℝ) : Set Torus :=
  {x | r<‖torusAxialProjection i (x-c)‖}

lemma isOpen_axialTube (i : Fin 3) (c : Torus) (r : ℝ) : IsOpen (axialTube i c r) :=
  isOpen_lt (((torusAxialProjection_continuous i).comp (continuous_id.sub continuous_const)).norm) continuous_const

lemma isOpen_axialTubeExterior (i : Fin 3) (c : Torus) (r : ℝ) : IsOpen (axialTubeExterior i c r) :=
  isOpen_lt continuous_const (((torusAxialProjection_continuous i).comp (continuous_id.sub continuous_const)).norm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialTube_zero_preconnected (i : Fin 3) (r : ℝ) : IsPreconnected (axialTube i 0 r) := by
  let P := axialProjection (EuclideanSpace.single i 1)
  let S : Set Cover := P ⁻¹' Metric.ball 0 r
  have hS : Convex ℝ S := (convex_ball (0 : Cover) r).linear_preimage P.toLinearMap
  have him : quotientMap '' S=axialTube i 0 r := by
    apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      change dist (P z) 0<r at hz
      rw [dist_zero_right] at hz
      change ‖torusAxialProjection i (quotientMap z-0)‖<r
      rw [sub_zero,← quotientMap_axialProjection]
      exact (norm_quotientMap_le (P z)).trans_lt hz
    · intro x hx
      refine ⟨shortestLift x,?_,quotientMap_shortestLift x⟩
      change dist (P (shortestLift x)) 0<r
      rw [dist_zero_right,norm_transverse_shortestLift]
      simpa only [axialTube,mem_ofPred_eq,sub_zero] using hx
  rw [← him]
  exact hS.isPreconnected.image _ continuous_quotientMap.continuousOn

lemma axialTubeExterior_zero_preconnected (i : Fin 3) {r : ℝ} (hr0 : 0≤r) (hr : r<1/2) :
    IsPreconnected (axialTubeExterior i 0 r) := by
  let v : Cover := EuclideanSpace.single i 1
  have hv : ‖v‖=1 := coordinateAxis_norm i
  let P := axialProjection v
  let S := euclideanCylinder v 0 (1/2)
  let T : Set Torus := quotientMap '' S
  have hS : IsPreconnected S := isPreconnected_euclideanCylinder hv 0 (1/2)
  have hT : IsPreconnected T := hS.image _ continuous_quotientMap.continuousOn
  have hTS : T⊆axialTubeExterior i 0 r := by
    intro x hx
    have hh := (quotientMap_image_small_cylinder i 0 (by norm_num : (1/2 : ℝ)≤1/2)).subset hx
    change ‖torusAxialProjection i (x-quotientMap 0)‖=1/2 at hh
    change r<‖torusAxialProjection i (x-0)‖
    have hq : quotientMap 0=(0 : Torus) := rfl
    rw [hq] at hh
    rw [hh]
    exact hr
  obtain ⟨j,k,hji,hki,hjk⟩ := fin_three_other_coordinates i
  let z₀ : Cover := (1/2 : ℝ) • EuclideanSpace.single j 1
  have hiz : ⟪v,z₀⟫=0 := by
    simp [v,z₀,EuclideanSpace.inner_single_left,Ne.symm hji]
  have hz₀ : z₀∈S := by
    change ‖P (z₀-0)‖=1/2
    rw [sub_zero,axialProjection_tangent hiz]
    simp [z₀,norm_smul]
  apply isPreconnected_of_forall (quotientMap z₀)
  intro x hx
  have hx' : r<‖torusAxialProjection i x‖ := by simpa only [axialTubeExterior,mem_ofPred_eq,sub_zero] using hx
  let z := shortestLift x
  let p := P z
  have hn : ‖p‖=‖torusAxialProjection i x‖ := norm_transverse_shortestLift i x
  have hp0 : 0<‖p‖ := hr0.trans_lt (hx'.trans_eq hn.symm)
  let k : ℝ := (1/2)/‖p‖
  let w := z+(k-1) • p
  have hk : 0<k := div_pos (by norm_num) hp0
  have hwp : P w=k • p := by
    change P (z+(k-1) • P z)=k • P z
    rw [map_add,map_smul,axialProjection_idempotent hv]
    module
  have hw : ‖P w‖=1/2 := by
    rw [hwp,norm_smul,Real.norm_of_nonneg hk.le]
    dsimp [k]; field_simp
  have hwS : w∈S := by change ‖P (w-0)‖=1/2; rwa [sub_zero]
  let f : ℝ → Torus := fun t => quotientMap (z+(((1-t)+t*k)-1) • p)
  have hf : Continuous f := continuous_quotientMap.comp
    (continuous_const.add (((continuous_const.sub continuous_id |>.add (continuous_id.mul continuous_const)).sub continuous_const).smul continuous_const))
  have hf0 : f 0=x := by simp [f,z,quotientMap_shortestLift]
  have hf1 : f 1=quotientMap w := by simp [f,w]
  have hpt (t : ℝ) : P (z+(((1-t)+t*k)-1) • p)=((1-t)+t*k) • p := by
    change P (z+(((1-t)+t*k)-1) • P z)=((1-t)+t*k) • P z
    rw [map_add,map_smul,axialProjection_idempotent hv]
    module
  have hfS : f '' Icc 0 1⊆axialTubeExterior i 0 r := by
    rintro y ⟨t,ht,rfl⟩
    have ht0 : 0≤1-t := sub_nonneg.mpr ht.2
    have ha : 0≤(1-t)+t*k := add_nonneg ht0 (mul_nonneg ht.1 hk.le)
    have hc : ∀ j,|(((1-t)+t*k) • p) j|≤1/2 := by
      intro j
      have hpj : |p j|≤1/2 := by
        change |axialProjection (EuclideanSpace.single i 1) (shortestLift x) j|≤1/2
        rw [axialProjection_axis_apply]
        split_ifs
        · norm_num
        · exact shortestLift_half_cube x j
      have hwj : |(P w) j|≤1/2 := by simpa only [Real.norm_eq_abs,hw] using PiLp.norm_apply_le (P w) j
      have he : (((1-t)+t*k) • p) j=(1-t)*p j+t*(P w) j := by
        rw [hwp]; simp only [PiLp.smul_apply,smul_eq_mul]; ring
      rw [he]
      calc
        _≤|(1-t)*p j|+|t*(P w) j| := abs_add_le _ _
        _=(1-t)*|p j|+t*|(P w) j| := by rw [abs_mul,abs_mul,abs_of_nonneg ht0,abs_of_nonneg ht.1]
        _≤(1-t)*(1/2)+t*(1/2) := add_le_add (mul_le_mul_of_nonneg_left hpj ht0) (mul_le_mul_of_nonneg_left hwj ht.1)
        _=1/2 := by ring
    change r<‖torusAxialProjection i (quotientMap (z+(((1-t)+t*k)-1) • p)-0)‖
    rw [sub_zero,← quotientMap_axialProjection,hpt,norm_quotientMap_eq_of_half_cube hc,norm_smul,Real.norm_of_nonneg ha]
    have hkp : k*‖p‖=1/2 := by dsimp [k]; field_simp
    have hxp : r<‖p‖ := hx'.trans_eq hn.symm
    have hh : 0<(1-t)*(‖p‖-r)+t*((1/2)-r) := by
      by_cases ht1 : t=1
      · simpa only [ht1,sub_self,zero_mul,one_mul,zero_add] using sub_pos.mpr hr
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)) (sub_pos.mpr hxp))
          (mul_nonneg ht.1 (sub_nonneg.mpr hr.le))
    nlinarith
  refine ⟨T∪f '' Icc 0 1,union_subset hTS hfS,Or.inl ⟨z₀,hz₀,rfl⟩,
    Or.inr ⟨0,by norm_num,hf0⟩,?_⟩
  exact hT.union (quotientMap w) ⟨w,hwS,rfl⟩ ⟨1,by norm_num,hf1⟩
    (isPreconnected_Icc.image _ hf.continuousOn)

lemma axialTube_preconnected (i : Fin 3) (c : Torus) (r : ℝ) :
    IsPreconnected (axialTube i c r) := by
  have he : axialTube i c r=(fun x : Torus => x-c) ⁻¹' axialTube i 0 r := by
    ext x; simp only [axialTube,mem_preimage,mem_ofPred_eq,sub_zero]
  rw [he]
  simpa only [Homeomorph.coe_addRight,sub_eq_add_neg] using (Homeomorph.addRight (-c)).isPreconnected_preimage.mpr (axialTube_zero_preconnected i r)

lemma axialTubeExterior_preconnected (i : Fin 3) (c : Torus) {r : ℝ} (hr0 : 0≤r) (hr : r<1/2) :
    IsPreconnected (axialTubeExterior i c r) := by
  have he : axialTubeExterior i c r=(fun x : Torus => x-c) ⁻¹' axialTubeExterior i 0 r := by
    ext x; simp only [axialTubeExterior,mem_preimage,mem_ofPred_eq,sub_zero]
  rw [he]
  simpa only [Homeomorph.coe_addRight,sub_eq_add_neg] using (Homeomorph.addRight (-c)).isPreconnected_preimage.mpr (axialTubeExterior_zero_preconnected i hr0 hr)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_cylindrical_boundary_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) {c : Cover} {r : ℝ} (hr0 : 0<r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' euclideanCylinder (EuclideanSpace.single i 1) c r) :
    E =ᵐ[torusVolume] axialTube i (quotientMap c) r ∨
      E =ᵐ[torusVolume] (axialTube i (quotientMap c) r)ᶜ := by
  let U := openRepresentative E
  let a := quotientMap c
  let B := axialTube i a r
  let D := axialTubeExterior i a r
  have hbd' : frontier U={x : Torus | ‖torusAxialProjection i (x-a)‖=r} :=
    hbd.trans (quotientMap_image_small_cylinder i c hr.le)
  have hBa : Disjoint B (frontier U) := by
    rw [hbd']; exact disjoint_left.mpr fun x hx hz ↦ (ne_of_lt hx) hz
  have hDa : Disjoint D (frontier U) := by
    rw [hbd']; exact disjoint_left.mpr fun x hx hz ↦ (ne_of_gt hx) hz
  have hB := preconnected_avoiding_frontier (isOpen_openRepresentative E)
    (axialTube_preconnected i a r) hBa
  have hD := preconnected_avoiding_frontier (isOpen_openRepresentative E)
    (axialTubeExterior_preconnected i a hr0.le hr) hDa
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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma torusCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Torus) (i : Fin 3) :
    torusCoordinatePermute e x i=x (e i) := rfl

@[simp] lemma torusCoordinatePermute_inverse (e : Fin 3 ≃ Fin 3) (x : Torus) :
    torusCoordinatePermute e (torusCoordinatePermute e.symm x)=x := by ext i; simp

lemma torusCoordinatePermute_measurePreserving (e : Fin 3 ≃ Fin 3) :
    MeasurePreserving (torusCoordinatePermute e) torusVolume torusVolume := by
  convert product_to_torus_measurePreserving.comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => AddCircle (1 : ℝ)) e.symm).comp
      torus_to_product_measurePreserving) using 1
  funext x
  ext i
  simp [Function.comp_def,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft]

def coverCoordinatePermute (e : Fin 3 ≃ Fin 3) : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm

@[simp] lemma coverCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Cover) (i : Fin 3) :
    coverCoordinatePermute e x i=x (e i) := rfl

@[simp] lemma coverCoordinatePermute_inverse (e : Fin 3 ≃ Fin 3) (x : Cover) :
    coverCoordinatePermute e (coverCoordinatePermute e.symm x)=x := by ext i; simp

lemma quotientMap_coordinatePermute (e : Fin 3 ≃ Fin 3) (x : Cover) :
    quotientMap (coverCoordinatePermute e x)=torusCoordinatePermute e (quotientMap x) := rfl

lemma coverCoordinatePermute_lattice (e : Fin 3 ≃ Fin 3) (m : Fin 3 → ℤ) :
    coverCoordinatePermute e (latticeVector m)=latticeVector (fun j => m (e j)) := rfl

lemma coverCoordinatePermute_single (e : Fin 3 ≃ Fin 3) (j : Fin 3) :
    coverCoordinatePermute e (EuclideanSpace.single j 1)=EuclideanSpace.single (e.symm j) 1 := by
  exact LinearIsometryEquiv.piLpCongrLeft_single e.symm j (1 : ℝ)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinatePermutedField (e : Fin 3 ≃ Fin 3) (F : Cover → Cover) : Cover → Cover :=
  fun x => coverCoordinatePermute e.symm (F (coverCoordinatePermute e x))

lemma coordinatePermutedField_contDiff (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (coordinatePermutedField e F) :=
  (coverCoordinatePermute e.symm).toContinuousLinearEquiv.contDiff.comp
    (hF.comp (coverCoordinatePermute e).toContinuousLinearEquiv.contDiff)

lemma coordinatePermutedField_periodic (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,coordinatePermutedField e F (x+latticeVector n)=coordinatePermutedField e F x := by
  intro n x
  simp only [coordinatePermutedField,map_add,coverCoordinatePermute_lattice,hp]

lemma coordinatePermutedField_admissible (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : AdmissibleField F) : AdmissibleField (coordinatePermutedField e F) := by
  refine ⟨coordinatePermutedField_contDiff e hF.1,coordinatePermutedField_periodic e hF.2.1,?_⟩
  intro x
  simpa only [coordinatePermutedField,LinearIsometryEquiv.norm_map] using hF.2.2 (coverCoordinatePermute e x)

lemma coordinatePermutedField_divergence (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (coordinatePermutedField e F) x=divergence F (coverCoordinatePermute e x) := by
  have hd : HasFDerivAt (coordinatePermutedField e F)
      ((coverCoordinatePermute e.symm).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ F (coverCoordinatePermute e x)).comp
          (coverCoordinatePermute e).toContinuousLinearEquiv.toContinuousLinearMap)) x :=
    (coverCoordinatePermute e.symm).toContinuousLinearEquiv.hasFDerivAt.comp x
      (((hF.differentiable (by simp)) _).hasFDerivAt.comp x
        (coverCoordinatePermute e).toContinuousLinearEquiv.hasFDerivAt)
  unfold divergence
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,coverCoordinatePermute_single,
    coverCoordinatePermute_apply]
  exact e.symm.sum_comp (fun j : Fin 3 => (fderiv ℝ F (coverCoordinatePermute e x) (EuclideanSpace.single j 1)) j)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma flux_coordinatePermute (e : Fin 3 ≃ Fin 3) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (torusCoordinatePermute e ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,divergence (coordinatePermutedField e.symm F) x := by
  have hm := (torusCoordinatePermute e).continuous.measurable
  have hr := coordinatePermutedField_admissible e.symm hF
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) (hm hE),
    ← setIntegral_lift (continuous_divergence hr.1) (divergence_periodic hr.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (coordinatePermutedField e.symm F) (representative (torusCoordinatePermute e z))) := by
    funext z
    rw [coordinatePermutedField_divergence e.symm hF.1,← periodic_representative (divergence_periodic hF.2.1)
      (coverCoordinatePermute e.symm (representative (torusCoordinatePermute e z))),
      quotientMap_coordinatePermute,quotientMap_representative]
    have hh : torusCoordinatePermute e.symm (torusCoordinatePermute e z)=z := by
      simpa only [Equiv.symm_symm] using torusCoordinatePermute_inverse e.symm z
    rw [hh]
  rw [he]
  exact (torusCoordinatePermute_measurePreserving e).setIntegral_preimage_emb
    (torusCoordinatePermute e).toHomeomorph.measurableEmbedding
    (fun z => divergence (coordinatePermutedField e.symm F) (representative z)) E

lemma perimeter_coordinatePermute_le (e : Fin 3 ≃ Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusCoordinatePermute e ⁻¹' E)≤perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_coordinatePermute e hF hE]
  exact le_iSup_of_le (coordinatePermutedField e.symm F)
    (le_iSup_of_le (coordinatePermutedField_admissible e.symm hF) le_rfl)

lemma perimeter_coordinatePermute_measurable (e : Fin 3 ≃ Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusCoordinatePermute e ⁻¹' E)=perimeter E := by
  apply le_antisymm (perimeter_coordinatePermute_le e hE)
  have hh := perimeter_coordinatePermute_le e.symm ((torusCoordinatePermute e).continuous.measurable hE)
  have he : torusCoordinatePermute e.symm ⁻¹' (torusCoordinatePermute e ⁻¹' E)=E := by
    ext z; simp
  rwa [he] at hh

theorem perimeter_coordinatePermute (e : Fin 3 ≃ Fin 3) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) :
    perimeter (torusCoordinatePermute e ⁻¹' E)=perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp,← perimeter_congr_ae he]
  exact perimeter_coordinatePermute_measurable e (measurableSet_toMeasurable _ _)

lemma volume_coordinatePermute (e : Fin 3 ≃ Fin 3) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) :
    torusVolume (torusCoordinatePermute e ⁻¹' E)=torusVolume E :=
  (torusCoordinatePermute_measurePreserving e).measure_preimage hE

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma torusCoordinatePermute_norm (e : Fin 3 ≃ Fin 3) (x : Torus) :
    ‖torusCoordinatePermute e x‖=‖x‖ := by
  have h := (torusCoordinatePermute e).dist_eq x 0
  have hz : torusCoordinatePermute e 0=0 := by ext j; rfl
  simpa only [hz,dist_zero_right] using h

lemma torusAxialProjection_permute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (x : Torus) :
    torusAxialProjection (e.symm i) (torusCoordinatePermute e x)=
      torusCoordinatePermute e (torusAxialProjection i x) := by
  ext j
  simp only [torusCoordinatePermute_apply,torusAxialProjection_apply]
  have h : j=e.symm i ↔ e j=i := by
    constructor
    · intro h; rw [h,Equiv.apply_symm_apply]
    · intro h; rw [← h,Equiv.symm_apply_apply]
  simp only [h]

lemma axialTube_zero_model {r : ℝ} (hr : 0≤r) : axialTube 0 0 r=UpperComparison.centeredTube r := by
  ext x
  change ‖torusAxialProjection 0 (x-0)‖<r ↔ ‖x 1‖^2+‖x 2‖^2<r^2
  rw [sub_zero,← sq_lt_sq₀ (norm_nonneg _) hr,PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_three]

lemma axialTube_eq_permute {r : ℝ} (hr : 0≤r) (i : Fin 3) :
    axialTube i 0 r=torusCoordinatePermute (Equiv.swap (0 : Fin 3) i) ⁻¹' UpperComparison.centeredTube r := by
  rw [← axialTube_zero_model hr]
  ext x
  change ‖torusAxialProjection i (x-0)‖<r ↔
    ‖torusAxialProjection 0 (torusCoordinatePermute (Equiv.swap (0 : Fin 3) i) x-0)‖<r
  rw [sub_zero,sub_zero]
  have h := torusAxialProjection_permute (Equiv.swap (0 : Fin 3) i) i x
  simp only [Equiv.symm_swap,Equiv.swap_apply_right] at h
  rw [h,torusCoordinatePermute_norm]

lemma axialTube_eq_translate (i : Fin 3) (c : Torus) (r : ℝ) :
    axialTube i c r=(fun x : Torus => x+(-c)) ⁻¹' axialTube i 0 r := by
  ext x
  simp only [axialTube,mem_preimage,mem_ofPred_eq,sub_eq_add_neg,neg_zero,add_zero]

lemma axialTube_volume (i : Fin 3) (c : Torus) {r : ℝ} (hr0 : 0≤r) (hr : r≤1/2) :
    torusVolume (axialTube i c r)=ENNReal.ofReal (Real.pi*r^2) := by
  rw [axialTube_eq_translate,volume_translation (isOpen_axialTube i 0 r).measurableSet.nullMeasurableSet,
    axialTube_eq_permute hr0,volume_coordinatePermute _ (UpperComparison.measurableSet_centeredTube r).nullMeasurableSet,
    UpperComparison.volume_centeredTube hr0 hr]

lemma axialTube_perimeter (i : Fin 3) (c : Torus) {r : ℝ} (hr0 : 0<r) (hr : r<1/2) :
    perimeter (axialTube i c r)=ENNReal.ofReal (2*Real.pi*r) := by
  rw [axialTube_eq_translate,perimeter_translation (isOpen_axialTube i 0 r).measurableSet.nullMeasurableSet,
    axialTube_eq_permute hr0.le,perimeter_coordinatePermute _ (UpperComparison.measurableSet_centeredTube r).nullMeasurableSet,
    UpperComparison.centeredTube_eq_cubeTube_preimage hr0.le,
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

lemma small_minimizer_tube_phase {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) {i : Fin 3} {c : Torus} {r : ℝ}
    (hr0 : 0<r) (hr : r<1/2)
    (hph : E =ᵐ[torusVolume] axialTube i c r ∨ E =ᵐ[torusVolume] (axialTube i c r)ᶜ) :
    E =ᵐ[torusVolume] axialTube i c r := by
  rcases hph with h|h
  · exact h
  exfalso
  obtain ⟨F,hF,hFv,hFp⟩ := exists_bounded_competitor (V := V) ⟨hV.1.le,by linarith [hV.2]⟩
  have hP := (hmin.2.2 F hF hFv).trans hFp
  have heP : perimeter E = ENNReal.ofReal (2*Real.pi*r) :=
    (perimeter_congr_ae h).trans ((perimeter_compl (isOpen_axialTube i c r).measurableSet.nullMeasurableSet).trans
      (axialTube_perimeter i c hr0 hr))
  rw [heP] at hP
  have hP' : 2*Real.pi*r≤2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ)≤2)).mp
    simpa only [ENNReal.ofReal_ofNat] using hP
  have hv := congrArg ENNReal.toReal (measure_congr h)
  have hvb : torusVolume.real (axialTube i c r)=Real.pi*r^2 := by
    rw [Measure.real,axialTube_volume i c hr0.le hr.le,ENNReal.toReal_ofReal (by positivity)]
  change (torusVolume E).toReal=torusVolume.real (axialTube i c r)ᶜ at hv
  rw [hmin.2.1,ENNReal.toReal_ofReal hV.1.le,measureReal_compl (isOpen_axialTube i c r).measurableSet,
    hvb,Measure.real,torusVolume_univ,ENNReal.toReal_one] at hv
  have hh := mul_le_mul_of_nonneg_right hP' hr0.le
  nlinarith only [hv,hh,hV.2,hr]

lemma axialTube_isometric_model (i : Fin 3) (c : Torus) {r : ℝ} (hr : 0≤r) :
    ∃ φ : Torus ≃ᵢ Torus,φ '' UpperComparison.centeredTube r=axialTube i c r := by
  let e := Equiv.swap (0 : Fin 3) i
  let p := torusCoordinatePermute e
  let φ := p.trans (IsometryEquiv.addRight c)
  have he (y : Torus) : p (φ y-c)=y := by
    change p (p y+c-c)=y
    rw [add_sub_cancel_right]
    exact (show torusCoordinatePermute e (torusCoordinatePermute e.symm y)=y from
      torusCoordinatePermute_inverse e y)
  refine ⟨φ,?_⟩
  rw [axialTube_eq_translate,axialTube_eq_permute hr]
  ext x
  change (∃ y∈UpperComparison.centeredTube r,φ y=x) ↔ p (x+(-c))∈UpperComparison.centeredTube r
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [← sub_eq_add_neg,he] using hy
  · intro hx
    refine ⟨φ.symm x,?_,φ.apply_symm_apply x⟩
    have hh := he (φ.symm x)
    rw [φ.apply_symm_apply] at hh
    simpa only [← sub_eq_add_neg,hh] using hx

theorem isMinimizerAt_cylindrical_standard_tube {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) {c : Cover} {r : ℝ} (hr0 : 0<r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' euclideanCylinder (EuclideanSpace.single i 1) c r) :
    4*Real.pi/81≤V ∧ V≤1/Real.pi ∧ CongruentAE E (canonicalTube V) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  have hae := small_minimizer_tube_phase hV hmin hr0 hr
    (isMinimizerAt_cylindrical_boundary_phase hV' hE hmin i hr0 hr hbd)
  have hv := congrArg ENNReal.toReal (measure_congr hae)
  rw [hmin.2.1,axialTube_volume i (quotientMap c) hr0.le hr.le,
    ENNReal.toReal_ofReal hV.1.le,ENNReal.toReal_ofReal (by positivity)] at hv
  obtain ⟨hs0,hs,hsv⟩ := UpperComparison.canonicalBall_radius_properties hV
  let s : ℝ := (3*V/(4*Real.pi))^(1/3 : ℝ)
  change 0<s at hs0
  change s^3*(Real.pi*4/3)=V at hsv
  have hP := isMinimizerAt_perimeter_le_candidateProfile hV' hmin
  rw [perimeter_congr_ae hae,axialTube_perimeter i (quotientMap c) hr0 hr] at hP
  have hPball : 2*Real.pi*r≤4*Real.pi*s^2 := by
    have hb : candidateProfile V≤(36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ) := by
      unfold candidateProfile
      rw [min_eq_left (by linarith [hV.2] : V≤1-V)]
      exact min_le_left _ _
    have hh := hP.trans (ENNReal.ofReal_le_ofReal hb)
    rw [← UpperComparison.ballArea_formula hV.1.le] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hPslab : 2*Real.pi*r≤2 := by
    have hb : candidateProfile V≤2 := (min_le_right _ _).trans (min_le_right _ _)
    have hh := hP.trans (ENNReal.ofReal_le_ofReal hb)
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ)≤2)).mp hh
  have hrs : r≤2*s^2 := by nlinarith [Real.pi_pos]
  have hrseq : r^2=(4/3)*s^3 := by
    have hz : Real.pi*(r^2-(4/3)*s^3)=0 := by nlinarith only [hv,hsv]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left Real.pi_ne_zero)
  have hsThird : 1/3 ≤ s := by
    have hh := (sq_le_sq₀ hr0.le (by positivity : 0≤2*s^2)).mpr hrs
    have hp : 0<s^3 := pow_pos hs0 _
    have hh' : s^3*(s-1/3)≥0 := by nlinarith only [hh,hrseq]
    have hn : 0 ≤ s-1/3 := (mul_nonneg_iff_of_pos_left hp).mp hh'
    linarith
  have hlow : 4*Real.pi/81≤V := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1/3) hsThird 3
    have ht := mul_le_mul_of_nonneg_right hh (show 0≤Real.pi*4/3 by positivity)
    nlinarith only [ht,hsv]
  have hupp : V≤1/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    have hh : Real.pi*r≤1 := by linarith only [hPslab]
    have hsq := (sq_le_sq₀ (by positivity : 0≤Real.pi*r) (by norm_num : (0 : ℝ)≤1)).mpr hh
    rw [hv]
    nlinarith only [hsq]
  refine ⟨hlow,hupp,?_⟩
  have hrsqrt : r=Real.sqrt (V/Real.pi) := by
    rw [hv,mul_div_cancel_left₀ _ Real.pi_ne_zero,Real.sqrt_sq hr0.le]
  obtain ⟨φ,hφ⟩ := axialTube_isometric_model i (quotientMap c) hr0.le
  refine ⟨φ,hae.trans ?_⟩
  rw [← hφ]
  exact Filter.Eventually.of_forall (fun x => by rw [hrsqrt]; rfl)

end CubicTorus

end
end

end OAI
