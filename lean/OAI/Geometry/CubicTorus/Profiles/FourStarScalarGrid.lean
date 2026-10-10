import Mathlib
import OAI.Geometry.CubicTorus.Reflection.DelaunayPeriodicMoments

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_no_monotone_revolution {V : ℝ} (hVhalf : V∈Ioc (0 : ℝ) (1/2))
    {G : Set Torus} (hG : MeasurableSet G) (hm : IsMinimizerAt V G)
    {b : Fin 3 → Bool} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube G (chamberCorner b) r)
    (hangle : ∀ t a,r (t,a)=r (t,0))
    (heven : ∀ t a,r (-t,a)=r (t,a))
    (hneg : ∀ t∈Ioo (chamberCorner b 0) (chamberCorner b 0+1/2),
      deriv (fun s => r (s,0)) t<0) : False := by
  have hV : V∈Ioo (0 : ℝ) 1 := ⟨hVhalf.1,by linarith [hVhalf.2]⟩
  let R := fun t => r (t,0)
  let p := deriv R
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := hr.1.comp (contDiff_id.prodMk contDiff_const)
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := (contDiff_infty_iff_deriv.mp hR).2
  have hRp : Function.Periodic R 1 := fun t => hr.2.1 t 0
  have hpp : Function.Periodic p 1 := periodic_deriv_real hRp
  have hd (t) : HasDerivAt R (p t) t := (hR.differentiable (by simp) t).hasDerivAt
  have hdp (t) : HasDerivAt p (deriv p t) t := (hp.differentiable (by simp) t).hasDerivAt
  have hpos (t) : 0<R t := (hr.2.2.2.1 (t,0)).1
  have hn : ¬∀ t,R t=R 0 := by
    intro he
    have hf : R=fun _ => R 0 := funext he
    have hz : deriv R (chamberCorner b 0+1/4)=0 := by rw [hf,deriv_const]
    have hh := hneg (chamberCorner b 0+1/4) ⟨by linarith,by linarith⟩
    change deriv R (chamberCorner b 0+1/4)<0 at hh
    linarith only [hz,hh]
  obtain ⟨μ,H,σ,N,hN,hNp,hμ,ha,hu,hstab,hσ,hsign,hCMC,hfirst⟩ :=
    hr.exists_revolution_CMC hV hG hm hangle
  change ∀ t,H/σ=1/(R t*Real.sqrt (1+(p t)^2))-deriv p t/(Real.sqrt (1+(p t)^2))^3 at hCMC
  obtain ⟨a,d,ha,hband,hrad,hext,hH,hf,hrec⟩ :=
    delaunay_nonconstant_parameters hd hdp hpos hRp hpp hCMC hn
  have hc : chamberCorner b 0=0 ∨ chamberCorner b 0=1/2 := by
    simp only [chamberCorner]
    cases b 0 <;> simp
  have hmean := delaunay_chamber_monotone_mean ha hband hc hd hRp
    (fun t => heven t 0) hneg hf
  have hstrict := delaunay_area_gt_cylinder hR.continuous hp.continuous hpos ha hband hf (hrec 2) hmean
  have harea := hr.revolution_area_le_perimeter hV hG hm hμ hangle
  have hvolume := hr.revolution_volume hV hG hm hangle
  have hmV : (∫ t in (0 : ℝ)..1,R t^2)=V/Real.pi := by
    apply (eq_div_iff Real.pi_ne_zero).mpr
    change V=Real.pi*(∫ t in (0 : ℝ)..1,R t^2) at hvolume
    linarith only [hvolume]
  have hupper : perimeter G≤ENNReal.ofReal (2*Real.sqrt (Real.pi*V)) :=
    (hm.2.2 _ (UpperComparison.finitePerimeter_canonicalTube hVhalf)
      (UpperComparison.volume_canonicalTube hVhalf)).trans
      (UpperComparison.perimeter_canonicalTube_le hVhalf)
  have hupper' : (perimeter G).toReal≤2*Real.sqrt (Real.pi*V) := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hgt := mul_lt_mul_of_pos_left hstrict (show 0<2*Real.pi by positivity)
  rw [hmV,UpperComparison.tubeArea_formula hV.1.le] at hgt
  exact (not_lt_of_ge hupper') (hgt.trans_le harea)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_strict_two_vertices_impossible {V : ℝ} (hVhalf : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ j : Fin 3,coordinateReflection j ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (j : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j)
    (i : Fin 3)
    (hv : ∀ b : Fin 3 → Bool,quotientMap (chamberVertex c b)∈openRepresentative E ↔
      b=(fun _ => false) ∨ b=(fun j => decide (j=i))) : False := by
  have hV : V∈Ioo (0 : ℝ) 1 := ⟨hVhalf.1,by linarith [hVhalf.2]⟩
  obtain ⟨e,r,hr⟩ := isMinimizerAt_two_vertices_smooth_tube hV hE hm hμ hN hp ha hs hsg i hv
  let G := torusCoordinatePermute e ⁻¹' E
  have hG : MeasurableSet G := (torusCoordinatePermute e).continuous.measurable hE
  have hmG : IsMinimizerAt V G := isMinimizerAt_coordinatePermute hm e
  have hsG := reflection_invariant_coordinatePermute hs e
  obtain ⟨ν,M,hM,hMp,hν,haM,hrot⟩ := hr.exists_rotation_zero hV hG hmG _ (hsG 1) (hsG 2)
  have hangle := hr.radial_independent_angle hV hG hmG hν hM hMp haM hrot
  exact isMinimizerAt_no_monotone_revolution hVhalf hG hmG hr hangle
    (hr.axial_even hG (hsG 0))
    (hr.deriv_negative_chamber hV hG hmG (isNormalMeasure_coordinatePermute hE hμ e)
      (coordinatePermutedField_contDiff e hN) (coordinatePermutedField_periodic e hp)
      (permuted_normal_ae hN.continuous hp ha e) hangle (chamberSign_coordinatePermute hE hsg e))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma secondTransition_mem_Ioo_half : 1/Real.pi∈Ioo (0 : ℝ) (1/2) := by
  exact ⟨by positivity,(div_lt_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩

theorem isMinimizerAt_second_transition_nonstandard_star
    {E : Set Torus} (hmE : IsMinimizerAt (1/Real.pi) E)
    (hnstd : ¬SmallStandardRegion (1/Real.pi) E) :
    ∃ (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
       (_hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hp : ∀ m x,N (x+latticeVector m)=N x)
      (c : Fin 3 → Bool) (H : ℝ),
      MeasurableSet F ∧ IsMinimizerAt (1/Real.pi) F ∧ IsNormalMeasure F μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ j : Fin 3,coordinateReflection j ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ (x : Cover) (j : Fin 3),
        quotientMap x∈frontier (openRepresentative F)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j) ∧
      (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
        H*directionalFlux F D.coordinate D.function) ∧
      (∑ j : Fin 3,axialFluxWeight μ j)=2 ∧
      (∀ j : Fin 3,0≤axialFluxWeight μ j ∧ axialFluxWeight μ j<1) ∧
      (∀ j : Fin 3,quotientMap (chamberVertex c (fun l => decide (l=j)))∈openRepresentative F) ∧
      (∀ j : Fin 3,quotientMap (chamberVertex c (fun l => decide (l≠j)))∉closure (openRepresentative F)) := by
  have hvh := secondTransition_mem_Ioo_half
  have hV : 1/Real.pi∈Ioo (0 : ℝ) 1 := ⟨hvh.1,by linarith [hvh.2]⟩
  obtain ⟨v,F,μ,N,hN,hp,c,H,hF,he,hm,hcon,hμ,ha,hs,hsg,hH,_,hws,hw,hvi,_⟩ :=
    isMinimizerAt_nonstandard_section_system ⟨hvh.1,hvh.2.le⟩ hmE hnstd
  have hnF : ¬SmallStandardRegion (1/Real.pi) F := fun h => hnstd (smallStandardRegion_of_translated he h)
  have hnstdF : ¬StandardRegionAt (1/Real.pi) F := by
    simpa only [StandardRegionAt,ite_eq_left hvh.2.le] using hnF
  have hR : ∀ i : Fin 3,F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F) := by
    intro i
    rw [axisReflection_eq_coordinateReflection]
    exact (hs i).symm
  have hd := isMinimizerAt_chamber_upper_downset hV hF hm hμ hN hp ha hs hsg
  have heq (j : Fin 3) :
      quotientMap (orientedUpperVertex c (fun k => if k=j then true else false))=
        quotientMap (chamberVertex c (fun k => decide (k=j))) := by
    rw [quotient_orientedUpperVertex_eq]
    congr 2
  obtain ⟨i,hi⟩ := hvi
  have hiO : quotientMap (chamberVertex c (fun j => decide (j=i)))∈openRepresentative F :=
    mem_open_of_mem_closure_not_frontier (isOpen_openRepresentative F) hi
      (isMinimizerAt_reflection_vertex_excluded hV hF hm hμ hN hp ha hs
        (chamberVertex_sine_zero c _))
  have hno (k : Fin 3)
      (hk : quotientMap (chamberVertex c (fun j => decide (j=k)))∉openRepresentative F)
      (hall : ∀ j : Fin 2,quotientMap (chamberVertex c (fun l => decide (l=k.succAbove j)))∈openRepresentative F) : False := by
    apply isMinimizerAt_fixed_downset_not_three_vertices hm hnstdF hR c hd k
    · rwa [heq]
    · intro j
      rw [heq]
      exact hall j
  have hall : ∀ j : Fin 3,quotientMap (chamberVertex c (fun l => decide (l=j)))∈openRepresentative F := by
    rcases three_axes_dichotomy _ ⟨i,hiO⟩ hno with hall|⟨k,hk⟩
    · exact hall
    · obtain ⟨hzero,_,hdown⟩ := isMinimizerAt_chamber_vertex_order hV hF hm hμ ha
        (fun x hx j => (hsg x j ⟨hx.1,mem_iInter.mp hx.2 j⟩).le) hs
      have hv := bool_vertex_two_point_ideal hzero hdown k ((hk k).mpr rfl)
        (fun j hj => (hk j).mp hj)
      exact (isMinimizerAt_strict_two_vertices_impossible ⟨hvh.1,hvh.2.le⟩ hF hm hμ hN hp ha hs hsg k hv).elim
  exact ⟨F,μ,N,hN,hp,c,H,hF,hm,hμ,ha,hs,hsg,hH,hws,hw,hall,
    isMinimizerAt_smaller_side_double_vertices_vacant hvh hF hm hμ hN hp ha hs hsg hH⟩
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Reduction

lemma UpperSupport.deriv_le_left_secant {I C : ℝ → ℝ} {a V : ℝ}
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) I) (ha : 0≤a) (hV : V≤1)
    (haV : a<V) (hs : UpperSupport I C V) :
    deriv C V≤(I V-I a)/(V-a) := by
  have hd := (hs.smooth.differentiableAt (by norm_num)).hasDerivAt
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  apply le_of_tendsto ht
  filter_upwards [hs.above.filter_mono nhdsWithin_le_nhds,
    (show ∀ᶠ W in 𝓝 V, a<W from Ioi_mem_nhds haV).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with W hW haW hWV
  have hv : V∈Icc (0 : ℝ) 1 := ⟨ha.trans haV.le,hV⟩
  have ha' : a∈Icc (0 : ℝ) 1 := ⟨ha,haV.le.trans hV⟩
  have hw : W∈Icc (0 : ℝ) 1 := ⟨ha.trans haW.le,hWV.le.trans hV⟩
  have hm := hc.antitoneOn_slope_lt hv ⟨ha',haV⟩ ⟨hw,hWV⟩ haW.le
  have he : slope I V a=(I V-I a)/(V-a) := by
    rw [slope_def_field]
    apply (div_eq_div_iff (sub_ne_zero.mpr haV.ne) (sub_ne_zero.mpr haV.ne')).mpr
    ring
  have hcomp : slope C V W ≤ slope I V W := by
    simp only [slope_def_field,hs.contact]
    exact div_le_div_of_nonpos_of_le (sub_nonpos.mpr hWV.le) (sub_le_sub_right hW _)
  exact hcomp.trans (hm.trans_eq he)

lemma UpperSupport.power_three_halves_contact {I C : ℝ → ℝ} {V : ℝ}
    (hs : UpperSupport I C V) (hI : ∀ W,0≤I W) (hp : 0<I V) :
    UpperSupport (fun W ↦ I W^(3/2 : ℝ)) (fun W ↦ C W^(3/2 : ℝ)) V := by
  have hc : 0<C V := hs.contact ▸ hp
  refine ⟨hs.smooth.rpow_const_of_ne hc.ne',by rw [hs.contact],?_⟩
  filter_upwards [hs.above] with W hW
  exact Real.rpow_le_rpow (hI W) hW (by norm_num)

end Reduction

theorem profile_upper_support_power_secant {a V : ℝ} (ha : 0≤a) (hV : V∈Ioo 0 1)
    (haV : a<V) {C : ℝ → ℝ} (hs : Reduction.UpperSupport isoperimetricProfile C V) :
    (3/2 : ℝ)*deriv C V*Real.sqrt (isoperimetricProfile V) ≤
      (isoperimetricProfile V^(3/2 : ℝ)-isoperimetricProfile a^(3/2 : ℝ))/(V-a) := by
  have hp := isoperimetricProfile_pos hV
  have hsp := hs.power_three_halves_contact isoperimetricProfile_nonneg hp
  have hh := hsp.deriv_le_left_secant concaveOn_isoperimetricProfile_three_halves ha hV.2.le haV
  have hc : C V≠0 := ne_of_gt (hs.contact ▸ hp)
  rw [deriv_rpow_const (hs.smooth.differentiableAt (by norm_num)) (Or.inl hc),hs.contact] at hh
  norm_num only [show (3/2 : ℝ)-1=1/2 by norm_num] at hh
  rw [←Real.sqrt_eq_rpow] at hh
  nlinarith only [hh]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isoperimetricProfile_first_transition :
    isoperimetricProfile (4*Real.pi/81)=2*Real.pi/9 := by
  have hV := firstTransition_mem_Ioo_half
  obtain ⟨E,hm⟩ := exists_isMinimizerAt (show 4*Real.pi/81∈Ioo (0 : ℝ) 1 from
    ⟨hV.1,by linarith [hV.2]⟩)
  have hs := isMinimizerAt_first_transition_standard hm
  have hP := (hs.bv_data ⟨hV.1,hV.2.le⟩).2.2
  rw [candidateProfile_tube (show 4*Real.pi/81∈Icc TwoVolume.V₁ TwoVolume.V₂ from
    ⟨le_rfl,TwoVolume.transitions.2.1.le⟩)] at hP
  have hsqrt : Real.sqrt (Real.pi*(4*Real.pi/81))=2*Real.pi/9 := by
    apply Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity) |>.mpr
    ring
  rw [hsqrt] at hP
  rw [isoperimetricProfile_eq_of_isMinimizerAt hm,hP,ENNReal.toReal_ofReal (by positivity)]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma first_transition_power_gt :
    (29/50 : ℝ)<(2*Real.pi/9)^(3/2 : ℝ) := by
  have hp : (157/50 : ℝ)<Real.pi := by linarith [Real.pi_gt_d4]
  have hb : (25/36 : ℝ)<2*Real.pi/9 := by linarith
  have hs : (5/6 : ℝ)<Real.sqrt (2*Real.pi/9) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    nlinarith
  have he : (2*Real.pi/9)^(3/2 : ℝ)=(2*Real.pi/9)*Real.sqrt (2*Real.pi/9) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = (2*Real.pi/9)^((1 : ℝ)+1/2) := by congr 1; norm_num
      _ = (2*Real.pi/9)^(1 : ℝ)*(2*Real.pi/9)^(1/2 : ℝ) :=
        Real.rpow_add (by positivity) _ _
      _ = _ := by rw [Real.rpow_one]
  rw [he]
  have hh := mul_lt_mul_of_pos_left hs (show 0<2*Real.pi/9 by positivity)
  nlinarith only [hh,hp]

lemma transition_gap_gt : (4/25 : ℝ)<1/Real.pi-4*Real.pi/81 := by
  have hp := Real.pi_pos
  have hu : Real.pi<(22/7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hq : Real.pi^2<(22/7 : ℝ)^2 := by nlinarith
  have hh : (4/25 : ℝ)*Real.pi+4*Real.pi^2/81<1 := by nlinarith
  apply (lt_sub_iff_add_lt).mpr
  apply (lt_div_iff₀ hp).mpr
  nlinarith only [hh]

theorem second_endpoint_support_curvature {C : ℝ → ℝ}
    (hs : Reduction.UpperSupport isoperimetricProfile C (1/Real.pi)) :
    (deriv C (1/Real.pi))^2*isoperimetricProfile (1/Real.pi)<Real.pi := by
  have hvh : 1/Real.pi∈Ioo (0 : ℝ) (1/2) :=
    ⟨by positivity,(div_lt_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  have hv : 1/Real.pi∈Ioo (0 : ℝ) 1 := ⟨hvh.1,by linarith [hvh.2]⟩
  have hp := isoperimetricProfile_pos hv
  have hupper : isoperimetricProfile (1/Real.pi)≤1 := by
    have hh := isoperimetricProfile_le_candidate ⟨hv.1.le,hv.2.le⟩
    rw [candidateProfile_slab (show 1/Real.pi∈Icc TwoVolume.V₂ (1-TwoVolume.V₂) from
      ⟨le_rfl,by change 1/Real.pi≤1-1/Real.pi; linarith [hvh.2]⟩)] at hh
    norm_num at hh ⊢
    exact hh
  have hh := profile_upper_support_power_secant (a := 4*Real.pi/81)
    (by positivity) hv (by linarith [transition_gap_gt]) hs
  rw [isoperimetricProfile_first_transition] at hh
  have hpow : isoperimetricProfile (1/Real.pi)^(3/2 : ℝ)≤1 := by
    simpa using Real.rpow_le_rpow hp.le hupper (by norm_num : (0 : ℝ)≤3/2)
  have hd := profile_upper_support_slope_nonneg hvh hs
  let q := deriv C (1/Real.pi)*Real.sqrt (isoperimetricProfile (1/Real.pi))
  have hq0 : 0≤q := mul_nonneg hd (Real.sqrt_nonneg _)
  have hq : q<7/4 := by
    by_contra! hn
    have hΔ := transition_gap_gt
    have hΔ0 : 0<1/Real.pi-4*Real.pi/81 := by linarith
    have hm := (le_div_iff₀ hΔ0).mp hh
    have hmul := mul_le_mul_of_nonneg_right hn hΔ0.le
    change (7/4 : ℝ)*(1/Real.pi-4*Real.pi/81)≤q*(1/Real.pi-4*Real.pi/81) at hmul
    have he : (3/2 : ℝ)*deriv C (1/Real.pi)*Real.sqrt (isoperimetricProfile (1/Real.pi))*
        (1/Real.pi-4*Real.pi/81)=(3/2 : ℝ)*(q*(1/Real.pi-4*Real.pi/81)) := by dsimp [q]; ring
    rw [he] at hm
    linarith [first_transition_power_gt]
  have hsq : q^2<(7/4 : ℝ)^2 := by nlinarith
  have he : q^2=(deriv C (1/Real.pi))^2*isoperimetricProfile (1/Real.pi) := by
    dsimp [q]
    rw [mul_pow,Real.sq_sqrt hp.le]
  rw [he] at hsq
  linarith [Real.pi_gt_d4]

theorem isMinimizerAt_second_endpoint_curvature {E : Set Torus}
    (hE : MeasurableSet E) (hm : IsMinimizerAt (1/Real.pi) E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) :
    (H/2)^2*((perimeter E).toReal/2)<Real.pi := by
  have hv : 1/Real.pi∈Ioo (0 : ℝ) 1 :=
    ⟨by positivity,(div_lt_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  obtain ⟨N,C,hN,hp,ha,hs,hd,_⟩ := Periodic.profile_hessian_of_CMC hv hE hm hμ
    (fun _ hF hpF => Periodic.weakCMC_identity hμ hH hF hpF)
  have hh := second_endpoint_support_curvature hs
  rwa [hd,isoperimetricProfile_eq_of_isMinimizerAt hm] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem second_endpoint_support_linear_bound {C : ℝ → ℝ}
    (hs : Reduction.UpperSupport isoperimetricProfile C (1/Real.pi)) :
    deriv C (1/Real.pi)*Real.sqrt (isoperimetricProfile (1/Real.pi))<7/4 := by
  have hvh : 1/Real.pi∈Ioo (0 : ℝ) (1/2) :=
    ⟨by positivity,(div_lt_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  have hv : 1/Real.pi∈Ioo (0 : ℝ) 1 := ⟨hvh.1,by linarith [hvh.2]⟩
  have hp := isoperimetricProfile_pos hv
  have hupper : isoperimetricProfile (1/Real.pi)≤1 := by
    have hh := isoperimetricProfile_le_candidate ⟨hv.1.le,hv.2.le⟩
    rw [candidateProfile_slab (show 1/Real.pi∈Icc TwoVolume.V₂ (1-TwoVolume.V₂) from
      ⟨le_rfl,by change 1/Real.pi≤1-1/Real.pi; linarith [hvh.2]⟩)] at hh
    norm_num at hh ⊢
    exact hh
  have hh := profile_upper_support_power_secant (a := 4*Real.pi/81)
    (by positivity) hv (by linarith [transition_gap_gt]) hs
  rw [isoperimetricProfile_first_transition] at hh
  have hpow : isoperimetricProfile (1/Real.pi)^(3/2 : ℝ)≤1 := by
    simpa using Real.rpow_le_rpow hp.le hupper (by norm_num : (0 : ℝ)≤3/2)
  have hd := profile_upper_support_slope_nonneg hvh hs
  let q := deriv C (1/Real.pi)*Real.sqrt (isoperimetricProfile (1/Real.pi))
  have hq0 : 0≤q := mul_nonneg hd (Real.sqrt_nonneg _)
  have hq : q<7/4 := by
    by_contra! hn
    have hΔ := transition_gap_gt
    have hΔ0 : 0<1/Real.pi-4*Real.pi/81 := by linarith
    have hm := (le_div_iff₀ hΔ0).mp hh
    have hmul := mul_le_mul_of_nonneg_right hn hΔ0.le
    change (7/4 : ℝ)*(1/Real.pi-4*Real.pi/81)≤q*(1/Real.pi-4*Real.pi/81) at hmul
    have he : (3/2 : ℝ)*deriv C (1/Real.pi)*Real.sqrt (isoperimetricProfile (1/Real.pi))*
        (1/Real.pi-4*Real.pi/81)=(3/2 : ℝ)*(q*(1/Real.pi-4*Real.pi/81)) := by dsimp [q]; ring
    rw [he] at hm
    linarith [first_transition_power_gt]
  exact hq

theorem isMinimizerAt_second_endpoint_linear_bound {E : Set Torus}
    (hE : MeasurableSet E) (hm : IsMinimizerAt (1/Real.pi) E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) :
    (H/2)*((μ.mass : ℝ)/2)<7/4 := by
  have hvh : 1/Real.pi∈Ioo (0 : ℝ) (1/2) :=
    ⟨by positivity,(div_lt_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  have hv : 1/Real.pi∈Ioo (0 : ℝ) 1 := ⟨hvh.1,by linarith [hvh.2]⟩
  obtain ⟨N,C,hN,hp,ha,hs,hd,_⟩ := Periodic.profile_hessian_of_CMC hv hE hm hμ
    (fun _ hF hpF => Periodic.weakCMC_identity hμ hH hF hpF)
  have hh := second_endpoint_support_linear_bound hs
  rw [hd,isoperimetricProfile_eq_of_isMinimizerAt hm,←hμ.1] at hh
  obtain ⟨hA,_,hA1⟩ := isMinimizerAt_halfMass_competitor_bounds ⟨hvh.1,hvh.2.le⟩ hm hμ
  have hH0 := isMinimizerAt_coordinate_multiplier_nonneg hvh hE hm hμ hH
  have hsq := Real.sq_sqrt hA.le
  have hs0 := Real.sqrt_nonneg ((μ.mass : ℝ)/2)
  have hAsq : (μ.mass : ℝ)/2≤Real.sqrt ((μ.mass : ℝ)/2) := by nlinarith
  exact (mul_le_mul_of_nonneg_left hAsq (by linarith : 0≤H/2)).trans_lt hh
end CubicTorus

end
end

section

noncomputable section
namespace CubicTorus

lemma corner_root_basic_bound {t d x : ℝ} (ht : t<1) (_hx : 0≤x)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2)) : x*(1+t)≤Real.pi := by
  have hf : (Real.pi-x*(1+t))*(1-t)=Real.pi*d^2 := by nlinarith only [he]
  have hh : 0≤(Real.pi-x*(1+t))*(1-t) := hf ▸ mul_nonneg Real.pi_pos.le (sq_nonneg d)
  have := (mul_nonneg_iff_of_pos_right (show 0<1-t by linarith)).mp hh
  linarith

lemma corner_root_d_bound {t d x : ℝ} (ht0 : 0≤t) (ht : t<1) (hx : 0≤x)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2)) : d^2≤1-t := by
  have ha : 0≤1-t^2 := by nlinarith
  have hh : 0≤Real.pi*(1-t-d^2) := he ▸ mul_nonneg hx ha
  have := (mul_nonneg_iff_of_pos_left Real.pi_pos).mp hh
  linarith

lemma corner_root_interval_bound {t d x l u D X : ℝ}
    (ht0 : 0≤t) (hd0 : 0≤d) (hx0 : 0≤x)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2))
    (hl : l≤t) (hu : t≤u) (hD : D≤d) (hD0 : 0≤D)
    (hu1 : u<1) (hc : 0≤1-l-D^2)
    (hnum : (22/7 : ℝ)*(1-l-D^2)≤X*(1-u^2)) : x≤X := by
  have hpu : Real.pi≤(22/7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hds : D^2≤d^2 := by nlinarith
  have hts : t^2≤u^2 := by nlinarith
  have ha := mul_nonneg hx0 (sub_nonneg.mpr hts)
  have hb := mul_nonneg Real.pi_pos.le (show 0≤t-l+(d^2-D^2) by linarith)
  have hp := mul_le_mul_of_nonneg_right hpu hc
  have hq : x*(1-u^2)≤X*(1-u^2) := by nlinarith only [he,ha,hb,hp,hnum]
  exact (mul_le_mul_iff_left₀ (show 0<1-u^2 by nlinarith)).mp hq

lemma corner_root_simple_bound {t d x l X : ℝ} (ht : t<1) (hx0 : 0≤x)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2)) (hl : l≤t) (hl0 : -1<l)
    (hnum : (22/7 : ℝ)≤X*(1+l)) : x≤X := by
  have hb := corner_root_basic_bound ht hx0 he
  have ha := mul_nonneg hx0 (sub_nonneg.mpr hl)
  have hp : Real.pi<(22/7 : ℝ) := by linarith [Real.pi_lt_d4]
  exact (mul_le_mul_iff_left₀ (show 0<1+l by linarith)).mp (by nlinarith only [ha,hb,hnum,hp])

lemma corner_box_strict {t d x u E X : ℝ}
    (ht0 : 0≤t) (hd0 : 0≤d) (hx0 : 0≤x)
    (hu : t≤u) (hE : d≤E) (hX : x≤X)
    (hnum : E+(u^2+(u+X*E)^2)/(157/50 : ℝ)<1) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hu0 : 0≤u := ht0.trans hu
  have hE0 : 0≤E := hd0.trans hE
  have hX0 : 0≤X := hx0.trans hX
  have hm := mul_le_mul hX hE hd0 hX0
  have hsum : t+x*d≤u+X*E := by linarith
  have hsum0 : 0≤t+x*d := add_nonneg ht0 (mul_nonneg hx0 hd0)
  have hs : t^2+(t+x*d)^2≤u^2+(u+X*E)^2 := by nlinarith
  have hp : (157/50 : ℝ)<Real.pi := by linarith [Real.pi_gt_d4]
  have hs0 : 0≤u^2+(u+X*E)^2 := by positivity
  have hdiv := div_le_div_of_nonneg_left hs0 (by norm_num : (0 : ℝ)<157/50) hp.le
  have hdiv' := div_le_div_of_nonneg_right hs Real.pi_pos.le
  linarith

lemma corner_box_root_impossible {t d x l u E : ℝ}
    (ht0 : 0≤t) (hd0 : 0≤d) (_hx0 : 0≤x) (hx : x≤7/4)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2))
    (hl : l≤t) (hl0 : 0≤l) (hu : t≤u) (hu1 : u≤1)
    (hE : d≤E) (he0 : 0≤1-u-E^2)
    (hnum : (7/4 : ℝ)*(1-l^2)<(157/50 : ℝ)*(1-u-E^2)) : False := by
  have hdE : d^2≤E^2 := by nlinarith
  have hlt : l^2≤t^2 := by nlinarith
  have ht1 : t^2≤1 := by nlinarith
  have ha := mul_le_mul_of_nonneg_right hx (sub_nonneg.mpr ht1)
  have hb := mul_nonneg (show (0 : ℝ)≤7/4 by norm_num) (sub_nonneg.mpr hlt)
  have hc := mul_nonneg Real.pi_pos.le (show 0≤u-t+(E^2-d^2) by linarith)
  have hp : (157/50 : ℝ)≤Real.pi := by linarith [Real.pi_gt_d4]
  have hq := mul_le_mul_of_nonneg_right hp he0
  nlinarith only [he,ha,hb,hc,hq,hnum]

end CubicTorus

end
end

section

noncomputable section
namespace CubicTorus

structure CornerRootData (t d x : ℝ) : Prop where
  t0 : 0≤t
  t1 : t<1
  d0 : 0≤d
  d3 : d^2≤1/3
  x0 : 0≤x
  xcap : x≤7/4
  root : Real.pi*(1-t-d^2)=x*(1-t^2)

namespace CornerRootData
lemma dbound {t d x : ℝ} (h : CornerRootData t d x) : d^2≤1-t :=
  corner_root_d_bound h.t0 h.t1 h.x0 h.root
end CornerRootData

lemma corner_grid_0 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (0/1 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (_hd : (0/1 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_1 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (_hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  exact (corner_box_root_impossible h.t0 h.d0 h.x0 h.xcap h.root
    hl (by norm_num) hu (by norm_num) he (by norm_num) (by norm_num)).elim

lemma corner_grid_2 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (0/1 : ℝ)≤t) (hu : t≤(1/8 : ℝ))
    (_hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_3 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (_hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_4 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (_hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_5 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (_hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_6 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (_hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_7 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(17/128 : ℝ))
    (_hd : (91/160 : ℝ)≤d) (he : d≤(1651/2880 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_8 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(17/128 : ℝ))
    (hd : (1651/2880 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(398798312/228146625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_9 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(17/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (1651/2880 : ℝ) with hm|hm
  · exact corner_grid_7 h hl hu hd hm
  · exact corner_grid_8 h hl hu hm.le he

private lemma corner_grid_10 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/128 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(1651/2880 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(111352/63875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_11 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/128 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (1651/2880 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(8933998/5173875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_12 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/128 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (1651/2880 : ℝ) with hm|hm
  · exact corner_grid_10 h hl hu hd hm
  · exact corner_grid_11 h hl hu hm.le he

private lemma corner_grid_13 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/128 : ℝ) with hm|hm
  · exact corner_grid_9 h hl hm hd he
  · exact corner_grid_12 h hm.le hu hd he

private lemma corner_grid_14 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_6 h hl hu hd hm
  · exact corner_grid_13 h hl hu hm.le he

private lemma corner_grid_15 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (9/64 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (_hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_16 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(19/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(1651/2880 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1609696/934675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_17 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(19/128 : ℝ))
    (hd : (1651/2880 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(387393512/227126025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_18 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(19/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (1651/2880 : ℝ) with hm|hm
  · exact corner_grid_16 h hl hu hd hm
  · exact corner_grid_17 h hl hu hm.le he

private lemma corner_grid_19 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/128 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(297418/174825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_20 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/128 : ℝ) with hm|hm
  · exact corner_grid_18 h hl hm hd he
  · exact corner_grid_19 h hm.le hu hd he

private lemma corner_grid_21 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_15 h hl hu hd hm
  · exact corner_grid_20 h hl hu hm.le he

private lemma corner_grid_22 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/64 : ℝ) with hm|hm
  · exact corner_grid_14 h hl hm hd he
  · exact corner_grid_21 h hm.le hu hd he

private lemma corner_grid_23 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_5 h hl hu hd hm
  · exact corner_grid_22 h hl hu hm.le he

private lemma corner_grid_24 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (5/32 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (_hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_25 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(793/1440 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3872/2223 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_26 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (793/1440 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(11971861/7002450 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_27 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (793/1440 : ℝ) with hm|hm
  · exact corner_grid_25 h hl hu hd hm
  · exact corner_grid_26 h hl hu hm.le he

private lemma corner_grid_28 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/64 : ℝ) with hm|hm
  · exact corner_grid_24 h hl hm hd he
  · exact corner_grid_27 h hm.le hu hd he

private lemma corner_grid_29 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(96796832/56345625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_30 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(21/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4688288/2790025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_31 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/128 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(384824/231875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_32 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/128 : ℝ) with hm|hm
  · exact corner_grid_30 h hl hm hd he
  · exact corner_grid_31 h hm.le hu hd he

private lemma corner_grid_33 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_29 h hl hu hd hm
  · exact corner_grid_32 h hl hu hm.le he

private lemma corner_grid_34 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5871602/3501225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_35 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(23/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4547488/2774625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_36 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/128 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(19987/12350 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_37 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/128 : ℝ) with hm|hm
  · exact corner_grid_35 h hl hm hd he
  · exact corner_grid_36 h hm.le hu hd he

private lemma corner_grid_38 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_34 h hl hu hd hm
  · exact corner_grid_37 h hl hu hm.le he

private lemma corner_grid_39 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/64 : ℝ) with hm|hm
  · exact corner_grid_33 h hl hm hd he
  · exact corner_grid_38 h hm.le hu hd he

private lemma corner_grid_40 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_28 h hl hu hd hm
  · exact corner_grid_39 h hl hu hm.le he

lemma corner_grid_41 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/32 : ℝ) with hm|hm
  · exact corner_grid_23 h hl hm hd he
  · exact corner_grid_40 h hm.le hu hd he

end CubicTorus
end
end

end OAI
