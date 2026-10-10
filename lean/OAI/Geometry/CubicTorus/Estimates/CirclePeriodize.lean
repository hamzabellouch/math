import Mathlib
import OAI.Geometry.CubicTorus.Estimates.LatticeHeightHom

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_zero_curvature_not_preconnected {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hq : ∀ x,quotientMap x∈frontier (openRepresentative E) →
      coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))=0) :
    ¬IsPreconnected (frontier (openRepresentative E)) := by
  intro hconn
  have hloc := isMinimizerAt_zero_curvature_local_normal hV hE hmin hμ hN hp hae hu hq
  have hplane (a : Cover) (ha : quotientMap a∈frontier (openRepresentative E))
      (b : Cover) (hb : ⟪N a,b-a⟫=0) :
      quotientMap b∈frontier (openRepresentative E) ∧ N b=N a :=
    closed_flat_set_contains_plane (isClosed_frontier.preimage continuous_quotientMap)
      hN.continuous (fun a ha ↦ (hloc a ha).2) ha b hb
  have hpar {a b : Cover} (ha : quotientMap a∈frontier (openRepresentative E))
      (hb : quotientMap b∈frontier (openRepresentative E)) : N b=N a ∨ N b= -N a :=
    complete_planes_normals_parallel (fun x hx ↦ (hloc x hx).1) hplane ha hb
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hmpos : 0<(μ : Measure NormalBundle).real univ := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal,hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne
  have : NeZero (μ : Measure NormalBundle) := ⟨by intro hz; simp [hz,Measure.real] at hmpos⟩
  obtain ⟨z,hz⟩ := hbd.exists
  let n := N z.1
  have hn : ‖n‖=1 := (hloc z.1 hz).1
  have hc : ∀ x∈frontier (openRepresentative E),N (representative x)=n := by
    intro x hx
    have hm : MapsTo (fun x : Torus ↦ N (representative x))
        (frontier (openRepresentative E)) ({n,-n} : Set Cover) := by
      intro y hy
      have hh := hpar (a := z.1) (b := representative y) hz
        (by simpa only [quotientMap_representative] using hy)
      simpa only [mem_insert_iff,mem_singleton_iff,n] using hh
    have hh := hconn.constant_of_mapsTo (Set.toFinite ({n,-n} : Set Cover)).isDiscrete
      (continuous_periodic_descent hN.continuous hp).continuousOn hm hx hz
    simpa only [periodic_representative hp] using hh
  have hconst : ∀ᵐ z ∂(μ : Measure NormalBundle),(z.2 : Cover)=n := by
    filter_upwards [hbd,hae] with w hw he
    have hh := hc (quotientMap w.1) hw
    rw [periodic_representative hp] at hh
    exact he.symm.trans hh
  have hf : AdmissibleField (fun _ : Cover ↦ n) := ⟨contDiff_const,fun _ _ ↦ rfl,fun _ ↦ hn.le⟩
  have hflux := hμ.2 _ hf
  have hi : (∫ w,normalTest (fun _ : Cover ↦ n) hf.1.continuous w ∂(μ : Measure NormalBundle))=
      (μ : Measure NormalBundle).real univ := by
    calc
      _=(∫ _ : NormalBundle,(1 : ℝ) ∂(μ : Measure NormalBundle)) := by
        apply integral_congr_ae
        filter_upwards [hconst] with w hw
        simp only [normalTest,ContinuousMap.coe_mk,hw,real_inner_self_eq_norm_sq,hn,one_pow]
      _=_ := by simp
  rw [hi] at hflux
  have hd : divergence (fun _ : Cover ↦ n) = fun _ ↦ 0 := by
    funext x
    simp [divergence]
  rw [hd,integral_zero] at hflux
  exact hmpos.ne' hflux

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma real_periodic_deriv {f : ℝ → ℝ} (hp : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro x
  rw [← deriv_comp_add_const]
  exact congrArg (fun g : ℝ → ℝ ↦ deriv g x) (funext hp)

lemma continuous_periodic_lift {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : Continuous f) : Continuous hp.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact hf

theorem integerCharacter_directional_variation {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hP : perimeter ((integerCharacter m) ⁻¹' K) ≠ ⊤)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : Function.Periodic ψ 1) (hb : ∀ t,|ψ t|≤1) (a : ℝ) :
    ‖latticeVector m‖ * |∫ t in a..a+1,
      K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ))| ≤
      (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  let n := latticeVector m
  let l : Cover →L[ℝ] ℝ := innerSL ℝ n
  let f : Cover → ℝ := fun x ↦ ψ (l x)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hψ.comp l.contDiff
  have hper : ∀ z x,f (x+latticeVector z)=f x := by
    intro z x
    change ψ (⟪n,x+latticeVector z⟫)=ψ ⟪n,x⟫
    rw [inner_add_right]
    have he : ⟪n,latticeVector z⟫ = (∑ i,m i*z i : ℤ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct,star_trivial,n,latticeVector,WithLp.ofLp_toLp,Int.cast_sum,Int.cast_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    simpa only [mul_one] using hp.int_mul (∑ i,m i*z i) ⟪n,x⟫
  have hdir := abs_directional_flux_le hP hf hper (fun x ↦ hb (l x)) n
  have hd (x : Cover) : fderiv ℝ f x n=deriv ψ ⟪n,x⟫*‖n‖^2 := by
    have hh := ((hψ.differentiable (by simp)).differentiableAt.hasDerivAt).comp_hasFDerivAt
      x l.hasFDerivAt
    change (fderiv ℝ (ψ ∘ l) x) n=_
    rw [hh.fderiv]
    simp only [smul_apply,smul_eq_mul,l,innerSL_apply_apply]
    rw [real_inner_self_eq_norm_sq]
  simp_rw [hd] at hdir
  rw [integral_mul_const,abs_mul,abs_of_nonneg (sq_nonneg ‖n‖)] at hdir
  let g : AddCircle (1 : ℝ) → ℝ := K.indicator (real_periodic_deriv hp).lift
  have hg : Measurable g := (continuous_periodic_lift (real_periodic_deriv hp)
    (hψ.continuous_deriv (by simp))).measurable.indicator hK
  have hint : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((integerCharacter m) ⁻¹' K),
      deriv ψ ⟪n,x⟫) = ∫ t in a..a+1,g (t : AddCircle (1 : ℝ)) := by
    rw [← lift_indicator_integral (hK.preimage (continuous_integerCharacter m).measurable).nullMeasurableSet]
    have he (x : Cover) : (quotientMap ⁻¹' ((integerCharacter m) ⁻¹' K)).indicator
        (fun x ↦ deriv ψ ⟪n,x⟫) x = g (integerCharacter m (quotientMap x)) := by
      by_cases hx : integerCharacter m (quotientMap x)∈K
      · rw [Set.indicator_of_mem (show x∈quotientMap ⁻¹' ((integerCharacter m) ⁻¹' K) from hx)]
        change _=K.indicator (real_periodic_deriv hp).lift (integerCharacter m (quotientMap x))
        rw [Set.indicator_of_mem hx,integerCharacter_quotientMap]
        rfl
      · rw [Set.indicator_of_notMem (show x∉quotientMap ⁻¹' ((integerCharacter m) ⁻¹' K) from hx)]
        exact (Set.indicator_of_notMem hx _).symm
    simp_rw [he]
    have hh := integral_map (μ := volume.restrict fundamentalCube) quotientMap_measurePreserving.measurable.aemeasurable
      (hg.comp (continuous_integerCharacter m).measurable).aestronglyMeasurable
    rw [quotientMap_measurePreserving.map_eq] at hh
    simp only [Function.comp_apply] at hh
    rw [← hh]
    have hh' := integral_map (μ := torusVolume) (integerCharacter_measurePreserving hm).measurable.aemeasurable
      (show AEStronglyMeasurable g (Measure.map (integerCharacter m) torusVolume) from
        hg.aestronglyMeasurable)
    rw [(integerCharacter_measurePreserving hm).map_eq] at hh'
    rw [← hh',AddCircle.intervalIntegral_preimage]
  rw [hint] at hdir
  have hn : 0<‖n‖ := by
    apply norm_pos_iff.mpr
    intro hn
    apply hm
    funext i
    have hi := congrArg (fun x : Cover ↦ x i) hn
    simp only [n,latticeVector,WithLp.ofLp_toLp,PiLp.zero_apply] at hi
    exact_mod_cast hi
  nlinarith [abs_nonneg (∫ t in a..a+1,g (t : AddCircle (1 : ℝ)))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma finite_integer_support_near {f : ℝ → ℝ} (hf : HasCompactSupport f) (a : ℝ) :
    ∃ s : Finset ℤ,∀ x∈Metric.ball a 1,∀ n∉s,f (x+n)=0 := by
  classical
  obtain ⟨R,_,hR⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|a|+1)
  refine ⟨Finset.Icc (-(N : ℤ)) N,?_⟩
  intro x hx n hn
  by_contra h
  have hb := hR _ (subset_tsupport f h)
  have hx' : |x-a|<1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hx
  have ha : |x|≤|a|+1 := by
    have hh := abs_add_le (x-a) a
    rw [sub_add_cancel] at hh
    linarith
  have hn' : |(n : ℝ)|<N := by
    have hh := norm_sub_le (x+n) x
    simp only [Real.norm_eq_abs] at hh
    rw [add_sub_cancel_left] at hh
    rw [Real.norm_eq_abs] at hb
    linarith
  apply hn
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast (abs_le.mp hn'.le).1
  · exact_mod_cast (abs_le.mp hn'.le).2

def circlePeriodize (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑' n : ℤ,f (x+n)

lemma circlePeriodize_periodic (f : ℝ → ℝ) : Function.Periodic (circlePeriodize f) 1 := by
  intro x
  unfold circlePeriodize
  calc
    _ = ∑' n : ℤ,f (x+(n+1 : ℤ)) := by
      apply tsum_congr
      intro n
      congr 1
      push_cast
      ring
    _ = _ := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n ↦ f (x+n))

lemma circlePeriodize_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) : ContDiff ℝ (⊤ : ℕ∞) (circlePeriodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  obtain ⟨s,hs⟩ := finite_integer_support_near hs a
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ∑ n∈s,f (x+n)) :=
    ContDiff.sum fun n _ ↦ hf.comp (contDiff_id.add contDiff_const)
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds a (by norm_num : (0 : ℝ)<1)] with x hx
  exact tsum_eq_sum (hs x hx)

lemma circlePeriodize_eventuallyEq {f : ℝ → ℝ} (hc : HasCompactSupport f)
    {a : ℝ} (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    {x : ℝ} (hx : x∈Icc (a-1/2) (a+1/2)) : circlePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s,hlocal⟩ := finite_integer_support_near hc x
  have hz (n : ℤ) (hn : n≠0) : ∀ᶠ y in 𝓝 x,f (y+n)=0 := by
    have hnot : x+n∉tsupport f := by
      intro h
      have hh := hs h
      have hlo : (-1 : ℝ)<n := by linarith [hx.2,hh.1]
      have hhi : (n : ℝ)<1 := by linarith [hx.1,hh.2]
      have hlo' : (-1 : ℤ)<n := by exact_mod_cast hlo
      have hhi' : n<1 := by exact_mod_cast hhi
      omega
    exact (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
      (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x,∀ n∈s,n≠0 → f (y+n)=0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n=0
    · exact Eventually.of_forall fun _ h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun _ h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ)<1),hfin] with y hy hz
  unfold circlePeriodize
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro n hn
    by_cases hs : n∈s
    · exact hz n hs hn
    · exact hlocal y hy n hs

lemma circlePeriodize_unit_bounds {f : ℝ → ℝ} {a : ℝ}
    (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    (hb : ∀ x,0≤f x ∧ f x≤1) (x : ℝ) :
    0≤circlePeriodize f x ∧ circlePeriodize f x≤1 := by
  classical
  by_cases hn : ∃ n : ℤ,f (x+n)≠0
  · obtain ⟨n,hn⟩ := hn
    have huniq (m : ℤ) (hm : m≠n) : f (x+m)=0 := by
      by_contra hm'
      have h1 := hs (subset_tsupport f hn)
      have h2 := hs (subset_tsupport f hm')
      have hlo : (-1 : ℝ)<(m-n : ℤ) := by push_cast; linarith [h1.2,h2.1]
      have hhi : ((m-n : ℤ) : ℝ)<1 := by push_cast; linarith [h1.1,h2.2]
      have hlo' : (-1 : ℤ) < m-n := by exact_mod_cast hlo
      have hhi' : m-n<1 := by exact_mod_cast hhi
      omega
    rw [circlePeriodize,tsum_eq_single n huniq]
    exact hb _
  · push Not at hn
    unfold circlePeriodize
    simp only [hn,tsum_zero,le_refl,zero_le_one,and_self]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem circle_positive_transition_lower_bound {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hP : perimeter ((integerCharacter m) ⁻¹' K)≠⊤)
    {a r : ℝ} (hr : 0<r)
    (hphase : ∀ t∈Ioo (a-r) (a+r),(t : AddCircle (1 : ℝ))∈K ↔ a<t) :
    2*‖latticeVector m‖ ≤ (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  classical
  let R := min r (1/4)/2
  have hR : 0<R := by dsimp [R]; positivity
  have hRr : R<r := by have hh := min_le_left r (1/4 : ℝ); dsimp [R]; linarith
  have hRh : R<1/2 := by have hh := min_le_right r (1/4 : ℝ); dsimp [R]; linarith
  let b : ContDiffBump a := ⟨R/2,R,half_pos hR,by linarith⟩
  have hbc : ContDiff ℝ (⊤ : ℕ∞) (b : ℝ → ℝ) := b.contDiff
  have hbs : tsupport (b : ℝ → ℝ) ⊆ Ioo (a-1/2) (a+1/2) := by
    rw [b.tsupport_eq,Real.closedBall_eq_Icc]
    intro t ht
    change a-R≤t ∧ t≤a+R at ht
    constructor <;> linarith [ht.1,ht.2]
  have hbr : tsupport (b : ℝ → ℝ) ⊆ Ioo (a-r) (a+r) := by
    rw [b.tsupport_eq,Real.closedBall_eq_Icc]
    intro t ht
    change a-R≤t ∧ t≤a+R at ht
    constructor <;> linarith [ht.1,ht.2]
  let ψ : ℝ → ℝ := fun t ↦ 2*circlePeriodize b t-1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (contDiff_const.mul (circlePeriodize_contDiff b.contDiff b.hasCompactSupport)).sub contDiff_const
  have hp : Function.Periodic ψ 1 := fun t ↦ by
    dsimp only [ψ]
    rw [circlePeriodize_periodic b t]
  have hb (t : ℝ) : |ψ t|≤1 := by
    have hh := circlePeriodize_unit_bounds hbs (fun t ↦ ⟨b.nonneg,b.le_one⟩) t
    apply abs_le.mpr
    dsimp [ψ]
    constructor <;> linarith [hh.1,hh.2]
  have hd (t : ℝ) (ht : t∈Icc (a-1/2) (a+1/2)) : deriv ψ t=2*deriv b t := by
    have he := circlePeriodize_eventuallyEq b.hasCompactSupport hbs ht
    have hd := (circlePeriodize_contDiff b.contDiff b.hasCompactSupport).differentiable (by simp)
    dsimp only [ψ]
    rw [deriv_sub_const,deriv_const_mul 2 (hd t),he.deriv_eq]
  have he (t : ℝ) (ht : t∈Icc (a-1/2) (a+1/2)) :
      K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ))=
        2*(Ioi a).indicator (deriv b) t := by
    by_cases hs : t∈tsupport (b : ℝ → ℝ)
    · have hph := hphase t (hbr hs)
      by_cases hat : a<t
      · rw [Set.indicator_of_mem (hph.mpr hat),Set.indicator_of_mem (show t∈Ioi a from hat)]
        exact hd t ht
      · rw [Set.indicator_of_notMem (mt hph.mp hat),Set.indicator_of_notMem (show t∉Ioi a from hat),mul_zero]
    · have hz := deriv_of_notMem_tsupport hs
      have hz' : (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ))=0 := by
        change deriv ψ t=0
        rw [hd t ht,hz,mul_zero]
      rw [Set.indicator_apply,Set.indicator_apply]
      split_ifs <;> simp_all only [mul_zero]
  have hflux : (∫ t in (a-1/2)..(a-1/2)+1,
      K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ)))= -2 := by
    rw [show a-1/2+1=a+1/2 by ring]
    rw [intervalIntegral.integral_congr (fun t ht ↦ he t (by
      simpa only [uIcc_of_le (show a-1/2≤a+1/2 by linarith)] using ht)),
      intervalIntegral.integral_const_mul]
    have hi : (∫ t in (a-1/2)..a+1/2,(Ioi a).indicator (deriv b) t)= -1 := by
      rw [intervalIntegral.integral_of_le (by linarith),integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi]
      have hset : Ioi a ∩ Ioc (a-1/2) (a+1/2)=Ioc a (a+1/2) := by
        ext t
        simp only [Set.mem_inter_iff,Set.mem_Ioi,Set.mem_Ioc]
        constructor
        · rintro ⟨h1,h2,h3⟩; exact ⟨h1,h3⟩
        · rintro ⟨h1,h2⟩; exact ⟨h1,by linarith,h2⟩
      rw [hset,← intervalIntegral.integral_of_le (show a≤a+1/2 by linarith)]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ ↦ (hbc.differentiable (by simp)).differentiableAt.hasDerivAt)
        ((hbc.continuous_deriv (by simp)).intervalIntegrable _ _)]
      rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by dsimp [b]; positivity)),
        b.zero_of_le_dist]
      · norm_num
      · change R≤dist (a+1/2) a
        rw [Real.dist_eq,show a+1/2-a=(1/2 : ℝ) by ring,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
        exact hRh.le
    rw [hi]
    norm_num
  have hh := integerCharacter_directional_variation hm hK hP hψ hp hb (a-1/2)
  rw [hflux] at hh
  simpa only [abs_neg,abs_of_pos (by norm_num : (0 : ℝ)<2),mul_comm] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem circle_hat_calibration {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hP : perimeter ((integerCharacter m) ⁻¹' K)≠⊤)
    {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbi : Integrable b volume)
    (hb0 : ∀ t,0≤b t) (hb1 : ∫ t,b t=1)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a≤c)
    (hshort : c-a+2*r<1) :
    2*‖latticeVector m‖ * |(∫ t : ℝ, K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*b (t-a))-
      ∫ t : ℝ,K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*b (t-c)| ≤
        (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  classical
  let f : ℝ → ℝ := fun t ↦ K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))
  have hf : Measurable f := ((measurable_const.indicator hK).comp
    QuotientAddGroup.continuous_mk.measurable)
  have hf1 (t : ℝ) : |f t|≤1 := by simp only [f,Set.indicator_apply]; split_ifs <;> norm_num
  let H := intervalSmoothHat b a c
  let d := (a+c)/2
  have hHs : tsupport H ⊆ Ioo (d-1/2) (d+1/2) := by
    apply (intervalSmoothHat_support hb.continuous hs hac).trans
    intro x hx
    dsimp only [d]
    constructor <;> linarith [hx.1,hx.2]
  have hHc : HasCompactSupport H := by
    apply IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H)
    exact (intervalSmoothHat_support hb.continuous hs hac)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := intervalSmoothHat_contDiff hb a c
  let ψ : ℝ → ℝ := fun t ↦ 2*circlePeriodize H t-1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (contDiff_const.mul (circlePeriodize_contDiff hH hHc)).sub contDiff_const
  have hp : Function.Periodic ψ 1 := fun t ↦ by
    dsimp only [ψ]
    rw [circlePeriodize_periodic H t]
  have hbψ (t : ℝ) : |ψ t|≤1 := by
    have hh := circlePeriodize_unit_bounds hHs (fun t ↦
      ⟨intervalSmoothHat_nonneg hb.continuous hb0 hac t,
        intervalSmoothHat_le_one hb.continuous hbi hb0 hb1 hac t⟩) t
    apply abs_le.mpr
    dsimp only [ψ]
    constructor <;> linarith [hh.1,hh.2]
  have hd (t : ℝ) (ht : t∈Icc (d-1/2) (d+1/2)) : deriv ψ t=2*deriv H t := by
    have he := circlePeriodize_eventuallyEq hHc hHs ht
    dsimp only [ψ]
    rw [deriv_sub_const,deriv_const_mul 2
      ((circlePeriodize_contDiff hH hHc).differentiable (by simp) t),he.deriv_eq]
  have hint : (∫ t in (d-1/2)..(d-1/2)+1,
      K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ)))=
      2*((∫ t : ℝ,f t*b (t-a))-∫ t : ℝ,f t*b (t-c)) := by
    rw [show d-1/2+1=d+1/2 by ring]
    have hi : (∫ t in (d-1/2)..d+1/2,f t*deriv H t)=∫ t : ℝ,f t*deriv H t := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hn : t∉tsupport H := by
        intro hh
        exact ht ⟨(hHs hh).1,(hHs hh).2.le⟩
      rw [deriv_of_notMem_tsupport hn,mul_zero]
    calc
      _ = 2*(∫ t in (d-1/2)..d+1/2,f t*deriv H t) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t∈Icc (d-1/2) (d+1/2) := by
          simpa only [uIcc_of_le (show d-1/2≤d+1/2 by linarith)] using ht
        change K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ))=2*(f t*deriv H t)
        by_cases hk : (t : AddCircle (1 : ℝ))∈K
        · rw [Set.indicator_of_mem hk]
          change deriv ψ t=2*(K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*deriv H t)
          rw [Set.indicator_of_mem hk,one_mul,hd t ht']
        · rw [Set.indicator_of_notMem hk]
          change 0=2*(K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*deriv H t)
          rw [Set.indicator_of_notMem hk,zero_mul,mul_zero]
      _ = _ := by
        rw [hi]
        have he (t : ℝ) : deriv H t=b (t-a)-b (t-c) :=
          (intervalSmoothHat_hasDerivAt hb.continuous a c t).deriv
        simp_rw [he,mul_sub]
        rw [integral_sub (bounded_mul_shift_integrable hf hf1 hbi a)
          (bounded_mul_shift_integrable hf hf1 hbi c)]
        ring
  have hh := integerCharacter_directional_variation hm hK hP hψ hp hbψ (d-1/2)
  rw [hint,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hh
  convert hh using 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem circle_nontrivial_phase_lower_bound {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hpos : volume K≠0) (hneg : volume Kᶜ≠0)
    (hP : perimeter ((integerCharacter m) ⁻¹' K)≠⊤) :
    2*‖latticeVector m‖ ≤ (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  classical
  let f : ℝ → ℝ := fun t ↦ K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))
  have hf : Measurable f := (measurable_const.indicator hK).comp
    QuotientAddGroup.continuous_mk.measurable
  have hf1 (t : ℝ) : |f t|≤1 := by
    simp only [f,Set.indicator_apply]
    split_ifs <;> norm_num
  let G (x : ℝ) := Tendsto
    (fun n ↦ ∫ t : ℝ,f t*(angularMollifier n).normed volume (t-x)) atTop (𝓝 (f x))
  have hg : ∀ᵐ x : ℝ ∂volume,G x ∧ x≠1 := by
    have hn : ∀ᵐ x : ℝ ∂volume,x≠1 := by
      rw [ae_iff]
      simp only [not_not]
      convert (measure_singleton (μ := volume) (1 : ℝ)) using 1
      congr 1
    filter_upwards [angular_smoothing_ae_tendsto hf hf1,hn] with x hx hn
    exact ⟨hx,hn⟩
  have hpos' : volume ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K ∩ Ioc 0 1)≠0 := by
    have hh := hpos
    rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0 hK] at hh
    simpa only [zero_add] using hh
  have hneg' : volume ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' Kᶜ ∩ Ioc 0 1)≠0 := by
    have hh := hneg
    rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0 hK.compl] at hh
    simpa only [zero_add] using hh
  obtain ⟨x,hx,hgx,hx1⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos' (ae_restrict_of_ae hg)
  obtain ⟨y,hy,hgy,hy1⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hneg' (ae_restrict_of_ae hg)
  have hxval : f x=1 := Set.indicator_of_mem (show (x : AddCircle (1 : ℝ))∈K from hx.1) _
  have hyval : f y=0 := Set.indicator_of_notMem (show (y : AddCircle (1 : ℝ))∉K from hy.1) _
  have hxi : x∈Ioo (0 : ℝ) 1 := ⟨hx.2.1,lt_of_le_of_ne hx.2.2 hx1⟩
  have hyi : y∈Ioo (0 : ℝ) 1 := ⟨hy.2.1,lt_of_le_of_ne hy.2.2 hy1⟩
  have hbound (a c : ℝ) (hac : a≤c) (hshort : c-a<1) (ha : G a) (hc : G c) :
      2*‖latticeVector m‖*|f a-f c| ≤ (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
    have ht := ((ha.sub hc).abs).const_mul (2*‖latticeVector m‖)
    apply le_of_tendsto ht
    have hrad : ∀ᶠ n : ℕ in atTop,(angularMollifier n).rOut<(1-(c-a))/2 :=
      (tendsto_order.mp angularMollifier_radius_tendsto).2 _ (by linarith)
    filter_upwards [hrad] with n hn
    apply circle_hat_calibration hm hK hP (angularMollifier n).contDiff_normed
      (angularMollifier n).integrable_normed (angularMollifier n).nonneg_normed
      (angularMollifier n).integral_normed (r := (angularMollifier n).rOut) ?_ hac (by linarith)
    rw [(angularMollifier n).tsupport_normed_eq,Real.closedBall_eq_Icc]
    simp only [zero_sub,zero_add,Subset.refl]
  rcases le_total x y with hxy|hyx
  · have hh := hbound x y hxy (by linarith [hxi.1,hyi.2]) hgx hgy
    simpa only [hxval,hyval,sub_zero,abs_one,mul_one] using hh
  · have hh := hbound y x hyx (by linarith [hyi.1,hxi.2]) hgy hgx
    simpa only [hxval,hyval,zero_sub,abs_neg,abs_one,mul_one] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integer_lattice_norm_ge_one {m : Fin 3 → ℤ} (hm : m≠0) : 1≤‖latticeVector m‖ := by
  have hi : ∃ i,m i≠0 := by
    by_contra hn
    push Not at hn
    exact hm (funext hn)
  obtain ⟨i,hi⟩ := hi
  have hz : (1 : ℤ)≤|m i| := by
    have hh := abs_pos.mpr hi
    omega
  have hz' : (1 : ℝ)≤|(m i : ℝ)| := by exact_mod_cast hz
  have hh := PiLp.norm_apply_le (latticeVector m) i
  simp only [latticeVector,WithLp.ofLp_toLp,Real.norm_eq_abs] at hh
  exact hz'.trans hh

theorem Periodic.isMinimizerAt_connected_or_unit_integer_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      (perimeter E=2 ∧ ∃ (m : Fin 3 → ℤ) (K : Set (AddCircle (1 : ℝ))),m≠0 ∧
        ‖latticeVector m‖=1 ∧ IsOpen K ∧ openRepresentative E=(integerCharacter m) ⁻¹' K ∧
        volume K=ENNReal.ofReal V) := by
  rcases Periodic.isMinimizerAt_connected_or_circle_phase hV hE hmin with hconn|
    ⟨m,K,hm,hK,he,hvol⟩
  · exact Or.inl hconn
  have hper : perimeter ((integerCharacter m) ⁻¹' K)=perimeter E := by
    rw [← he]
    exact perimeter_congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin)
  have hpos : volume K≠0 := by rw [hvol]; exact (ENNReal.ofReal_pos.mpr hV.1).ne'
  have hneg : volume Kᶜ≠0 := by
    rw [measure_compl hK.measurableSet (measure_ne_top _ _),hvol]
    have hv : ENNReal.ofReal V<(1 : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr hV.2
    simpa only [measure_univ] using tsub_pos_iff_lt.mpr hv |>.ne'
  have hlo := circle_nontrivial_phase_lower_bound hm hK.measurableSet hpos hneg
    (hper ▸ hmin.1.2.ne)
  rw [hper] at hlo
  have hupper : perimeter E≤2 :=
    (hmin.2.2 (stripe V) (finitePerimeter_stripe ⟨hV.1.le,hV.2.le⟩)
      (volume_stripe ⟨hV.1.le,hV.2.le⟩)).trans (perimeter_stripe_le ⟨hV.1.le,hV.2.le⟩)
  have hup : (perimeter E).toReal≤2 := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞)≠⊤) hupper
  have hnorm := integer_lattice_norm_ge_one hm
  have heq : (perimeter E).toReal=2 := by linarith
  have hper2 : perimeter E=2 := by
    rw [← ENNReal.ofReal_toReal hmin.1.2.ne,heq]
    norm_num
  exact Or.inr ⟨hper2,m,K,hm,by linarith,hK,he,hvol⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integer_lattice_norm_one_coordinate {m : Fin 3 → ℤ} (hn : ‖latticeVector m‖=1) :
    ∃ i : Fin 3,m=Pi.single i 1 ∨ m=Pi.single i (-1) := by
  classical
  have hm : m≠0 := by intro h; rw [h,latticeVector_zero,norm_zero] at hn; norm_num at hn
  have hi : ∃ i,m i≠0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  obtain ⟨i,hi⟩ := hi
  have hs : ∑ j : Fin 3,(m j : ℝ)^2=1 := by
    have hh := (EuclideanSpace.real_norm_sq_eq (latticeVector m)).symm
    rw [hn,one_pow] at hh
    simpa only [latticeVector,WithLp.ofLp_toLp] using hh
  have hmi : |(m i : ℝ)|=1 := by
    have hz : (1 : ℤ)≤|m i| := by have hh := abs_pos.mpr hi; omega
    have hz' : (1 : ℝ)≤|(m i : ℝ)| := by exact_mod_cast hz
    have hh := PiLp.norm_apply_le (latticeVector m) i
    rw [hn] at hh
    simp only [latticeVector,WithLp.ofLp_toLp,Real.norm_eq_abs] at hh
    exact le_antisymm hh hz'
  have hmisq : (m i : ℝ)^2=1 := by nlinarith [sq_abs (m i : ℝ)]
  have herase : ∑ j∈Finset.univ.erase i,(m j : ℝ)^2=0 := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 3)) (fun j ↦ (m j : ℝ)^2)
      (Finset.mem_univ i)
    linarith
  have hz (j : Fin 3) (hji : j≠i) : m j=0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (m j : ℝ))).mp herase
      j (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
    exact_mod_cast sq_eq_zero_iff.mp hh
  have hi' : m i=1 ∨ m i= -1 := by
    have hh : (m i : ℝ)=1 ∨ (m i : ℝ)= -1 := (abs_eq (by norm_num : (0 : ℝ)≤1)).mp hmi
    exact_mod_cast hh
  refine ⟨i,?_⟩
  rcases hi' with hi'|hi'
  · left
    ext j
    by_cases hji : j=i
    · subst j; simpa only [Pi.single_eq_same] using hi'
    · rw [Pi.single_eq_of_ne hji,hz j hji]
  · right
    ext j
    by_cases hji : j=i
    · subst j; simpa only [Pi.single_eq_same] using hi'
    · rw [Pi.single_eq_of_ne hji,hz j hji]

theorem Periodic.isMinimizerAt_connected_or_coordinate_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      (perimeter E=2 ∧ ∃ (i : Fin 3) (m : Fin 3 → ℤ) (K : Set (AddCircle (1 : ℝ))),
        (m=Pi.single i 1 ∨ m=Pi.single i (-1)) ∧ IsOpen K ∧
        openRepresentative E=(integerCharacter m) ⁻¹' K ∧ volume K=ENNReal.ofReal V) := by
  let F := toMeasurable torusVolume E
  have hae : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hae).mpr hmin
  have hrep : openRepresentative F=openRepresentative E := by
    unfold openRepresentative
    have hc : Fᶜ =ᵐ[torusVolume] Eᶜ := by
      filter_upwards [hae] with z hz
      exact congrArg Not hz
    exact congrArg (fun A : Set Torus ↦ Aᶜ) (volumeSupport_congr_ae hc)
  have hp : perimeter F=perimeter E := perimeter_congr_ae hae
  rcases Periodic.isMinimizerAt_connected_or_unit_integer_phase hV hF hmF with hc|
    ⟨hper,m,K,hm,hn,hK,he,hvol⟩
  · exact Or.inl (hrep ▸ hc)
  obtain ⟨i,hi⟩ := integer_lattice_norm_one_coordinate hn
  exact Or.inr ⟨hp ▸ hper,i,m,K,hi,hK,hrep ▸ he,hvol⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circlePeriodize_abs_le_one {f : ℝ → ℝ} {a : ℝ}
    (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    (hb : ∀ x,|f x|≤1) (x : ℝ) : |circlePeriodize f x|≤1 := by
  classical
  by_cases hn : ∃ n : ℤ,f (x+n)≠0
  · obtain ⟨n,hn⟩ := hn
    have huniq (m : ℤ) (hm : m≠n) : f (x+m)=0 := by
      by_contra hm'
      have h1 := hs (subset_tsupport f hn)
      have h2 := hs (subset_tsupport f hm')
      have hlo : (-1 : ℝ)<(m-n : ℤ) := by push_cast; linarith [h1.2,h2.1]
      have hhi : ((m-n : ℤ) : ℝ)<1 := by push_cast; linarith [h1.1,h2.2]
      have hlo' : (-1 : ℤ) < m-n := by exact_mod_cast hlo
      have hhi' : m-n<1 := by exact_mod_cast hhi
      omega
    rw [circlePeriodize,tsum_eq_single n huniq]
    exact hb _
  · push Not at hn
    simp only [circlePeriodize,hn,tsum_zero,abs_zero,zero_le_one]

theorem circle_compact_calibration {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hP : perimeter ((integerCharacter m) ⁻¹' K)≠⊤)
    {H : ℝ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H)
    {a : ℝ} (hs : tsupport H ⊆ Ioo (a-1/2) (a+1/2)) (hb : ∀ t,|H t|≤1) :
    ‖latticeVector m‖*|∫ t : ℝ,K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*
      deriv H t| ≤ (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  let ψ := circlePeriodize H
  have hp : Function.Periodic ψ 1 := circlePeriodize_periodic H
  have hd (t : ℝ) (ht : t∈Icc (a-1/2) (a+1/2)) : deriv ψ t=deriv H t :=
    (circlePeriodize_eventuallyEq hHc hs ht).deriv_eq
  have hi : (∫ t in (a-1/2)..(a-1/2)+1,
      K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ))) =
      ∫ t : ℝ,K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*deriv H t := by
    rw [show a-1/2+1=a+1/2 by ring]
    calc
      _ = ∫ t in (a-1/2)..a+1/2,K.indicator (fun _ ↦ (1 : ℝ))
          (t : AddCircle (1 : ℝ))*deriv H t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t∈Icc (a-1/2) (a+1/2) := by
          simpa only [uIcc_of_le (show a-1/2≤a+1/2 by linarith)] using ht
        change K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ)) =
          K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*deriv H t
        by_cases hk : (t : AddCircle (1 : ℝ))∈K
        · rw [Set.indicator_of_mem hk,Set.indicator_of_mem hk,one_mul]
          exact hd t ht'
        · rw [Set.indicator_of_notMem hk,Set.indicator_of_notMem hk,zero_mul]
      _ = _ := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro t ht
        have hn : t∉tsupport H := fun hh ↦ ht ⟨(hs hh).1,(hs hh).2.le⟩
        rw [deriv_of_notMem_tsupport hn,mul_zero]
  have hh := integerCharacter_directional_variation hm hK hP
    (circlePeriodize_contDiff hH hHc) hp (circlePeriodize_abs_le_one hs hb) (a-1/2)
  rwa [hi] at hh

theorem circle_good_partition_variation {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hP : perimeter ((integerCharacter m) ⁻¹' K)≠⊤)
    (u : ℕ → ℝ) (hu : Monotone u) {a c : ℝ} (hus : ∀ i,u i∈Icc a c)
    (hshort : c-a<1) (n : ℕ)
    (hg : ∀ i,Tendsto (fun j ↦ ∫ t : ℝ,
      K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*
        (angularMollifier j).normed volume (t-u i)) atTop
      (𝓝 (K.indicator (fun _ ↦ (1 : ℝ)) (u i : AddCircle (1 : ℝ))))) :
    ‖latticeVector m‖*(∑ i∈Finset.range n,
      |K.indicator (fun _ ↦ (1 : ℝ)) (u i : AddCircle (1 : ℝ))-
        K.indicator (fun _ ↦ (1 : ℝ)) (u (i+1) : AddCircle (1 : ℝ))|) ≤
      (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  classical
  let f : ℝ → ℝ := fun t ↦ K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))
  have hf : Measurable f := (measurable_const.indicator hK).comp
    QuotientAddGroup.continuous_mk.measurable
  have hf1 (t : ℝ) : |f t|≤1 := by
    simp only [f,Set.indicator_apply]; split_ifs <;> norm_num
  let σ : ℕ → ℝ := fun i ↦ if 0≤f (u i)-f (u (i+1)) then 1 else -1
  have hσ (i : ℕ) : |σ i|≤1 := by dsimp [σ]; split_ifs <;> norm_num
  have he (i : ℕ) : σ i*(f (u i)-f (u (i+1)))=|f (u i)-f (u (i+1))| := by
    dsimp [σ]
    split_ifs with h
    · rw [one_mul,abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have ht := ((tendsto_finsetSum (Finset.range n) (fun i _ ↦
    ((hg i).sub (hg (i+1))).const_mul (σ i))).abs).const_mul ‖latticeVector m‖
  have hlim : ‖latticeVector m‖*|∑ i∈Finset.range n,σ i*(f (u i)-f (u (i+1)))| =
      ‖latticeVector m‖*∑ i∈Finset.range n,|f (u i)-f (u (i+1))| := by
    simp_rw [he]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ ↦ abs_nonneg _))]
  change Tendsto _ _ (𝓝 (‖latticeVector m‖*|∑ i∈Finset.range n,
    σ i*(f (u i)-f (u (i+1)))|)) at ht
  rw [hlim] at ht
  apply le_of_tendsto ht
  have hrad : ∀ᶠ j : ℕ in atTop,(angularMollifier j).rOut<(1-(c-a))/2 :=
    (tendsto_order.mp angularMollifier_radius_tendsto).2 _ (by linarith)
  filter_upwards [hrad] with j hj
  let b := (angularMollifier j).normed volume
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := (angularMollifier j).contDiff_normed
  let H := partitionSmoothTest b u σ n
  have hsub : tsupport H ⊆ Icc (a-(angularMollifier j).rOut) (c+(angularMollifier j).rOut) := by
    apply partitionSmoothTest_support hb.continuous _ hu hus
    rw [(angularMollifier j).tsupport_normed_eq,Real.closedBall_eq_Icc]
    simp only [zero_sub,zero_add,Subset.refl]
  have hHc : HasCompactSupport H :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H) hsub
  have hHs : tsupport H ⊆ Ioo ((a+c)/2-1/2) ((a+c)/2+1/2) := by
    intro t ht
    have hh := hsub ht
    constructor <;> linarith [hh.1,hh.2]
  have hh := circle_compact_calibration hm hK hP
    (partitionSmoothTest_contDiff hb u σ n) hHc hHs
    (partitionSmoothTest_bound hb.continuous
      (angularMollifier j).integrable_normed (angularMollifier j).nonneg_normed
      (angularMollifier j).integral_normed hu hσ n)
  rw [partitionSmoothTest_flux hf hf1 hb.continuous
    (angularMollifier j).integrable_normed] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def circlePhaseGood (K : Set (AddCircle (1 : ℝ))) (x : ℝ) : Prop :=
  Tendsto (fun n ↦ ∫ t : ℝ,K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*
    (angularMollifier n).normed volume (t-x)) atTop
    (𝓝 (K.indicator (fun _ ↦ (1 : ℝ)) (x : AddCircle (1 : ℝ))))

lemma circlePhaseGood_ae {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K) :
    ∀ᵐ x : ℝ ∂volume,circlePhaseGood K x := by
  apply angular_smoothing_ae_tendsto
    ((measurable_const.indicator hK).comp QuotientAddGroup.continuous_mk.measurable)
  intro t
  change |K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))|≤1
  classical
  by_cases ht : (t : AddCircle (1 : ℝ))∈K
  · rw [Set.indicator_of_mem ht]; norm_num
  · rw [Set.indicator_of_notMem ht]; norm_num

theorem circle_no_four_alternations {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hn : ‖latticeVector m‖=1) (hP : perimeter ((integerCharacter m) ⁻¹' K)=2)
    {a b c d : ℝ} (hab : a≤b) (hbc : b≤c) (hcd : c≤d) (hshort : d-a<1)
    (ha : circlePhaseGood K a) (hb : circlePhaseGood K b)
    (hc : circlePhaseGood K c) (hd : circlePhaseGood K d)
    (ha0 : (a : AddCircle (1 : ℝ))∉K) (hb1 : (b : AddCircle (1 : ℝ))∈K)
    (hc0 : (c : AddCircle (1 : ℝ))∉K) (hd1 : (d : AddCircle (1 : ℝ))∈K) : False := by
  classical
  let u : ℕ → ℝ := fun i ↦ if i=0 then a else if i=1 then b else if i=2 then c else d
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases h0 : i=0
    · subst i; simpa [u] using hab
    by_cases h1 : i=1
    · subst i; simpa [u] using hbc
    by_cases h2 : i=2
    · subst i; simpa [u] using hcd
    simp only [u,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,
      ite_eq_right (by omega : i+1≠0),ite_eq_right (by omega : i+1≠1),
      ite_eq_right (by omega : i+1≠2),le_refl]
  have hus (i : ℕ) : u i∈Icc a d := by
    dsimp [u]
    split_ifs <;> constructor <;> linarith
  have hg (i : ℕ) : circlePhaseGood K (u i) := by
    dsimp [u]
    split_ifs <;> assumption
  have hh := circle_good_partition_variation hm hK (by rw [hP]; norm_num) u hu hus hshort 3 hg
  rw [hn,hP] at hh
  norm_num [Finset.sum_range_succ,u,Set.indicator_of_mem hb1,Set.indicator_of_mem hd1,
    Set.indicator_of_notMem ha0,Set.indicator_of_notMem hc0] at hh

end CubicTorus

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
