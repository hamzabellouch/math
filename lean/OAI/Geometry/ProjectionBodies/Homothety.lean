import OAI.Geometry.ProjectionBodies.BrunnMinkowski

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

lemma quantile_first_moment {l r : ℝ} {f Q : ℝ → ℝ}
    (hQc : Continuous Q) (hQ0 : Q 0=l) (hQ1 : Q 1=r)
    (hQd : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt Q (f (Q s))⁻¹ s)
    (hfp : ∀ s ∈ Ioo (0:ℝ) 1, 0 < f (Q s)) :
    (∫ s in (0:ℝ)..1, Q s)=(∫ x in l..r, x*f x) := by
  have hdu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), HasDerivAt Q (f (Q s))⁻¹ s := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using hQd
  have hpu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), 0 ≤ (f (Q s))⁻¹ := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using
      fun s hs => (inv_pos.mpr (hfp s hs)).le
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := fun x => x*f x) hQc.continuousOn hdu hpu
  rw [hQ0,hQ1] at he
  refine (intervalIntegral.integral_congr_ae_restrict ?_).trans he
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simp [(hfp s hs).ne']

/-- Equality in slice transport forces the two full marginal distributions to
be translates. In particular both projection endpoints differ by the difference
of their first moments. -/
theorem slice_transport_equality {m : ℕ} (hm : 0 < m) {a b l r L R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) (hlr : l<r) (hLR : L<R)
    {f g h : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo l r)) (hg : ContinuousOn g (Ioo L R))
    (hfi : IntervalIntegrable f volume l r) (hgi : IntervalIntegrable g volume L R)
    (hfp : ∀ x ∈ Ioo l r, 0 < f x) (hgp : ∀ x ∈ Ioo L R, 0 < g x)
    (hfI : (∫ x in l..r, f x)=1) (hgI : (∫ x in L..R, g x)=1)
    (hhi : IntervalIntegrable h volume (a*l+b*L) (a*r+b*R))
    (hbound : ∀ x ∈ Ioo l r, ∀ y ∈ Ioo L R,
      (a*(f x)^((m:ℝ)⁻¹)+b*(g y)^((m:ℝ)⁻¹))^m ≤ h (a*x+b*y))
    (hI : (∫ z in (a*l+b*L)..(a*r+b*R), h z)=1) :
    l-L=(∫ x in l..r, x*f x)-(∫ y in L..R, y*g y) ∧
    r-R=(∫ x in l..r, x*f x)-(∫ y in L..R, y*g y) := by
  obtain ⟨Q,hQc,hQ0,hQ1,hQmem,hQd⟩ := exists_interval_quantile hlr hf hfi hfp hfI
  obtain ⟨P,hPc,hP0,hP1,hPmem,hPd⟩ := exists_interval_quantile hLR hg hgi hgp hgI
  let z : ℝ → ℝ := fun s => a*Q s+b*P s
  let z' : ℝ → ℝ := fun s => a/(f (Q s))+b/(g (P s))
  have hzc : Continuous z := by dsimp [z]; fun_prop
  have hzd : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt z (z' s) s := by
    intro s hs
    convert ((hQd s hs).2.const_mul a).add ((hPd s hs).2.const_mul b) using 1
    all_goals rfl
  have hzp : ∀ s ∈ Ioo (0:ℝ) 1, 0<z' s := by
    intro s hs
    exact add_pos (div_pos ha (hfp _ (hQd s hs).1)) (div_pos hb (hgp _ (hPd s hs).1))
  have hz0 : z 0=a*l+b*L := by dsimp [z]; rw [hQ0,hP0]
  have hz1 : z 1=a*r+b*R := by dsimp [z]; rw [hQ1,hP1]
  have hzz : z 0 ≤ z 1 := by rw [hz0,hz1]; nlinarith
  have hhi : IntervalIntegrable h volume (z 0) (z 1) := by
    rwa [hz0,hz1]
  have hzdu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), HasDerivAt z (z' s) s := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using hzd
  have hzpu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), 0≤z' s := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using fun s hs => (hzp s hs).le
  have hint : IntervalIntegrable (fun s => h (z s)*z' s) volume 0 1 :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hzc.continuousOn hzdu hzpu).mpr hhi
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := h) hzc.continuousOn hzdu hzpu
  change (∫ s in (0:ℝ)..1, h (z s)*z' s) = _ at hsub
  have hpt : ∀ s ∈ Ioo (0:ℝ) 1, 1 ≤ h (z s)*z' s := by
    intro s hs
    let p := (f (Q s))^((m:ℝ)⁻¹)
    let q := (g (P s))^((m:ℝ)⁻¹)
    have hp : 0<p := Real.rpow_pos_of_pos (hfp _ (hQd s hs).1) _
    have hq : 0<q := Real.rpow_pos_of_pos (hgp _ (hPd s hs).1) _
    have hpm : p^m=f (Q s) := Real.rpow_inv_natCast_pow (hfp _ (hQd s hs).1).le hm.ne'
    have hqm : q^m=g (P s) := Real.rpow_inv_natCast_pow (hgp _ (hPd s hs).1).le hm.ne'
    have ht := (transport_scalar hm ha hb hab hp hq).1
    rw [hpm,hqm] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (hbound _ (hQd s hs).1 _ (hPd s hs).1) (hzp s hs).le)
  have hae : (fun _ : ℝ => (1:ℝ)) ≤ᵐ[volume.restrict (Icc (0:ℝ) 1)] (fun s => h (z s)*z' s) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ hpt)
  have hInt : (∫ s in Icc (0:ℝ) 1, h (z s)*z' s)=1 := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      hsub,hz0,hz1,hI]
  have hOne : (∫ _ in Icc (0:ℝ) 1, (1:ℝ))=1 := by simp
  have hAe : (fun _ : ℝ => (1:ℝ)) =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      (fun s => h (z s)*z' s) :=
    (integral_eq_iff_of_ae_le (integrableOn_const isCompact_Icc.measure_ne_top)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hint) hae).mp
        (hOne.trans hInt.symm)
  have hAe' : (fun s => f (Q s)) =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] (fun s => g (P s)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc] at hAe
    filter_upwards [hAe,ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    let p := (f (Q s))^((m:ℝ)⁻¹)
    let q := (g (P s))^((m:ℝ)⁻¹)
    have hp : 0 < p := Real.rpow_pos_of_pos (hfp _ (hQd s hsmem).1) _
    have hq : 0 < q := Real.rpow_pos_of_pos (hgp _ (hPd s hsmem).1) _
    have hpm : p^m=f (Q s) := Real.rpow_inv_natCast_pow (hfp _ (hQd s hsmem).1).le hm.ne'
    have hqm : q^m=g (P s) := Real.rpow_inv_natCast_pow (hgp _ (hPd s hsmem).1).le hm.ne'
    have ht := transport_scalar hm ha hb hab hp hq
    have hle : (a*p+b*q)^m*(a/(p^m)+b/(q^m)) ≤ 1 := by
      rw [hpm,hqm,hs]
      exact mul_le_mul_of_nonneg_right (hbound _ (hQd s hsmem).1 _ (hPd s hsmem).1) (hzp s hsmem).le
    have hpq : p=q := ht.2.mp (le_antisymm hle ht.1)
    exact hpm.symm.trans ((congrArg (fun x : ℝ => x^m) hpq).trans hqm)
  have hfg : EqOn (fun s => f (Q s)) (fun s => g (P s)) (Ioo (0:ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq hAe' isOpen_Ioo
      (hf.comp hQc.continuousOn (fun s hs => (hQd s hs).1))
      (hg.comp hPc.continuousOn (fun s hs => (hPd s hs).1))
  obtain ⟨c,hc⟩ := IsOpen.exists_eq_add_of_deriv_eq isOpen_Ioo (convex_Ioo (0:ℝ) 1).isPreconnected
    (fun s hs => (hQd s hs).2.differentiableAt.differentiableWithinAt)
    (fun s hs => (hPd s hs).2.differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hQd s hs).2.deriv,(hPd s hs).2.deriv]
      exact congrArg Inv.inv (hfg hs))
  have hcc : EqOn Q (fun s => P s+c) (Icc (0:ℝ) 1) := by
    simpa only [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] using hc.closure hQc (hPc.add continuous_const)
  have hQInt := quantile_first_moment hQc hQ0 hQ1 (fun s hs => (hQd s hs).2)
    (fun s hs => hfp _ (hQd s hs).1)
  have hPInt := quantile_first_moment hPc hP0 hP1 (fun s hs => (hPd s hs).2)
    (fun s hs => hgp _ (hPd s hs).1)
  have hcInt : (∫ s in (0:ℝ)..1, Q s)=(∫ s in (0:ℝ)..1, P s)+c := by
    rw [intervalIntegral.integral_congr (fun s hs => hcc (by simpa only [uIcc_of_le zero_le_one] using hs)),
      intervalIntegral.integral_add (hPc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  have hc0 := hcc (show (0:ℝ) ∈ Icc 0 1 by norm_num)
  have hc1 := hcc (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  dsimp only at hc0 hc1
  rw [hQ0,hP0] at hc0
  rw [hQ1,hP1] at hc1
  rw [hQInt,hPInt] at hcInt
  constructor <;> linarith

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_moment_indicator {K : Set (E × ℝ)} (hK : IsCompact K) (s : ℝ) :
    (∫ x : E, K.indicator Prod.snd (x,s))=s*sliceDensity K s := by
  have he : (fun x : E => K.indicator Prod.snd (x,s)) =
      (horizontalSlice K s).indicator (fun _ => s) := by
    funext x
    by_cases hx : (x,s) ∈ K
    · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (show x ∈ horizontalSlice K s from hx)]
    · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show x ∉ horizontalSlice K s from hx)]
  rw [he,integral_indicator (horizontalSlice_compact hK s).measurableSet,setIntegral_const]
  simp only [smul_eq_mul,sliceDensity,mul_comm]

lemma sliceDensity_moment_integrable {K : Set (E × ℝ)} (hK : IsCompact K) :
    Integrable (fun s => s*sliceDensity K s) := by
  have hi : Integrable (K.indicator Prod.snd) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (continuous_snd.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  exact hi.integral_prod_right.congr (Eventually.of_forall fun s => sliceDensity_moment_indicator hK s)

lemma sliceDensity_moment {K : Set (E × ℝ)} (hK : IsCompact K) :
    (∫ s, s*sliceDensity K s)=(∫ x in K, x.2) := by
  have hi : Integrable (K.indicator Prod.snd) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (continuous_snd.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have he := integral_prod_symm (K.indicator Prod.snd) hi
  simp_rw [sliceDensity_moment_indicator hK] at he
  rw [← he,← Measure.volume_eq_prod,integral_indicator hK.measurableSet]

lemma sliceDensity_interval_moment {K : Set (E × ℝ)} (hK : IsCompact K) {l r : ℝ}
    (hlr : l≤r) (hp : Prod.snd '' K ⊆ Icc l r) :
    (∫ s in l..r, s*sliceDensity K s)=(∫ x in K, x.2) := by
  rw [intervalIntegral.integral_of_le hlr,← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact sliceDensity_moment hK
  · intro s hs
    rw [sliceDensity_zero_of_notMem (fun h => hs (hp h)),mul_zero]

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Equality in the actual product-body step identifies both extreme heights
with the difference of the (unit-volume) vertical first moments. -/
theorem brunnMinkowski_product_unit_equality {m : ℕ} (hm0 : 0 < m) (hm : BrunnMinkowskiRoot E m)
    {K M : Set (E × ℝ)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) (hvK : volume.real K=1) (hvM : volume.real M=1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hvC : volume.real (a • K+b • M)=1)
    {l r L R : ℝ} (hlr : l<r) (hLR : L<R)
    (hpr : Prod.snd '' K=Icc l r) (hPR : Prod.snd '' M=Icc L R) :
    l-L=(∫ x in K, x.2)-(∫ x in M, x.2) ∧
    r-R=(∫ x in K, x.2)-(∫ x in M, x.2) := by
  have hl : l ∈ Prod.snd '' K := by rw [hpr]; exact left_mem_Icc.mpr hlr.le
  have hr : r ∈ Prod.snd '' K := by rw [hpr]; exact right_mem_Icc.mpr hlr.le
  have hL : L ∈ Prod.snd '' M := by rw [hPR]; exact left_mem_Icc.mpr hLR.le
  have hR : R ∈ Prod.snd '' M := by rw [hPR]; exact right_mem_Icc.mpr hLR.le
  have hC : IsCompact (a • K+b • M) := (hK.smul a).add (hM.smul b)
  have hbounds : Prod.snd '' (a • K+b • M) ⊆ Icc (a*l+b*L) (a*r+b*R) := by
    rintro s ⟨_,⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩,rfl⟩
    have hx' : x.2 ∈ Icc l r := by rw [← hpr]; exact mem_image_of_mem _ hx
    have hy' : y.2 ∈ Icc L R := by rw [← hPR]; exact mem_image_of_mem _ hy
    change a*l+b*L ≤ a*x.2+b*y.2 ∧ a*x.2+b*y.2 ≤ a*r+b*R
    exact ⟨add_le_add (mul_le_mul_of_nonneg_left hx'.1 ha.le) (mul_le_mul_of_nonneg_left hy'.1 hb.le),
      add_le_add (mul_le_mul_of_nonneg_left hx'.2 ha.le) (mul_le_mul_of_nonneg_left hy'.2 hb.le)⟩
  have hmain : l-L=(∫ s in l..r, s*sliceDensity K s)-(∫ t in L..R, t*sliceDensity M t) ∧
      r-R=(∫ s in l..r, s*sliceDensity K s)-(∫ t in L..R, t*sliceDensity M t) := by
    apply slice_transport_equality hm0 ha hb hab hlr hLR
      (sliceDensity_continuous hm0 hm hK hcK hiK hl hr)
      (sliceDensity_continuous hm0 hm hM hcM hiM hL hR)
      (sliceDensity_integrable hK).intervalIntegrable
      (sliceDensity_integrable hM).intervalIntegrable
      (fun s hs => sliceDensity_pos hK hcK hiK hl hr hs)
      (fun s hs => sliceDensity_pos hM hcM hiM hL hR hs)
    · rw [sliceDensity_interval_integral hK hlr.le (by rw [hpr]),hvK]
    · rw [sliceDensity_interval_integral hM hLR.le (by rw [hPR]),hvM]
    · exact (sliceDensity_integrable hC).intervalIntegrable
    · intro s hs t ht
      have hroot := hm (horizontalSlice K s) (horizontalSlice M t)
        (horizontalSlice_compact hK s) (horizontalSlice_convex hcK s)
        (horizontalSlice_interior_nonempty hcK hiK hl hr hs)
        (horizontalSlice_compact hM t) (horizontalSlice_convex hcM t)
        (horizontalSlice_interior_nonempty hcM hiM hL hR ht) a b ha.le hb.le hab
      have hf0 := sliceDensity_nonneg K s
      have hg0 := sliceDensity_nonneg M t
      have hroot' := pow_le_pow_left₀ (by positivity : 0 ≤ a*(sliceDensity K s)^((m:ℝ)⁻¹)+b*(sliceDensity M t)^((m:ℝ)⁻¹)) hroot m
      rw [Real.rpow_inv_natCast_pow measureReal_nonneg hm0.ne'] at hroot'
      exact hroot'.trans (measureReal_mono (horizontalSlice_minkowski_subset K M a b s t)
        (horizontalSlice_compact hC _).measure_ne_top)
    · rw [sliceDensity_interval_integral hC (by nlinarith) hbounds,hvC]
  rwa [sliceDensity_interval_moment hK hlr.le (by rw [hpr]),
    sliceDensity_interval_moment hM hLR.le (by rw [hPR])] at hmain

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Pointwise RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

/-- The unnormalized Euclidean first moment. It is the barycenter for unit
volume bodies, the only place where it is used below. -/
def firstMoment {n : ℕ} (K : Set (Space n)) : Space n := ∫ x in K, x

lemma shadowContinuousEquiv_inner {n : ℕ} (u : Sphere n)
    (z : perpendicular (u : Space n) × ℝ) :
    ⟪(u : Space n),shadowContinuousEquiv u z⟫=z.2 := by
  rw [shadowContinuousEquiv_apply,inner_add_right,perpendicular_inner,
    real_inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
  ring

lemma shadow_vertical_image {n : ℕ} (u : Sphere n) (K : Set (Space n)) :
    Prod.snd '' (shadowContinuousEquiv u ⁻¹' K)=(fun x => ⟪(u : Space n),x⟫) '' K := by
  ext s
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨shadowContinuousEquiv u z,hz,shadowContinuousEquiv_inner u z⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(shadowContinuousEquiv u).symm x,by simpa using hx,?_⟩
    rw [← shadowContinuousEquiv_inner u,ContinuousLinearEquiv.apply_symm_apply]

lemma shadow_firstMoment {n : ℕ} (u : Sphere n) {K : Set (Space n)} (hK : IsCompact K) :
    (∫ z in shadowContinuousEquiv u ⁻¹' K, z.2)=⟪(u : Space n),firstMoment K⟫ := by
  have he : MeasurePreserving (shadowContinuousEquiv u) := shadowMeasurableEquiv_measurePreserving u
  have hi := (he.restrict_preimage hK.measurableSet).integral_comp
    (shadowContinuousEquiv u).toHomeomorph.measurableEmbedding (fun x => ⟪(u : Space n),x⟫)
  simp_rw [shadowContinuousEquiv_inner] at hi
  rw [hi]
  exact integral_inner (continuous_id.continuousOn.integrableOn_compact hK) _

lemma perpendicular_finrank {n : ℕ} (u : Sphere n) :
    Module.finrank ℝ (perpendicular (u : Space n))=n-1 := by
  have hu : (u : Space n) ≠ 0 := by intro h; simpa [h] using norm_coe u
  have hr := (Submodule.span ℝ {(u : Space n)}).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hu] at hr
  have he : Module.finrank ℝ (Space n)=n := by simp [Space]
  rw [he] at hr
  change Module.finrank ℝ ((Submodule.span ℝ {(u : Space n)})ᗮ)=n-1
  omega

/-- Equality for an intermediate Minkowski combination of unit-volume bodies
identifies every directional support difference with the first-moment shift. -/
theorem brunnMinkowski_unit_support_equality {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) (hvK : volume.real K=1) (hvM : volume.real M=1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hvC : volume.real (a • K+b • M)=1) (u : Sphere n) :
    support K u-support M u=⟪(u : Space n),firstMoment K-firstMoment M⟫ := by
  let e := shadowContinuousEquiv u
  have he : MeasurePreserving e := shadowMeasurableEquiv_measurePreserving u
  have hPK : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hPM : IsCompact (e ⁻¹' M) := e.toHomeomorph.isCompact_preimage.mpr hM
  have hiPK : (interior (e ⁻¹' K)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' K)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiK
    exact ⟨e.symm x,by simpa using hx⟩
  have hiPM : (interior (e ⁻¹' M)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' M)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiM
    exact ⟨e.symm x,by simpa using hx⟩
  have hcPK := hcK.linear_preimage e.toLinearMap
  have hcPM := hcM.linear_preimage e.toLinearMap
  obtain ⟨l,r,hlr,hpr⟩ := vertical_projection_interval hPK hcPK hiPK
  obtain ⟨L,R,hLR,hPR⟩ := vertical_projection_interval hPM hcPM hiPM
  have hv (S : Set (Space n)) (hS : IsCompact S) : volume.real (e ⁻¹' S)=volume.real S :=
    congrArg ENNReal.toReal (he.measure_preimage hS.measurableSet.nullMeasurableSet)
  have hm0 : 0 < Module.finrank ℝ (perpendicular (u : Space n)) := by
    rw [perpendicular_finrank]; omega
  have heq := brunnMinkowski_product_unit_equality hm0 (brunnMinkowski_innerProduct hm0)
    hPK hcPK hiPK hPM hcPM hiPM ((hv K hK).trans hvK) ((hv M hM).trans hvM) ha hb hab
    (by rw [← linearEquiv_preimage_combo,hv _ ((hK.smul _).add (hM.smul _)),hvC]) hlr hLR hpr hPR
  have hr : support K u=r := by
    unfold support
    rw [← shadow_vertical_image u K,hpr,csSup_Icc hlr.le]
  have hR : support M u=R := by
    unfold support
    rw [← shadow_vertical_image u M,hPR,csSup_Icc hLR.le]
  rw [hr,hR,heq.2,inner_sub_right]
  change (∫ z in shadowContinuousEquiv u ⁻¹' K, z.2)-
      (∫ z in shadowContinuousEquiv u ⁻¹' M, z.2)=_
  rw [shadow_firstMoment u hK,shadow_firstMoment u hM]

lemma support_translate {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hKn : K.Nonempty) (c u : Space n) :
    support ((fun x => c+x) '' K) u=⟪u,c⟫+support K u := by
  apply le_antisymm
  · apply (support_le_iff (hK.image (by fun_prop)) (hKn.image _)).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [inner_add_right]
    exact add_le_add_right (inner_le_support hK hx u) _
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he,← inner_add_right]
    exact inner_le_support (hK.image (by fun_prop)) (mem_image_of_mem _ hx) u

/-- The unrestricted translated-body equality case of the unit-volume
Brunn--Minkowski inequality (no origin symmetry or boundary regularity). -/
theorem brunnMinkowski_unit_equality {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) (hvK : volume.real K=1) (hvM : volume.real M=1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hvC : volume.real (a • K+b • M)=1) :
    K=(fun x => firstMoment K-firstMoment M+x) '' M := by
  have hKn := hiK.mono interior_subset
  have hMn := hiM.mono interior_subset
  apply (support_eq_iff hK hcK hKn (hM.image (by fun_prop))
    (hcM.translate _) (hMn.image _)).mp
  funext x
  rw [support_translate hM hMn]
  by_cases hx : x=0
  · subst x
    simp [support,hKn,hMn]
  · let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
    have hxu : x=‖x‖ • (u : Space n) := by
      change x=‖x‖ • (‖x‖⁻¹ • x)
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]
    have he := brunnMinkowski_unit_support_equality hn hK hcK hiK hM hcM hiM hvK hvM ha hb hab hvC u
    rw [hxu,support_smul hK hKn (norm_nonneg x),support_smul hM hMn (norm_nonneg x),real_inner_smul_left]
    rw [← he]
    ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

def volumeRoot {n : ℕ} (K : Set (Space n)) : ℝ := (volume.real K)^((n:ℝ)⁻¹)

lemma volumeRoot_pos {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) : 0 < volumeRoot K :=
  Real.rpow_pos_of_pos (volumeReal_pos_of_body hK hi) _

lemma volumeRoot_pow {n : ℕ} (hn : 0 < n) (K : Set (Space n)) :
    volumeRoot K^n=volume.real K :=
  Real.rpow_inv_natCast_pow measureReal_nonneg hn.ne'

lemma volumeRoot_smul {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) (K : Set (Space n)) :
    volumeRoot (r • K)=r*volumeRoot K := by
  unfold volumeRoot
  rw [volumeReal_smul_nonneg hr]
  have hd : Module.finrank ℝ (Space n)=n := by simp [Space]
  rw [hd,Real.mul_rpow (pow_nonneg hr _) measureReal_nonneg,← Real.rpow_natCast,
    ← Real.rpow_mul hr, mul_inv_cancel₀ (by exact_mod_cast hn.ne'),Real.rpow_one]

lemma interior_add_nonempty_left {n : ℕ} {K M : Set (Space n)}
    (hiK : (interior K).Nonempty) (hM : M.Nonempty) : (interior (K+M)).Nonempty := by
  obtain ⟨y,hy⟩ := hM
  obtain ⟨x,hx⟩ := hiK
  refine ⟨x+y,?_⟩
  exact (isOpen_interior.add_right.subset_interior_iff.mpr
    (add_subset_add interior_subset Subset.rfl)) (add_mem_add hx hy)

/-- The homogeneous, additive form of Brunn--Minkowski. -/
theorem brunnMinkowski_add {n : ℕ} (hn : 0 < n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) :
    volumeRoot K+volumeRoot M ≤ volumeRoot (K+M) := by
  have h := brunnMinkowski_space hn K M hK hcK hiK hM hcM hiM
    (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
  change (1/2)*volumeRoot K+(1/2)*volumeRoot M ≤ volumeRoot ((1/2:ℝ) • K+(1/2:ℝ) • M) at h
  rw [← smul_add,volumeRoot_smul hn (by norm_num)] at h
  linarith

/-- Equality in the homogeneous additive form, retaining arbitrary translation. -/
theorem brunnMinkowski_add_equality {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty)
    (hv : volumeRoot (K+M)=volumeRoot K+volumeRoot M) :
    ∃ z : Space n, ∃ c : ℝ, 0 < c ∧ K=(fun x => z+c • x) '' M := by
  let p := volumeRoot K
  let q := volumeRoot M
  have hp : 0 < p := volumeRoot_pos hK hiK
  have hq : 0 < q := volumeRoot_pos hM hiM
  have hpq : 0 < p+q := add_pos hp hq
  have hd : Module.finrank ℝ (Space n)=n := by simp [Space]
  have hUK : volume.real (p⁻¹ • K)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hp.le),hd,inv_pow,volumeRoot_pow (by omega)]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hK hiK).ne'
  have hUM : volume.real (q⁻¹ • M)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hq.le),hd,inv_pow,volumeRoot_pow (by omega)]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hM hiM).ne'
  have hiUK : (interior (p⁻¹ • K)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hp.ne')]
    exact hiK.image _
  have hiUM : (interior (q⁻¹ • M)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hq.ne')]
    exact hiM.image _
  have hsets : (p/(p+q)) • (p⁻¹ • K)+(q/(p+q)) • (q⁻¹ • M)=(p+q)⁻¹ • (K+M) := by
    rw [smul_add,smul_smul,smul_smul]
    congr 2 <;> field_simp
  have hunit : volume.real ((p/(p+q)) • (p⁻¹ • K)+(q/(p+q)) • (q⁻¹ • M))=1 := by
    rw [hsets,volumeReal_smul_nonneg (inv_nonneg.mpr hpq.le),hd,inv_pow,
      ← volumeRoot_pow (by omega) (K+M),hv]
    exact inv_mul_cancel₀ (pow_ne_zero _ hpq.ne')
  have he := brunnMinkowski_unit_equality hn (hK.smul _) (hcK.smul _) hiUK
    (hM.smul _) (hcM.smul _) hiUM hUK hUM (div_pos hp hpq) (div_pos hq hpq)
    (by rw [← add_div,div_self hpq.ne']) hunit
  let d := firstMoment (p⁻¹ • K)-firstMoment (q⁻¹ • M)
  refine ⟨p • d,p/q,div_pos hp hq,?_⟩
  calc
    K = p • (p⁻¹ • K) := by rw [smul_smul,mul_inv_cancel₀ hp.ne',one_smul]
    _ = p • ((fun x => d+x) '' (q⁻¹ • M)) := by rw [he]
    _ = (fun x => p • d+(p/q) • x) '' M := by
      rw [← image_smul,image_image,← image_smul,image_image]
      congr 1
      funext x
      simp only [smul_add,smul_smul,div_eq_mul_inv]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

lemma minkowski_parameter_combo {n : ℕ} {K M : Set (Space n)}
    (hcK : Convex ℝ K) (hcM : Convex ℝ M) {s t a b : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a • (K+s • M)+b • (K+t • M)=K+(a*s+b*t) • M := by
  rw [smul_add,smul_add,smul_smul,smul_smul,add_add_add_comm,
    ← hcK.add_smul ha hb,hab,one_smul,← hcM.add_smul (mul_nonneg ha hs) (mul_nonneg hb ht)]

lemma minkowski_volumeRoot_concave {n : ℕ} (hn : 0 < n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hMn : M.Nonempty) : ConcaveOn ℝ (Ici 0) (fun t : ℝ => volumeRoot (K+t • M)) := by
  refine ⟨convex_Ici _,?_⟩
  intro s hs t ht a b ha hb hab
  have hSM : (s • M).Nonempty := hMn.image _
  have hTM : (t • M).Nonempty := hMn.image _
  have h := brunnMinkowski_space hn (K+s • M) (K+t • M)
    (hK.add (hM.smul _)) (hcK.add (hcM.smul _)) (interior_add_nonempty_left hiK hSM)
    (hK.add (hM.smul _)) (hcK.add (hcM.smul _)) (interior_add_nonempty_left hiK hTM) a b ha hb hab
  rw [minkowski_parameter_combo hcK hcM hs ht ha hb hab] at h
  exact h

lemma volumeRoot_diff_factor {n : ℕ} (hn : 0 < n) {K : Set (Space n)}
    (hv : 0 < volume.real K) :
    ((n:ℝ)*volumeRoot K^(n-1))*((n:ℝ)⁻¹*(volume.real K)^((n:ℝ)⁻¹-1))=1 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.rpow_sub hv,Real.rpow_one]
  change (n*volumeRoot K^(n-1))*((n:ℝ)⁻¹*(volumeRoot K/volume.real K))=1
  have hp : volumeRoot K^(n-1)*volumeRoot K=volume.real K := by
    rw [← pow_succ,Nat.sub_add_cancel hn,volumeRoot_pow hn]
  field_simp
  nlinarith [hp]

/-- The sharp first-variation inequality together with its global translated
homothety equality implication, derived from actual Brunn--Minkowski concavity. -/
theorem minkowski_derivative_bound_equality {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) {d : ℝ}
    (hd : HasDerivWithinAt (fun t : ℝ => volume.real (K+t • M)) d (Ici 0) 0) :
    (n:ℝ)*volumeRoot K^(n-1)*volumeRoot M ≤ d ∧
      (d=(n:ℝ)*volumeRoot K^(n-1)*volumeRoot M →
        ∃ z : Space n, ∃ c : ℝ, 0 < c ∧ K=(fun x => z+c • x) '' M) := by
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hMn := hiM.mono interior_subset
  have hzero : K+(0:ℝ) • M=K := by simp [zero_smul_set hMn]
  have hvK := volumeReal_pos_of_body hK hiK
  have hf := hd.rpow_const (p := (n:ℝ)⁻¹) (Or.inl (by rw [hzero]; exact hvK.ne'))
  rw [hzero] at hf
  have hc := minkowski_volumeRoot_concave hn0 hK hcK hiK hM hcM hMn
  have hs := hc.slope_le_of_hasDerivWithinAt (by norm_num : (0:ℝ) ∈ Ici 0) (by norm_num : (1:ℝ) ∈ Ici 0)
    (by norm_num : (0:ℝ) < 1) hf
  rw [slope_def_field,hzero,one_smul,sub_zero,div_one] at hs
  have hlow := brunnMinkowski_add hn0 hK hcK hiK hM hcM hiM
  let D : ℝ := n*volumeRoot K^(n-1)
  let C : ℝ := (n:ℝ)⁻¹*(volume.real K)^((n:ℝ)⁻¹-1)
  have hD : 0 < D := mul_pos hnR (pow_pos (volumeRoot_pos hK hiK) _)
  have hDC : D*C=1 := volumeRoot_diff_factor hn0 hvK
  have hs' : D*(volumeRoot (K+M)-volumeRoot K) ≤ d := by
    have he : D*(d*C)=d := by calc
      _ = d*(D*C) := by ring
      _ = d := by rw [hDC,mul_one]
    rw [← he]
    apply mul_le_mul_of_nonneg_left _ hD.le
    simpa only [C,mul_assoc] using hs
  constructor
  · change D*volumeRoot M ≤ d
    exact (mul_le_mul_of_nonneg_left (by linarith : volumeRoot M ≤ volumeRoot (K+M)-volumeRoot K) hD.le).trans hs'
  · intro heq
    have hv : volumeRoot (K+M)=volumeRoot K+volumeRoot M := by
      change d=D*volumeRoot M at heq
      rw [heq] at hs'
      have ht := (mul_le_mul_iff_right₀ hD).mp hs'
      linarith
    exact brunnMinkowski_add_equality hn hK hcK hiK hM hcM hiM hv

end PettyProjection
end

end OAI
