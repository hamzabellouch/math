import OAI.Geometry.ProjectionBodies.ShadowSlices

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- The strict scalar inequality in the slice transport proof of
Brunn--Minkowski. The variables `p,q` are the positive slice-volume roots. -/
lemma transport_scalar {m : ℕ} (hm : 0 < m) {a b p q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) (hp : 0 < p) (hq : 0 < q) :
    1 ≤ (a*p+b*q)^m*(a/(p^m)+b/(q^m)) ∧
      ((a*p+b*q)^m*(a/(p^m)+b/(q^m))=1 ↔ p=q) := by
  let D := p^a*q^b
  have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hq _)
  have hX : D ≤ a*p+b*q := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le hp.le hq.le hab
  have hXi : D < a*p+b*q ↔ p ≠ q :=
    Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos ha hb hp.le hq.le hab
  have hY : (D^m)⁻¹ ≤ a/(p^m)+b/(q^m) := by
    have hh := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le
      (inv_nonneg.mpr (pow_nonneg hp.le m)) (inv_nonneg.mpr (pow_nonneg hq.le m)) hab
    convert hh using 1
    · dsimp [D]
      rw [mul_pow,mul_inv,Real.inv_rpow (pow_nonneg hp.le m),
        Real.inv_rpow (pow_nonneg hq.le m)]
      rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hp.le,
        ← Real.rpow_mul hq.le]
      rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hp.le,
        ← Real.rpow_mul hq.le]
      simp only [mul_comm]
    · simp only [div_eq_mul_inv]
  have hYP : 0 < a/(p^m)+b/(q^m) := by positivity
  have hX0 : 0 < a*p+b*q := by positivity
  have hle : 1 ≤ (a*p+b*q)^m*(a/(p^m)+b/(q^m)) := by
    calc
      1 = D^m*(D^m)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ hD.ne')).symm
      _ ≤ (a*p+b*q)^m*(a/(p^m)+b/(q^m)) :=
        mul_le_mul (pow_le_pow_left₀ hD.le hX m) hY (inv_nonneg.mpr (pow_nonneg hD.le _))
          (pow_nonneg hX0.le _)
  refine ⟨hle,⟨fun he => ?_,fun he => ?_⟩⟩
  · by_contra hn
    have hlt : D^m < (a*p+b*q)^m := pow_lt_pow_left₀ (hXi.mpr hn) hD.le hm.ne'
    have hh : 1 < (a*p+b*q)^m*(a/(p^m)+b/(q^m)) := calc
      1 = D^m*(D^m)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ hD.ne')).symm
      _ ≤ D^m*(a/(p^m)+b/(q^m)) := mul_le_mul_of_nonneg_left hY (pow_nonneg hD.le _)
      _ < _ := mul_lt_mul_of_pos_right hlt hYP
    linarith
  · subst q
    rw [← add_mul,hab,one_mul,← add_div,hab]
    exact mul_one_div_cancel (pow_ne_zero _ hp.ne')

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- The inverse cumulative mass coordinate on a compact interval. Zero density
at the two endpoints is allowed; the derivative is needed only in the interior. -/
theorem exists_interval_quantile {l r : ℝ} (hlr : l < r) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo l r)) (hI : IntervalIntegrable f volume l r)
    (hpos : ∀ x ∈ Ioo l r, 0 < f x)
    (hmass : (∫ x in l..r, f x)=1) :
    ∃ Q : ℝ → ℝ, Continuous Q ∧ Q 0=l ∧ Q 1=r ∧
      (∀ s ∈ Icc (0:ℝ) 1, Q s ∈ Icc l r) ∧
      (∀ s ∈ Ioo (0:ℝ) 1, Q s ∈ Ioo l r ∧
        HasDerivAt Q (f (Q s))⁻¹ s) := by
  let F : ℝ → ℝ := fun x => ∫ y in l..x, f y
  have hFc : ContinuousOn F (Icc l r) := by
    simpa only [uIcc_of_le hlr.le] using
      (intervalIntegral.continuousOn_primitive_interval' hI left_mem_uIcc)
  have hd : ∀ x ∈ Ioo l r, HasDerivAt F (f x) x := by
    intro x hx
    have hc : ContinuousAt f x := hf.continuousAt (Ioo_mem_nhds hx.1 hx.2)
    exact intervalIntegral.integral_hasDerivAt_right (hI.mono_set (by
      simp only [uIcc_of_le hlr.le,uIcc_of_le hx.1.le]
      exact Icc_subset_Icc_right hx.2.le))
      (hf.stronglyMeasurableAtFilter isOpen_Ioo x hx) hc
  have hmono : StrictMonoOn F (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc l r) hFc
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x hx).deriv]
    exact hpos x hx
  have hFl : F l=0 := intervalIntegral.integral_same
  have hFr : F r=1 := hmass
  have hIm : F '' Icc l r = Icc (0:ℝ) 1 := by
    simpa only [hFl,hFr] using hFc.image_Icc_of_monotoneOn hlr.le hmono.monotoneOn
  let e : Icc l r ≃o Icc (0:ℝ) 1 :=
    (hmono.orderIso F (Icc l r)).trans (Set.orderIsoOfEq _ _ hIm)
  let Q : ℝ → ℝ := fun s => (e.symm (projIcc 0 1 (by norm_num) s)).val
  have hQc : Continuous Q := continuous_subtype_val.comp
    (e.symm.continuous.comp continuous_projIcc)
  have hQmem : ∀ s, Q s ∈ Icc l r := fun s => (e.symm (projIcc 0 1 (by norm_num) s)).property
  have hFQ : ∀ s ∈ Icc (0:ℝ) 1, F (Q s)=s := by
    intro s hs
    have he := congrArg Subtype.val (e.apply_symm_apply (projIcc 0 1 (by norm_num) s))
    change F (Q s) = (projIcc 0 1 (by norm_num) s).val at he
    simpa only [projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) hs] using he
  have hQ0 : Q 0=l := hmono.injOn (hQmem 0) (left_mem_Icc.mpr hlr.le)
    ((hFQ 0 (by norm_num)).trans hFl.symm)
  have hQ1 : Q 1=r := hmono.injOn (hQmem 1) (right_mem_Icc.mpr hlr.le)
    ((hFQ 1 (by norm_num)).trans hFr.symm)
  refine ⟨Q,hQc,hQ0,hQ1,fun s _ => hQmem s,?_⟩
  intro s hs
  have hQi : Q s ∈ Ioo l r := by
    refine ⟨lt_of_le_of_ne (hQmem s).1 ?_,lt_of_le_of_ne (hQmem s).2 ?_⟩
    · intro he
      have hy := hFQ s ⟨hs.1.le,hs.2.le⟩
      rw [← he,hFl] at hy
      linarith [hs.1]
    · intro he
      have hy := hFQ s ⟨hs.1.le,hs.2.le⟩
      rw [he,hFr] at hy
      linarith [hs.2]
  refine ⟨hQi,HasDerivAt.of_local_left_inverse hQc.continuousAt (hd _ hQi)
    (hpos _ hQi).ne' ?_⟩
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact hFQ t ⟨ht.1.le,ht.2.le⟩

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- The analytic step of the slice proof. All three functions here are actual
slice densities when this result is applied to convex bodies. -/
theorem slice_transport {m : ℕ} (hm : 0 < m) {a b l r L R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) (hlr : l<r) (hLR : L<R)
    {f g h : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo l r)) (hg : ContinuousOn g (Ioo L R))
    (hfi : IntervalIntegrable f volume l r) (hgi : IntervalIntegrable g volume L R)
    (hfp : ∀ x ∈ Ioo l r, 0<f x) (hgp : ∀ x ∈ Ioo L R, 0<g x)
    (hfI : (∫ x in l..r, f x)=1) (hgI : (∫ x in L..R, g x)=1)
    (hhi : IntervalIntegrable h volume (a*l+b*L) (a*r+b*R))
    (hbound : ∀ x ∈ Ioo l r, ∀ y ∈ Ioo L R,
      (a*(f x)^((m:ℝ)⁻¹)+b*(g y)^((m:ℝ)⁻¹))^m ≤ h (a*x+b*y)) :
    1 ≤ ∫ z in (a*l+b*L)..(a*r+b*R), h z := by
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
  have hi := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0:ℝ)≤1)
    intervalIntegrable_const hint hae
  rw [intervalIntegral.integral_const] at hi
  norm_num at hi
  rw [hsub,hz0,hz1] at hi
  exact hi

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

def horizontalSlice (K : Set (E × ℝ)) (s : ℝ) : Set E := (fun y => (y,s)) ⁻¹' K

omit [NormedSpace ℝ E] in
lemma horizontalSlice_compact {K : Set (E × ℝ)} (hK : IsCompact K) (s : ℝ) :
    IsCompact (horizontalSlice K s) :=
  (IsClosedEmbedding.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft s)
    (isClosedMap_prodMk_right s)).isCompact_preimage hK

lemma horizontalSlice_convex {K : Set (E × ℝ)} (hK : Convex ℝ K) (s : ℝ) :
    Convex ℝ (horizontalSlice K s) := by
  intro x hx y hy a b ha hb hab
  have h := hK hx hy ha hb hab
  change (a • x+b • y,s) ∈ K
  simpa only [Prod.smul_mk,Prod.mk_add_mk,← add_smul,hab,one_smul] using h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma horizontalSlice_nonempty_iff {K : Set (E × ℝ)} {s : ℝ} :
    (horizontalSlice K s).Nonempty ↔ s ∈ Prod.snd '' K := by
  constructor
  · rintro ⟨x,hx⟩; exact ⟨(x,s),hx,rfl⟩
  · rintro ⟨⟨x,t⟩,hx,rfl⟩; exact ⟨x,hx⟩

lemma horizontalSlice_minkowski_subset (K M : Set (E × ℝ)) (a b s t : ℝ) :
    a • horizontalSlice K s+b • horizontalSlice M t ⊆
      horizontalSlice (a • K+b • M) (a*s+b*t) := by
  rintro _ ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
  exact ⟨a • (x,s),smul_mem_smul_set hx,b • (y,t),smul_mem_smul_set hy,rfl⟩

lemma horizontalSlice_combo_subset {K : Set (E × ℝ)} (hK : Convex ℝ K)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) (s t : ℝ) :
    a • horizontalSlice K s+b • horizontalSlice K t ⊆
      horizontalSlice K (a*s+b*t) := by
  rintro _ ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
  exact hK hx hy ha hb hab

omit [NormedSpace ℝ E] in
lemma interior_slice_of_interior {K : Set (E × ℝ)} {x : E} {s : ℝ}
    (hx : (x,s) ∈ interior K) : x ∈ interior (horizontalSlice K s) :=
  preimage_interior_subset_interior_preimage (by fun_prop) hx

/-- A projection point strictly between two attained heights is a height of an
interior point. No smoothness of the convex body is imposed. -/
lemma interior_point_at_height {K : Set (E × ℝ)} (hK : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r s : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) (hs : s ∈ Ioo l r) :
    ∃ x : E, (x,s) ∈ interior K := by
  obtain ⟨⟨x0,s0⟩,h0⟩ := hi
  obtain ⟨⟨xl,sl⟩,hxl,hl⟩ := hl
  obtain ⟨⟨xr,sr⟩,hxr,hr⟩ := hr
  change sl=l at hl
  change sr=r at hr
  subst sl; subst sr
  obtain h | h | h := lt_trichotomy s s0
  · let t := (s0-s)/(s0-l)
    have hd : 0<s0-l := by linarith [hs.1]
    have ht0 : 0≤t := (div_pos (by linarith) hd).le
    have ht1 : t<1 := (div_lt_one hd).mpr (by linarith [hs.1])
    have hc := hK.combo_interior_self_mem_interior h0 hxl (by linarith : 0<1-t) ht0 (by ring : (1-t)+t=1)
    refine ⟨(1-t) • x0+t • xl,?_⟩
    convert hc using 1
    ext
    · rfl
    · dsimp [t]
      field_simp
      ring
  · subst s
    exact ⟨x0,h0⟩
  · let t := (s-s0)/(r-s0)
    have hd : 0<r-s0 := by linarith [hs.2]
    have ht0 : 0≤t := (div_pos (by linarith) hd).le
    have ht1 : t<1 := (div_lt_one hd).mpr (by linarith [hs.2])
    have hc := hK.combo_interior_self_mem_interior h0 hxr (by linarith : 0<1-t) ht0 (by ring : (1-t)+t=1)
    refine ⟨(1-t) • x0+t • xr,?_⟩
    convert hc using 1
    ext
    · rfl
    · dsimp [t]
      field_simp
      ring

lemma horizontalSlice_interior_nonempty {K : Set (E × ℝ)} (hK : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r s : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) (hs : s ∈ Ioo l r) :
    (interior (horizontalSlice K s)).Nonempty := by
  obtain ⟨x,hx⟩ := interior_point_at_height hK hi hl hr hs
  exact ⟨x,interior_slice_of_interior hx⟩

lemma vertical_projection_interval {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    ∃ l r : ℝ, l<r ∧ Prod.snd '' K=Icc l r := by
  have hn : K.Nonempty := hi.mono interior_subset
  refine ⟨sInf (Prod.snd '' K),sSup (Prod.snd '' K),?_,
    compact_convex_real_interval (hK.image continuous_snd)
      (hc.linear_image (LinearMap.snd ℝ E ℝ)) (hn.image _)⟩
  have hInt : (interior (Prod.snd '' K)).Nonempty :=
    (hi.image Prod.snd).mono (isOpenMap_snd.image_interior_subset K)
  rw [compact_convex_real_interval (hK.image continuous_snd)
    (hc.linear_image (LinearMap.snd ℝ E ℝ)) (hn.image _),interior_Icc] at hInt
  exact nonempty_Ioo.mp hInt

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

def sliceDensity (K : Set (E × ℝ)) (s : ℝ) : ℝ := volume.real (horizontalSlice K s)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_nonneg (K : Set (E × ℝ)) (s : ℝ) : 0 ≤ sliceDensity K s := measureReal_nonneg

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma sliceDensity_pos {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) {l r s : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) (hs : s ∈ Ioo l r) :
    0 < sliceDensity K s := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) (horizontalSlice_compact hK s).measure_ne_top
  exact lt_of_lt_of_le (isOpen_interior.measure_pos volume
    (horizontalSlice_interior_nonempty hc hi hl hr hs)) (measure_mono interior_subset)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_zero_of_notMem {K : Set (E × ℝ)} {s : ℝ}
    (hs : s ∉ Prod.snd '' K) : sliceDensity K s=0 := by
  have he : horizontalSlice K s=∅ := not_nonempty_iff_eq_empty.mp
    (fun h => hs (horizontalSlice_nonempty_iff.mp h))
  simp [sliceDensity,he]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_indicator_integral {K : Set (E × ℝ)} (hK : IsCompact K) (s : ℝ) :
    (∫ x : E, K.indicator (fun _ => (1:ℝ)) (x,s))=sliceDensity K s := by
  have he : (fun x : E => K.indicator (fun _ => (1:ℝ)) (x,s)) =
      (horizontalSlice K s).indicator (fun _ => (1:ℝ)) := by
    funext x
    by_cases hx : (x,s) ∈ K
    · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (show x ∈ horizontalSlice K s from hx)]
    · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show x ∉ horizontalSlice K s from hx)]
  rw [he,integral_indicator (horizontalSlice_compact hK s).measurableSet,setIntegral_const]
  simp only [smul_eq_mul,mul_one,sliceDensity]

lemma sliceDensity_integrable {K : Set (E × ℝ)} (hK : IsCompact K) :
    Integrable (sliceDensity K) := by
  have hi : Integrable (K.indicator (fun _ => (1:ℝ))) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  exact hi.integral_prod_right.congr (Eventually.of_forall fun s => sliceDensity_indicator_integral hK s)

lemma sliceDensity_integral {K : Set (E × ℝ)} (hK : IsCompact K) :
    (∫ s, sliceDensity K s)=volume.real K := by
  have hi : Integrable (K.indicator (fun _ => (1:ℝ))) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  have he := integral_prod_symm (K.indicator (fun _ => (1:ℝ))) hi
  simp_rw [sliceDensity_indicator_integral hK] at he
  rw [← he,← Measure.volume_eq_prod,integral_indicator hK.measurableSet,setIntegral_const]
  simp only [smul_eq_mul,mul_one]

lemma sliceDensity_interval_integral {K : Set (E × ℝ)} (hK : IsCompact K) {l r : ℝ}
    (hlr : l≤r) (hp : Prod.snd '' K ⊆ Icc l r) :
    (∫ s in l..r, sliceDensity K s)=volume.real K := by
  rw [intervalIntegral.integral_of_le hlr,← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact sliceDensity_integral hK
  · intro s hs
    exact sliceDensity_zero_of_notMem (fun h => hs (hp h))

end
end PettyProjection
end

end OAI
