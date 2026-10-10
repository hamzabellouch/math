import OAI.MathematicalPhysics.Transonic.Exterior.Continuation

namespace OAI

section
noncomputable section
namespace SepticProfile.AxisBarriers

def D (sigma z u : ℝ) : ℝ := z*(1-sigma*z^2)*(1-u^2)
def N (kappa z u : ℝ) : ℝ := (1-(3/5:ℝ)*u^2)*(kappa*z*(1-u^2)+3*(z-u))
def lower (z : ℝ) : ℝ := (749/1000)*z
def polyDen (x : ℝ) : ℝ := 1-(41/200)*x-(347/5000)*x^2
def upper (z : ℝ) : ℝ := (3/4)*z/polyDen (z^2)
def upperDeriv (z : ℝ) : ℝ := (3/4)*(1+(41/200)*z^2+(1041/5000)*z^4)/(polyDen (z^2))^2

def residualPoly (x : ℝ) : ℝ :=
  9/1000+(220413/1600000)*x-(23123019/64000000)*x^2+
  (245617149/1280000000)*x^3+(1242882171/32000000000)*x^4-
  (95591862237/20000000000000)*x^5-(784539168171/500000000000000)*x^6-
  (43494981843/625000000000000)*x^7

lemma radius_bounds {z : ℝ} (hz : z ∈ Set.Icc 0 (9/10)) :
    0≤z^2 ∧ z^2≤81/100 ∧ (z^2)^2≤6561/10000 := by
  have h1 : 0≤z*(9/10-z) := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  have h2 : z^2≤81/100 := by nlinarith [hz.2]
  exact ⟨sq_nonneg z,h2,by nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr h2)]⟩

lemma polyDen_pos {z : ℝ} (hz : z ∈ Set.Icc 0 (9/10)) :
    78/100 < polyDen (z^2) := by
  have h := radius_bounds hz
  dsimp [polyDen]
  nlinarith [h.2.1,h.2.2]

lemma barriers_in_unit {z : ℝ} (hz : z ∈ Set.Icc 0 (9/10)) :
    0≤lower z ∧ lower z<upper z+(if z=0 then 1 else 0) ∧
      0≤upper z ∧ upper z<1 := by
  have hz0 := hz.1
  have hd := polyDen_pos hz
  have hd0 : 0 < polyDen (z^2) := by linarith
  have hx := radius_bounds hz
  have hdu : polyDen (z^2)≤1 := by dsimp [polyDen]; nlinarith [hx.1,sq_nonneg (z^2)]
  refine ⟨by dsimp [lower]; positivity,?_,by dsimp [upper]; positivity,?_⟩
  · by_cases h0 : z=0
    · simp [h0,lower,upper,polyDen]
    · rw [ite_eq_right h0,add_zero]
      have hzp : 0<z := lt_of_le_of_ne hz.1 (Ne.symm h0)
      dsimp [lower,upper]
      rw [lt_div_iff₀ hd0]
      nlinarith
  · dsimp [upper]
    rw [div_lt_one hd0]
    linarith [hz.2]

lemma upperDeriv_pos {z : ℝ} (hz : z ∈ Set.Icc 0 (9/10)) : 0<upperDeriv z := by
  have hd := polyDen_pos hz
  dsimp [upperDeriv]
  positivity

lemma upper_hasDeriv {z : ℝ} (hz : z ∈ Set.Icc 0 (9/10)) : HasDerivAt upper (upperDeriv z) z := by
  have hd : polyDen (z^2) ≠ 0 := by linarith [polyDen_pos hz]
  have hg : HasDerivAt (fun z : ℝ => polyDen (z^2))
      (-(41/100)*z-(347/1250)*z^3) z := by
    convert (((hasDerivAt_const z (1:ℝ)).sub (((hasDerivAt_id z).pow 2).const_mul (41/200))).sub
      ((((hasDerivAt_id z).pow 2).pow 2).const_mul (347/5000))) using 1 <;>
      first | rfl | (dsimp [polyDen]; ring)
  convert (((hasDerivAt_id z).const_mul (3/4)).div hg hd) using 1 <;>
    first | rfl | (dsimp [upper,upperDeriv,polyDen]; ring)

lemma residualPoly_pos {x : ℝ} (hx : x ∈ Set.Icc 0 (81/100)) : 0<residualPoly x := by
  have he : residualPoly x = (1/100000:ℝ) + (899000000000/22876792454961:ℝ)*x^0*(81/100-x)^7 +
    (17451408125000/22876792454961:ℝ)*x^1*(81/100-x)^6 +
    (82832988404375/30502389939948:ℝ)*x^2*(81/100-x)^5 +
    (5792980533458545/1464114717117504:ℝ)*x^3*(81/100-x)^4 +
    (1921567051918001291/732057358558752000:ℝ)*x^4*(81/100-x)^3 +
    (10162415437554180665821/15251194969974000000000:ℝ)*x^5*(81/100-x)^2 +
    (745226816895942492518749/114383962274805000000000000:ℝ)*x^6*(81/100-x)^1 +
    (3066525437817139243066501/7148997642175312500000000000:ℝ)*x^7*(81/100-x)^0 := by
    dsimp [residualPoly]
    ring
  rw [he]
  have h : 0≤81/100-x := sub_nonneg.mpr hx.2
  have : 0≤x := hx.1
  positivity

lemma upper_residual_identity {z : ℝ} (hd : polyDen (z^2) ≠ 0) :
    D (993/1000) z (upper z)*upperDeriv z-N 0 z (upper z) =
      z^3*residualPoly (z^2)/(polyDen (z^2))^4 := by
  dsimp [D,N,upper,upperDeriv]
  field_simp
  dsimp [polyDen,residualPoly]
  ring

lemma upper_strict_barrier {sigma kappa z : ℝ}
    (hs : sigma≤993/1000) (hk : kappa≤0) (hz : z ∈ Set.Ioc 0 (9/10)) :
    N kappa z (upper z)<D sigma z (upper z)*upperDeriv z := by
  have hzp := hz.1
  have hzc : z ∈ Set.Icc 0 (9/10) := ⟨le_of_lt hz.1,hz.2⟩
  have hu := barriers_in_unit hzc
  have hd := polyDen_pos hzc
  have hurd := upperDeriv_pos hzc
  have hup : 0<1-(upper z)^2 := by nlinarith [hu.2.2.1,hu.2.2.2]
  have huc : 0<1-(3/5:ℝ)*(upper z)^2 := by nlinarith [sq_nonneg (upper z)]
  have hpatch1 : D (993/1000) z (upper z)≤D sigma z (upper z) := by
    have hs0 : 0≤993/1000-sigma := sub_nonneg.mpr hs
    have hm : 0≤z*(993/1000-sigma)*z^2*(1-(upper z)^2) := by positivity
    dsimp [D]
    nlinarith only [hm]
  have hpatch2 : N kappa z (upper z)≤N 0 z (upper z) := by
    have hm : (1-(3/5:ℝ)*(upper z)^2)*kappa*z*(1-(upper z)^2)≤0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (le_of_lt huc) hk) (le_of_lt hz.1))
        (le_of_lt hup)
    dsimp [N]
    nlinarith only [hm]
  have hbase : 0<D (993/1000) z (upper z)*upperDeriv z-N 0 z (upper z) := by
    rw [upper_residual_identity (by linarith)]
    have hp := residualPoly_pos ⟨(radius_bounds hzc).1,(radius_bounds hzc).2.1⟩
    positivity
  have hm := mul_le_mul_of_nonneg_right hpatch1 (le_of_lt hurd)
  linarith

lemma lower_strict_barrier {sigma kappa z : ℝ}
    (hs : (991/1000:ℝ) ≤ sigma) (hk : -(1/500:ℝ)≤kappa) (hz : z ∈ Set.Ioc 0 (9/10)) :
    D sigma z (lower z)*(749/1000)<N kappa z (lower z) := by
  have hzp := hz.1
  have hzc : z ∈ Set.Icc 0 (9/10) := ⟨le_of_lt hz.1,hz.2⟩
  have hl0 : 0≤lower z := by dsimp [lower]; positivity
  have hl1 : lower z<1 := by dsimp [lower]; linarith [hz.2]
  have hup : 0<1-(lower z)^2 := by nlinarith
  have huc : 0<1-(3/5:ℝ)*(lower z)^2 := by nlinarith [sq_nonneg (lower z)]
  have hpatch1 : D sigma z (lower z)≤D (991/1000) z (lower z) := by
    have hs0 : 0≤ sigma-991/1000 := sub_nonneg.mpr hs
    have hm : 0≤z*(sigma-991/1000)*z^2*(1-(lower z)^2) := by positivity
    dsimp [D]
    nlinarith only [hm]
  have hpatch2 : N (-(1/500)) z (lower z)≤N kappa z (lower z) := by
    have hk0 : 0≤kappa+1/500 := by linarith
    have hm : 0≤(1-(3/5:ℝ)*(lower z)^2)*(kappa+1/500)*z*(1-(lower z)^2) := by positivity
    dsimp [N]
    nlinarith only [hm]
  have he : N (-(1/500)) z (lower z)-D (991/1000) z (lower z)*(749/1000) =
      z*((1/500)+(2276959251/2500000000)*z^2-
        (1041964269513503/2500000000000000)*(z^2)^2) := by
    dsimp [N,D,lower]
    ring
  have hbase : 0<N (-(1/500)) z (lower z)-D (991/1000) z (lower z)*(749/1000) := by
    rw [he]
    apply mul_pos hz.1
    have hx := radius_bounds hzc
    have hm := mul_nonneg hx.1 (sub_nonneg.mpr hx.2.1)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hpatch1 (by norm_num : (0:ℝ)≤749/1000)
  linarith

end SepticProfile.AxisBarriers

namespace SepticProfile.AxisBarriers
open Set RegularContinuation

lemma upper_lt_nine_tenths {z : ℝ} (hz : z ∈ Icc 0 (9/10)) : upper z<9/10 := by
  have hd := polyDen_pos hz
  dsimp [upper]
  rw [div_lt_iff₀ (by linarith : 0<polyDen (z^2))]
  linarith [hz.2]

lemma D_pos {sigma z u : ℝ} (hs : sigma≤993/1000)
    (hz : z ∈ Ioc 0 (9/10)) (hu : u ∈ Icc 0 (9/10)) : 0<D sigma z u := by
  have hz2 := radius_bounds ⟨le_of_lt hz.1,hz.2⟩
  have hu2 := radius_bounds hu
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg z)
  have h1 : 0<1-sigma*z^2 := by nlinarith [hz2.2.1]
  have h2 : 0<1-u^2 := by linarith [hu2.2.1]
  exact mul_pos (mul_pos hz.1 h1) h2

lemma field_contDiffOn {sigma kappa a b : ℝ} (hs : sigma≤993/1000)
    (ha : 0<a) (hb : b≤9/10) :
    ContDiffOn ℝ 1 (fun p : ℝ×ℝ => N kappa p.1 p.2/D sigma p.1 p.2)
      (Icc a b ×ˢ Icc 0 (9/10)) := by
  have hN : ContDiff ℝ 1 (fun p : ℝ×ℝ => N kappa p.1 p.2) := by unfold N; fun_prop
  have hD : ContDiff ℝ 1 (fun p : ℝ×ℝ => D sigma p.1 p.2) := by unfold D; fun_prop
  exact hN.contDiffOn.div hD.contDiffOn (fun p hp => ne_of_gt (D_pos hs
    ⟨lt_of_lt_of_le ha hp.1.1,le_trans hp.1.2 hb⟩ hp.2))

/-- The actual regular normalized source equation can be integrated all the way
to any b≤.9 while retaining the two explicit axis barriers. The clamping device
is not a replacement equation: the conclusion includes its complete removal. -/
theorem exists_between_barriers {sigma kappa a b u0 : ℝ}
    (hslo : (991/1000:ℝ) ≤ sigma) (hshi : sigma≤993/1000)
    (hklo : -(1/500:ℝ)≤kappa) (hkhi : kappa≤0)
    (ha : 0<a) (hab : a≤b) (hb : b≤9/10)
    (hu0 : u0 ∈ Icc (lower a) (upper a)) :
    ∃ u : ℝ → ℝ, u a=u0 ∧ ContinuousOn u (Icc a b) ∧
      (∀ t ∈ Icc a b, u t ∈ Icc (lower t) (upper t)) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u
        (N kappa t (u t)/D sigma t (u t)) (Icc a b) t := by
  let f : ℝ×ℝ → ℝ := fun p => N kappa p.1 p.2/D sigma p.1 p.2
  obtain ⟨u,hu,huc,hud⟩ := exists_clamped_solution hab (by norm_num : (0:ℝ)≤9/10)
    (field_contDiffOn hshi ha hb (kappa := kappa)) u0
  have ht0 {t : ℝ} (ht : t ∈ Icc a b) : t ∈ Icc 0 (9/10) :=
    ⟨le_trans (le_of_lt ha) ht.1,le_trans ht.2 hb⟩
  have htpos {t : ℝ} (ht : t ∈ Icc a b) : t ∈ Ioc 0 (9/10) :=
    ⟨lt_of_lt_of_le ha ht.1,le_trans ht.2 hb⟩
  have hlowD (t : ℝ) : HasDerivAt lower (749/1000) t := by
    convert (hasDerivAt_id t).const_mul (749/1000:ℝ) using 1 <;> first | rfl | simp
  have hright (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt u
      (f (t,clamp 0 (9/10) (u t))) (Ici t) t := by
    apply (hud t ⟨ht.1,le_of_lt ht.2⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  have hupper : ∀ t ∈ Icc a b, u t≤upper t := by
    apply image_le_of_deriv_right_lt_deriv_boundary' huc hright
      (B' := upperDeriv) (by simpa [hu] using hu0.2)
      (fun t ht => (upper_hasDeriv (ht0 ht)).continuousAt.continuousWithinAt)
      (fun t ht => (upper_hasDeriv (ht0 ⟨ht.1,le_of_lt ht.2⟩)).hasDerivWithinAt)
    intro t ht he
    have htz := ht0 ⟨ht.1,le_of_lt ht.2⟩
    have htu : upper t ∈ Icc 0 (9/10) :=
      ⟨(barriers_in_unit htz).2.2.1,le_of_lt (upper_lt_nine_tenths htz)⟩
    rw [he,clamp_eq htu]
    dsimp [f]
    exact (div_lt_iff₀ (D_pos hshi (htpos ⟨ht.1,le_of_lt ht.2⟩) htu)).mpr
      (by simpa [mul_comm] using upper_strict_barrier hshi hkhi (htpos ⟨ht.1,le_of_lt ht.2⟩))
  have hlower : ∀ t ∈ Icc a b, lower t≤u t := by
    have hh := image_le_of_deriv_right_lt_deriv_boundary'
      huc.neg (fun t ht => (hright t ht).neg)
      (B := fun t => -lower t) (B' := fun _ => -(749/1000:ℝ))
      (by change -u a ≤ -lower a; rw [hu]; linarith [hu0.1])
      (fun t _ => (hlowD t).neg.continuousAt.continuousWithinAt)
      (fun t _ => (hlowD t).neg.hasDerivWithinAt)
    have hh' : ∀ t ∈ Icc a b, -u t≤ -lower t := by
      apply hh
      intro t ht he
      have htz := ht0 ⟨ht.1,le_of_lt ht.2⟩
      have htu : lower t ∈ Icc 0 (9/10) := by
        refine ⟨(barriers_in_unit htz).1,?_⟩
        dsimp [lower]
        linarith [htz.2]
      have he' : u t=lower t := neg_inj.mp he
      rw [he',clamp_eq htu]
      dsimp [f]
      have hstrict := (lt_div_iff₀ (D_pos hshi (htpos ⟨ht.1,le_of_lt ht.2⟩) htu)).mpr
        (by simpa [mul_comm] using lower_strict_barrier hslo hklo (htpos ⟨ht.1,le_of_lt ht.2⟩))
      linarith
    intro t ht
    linarith [hh' t ht]
  refine ⟨u,hu,huc,fun t ht => ⟨hlower t ht,hupper t ht⟩,?_⟩
  intro t ht
  have htu : u t ∈ Icc 0 (9/10) :=
    ⟨le_trans (barriers_in_unit (ht0 ht)).1 (hlower t ht),
      le_trans (hupper t ht) (le_of_lt (upper_lt_nine_tenths (ht0 ht)))⟩
  simpa only [clamp_eq htu] using hud t ht

end SepticProfile.AxisBarriers

end
end

end OAI
