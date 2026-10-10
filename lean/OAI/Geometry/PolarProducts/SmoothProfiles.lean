import OAI.Geometry.PolarProducts.EmbeddingInverse

namespace OAI

section NonsqueezingInline

namespace SmoothProfiles
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

 def primitive (v : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0:ℝ)..s, v t

 theorem hasDerivAt_primitive {v : ℝ → ℝ} (hv : Continuous v) (s : ℝ) :
    HasDerivAt (primitive v) (v s) s :=
  intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable _ _)
    hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

 theorem contDiff_primitive {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (primitive v) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (hasDerivAt_primitive hv.continuous x).differentiableAt,
    by simpa only [(funext (fun x => (hasDerivAt_primitive hv.continuous x).deriv))] using hv⟩

 theorem primitive_zero {v : ℝ → ℝ} (hz : ∀ t ≤ 0, v t = 0) {s : ℝ} (hs : s ≤ 0) :
    primitive v s = 0 := by
  rw [primitive, intervalIntegral.integral_symm]
  have hi : ∫ t in s..0, v t = 0 := by
    calc
      _ = ∫ _t in s..0, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        hz t (by rw [Set.uIcc_of_le hs] at ht; exact ht.2))
      _ = _ := by simp
  simp only [hi, neg_zero]

 theorem primitive_nonneg {v : ℝ → ℝ} (_hv : Continuous v)
    (hn : ∀ t, 0 ≤ v t) (hz : ∀ t ≤ 0, v t = 0) (s : ℝ) : 0 ≤ primitive v s := by
  by_cases hs : s ≤ 0
  · simp only [primitive_zero hz hs, le_refl]
  · exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => hn t)

 theorem primitive_mono {v : ℝ → ℝ} (hv : Continuous v) (hn : ∀ t, 0 ≤ v t) :
    Monotone (primitive v) := by
  exact monotone_of_deriv_nonneg (fun t => (hasDerivAt_primitive hv t).differentiableAt)
    (fun t => by simpa only [(hasDerivAt_primitive hv t).deriv] using hn t)

 def exteriorSlope (δ : ℝ) (s : ℝ) : ℝ := Real.smoothTransition (s/δ)
 def exterior (δ : ℝ) : ℝ → ℝ := primitive (exteriorSlope δ)

 theorem contDiff_exteriorSlope (δ : ℝ) : ContDiff ℝ ∞ (exteriorSlope δ) :=
   Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)

 theorem contDiff_exterior (δ : ℝ) : ContDiff ℝ ∞ (exterior δ) :=
   contDiff_primitive (contDiff_exteriorSlope δ)

 theorem hasDerivAt_exterior (δ s : ℝ) : HasDerivAt (exterior δ) (exteriorSlope δ s) s :=
   hasDerivAt_primitive (contDiff_exteriorSlope δ).continuous s

 theorem exteriorSlope_nonneg (δ s : ℝ) : 0 ≤ exteriorSlope δ s := Real.smoothTransition.nonneg _
 theorem exteriorSlope_le_one (δ s : ℝ) : exteriorSlope δ s ≤ 1 := Real.smoothTransition.le_one _
 theorem exteriorSlope_zero {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ≤ 0) : exteriorSlope δ s = 0 :=
   Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs hδ.le)
 theorem exteriorSlope_one {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : δ ≤ s) : exteriorSlope δ s = 1 :=
   Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr hs)

 theorem exterior_zero {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ≤ 0) : exterior δ s = 0 :=
   primitive_zero (fun _ ht => exteriorSlope_zero hδ ht) hs

 theorem exterior_nonneg {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : 0 ≤ exterior δ s :=
   primitive_nonneg (contDiff_exteriorSlope δ).continuous (exteriorSlope_nonneg δ)
     (fun _ ht => exteriorSlope_zero hδ ht) s

 theorem exterior_affine {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : δ ≤ s) :
     exterior δ s = s-δ+exterior δ δ := by
   have hc := (contDiff_exteriorSlope δ).continuous
   have hi := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 δ)
     (hc.intervalIntegrable (μ := volume) δ s)
   change exterior δ δ+(∫ t in δ..s, exteriorSlope δ t) = exterior δ s at hi
   have he : (∫ t in δ..s, exteriorSlope δ t) = s-δ := by
     calc
       _ = ∫ _t in δ..s, (1 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
         exteriorSlope_one hδ (by rw [Set.uIcc_of_le hs] at ht; exact ht.1))
       _ = _ := by simp
   rw [he] at hi
   linarith

 theorem exterior_lower {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : s-δ ≤ exterior δ s := by
   by_cases hs : δ ≤ s
   · rw [exterior_affine hδ hs]; linarith [exterior_nonneg hδ δ]
   · linarith [exterior_nonneg hδ s]

 theorem exterior_upper {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : exterior δ s ≤ max s 0 := by
   by_cases hs : s ≤ 0
   · rw [exterior_zero hδ hs, max_eq_right hs]
   · have hs0 := le_of_not_ge hs
     calc
       exterior δ s ≤ ∫ _t in (0:ℝ)..s, (1 : ℝ) :=
         intervalIntegral.integral_mono_on hs0 ((contDiff_exteriorSlope δ).continuous.intervalIntegrable _ _)
           (continuous_const.intervalIntegrable _ _) (fun t _ => exteriorSlope_le_one δ t)
       _ = max s 0 := by simp [max_eq_left hs0]

 theorem primitive_zero_below {v : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hz : ∀ t ≤ b, v t = 0) {s : ℝ} (hs : s ≤ b) : primitive v s = 0 := by
  unfold primitive
  calc
    _ = ∫ _t in (0:ℝ)..s, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
      hz t (ht.2.trans (max_le hb hs)))
    _ = _ := by simp

 theorem primitive_const_above {v : ℝ → ℝ} (hv : Continuous v) {b : ℝ}
    (hz : ∀ t, b ≤ t → v t = 0) {s : ℝ} (hs : b ≤ s) : primitive v s = primitive v b := by
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hv.intervalIntegrable (μ := volume) 0 b) (hv.intervalIntegrable (μ := volume) b s)
  have he : (∫ t in b..s, v t) = 0 := by
    calc
      _ = ∫ _t in b..s, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        hz t (by rw [Set.uIcc_of_le hs] at ht; exact ht.1))
      _ = _ := by simp
  change primitive v b+_ = primitive v s at hi
  simpa only [he, add_zero] using hi.symm

 def ballSlope (r L ε s : ℝ) : ℝ :=
    r*Real.smoothTransition ((s-ε)/ε)*Real.smoothTransition ((L-ε-s)/ε)
 def ballProfile (r L ε : ℝ) : ℝ → ℝ := primitive (ballSlope r L ε)
 def ballHeight (r L ε : ℝ) : ℝ := ballProfile r L ε (L-ε)

 theorem contDiff_ballSlope (r L ε : ℝ) : ContDiff ℝ ∞ (ballSlope r L ε) :=
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε))).mul
      (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε))

 theorem contDiff_ballProfile (r L ε : ℝ) : ContDiff ℝ ∞ (ballProfile r L ε) :=
    contDiff_primitive (contDiff_ballSlope r L ε)

 theorem hasDerivAt_ballProfile (r L ε s : ℝ) :
    HasDerivAt (ballProfile r L ε) (ballSlope r L ε s) s :=
    hasDerivAt_primitive (contDiff_ballSlope r L ε).continuous s

 theorem ballSlope_nonneg {r : ℝ} (hr : 0 ≤ r) (L ε s : ℝ) : 0 ≤ ballSlope r L ε s :=
    mul_nonneg (mul_nonneg hr (Real.smoothTransition.nonneg _)) (Real.smoothTransition.nonneg _)

 theorem ballSlope_le {r : ℝ} (hr : 0 ≤ r) (L ε s : ℝ) : ballSlope r L ε s ≤ r := by
    have h1 := Real.smoothTransition.le_one ((s-ε)/ε)
    have h2 := Real.smoothTransition.le_one ((L-ε-s)/ε)
    have h0 := Real.smoothTransition.nonneg ((s-ε)/ε)
    have hp := mul_le_mul_of_nonneg_left h2 (mul_nonneg hr h0)
    have hq := mul_le_mul_of_nonneg_left h1 hr
    dsimp [ballSlope]
    nlinarith

 theorem ballSlope_zero_left (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≤ ε) :
    ballSlope r L ε s = 0 := by
    unfold ballSlope
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)]
    ring

 theorem ballSlope_zero_right (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : L-ε ≤ s) :
    ballSlope r L ε s = 0 := by
    unfold ballSlope
    rw [show Real.smoothTransition ((L-ε-s)/ε) = 0 from
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)]
    ring

 theorem ballSlope_middle (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ}
    (hs : 2*ε ≤ s) (ht : s ≤ L-2*ε) : ballSlope r L ε s = r := by
    unfold ballSlope
    rw [Real.smoothTransition.one_of_one_le ((one_le_div hε).mpr (by linarith)),
      Real.smoothTransition.one_of_one_le ((one_le_div hε).mpr (by linarith))]
    ring

 theorem ballProfile_zero (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≤ ε) :
    ballProfile r L ε s = 0 :=
    primitive_zero_below hε.le (fun _ ht => ballSlope_zero_left r L hε ht) hs

 theorem ballProfile_plateau (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : L-ε ≤ s) :
    ballProfile r L ε s = ballHeight r L ε :=
    primitive_const_above (contDiff_ballSlope r L ε).continuous
      (fun _ ht => ballSlope_zero_right r L hε ht) hs

 theorem ballProfile_nonneg {r : ℝ} (hr : 0 ≤ r) (L : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ ballProfile r L ε s :=
    primitive_nonneg (contDiff_ballSlope r L ε).continuous (ballSlope_nonneg hr L ε)
      (fun _ ht => ballSlope_zero_left r L hε (ht.trans hε.le)) s

 theorem ballProfile_le_height {r : ℝ} (hr : 0 ≤ r) (L : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ballProfile r L ε s ≤ ballHeight r L ε := by
    by_cases hs : L-ε ≤ s
    · rw [ballProfile_plateau r L hε hs]
    · exact primitive_mono (contDiff_ballSlope r L ε).continuous (ballSlope_nonneg hr L ε) (le_of_not_ge hs)

 theorem ballHeight_lower {r : ℝ} (hr : 0 ≤ r) (L : ℝ) {ε : ℝ} (hε : 0 < ε) (hL : 4*ε ≤ L) :
    r*(L-4*ε) ≤ ballHeight r L ε := by
    have hm := primitive_mono (contDiff_ballSlope r L ε).continuous (ballSlope_nonneg hr L ε)
    have hn := ballProfile_nonneg hr L hε (2*ε)
    have hc := (contDiff_ballSlope r L ε).continuous
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 (2*ε)) (hc.intervalIntegrable (μ := volume) (2*ε) (L-2*ε))
    have he : (∫ t in (2*ε)..(L-2*ε), ballSlope r L ε t) = r*(L-4*ε) := by
      calc
        _ = ∫ _t in (2*ε)..(L-2*ε), r := intervalIntegral.integral_congr (fun t ht => by
          rw [Set.uIcc_of_le (by linarith)] at ht
          exact ballSlope_middle r L hε ht.1 ht.2)
        _ = _ := by simp; ring
    change ballProfile r L ε (2*ε)+_ = ballProfile r L ε (L-2*ε) at hi
    rw [he] at hi
    have hmono : ballProfile r L ε (L-2*ε) ≤ ballHeight r L ε := hm (by linarith)
    linarith

 theorem exists_ball_parameters {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hAL : A < Real.pi*L) :
    ∃ r ε : ℝ, 0 < r ∧ r < Real.pi ∧ 0 < ε ∧ 4*ε < L ∧ A < r*(L-4*ε) := by
    obtain ⟨r,hrA,hrπ⟩ := exists_between ((div_lt_iff₀ hL).mpr (by simpa [mul_comm] using hAL))
    have hr : 0 < r := lt_of_le_of_lt (div_nonneg hA hL.le) hrA
    have hrl : A < r*L := (div_lt_iff₀ hL).mp hrA
    let ε := (r*L-A)/(8*r)
    have hε : 0 < ε := div_pos (sub_pos.mpr hrl) (by positivity)
    have he : 8*r*ε = r*L-A := by dsimp [ε]; field_simp
    refine ⟨r,ε,hr,hrπ,hε,?_,?_⟩ <;> nlinarith

end
end SmoothProfiles

end NonsqueezingInline

end OAI
