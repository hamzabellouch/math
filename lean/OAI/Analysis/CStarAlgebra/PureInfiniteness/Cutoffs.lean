import OAI.Analysis.CStarAlgebra.PureInfiniteness.OrthogonalSlots

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section MoreHer
variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_left_remainder_sq {e z : A} (he : IsSelfAdjoint e) :
    ‖z - e * z‖ ^ 2 = ‖twoSidedRemainder e (z * star z)‖ := by
  rw [pow_two, ← CStarRing.norm_self_mul_star]
  congr 1
  simp only [twoSidedRemainder, star_sub, star_mul, he.star_eq]
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_right_remainder_sq {e z : A} (he : IsSelfAdjoint e) :
    ‖z - z * e‖ ^ 2 = ‖twoSidedRemainder e (star z * z)‖ := by
  rw [← norm_star (z - z * e), star_sub, star_mul, he.star_eq,
    norm_left_remainder_sq he, star_star]

lemma norm_left_remainder_sq_le {e z b : A} (he : IsSelfAdjoint e)
    (hen : ‖e‖ ≤ 1) (hle : z * star z ≤ b) :
    ‖z - e * z‖ ^ 2 ≤ 2 * ‖b - e * b‖ := by
  rw [norm_left_remainder_sq he]
  exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (twoSidedRemainder_mono he hle)
    (twoSidedRemainder_nonneg he (mul_star_self_nonneg z))).trans
      (norm_twoSidedRemainder_le hen b)

lemma norm_right_remainder_sq_le {e z b : A} (he : IsSelfAdjoint e)
    (hen : ‖e‖ ≤ 1) (hle : star z * z ≤ b) :
    ‖z - z * e‖ ^ 2 ≤ 2 * ‖b - e * b‖ := by
  rw [norm_right_remainder_sq he]
  exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (twoSidedRemainder_mono he hle)
    (twoSidedRemainder_nonneg he (star_mul_self_nonneg z))).trans
      (norm_twoSidedRemainder_le hen b)

lemma mem_Her_of_moduli {h z : A} (hl : z * star z ∈ Her h)
    (hr : star z * z ∈ Her h) : z ∈ Her h := by
  let b := z * star z + star z * z
  have hb : 0 ≤ b := add_nonneg (mul_star_self_nonneg z) (star_mul_self_nonneg z)
  have hbh : b ∈ Her h := (Her h).add_mem hl hr
  have hbl : z * star z ≤ b := le_add_of_nonneg_right (star_mul_self_nonneg z)
  have hbr : star z * z ≤ b := le_add_of_nonneg_left (mul_star_self_nonneg z)
  have hzc : z ∈ closure (Her h : Set A) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨e, he, hesa, hen, hs⟩ := Her_exists_approx_unit hb
      (show 0 < ε^2 / 8 by positivity)
    have hδ : 2 * ‖b - e * b‖ < (ε / 2)^2 := by linarith
    have hle : ‖z - e * z‖ < ε / 2 := by
      exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp
        ((norm_left_remainder_sq_le hesa hen hbl).trans_lt hδ)
    have hre : ‖z - z * e‖ < ε / 2 := by
      exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp
        ((norm_right_remainder_sq_le hesa hen hbr).trans_lt hδ)
    refine ⟨e * z * e, ?_, ?_⟩
    · change e * z * e ∈ Her h
      simpa only [hesa.star_eq] using Her_sandwich (Her_mono_of_mem hbh he) z
    · rw [dist_eq_norm]
      have heq : z - e * z * e = (z - e * z) + e * (z - z * e) := by noncomm_ring
      rw [heq]
      calc
        ‖(z - e * z) + e * (z - z * e)‖ ≤ ‖z - e * z‖ + ‖e * (z - z * e)‖ := norm_add_le _ _
        _ ≤ ‖z - e * z‖ + ‖e‖ * ‖z - z * e‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ ‖z - e * z‖ + ‖z - z * e‖ := by nlinarith [norm_nonneg (z - z * e)]
        _ < ε := by linarith
  rwa [(isClosed_Her h).closure_eq] at hzc

end MoreHer
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section Ramps
variable [PartialOrder A] [StarOrderedRing A]

lemma norm_mem_quasispectrum_of_nonneg {a : A} (ha : 0 ≤ a) :
    ‖a‖ ∈ quasispectrum ℝ a := by
  simpa using quasispectrum.algebraMap_mem ℝ
    (NonUnitalIsometricContinuousFunctionalCalculus.isGreatest_quasispectrum a ha).1

def rampFn (l u t : ℝ) : ℝ := min 1 (max (t-l) 0 / (u-l))

lemma continuous_rampFn (l u : ℝ) : Continuous (rampFn l u) :=
  continuous_const.min (((continuous_id.sub continuous_const).max continuous_const).div_const _)

lemma rampFn_nonneg {l u t : ℝ} (hlu : l ≤ u) : 0 ≤ rampFn l u t :=
  le_min (by norm_num) (div_nonneg (le_max_right _ _) (sub_nonneg.mpr hlu))

lemma rampFn_le_one (l u t : ℝ) : rampFn l u t ≤ 1 := min_le_left _ _

lemma rampFn_zero {l u t : ℝ} (ht : t ≤ l) : rampFn l u t = 0 := by
  simp only [rampFn, max_eq_right (sub_nonpos.mpr ht), zero_div, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]

lemma rampFn_one {l u t : ℝ} (hlu : l < u) (ht : u ≤ t) : rampFn l u t = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ (sub_pos.mpr hlu)).mpr
  rw [one_mul, max_eq_left (sub_nonneg.mpr (hlu.le.trans ht))]
  linarith

def ramp (a : A) (l u : ℝ) : A := cfcₙ (rampFn l u) a

lemma ramp_nonneg (a : A) {l u : ℝ} (hlu : l ≤ u) : 0 ≤ ramp a l u :=
  cfcₙ_nonneg (fun _ _ => rampFn_nonneg hlu)

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_ramp_le_one (a : A) {l u : ℝ} (hlu : l ≤ u) : ‖ramp a l u‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro t _
  rw [Real.norm_eq_abs, abs_of_nonneg (rampFn_nonneg hlu)]
  exact rampFn_le_one _ _ _

lemma ramp_mem_Her_cut {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) :
    ramp a l u ∈ Her (cut a l) := by
  have hcomp : ramp a l u = cfcₙ (fun t : ℝ => min 1 (t / (u-l))) (cut a l) := by
    unfold ramp cut
    exact cfcₙ_comp (fun t : ℝ => min 1 (t / (u-l))) (fun t : ℝ => max (t-l) 0) a
      (continuous_const.min (continuous_id.div_const _)).continuousOn (by norm_num)
      ((continuous_id.sub continuous_const).max continuous_const).continuousOn
      (by simp [max_eq_right (neg_nonpos.mpr hl)]) (.of_nonneg ha)
  rw [hcomp]
  exact cfcₙ_mem (𝕜' := ℂ) _ (self_mem_Her (cut_nonneg a l))

lemma norm_ramp_eq_one {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l)
    (hlu : l < u) (hu : u ≤ ‖a‖) : ‖ramp a l u‖ = 1 := by
  apply le_antisymm (norm_ramp_le_one a hlu.le)
  have ht := norm_apply_le_norm_cfcₙ (rampFn l u) a
    (norm_mem_quasispectrum_of_nonneg ha) (continuous_rampFn l u).continuousOn
    (rampFn_zero hl) (.of_nonneg ha)
  change 1 ≤ ‖cfcₙ (rampFn l u) a‖
  simpa only [rampFn_one hlu hu, norm_one] using ht

lemma map_ramp {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : A →⋆ₙₐ[ℂ] B) {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) :
    π (ramp a l u) = ramp (π a) l u :=
  π.map_cfcₙ (rampFn l u) a (continuous_rampFn l u).continuousOn (rampFn_zero hl)
    (map_continuous π) (.of_nonneg ha) (.of_nonneg (map_nonneg π ha))

lemma map_cut {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : A →⋆ₙₐ[ℂ] B) {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 ≤ l) :
    π (cut a l) = cut (π a) l :=
  π.map_cfcₙ (fun t : ℝ => max (t-l) 0) a
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hl)]) (map_continuous π)
    (.of_nonneg ha) (.of_nonneg (map_nonneg π ha))

lemma cut_cut {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u) :
    cut (cut a l) u = cut a (l+u) := by
  let f : ℝ → ℝ := fun t => max (t-l) 0
  let g : ℝ → ℝ := fun t => max (t-u) 0
  have hcomp := cfcₙ_comp g f a
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [g, max_eq_right (neg_nonpos.mpr hu)])
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [f, max_eq_right (neg_nonpos.mpr hl)]) (.of_nonneg ha)
  change cfcₙ g (cfcₙ f a) = _
  rw [← hcomp]
  apply cfcₙ_congr
  intro t _
  dsimp [f, g]
  by_cases ht : l ≤ t
  · rw [max_eq_left (sub_nonneg.mpr ht)]
    congr 1
    ring
  · rw [max_eq_right (by linarith : t-l ≤ 0), zero_sub,
      max_eq_right (neg_nonpos.mpr hu), max_eq_right (by linarith : t-(l+u) ≤ 0)]

lemma norm_sub_cut_le {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 ≤ l) :
    ‖a - cut a l‖ ≤ l := by
  conv_lhs => arg 1; lhs; rw [← cfcₙ_id ℝ a (.of_nonneg ha)]
  rw [cut, ← cfcₙ_sub id (fun t : ℝ => max (t-l) 0) a continuousOn_id rfl
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hl)])]
  apply norm_cfcₙ_le
  intro t ht
  have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg a ha t ht
  dsimp only [id_eq]
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hh : max (t-l) 0 ≤ t := max_le (by linarith) ht0
    linarith
  · have hh := le_max_left (t-l) 0
    linarith

omit [StarOrderedRing A] in
lemma ramp_mul_cut {a : A} (_ha : 0 ≤ a) {l u v : ℝ} (hl : 0 ≤ l)
    (hlu : l < u) (huv : u ≤ v) : ramp a l u * cut a v = cut a v := by
  have hv : 0 ≤ v := hl.trans (hlu.le.trans huv)
  unfold ramp cut
  rw [← cfcₙ_mul (rampFn l u) (fun t : ℝ => max (t-v) 0) a (continuous_rampFn l u).continuousOn (rampFn_zero hl)
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hv)])]
  apply cfcₙ_congr
  intro t _
  dsimp only
  by_cases ht : v ≤ t
  · rw [rampFn_one hlu (huv.trans ht), one_mul]
  · rw [max_eq_right (by linarith : t-v ≤ 0), mul_zero]

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_map {B : Type*} [NonUnitalCStarAlgebra B] (π : A →⋆ₙₐ[ℂ] B)
    {h k : A} (hk : k ∈ Her h) : π k ∈ Her (π h) := by
  have hc : IsClosed {k : A | π k ∈ Her (π h)} :=
    (isClosed_Her (π h)).preimage (map_continuous π)
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change π (h * a * star h) ∈ Her (π h)
  simpa only [map_mul, map_star] using sandwich_mem_Her (π h) (π a)

lemma Her_fixed_left {h t : A} (ht : t * h = h) {k : A} (hk : k ∈ Her h) : t * k = k := by
  have hc : IsClosed {k : A | t * k = k} := isClosed_eq (by fun_prop) continuous_id
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change t * (h * a * star h) = h * a * star h
  simp only [← mul_assoc, ht]

lemma Her_killed_left {h t : A} (ht : t * h = 0) {k : A} (hk : k ∈ Her h) : t * k = 0 := by
  have hc : IsClosed {k : A | t * k = 0} := isClosed_eq (by fun_prop) continuous_const
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change t * (h * a * star h) = 0
  simp only [← mul_assoc, ht, zero_mul]

lemma positive_kernel_factor [PartialOrder A] [StarOrderedRing A] {x Q z : A} (hx : 0 ≤ x) (hQ : IsSelfAdjoint Q)
    (hz : Q * (x * Q * z) = 0) : x * Q * z = 0 := by
  let s := CFC.sqrt x
  have hs : IsSelfAdjoint s := .of_nonneg (CFC.sqrt_nonneg x)
  have hss : s * s = x := CFC.sqrt_mul_sqrt_self x hx
  have hzero : star (s * Q * z) * (s * Q * z) = 0 := by
    rw [star_mul, star_mul, hs.star_eq, hQ.star_eq]
    calc
      star z * (Q * s) * (s * Q * z) = star z * (Q * ((s * s) * Q * z)) := by noncomm_ring
      _ = 0 := by rw [hss, hz, mul_zero]
  have hz' := (CStarRing.star_mul_self_eq_zero_iff _).mp hzero
  rw [← hss, mul_assoc s s, mul_assoc s, hz', mul_zero]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma cut_eq_cfc (d : B) {ε : ℝ} (hε : 0 ≤ ε) :
    cut d ε = cfc (fun t : ℝ => max (t - ε) 0) d := by
  unfold cut
  apply cfcₙ_eq_cfc
  · exact ((continuous_id.sub continuous_const).max continuous_const).continuousOn
  · simp [max_eq_right (neg_nonpos.mpr hε)]

lemma continuous_reciprocalCutoff {η : ℝ} (hη : 0 < η) :
    Continuous (fun t : ℝ => (max t η)⁻¹) := by
  apply Continuous.inv₀ (continuous_id.max continuous_const)
  intro t
  exact ne_of_gt (hη.trans_le (le_max_right t η))

omit [PartialOrder B] [StarOrderedRing B] in
lemma cutoffHer_factor {x Q : B} (hx : IsSelfAdjoint x) (hQ : IsSelfAdjoint Q)
    {η : ℝ} (hη : 0 < η) {k : B} (hk : k ∈ Her (cut (x * Q * Q * x) η)) :
    ∃ z : B, k = x * Q * z := by
  let U := x * Q * Q * x
  let f : ℝ → ℝ := fun t => (max t η)⁻¹
  have hU : IsSelfAdjoint U := by
    change star (x * Q * Q * x) = x * Q * Q * x
    simp only [star_mul, hx.star_eq, hQ.star_eq]
    noncomm_ring
  have hf : Continuous f := continuous_reciprocalCutoff hη
  have hg : Continuous (fun t : ℝ => max (t - η) 0) :=
    (continuous_id.sub continuous_const).max continuous_const
  have hfix : (U * cfc f U) * cut U η = cut U η := by
    rw [cut_eq_cfc U hη.le]
    conv_lhs => lhs; lhs; rw [← cfc_id ℝ U hU]
    rw [← cfc_mul _ _ U continuousOn_id hf.continuousOn]
    simp only [id_eq]
    have hif : ContinuousOn (fun t : ℝ => t * f t) (spectrum ℝ U) := (continuous_id.mul hf).continuousOn
    rw [← cfc_mul _ _ U hif hg.continuousOn]
    apply cfc_congr
    intro t _
    dsimp only
    by_cases ht : η ≤ t
    · simp only [f, max_eq_left ht, mul_inv_cancel₀ (ne_of_gt (hη.trans_le ht)), one_mul]
    · rw [max_eq_right (by linarith : t - η ≤ 0), mul_zero]
  have hfixk := Her_fixed_left hfix hk
  refine ⟨Q * x * cfc f U * k, ?_⟩
  calc
    k = (U * cfc f U) * k := hfixk.symm
    _ = x * Q * (Q * x * cfc f U * k) := by dsimp [U]; noncomm_ring

lemma selfConsistent_cutoff_bound {x d : B} (hx : 0 ≤ x) (hd : 0 ≤ d)
    {η h : ℝ} (hη : 0 < η) (hh : 0 ≤ h)
    (hmem : d ∈ Her (cut (x * cfc (fun t : ℝ => max (h - t) 0) d *
      cfc (fun t : ℝ => max (h - t) 0) d * x) η)) :
    d ≤ h • (1 : B) := by
  let Q := cfc (fun t : ℝ => max (h - t) 0) d
  have hQ : IsSelfAdjoint Q := IsSelfAdjoint.cfc
  have hq : Continuous (fun t : ℝ => max (h - t) 0) :=
    (continuous_const.sub continuous_id).max continuous_const
  have hk : Continuous (fun t : ℝ => max (t - h) 0) :=
    (continuous_id.sub continuous_const).max continuous_const
  have hkill : Q * cut d h = 0 := by
    rw [cut_eq_cfc d hh]
    change cfc (fun t : ℝ => max (h-t) 0) d * cfc (fun t : ℝ => max (t-h) 0) d = 0
    rw [← cfc_mul _ _ d hq.continuousOn hk.continuousOn, ← cfc_zero d (R := ℝ)]
    apply cfc_congr
    intro t _
    by_cases ht : h ≤ t
    · simp [max_eq_right (by linarith : h - t ≤ 0)]
    · simp [max_eq_right (by linarith : t - h ≤ 0)]
  have hcutmem : cut d h ∈ Her (cut (x * Q * Q * x) η) :=
    Her_mono_of_mem hmem (cut_mem_Her hd h)
  obtain ⟨z, hz⟩ := cutoffHer_factor (.of_nonneg hx) hQ hη hcutmem
  have hcutzero : cut d h = 0 := by
    rw [hz]
    exact positive_kernel_factor hx hQ (by rwa [← hz])
  rw [cut_eq_cfc d hh, ← cfc_zero d (R := ℝ)] at hcutzero
  have hzspec := eqOn_of_cfc_eq_cfc (ha := IsSelfAdjoint.of_nonneg hd) hcutzero
  rw [← Algebra.algebraMap_eq_smul_one, ← cfc_const h d]
  conv_lhs => rw [← cfc_id ℝ d (.of_nonneg hd)]
  apply (cfc_le_iff _ _ d continuousOn_id continuousOn_const (.of_nonneg hd)).mpr
  intro t ht
  have hm : max (t - h) 0 = 0 := hzspec ht
  have := le_max_left (t - h) 0
  dsimp only [id_eq]
  linarith

end UnitalCutBounds

end MainGap

end

end OAI
