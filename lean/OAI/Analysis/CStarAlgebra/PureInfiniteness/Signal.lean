import OAI.Analysis.CStarAlgebra.PureInfiniteness.IdealComparison

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance signalCutPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance signalCutStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma Her_cut_lower {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 ≤ δ)
    {p : A} (hp : p ∈ Her (cut a δ)) :
    δ • (star p * p) ≤ star p * a * p := by
  have hc : IsClosed {p : A | δ • (star p * p) ≤ star p * a * p} :=
    isClosed_le (by fun_prop) (by fun_prop)
  apply closure_minimal (s := Set.range (fun w : A => cut a δ * w * star (cut a δ))) _ hc hp
  rintro _ ⟨w, rfl⟩
  change δ • (star (cut a δ * w * star (cut a δ)) *
      (cut a δ * w * star (cut a δ))) ≤
    star (cut a δ * w * star (cut a δ)) * a * (cut a δ * w * star (cut a δ))
  have hh := star_left_conjugate_le_conjugate (cut_sandwich_lower ha.isSelfAdjoint hδ)
    (w * cut a δ)
  simpa only [star_mul, (cut_nonneg a δ).isSelfAdjoint.star_eq,
    mul_smul_comm, smul_mul_assoc, mul_assoc] using hh

lemma norm_cut_le_sub {a : A} (ha : 0 ≤ a) {M δ : ℝ} (han : ‖a‖ ≤ M)
    (hδ : δ ≤ M) : ‖cut a δ‖ ≤ M - δ := by
  apply norm_cfcₙ_le
  intro t ht
  have htM : t ≤ M := (le_abs_self t).trans
    ((NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a ht ha.isSelfAdjoint).trans han)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) (sub_nonneg.mpr hδ)

lemma cut_eq_zero_of_norm_le_nonunital {a : A} (ha : 0 ≤ a) {δ : ℝ} (haδ : ‖a‖ ≤ δ) :
    cut a δ = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using norm_cut_le_sub ha haδ le_rfl) (norm_nonneg _)

end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
local instance signalComparisonPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance signalComparisonStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance signalOperatorPartialOrder (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance signalOperatorStarOrderedRing (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

lemma signal_cut_comparison (hP : PropertyP A) {a p : A} (ha : 0 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (hpH : p ∈ Her (ramp a δ (2*δ)))
    (hsignal : NormSignal (ramp a δ (2*δ)) p) :
    ScalarCuntzLE (cut a (2*δ)) (star p * a * p) := by
  let v := star p * a * p
  have hv : 0 ≤ v := star_left_conjugate_nonneg ha p
  let V : Unitization ℂ A := Unitization.inr v
  have hV : 0 ≤ V := Unitization.inr_nonneg_iff.mpr hv
  let J := closedIdeal V hV.isSelfAdjoint
  have hcut : (Unitization.inr (cut a (2*δ)) : Unitization ℂ A) ∈ J := by
    by_contra hh
    obtain ⟨R,hRJ,hRcut⟩ := exists_rep_killing_ideal J
      (closedIdeal_closed V hV.isSelfAdjoint)
      (fun x z hz => closedIdeal_left hV.isSelfAdjoint hz x)
      (fun x z hz => closedIdeal_right hV.isSelfAdjoint hz x) hh
    let π := R.hom.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
    have hvzero : π v = 0 := hRJ V (self_mem_closedIdeal V hV.isSelfAdjoint)
    have hlower := Her_cut_lower ha hδ.le
      (Her_mono_of_mem (ramp_mem_Her_cut ha hδ.le) hpH)
    have hpos := map_nonneg π (sub_nonneg.mpr hlower)
    have hsmul (r : ℝ) (z : A) : π (r • z)=r • π z :=
      LinearMapClass.map_smul_of_tower π r z
    change 0 ≤ π (v - δ • (star p * p)) at hpos
    rw [map_sub, hvzero, hsmul, map_mul, map_star] at hpos
    have hz : δ • (star (π p) * π p) = 0 :=
      le_antisymm (by simpa only [zero_sub, neg_nonneg] using hpos)
        (smul_nonneg hδ.le (star_mul_self_nonneg _))
    have hpzero : π p = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp
      ((smul_eq_zero.mp hz).resolve_left hδ.ne')
    have hnorm : 2*δ < ‖π a‖ := by
      by_contra! hn
      apply hRcut
      change π (cut a (2*δ)) = 0
      rw [map_cut π ha (by positivity), cut_eq_zero_of_norm_le (map_nonneg π ha) hn]
    have hramp : ‖π (ramp a δ (2*δ))‖ = 1 := by
      rw [map_ramp π ha hδ.le]
      exact norm_ramp_eq_one (map_nonneg π ha) hδ.le (by linarith) hnorm.le
    have hpn := hsignal R (by change (1/2:ℝ) < ‖π (ramp a δ (2*δ))‖; rw [hramp]; norm_num)
    change ‖π p‖ = 1 at hpn
    rw [hpzero, norm_zero] at hpn
    norm_num at hpn
  apply scalarCuntzLE_of_inr hv
  exact closedIdeal_comparison (Unitization.inr_nonneg_iff.mpr (cut_nonneg _ _)) hV
    ((hP v hv).map (Unitization.inrNonUnitalStarAlgHom ℂ A)) hcut

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance signalCoefficientPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance signalCoefficientStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma signal_coefficient (hP : PropertyP A) {a p : A} (ha : 0 ≤ a) (han : ‖a‖ ≤ 1)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1/2) (hρ : 0 < ρ) (hρδ : ρ ≤ 2*δ)
    (hpH : p ∈ Her (ramp a δ (2*δ))) (hsignal : NormSignal (ramp a δ (2*δ)) p) :
    ∃ w : A, ‖star (p*w)*a*(p*w)-a‖ < 2*δ+ρ ∧
      ‖p*w‖ ≤ Real.sqrt δ⁻¹ := by
  have hcomp := signal_cut_comparison hP ha hδ hpH hsignal
  obtain ⟨w,hw⟩ := hcomp.exists_approx hρ
  have hw' : ‖star (p*w)*a*(p*w) - cut a (2*δ)‖ < ρ := by
    simpa only [star_mul, mul_assoc] using hw
  refine ⟨w, ?_, ?_⟩
  · calc
      ‖star (p*w)*a*(p*w)-a‖ ≤
          ‖star (p*w)*a*(p*w)-cut a (2*δ)‖ + ‖cut a (2*δ)-a‖ := by simpa only [dist_eq_norm] using dist_triangle (star (p*w)*a*(p*w)) (cut a (2*δ)) a
      _ < ρ + 2*δ := add_lt_add_of_lt_of_le hw'
        (by simpa only [norm_sub_rev] using norm_sub_cut_le ha (by positivity : 0 ≤ 2*δ))
      _ = 2*δ+ρ := by ring
  · have hlower := star_left_conjugate_le_conjugate
      (Her_cut_lower ha hδ.le (Her_mono_of_mem (ramp_mem_Her_cut ha hδ.le) hpH)) w
    have hlower' : δ • (star (p*w)*(p*w)) ≤ star (p*w)*a*(p*w) := by
      simpa only [star_mul, mul_smul_comm, smul_mul_assoc, mul_assoc] using hlower
    have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hlower'
      (smul_nonneg hδ.le (star_mul_self_nonneg (p*w)))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, CStarRing.norm_star_mul_self] at hn
    have hupper : ‖star (p*w)*a*(p*w)‖ < 1 := by
      calc
        ‖star (p*w)*a*(p*w)‖ ≤
            ‖star (p*w)*a*(p*w)-cut a (2*δ)‖ + ‖cut a (2*δ)‖ := norm_le_norm_sub_add _ _
        _ < ρ + (1-2*δ) := add_lt_add_of_lt_of_le hw'
          (norm_cut_le_sub ha han (by linarith))
        _ ≤ 1 := by linarith
    have hsq : ‖p*w‖ ^ 2 ≤ δ⁻¹ := by
      have hh : δ * (‖p*w‖ ^ 2) ≤ 1 := by nlinarith
      have hh' := (le_inv_mul_iff₀ hδ).mpr hh
      simpa only [mul_one] using hh'
    have hsqrt := Real.sq_sqrt (inv_nonneg.mpr hδ.le)
    nlinarith [Real.sqrt_nonneg δ⁻¹, norm_nonneg (p*w)]

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance signalProductsPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance signalProductsStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma HerCompression.right_products {p q c : A} {κ : ℝ} (hκ : 0 ≤ κ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h : HerCompression p q c κ) (w z : A) :
    ‖star (p*w) * c * (q*z)‖ ≤ κ * ‖p*w‖ * ‖q*z‖ := by
  let : PartialOrder (Her p) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Her p) := CStarAlgebra.spectralOrderedRing _
  let : PartialOrder (Her q) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Her q) := CStarAlgebra.spectralOrderedRing _
  let ap := CStarAlgebra.increasingApproximateUnit (Her p)
  let aq := CStarAlgebra.increasingApproximateUnit (Her q)
  let pp : Her p := ⟨p, self_mem_Her hp⟩
  let qq : Her q := ⟨q, self_mem_Her hq⟩
  have htp : Tendsto (fun e : Her p => (e : A) * (p*w))
      (CStarAlgebra.approximateUnit (Her p)) (𝓝 (p*w)) := by
    have hh := ((continuous_subtype_val.tendsto pp).comp (ap.tendsto_mul_right pp)).mul
      (tendsto_const_nhds (x := w))
    change Tendsto (fun e : Her p => ((e : A) * p) * w) _ (𝓝 (p*w)) at hh
    simpa only [mul_assoc] using hh
  have htq : Tendsto (fun e : Her q => (e : A) * (q*z))
      (CStarAlgebra.approximateUnit (Her q)) (𝓝 (q*z)) := by
    have hh := ((continuous_subtype_val.tendsto qq).comp (aq.tendsto_mul_right qq)).mul
      (tendsto_const_nhds (x := z))
    change Tendsto (fun e : Her q => ((e : A) * q) * z) _ (𝓝 (q*z)) at hh
    simpa only [mul_assoc] using hh
  have ht := ((htp.comp tendsto_fst).star.mul (tendsto_const_nhds (x := c))).mul
    (htq.comp tendsto_snd)
  apply le_of_tendsto ht.norm
  filter_upwards [ap.eventually_norm.prod_mk aq.eventually_norm] with ef hef
  rcases ef with ⟨e,f⟩
  change ‖star ((e : A)*(p*w))*c*((f : A)*(q*z))‖ ≤ _
  have he : ‖(e : A)‖ ≤ 1 := hef.1
  have hf : ‖(f : A)‖ ≤ 1 := hef.2
  calc
    ‖star ((e : A)*(p*w))*c*((f : A)*(q*z))‖ =
        ‖star (p*w) * (star (e : A)*c*(f : A)) * (q*z)‖ := by
      simp only [star_mul, mul_assoc]
    _ ≤ ‖p*w‖ * ‖star (e : A)*c*(f : A)‖ * ‖q*z‖ := by
      grw [norm_mul_le, norm_mul_le, norm_star]
    _ ≤ ‖p*w‖ * (κ*‖(e : A)‖*‖(f : A)‖) * ‖q*z‖ := by
      gcongr
      simpa only [norm_star] using h (star (e : A)) (star_mem e.property) (f : A) f.property
    _ ≤ ‖p*w‖ * (κ*1*1) * ‖q*z‖ := by gcongr
    _ = κ * ‖p*w‖ * ‖q*z‖ := by ring

end MainGap

end

end OAI
