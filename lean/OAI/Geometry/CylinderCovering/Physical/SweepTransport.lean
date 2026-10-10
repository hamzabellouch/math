import OAI.Geometry.CylinderCovering.Physical.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Physical.Coordinates
import OAI.Geometry.CylinderCovering.Radial.SqrtRealization

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace RadialPhysical
open CylinderCovering

lemma mapToCanonical_injective {b : ℝ} (hb : 0 < b) :
    Function.Injective (mapToCanonical b) := by
  intro x y h
  have h' : (2/b) • x = (2/b) • y := sub_left_injective h
  exact (smul_right_injective _ (div_ne_zero (by norm_num) (ne_of_gt hb))) h'

lemma mapCenteredToCanonical_injective {b : ℝ} (hb : 0 < b) :
    Function.Injective (mapCenteredToCanonical b) := by
  exact smul_right_injective _ (div_ne_zero one_ne_zero (ne_of_gt hb))

lemma halfheight_upperSweep_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ) :
    mapToCanonical b '' upperSweepOn false b eta T (Icc (-b) b) =
      RadialPairedSweep.upperSweep (Real.sqrt 2) (effectiveTilt b eta)
        (fun r => 2*T (b*r)) := by
  have hb0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨s, hs, rho, hrho, x, hx, rfl⟩, rfl⟩
    have hbs : b*(s/b)=s := by field_simp
    refine ⟨s/b, ⟨?_, ?_⟩, 2*rho, ⟨by nlinarith [hrho.1], ?_⟩, 2*x/b, ?_, ?_⟩
    · apply (le_div_iff₀ hb).mpr
      linarith [hs.1]
    · apply (div_le_iff₀ hb).mpr
      linarith [hs.2]
    · change 2*rho ≤ 2*T (b*(s/b))
      rw [hbs]
      linarith [hrho.2]
    · change |x| ≤ b at hx
      rw [abs_div, abs_mul, abs_of_pos hb]
      norm_num
      apply (div_le_iff₀ hb).mpr
      linarith
    · ext i
      fin_cases i <;> simp [mapToCanonical, upperPoint, point, height,
        RadialPairedSweep.point, RadialCaps.G, effectiveTilt] <;> field_simp <;> ring
  · rintro ⟨r, hr, rho, hrho, x, hx, hz⟩
    refine ⟨upperPoint b eta (rho/2) (b*r) (b*x/2), ?_, ?_⟩
    · refine ⟨b*r, ⟨?_, ?_⟩, rho/2, ⟨by nlinarith [hrho.1], by linarith [hrho.2]⟩,
        b*x/2, ?_, rfl⟩
      · nlinarith [hr.1]
      · nlinarith [hr.2]
      · change |b*x/2| ≤ b
        rw [abs_div, abs_mul, abs_of_pos hb]
        norm_num
        nlinarith
    · rw [hz]
      ext i
      fin_cases i <;> simp [mapToCanonical, upperPoint, point, height,
        RadialPairedSweep.point, RadialCaps.G, effectiveTilt] <;> field_simp <;> ring

lemma halfheight_lowerSweep_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ) :
    mapToCanonical b '' lowerSweepOn false b eta T (Icc (-b) b) =
      RadialPairedSweep.lowerSweep (Real.sqrt 2) (effectiveTilt b eta)
        (fun r => 2*T (b*r)) := by
  have hb0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨s, hs, rho, hrho, x, hx, rfl⟩, rfl⟩
    have hbs : b*(s/b)=s := by field_simp
    refine ⟨s/b, ⟨?_, ?_⟩, 2*rho, ⟨by nlinarith [hrho.1], ?_⟩, 2*x/b, ?_, ?_⟩
    · apply (le_div_iff₀ hb).mpr
      linarith [hs.1]
    · apply (div_le_iff₀ hb).mpr
      linarith [hs.2]
    · change 2*rho ≤ 2*T (b*(s/b))
      rw [hbs]
      linarith [hrho.2]
    · change |x| ≤ b at hx
      rw [abs_div, abs_mul, abs_of_pos hb]
      norm_num
      apply (div_le_iff₀ hb).mpr
      linarith
    · ext i
      fin_cases i <;> simp [mapToCanonical, lowerPoint, point, height,
        RadialPairedSweep.point, RadialCaps.G, effectiveTilt] <;> field_simp <;> ring
  · rintro ⟨r, hr, rho, hrho, x, hx, hz⟩
    refine ⟨lowerPoint false b eta (rho/2) (b*r) (b*x/2), ?_, ?_⟩
    · refine ⟨b*r, ⟨?_, ?_⟩, rho/2, ⟨by nlinarith [hrho.1], by linarith [hrho.2]⟩,
        b*x/2, ?_, rfl⟩
      · nlinarith [hr.1]
      · nlinarith [hr.2]
      · change |b*x/2| ≤ b
        rw [abs_div, abs_mul, abs_of_pos hb]
        norm_num
        nlinarith
    · rw [hz]
      ext i
      fin_cases i <;> simp [mapToCanonical, lowerPoint, point, height,
        RadialPairedSweep.point, RadialCaps.G, effectiveTilt] <;> field_simp <;> ring

lemma centered_upperSweep_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ) :
    mapCenteredToCanonical b '' upperSweepOn true b eta T (Icc (-b) b) =
      RadialPairedSweep.upperSweep (Real.sqrt 2) (effectiveTilt b eta)
        (fun r => T (b*r)) := by
  have hb0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨s, hs, rho, hrho, x, hx, rfl⟩, rfl⟩
    have hbs : b*(s/b)=s := by field_simp
    refine ⟨s/b, ⟨?_, ?_⟩, rho, ⟨hrho.1, ?_⟩, x/b, ?_, ?_⟩
    · apply (le_div_iff₀ hb).mpr
      linarith [hs.1]
    · apply (div_le_iff₀ hb).mpr
      linarith [hs.2]
    · change rho ≤ T (b*(s/b))
      rw [hbs]
      linarith [hrho.2]
    · change |x| ≤ 2*b at hx
      rw [abs_div, abs_of_pos hb]
      apply (div_le_iff₀ hb).mpr
      linarith
    · ext i
      fin_cases i <;> simp [mapCenteredToCanonical, upperPoint, point, height,
        RadialPairedSweep.point, RadialCaps.G, effectiveTilt] <;> field_simp
      ring
  · rintro ⟨r, hr, rho, hrho, x, hx, hz⟩
    refine ⟨upperPoint b eta rho (b*r) (b*x), ?_, ?_⟩
    · refine ⟨b*r, ⟨?_, ?_⟩, rho, hrho,
        b*x, ?_, rfl⟩
      · nlinarith [hr.1]
      · nlinarith [hr.2]
      · change |b*x| ≤ 2*b
        rw [abs_mul, abs_of_pos hb]
        nlinarith
    · rw [hz]
      ext i
      fin_cases i <;> simp [mapCenteredToCanonical, upperPoint, point, height,
        RadialPairedSweep.point, RadialCaps.G, effectiveTilt] <;> field_simp
      ring

lemma centered_lowerSweep_image {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ) :
    mapCenteredToCanonical b '' lowerSweepOn true b eta T (Icc (-b) b) =
      RadialPairedSweep.lowerSweep (Real.sqrt 2) (effectiveTilt b eta)
        (fun r => T (b*r)) := by
  have hb0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨s, hs, rho, hrho, x, hx, rfl⟩, rfl⟩
    have hbs : b*(s/b)=s := by field_simp
    refine ⟨s/b, ⟨?_, ?_⟩, rho, ⟨hrho.1, ?_⟩, x/b, ?_, ?_⟩
    · apply (le_div_iff₀ hb).mpr
      linarith [hs.1]
    · apply (div_le_iff₀ hb).mpr
      linarith [hs.2]
    · change rho ≤ T (b*(s/b))
      rw [hbs]
      linarith [hrho.2]
    · change |x| ≤ 2*b at hx
      rw [abs_div, abs_of_pos hb]
      apply (div_le_iff₀ hb).mpr
      linarith
    · ext i
      fin_cases i <;> simp [mapCenteredToCanonical, lowerPoint, point, height,
        RadialPairedSweep.point, RadialCaps.G, effectiveTilt] <;> field_simp
      ring
  · rintro ⟨r, hr, rho, hrho, x, hx, hz⟩
    refine ⟨lowerPoint true b eta rho (b*r) (b*x), ?_, ?_⟩
    · refine ⟨b*r, ⟨?_, ?_⟩, rho, hrho,
        b*x, ?_, rfl⟩
      · nlinarith [hr.1]
      · nlinarith [hr.2]
      · change |b*x| ≤ 2*b
        rw [abs_mul, abs_of_pos hb]
        nlinarith
    · rw [hz]
      ext i
      fin_cases i <;> simp [mapCenteredToCanonical, lowerPoint, point, height,
        RadialPairedSweep.point, RadialCaps.G, effectiveTilt] <;> field_simp
      ring

lemma physical_canonical_tetrahedron :
    RadialCoordinates.canonicalTetrahedron = RadialPairedSweep.tetrahedron (Real.sqrt 2) := by
  ext z
  constructor
  · rintro ⟨x, y, t, htl, htu, hx, hy, hz⟩
    exact ⟨x, y, t, hx, hy, hz⟩
  · rintro ⟨x, y, t, hx, hy, hz⟩
    exact ⟨x, y, t, by linarith [abs_nonneg x], by linarith [abs_nonneg y], hx, hy, hz⟩

lemma centered_modelBody {b : ℝ} (hb : 0 < b) :
    modelBody true b = centeredTetrahedron b := by
  ext z
  constructor
  · rintro ⟨x, y, t, hx, hy, hz⟩
    refine ⟨x, y, t, ?_, ?_, hx, hy, hz⟩
    · nlinarith [abs_nonneg x]
    · nlinarith [abs_nonneg y]
  · rintro ⟨x, y, t, htl, htu, hx, hy, hz⟩
    exact ⟨x, y, t, hx, hy, hz⟩

theorem halfheight_coverage_of_canonical {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (hcover : RadialPairedSweep.tetrahedron (Real.sqrt 2) ⊆
      RadialPairedSweep.upperSweep (Real.sqrt 2) (effectiveTilt b eta) (fun r => 2*T (b*r)) ∪
        RadialPairedSweep.lowerSweep (Real.sqrt 2) (effectiveTilt b eta) (fun r => 2*T (b*r))) :
    modelBody false b ⊆ upperSweepOn false b eta T (Icc (-b) b) ∪
      lowerSweepOn false b eta T (Icc (-b) b) := by
  intro z hz
  have hz' : mapToCanonical b z ∈ RadialPairedSweep.tetrahedron (Real.sqrt 2) := by
    rw [← physical_canonical_tetrahedron, ← mapToCanonical_tetrahedron hb]
    exact ⟨z, hz, rfl⟩
  have h := hcover hz'
  rw [← halfheight_upperSweep_image hb eta T, ← halfheight_lowerSweep_image hb eta T] at h
  rcases h with ⟨v, hv, he⟩ | ⟨v, hv, he⟩
  · left
    exact (mapToCanonical_injective hb he) ▸ hv
  · right
    exact (mapToCanonical_injective hb he) ▸ hv

theorem centered_coverage_of_canonical {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ)
    (hcover : RadialPairedSweep.tetrahedron (Real.sqrt 2) ⊆
      RadialPairedSweep.upperSweep (Real.sqrt 2) (effectiveTilt b eta) (fun r => T (b*r)) ∪
        RadialPairedSweep.lowerSweep (Real.sqrt 2) (effectiveTilt b eta) (fun r => T (b*r))) :
    modelBody true b ⊆ upperSweepOn true b eta T (Icc (-b) b) ∪
      lowerSweepOn true b eta T (Icc (-b) b) := by
  intro z hz
  have hz' : mapCenteredToCanonical b z ∈ RadialPairedSweep.tetrahedron (Real.sqrt 2) := by
    rw [← physical_canonical_tetrahedron, ← mapCenteredToCanonical_tetrahedron hb]
    exact ⟨z, (centered_modelBody hb) ▸ hz, rfl⟩
  have h := hcover hz'
  rw [← centered_upperSweep_image hb eta T, ← centered_lowerSweep_image hb eta T] at h
  rcases h with ⟨v, hv, he⟩ | ⟨v, hv, he⟩
  · left
    exact (mapCenteredToCanonical_injective hb he) ▸ hv
  · right
    exact (mapCenteredToCanonical_injective hb he) ▸ hv

lemma physical_linear_cap_profile (b eta beta : ℝ) :
    (fun r => 2*linearCap b eta beta (b*r)) =
      RadialCaps.linearCap beta (effectiveTilt b eta) := by
  funext r
  rw [linearCap_dictionary]
  simp [RadialCaps.linearCap, canonicalProfile, RadialCaps.H, add_comm]

lemma physical_square_cap_profile (b eta beta : ℝ) :
    (fun r => 2*squareCap b eta beta (b*r)) =
      RadialSqrtCap.cap beta (effectiveTilt b eta) := by
  funext r
  rw [squareCap_dictionary]
  simp [RadialSqrtCap.cap, RadialCaps.sqrtCap, canonicalProfile, RadialCaps.H, add_comm]

lemma centered_linear_cap_profile (b eta beta : ℝ) :
    (fun r => centeredLinearCap b eta beta (b*r)) =
      RadialCaps.linearCap beta (effectiveTilt b eta) := by
  funext r
  rw [centeredLinearCap_dictionary]
  simp [RadialCaps.linearCap, canonicalProfile, RadialCaps.H, add_comm]

theorem halfheight_linear_covers {b eta beta : ℝ} (hb : 0 < b)
    (hbeta : 0 ≤ beta) (heta : 0 < eta)
    (hsmall : eta*b^2 ≤ 2*beta/9) :
    modelBody false b ⊆ upperSweepOn false b eta (linearCap b eta beta) (Icc (-b) b) ∪
      lowerSweepOn false b eta (linearCap b eta beta) (Icc (-b) b) := by
  apply halfheight_coverage_of_canonical hb
  rw [physical_linear_cap_profile]
  exact RadialCapCoverage.linear_covers hbeta (mul_pos heta (sq_pos_of_pos hb)) hsmall

theorem centered_linear_covers {b eta beta : ℝ} (hb : 0 < b)
    (hbeta : 0 ≤ beta) (heta : 0 < eta)
    (hsmall : eta*b^2 ≤ 2*beta/9) :
    modelBody true b ⊆ upperSweepOn true b eta (centeredLinearCap b eta beta) (Icc (-b) b) ∪
      lowerSweepOn true b eta (centeredLinearCap b eta beta) (Icc (-b) b) := by
  apply centered_coverage_of_canonical hb
  rw [centered_linear_cap_profile]
  exact RadialCapCoverage.linear_covers hbeta (mul_pos heta (sq_pos_of_pos hb)) hsmall

theorem eventually_halfheight_linear_covers {b beta : ℝ} (hb : 0 < b) (hbeta : 0 < beta) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,
      modelBody false b ⊆ upperSweepOn false b eta (linearCap b eta beta) (Icc (-b) b) ∪
        lowerSweepOn false b eta (linearCap b eta beta) (Icc (-b) b) := by
  have hδ : 0 < (2*beta/9)/b^2 := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with eta heta
  exact halfheight_linear_covers hb hbeta.le heta.1
    ((lt_div_iff₀ (sq_pos_of_pos hb)).mp heta.2).le

theorem eventually_centered_linear_covers {b beta : ℝ} (hb : 0 < b) (hbeta : 0 < beta) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,
      modelBody true b ⊆ upperSweepOn true b eta (centeredLinearCap b eta beta) (Icc (-b) b) ∪
        lowerSweepOn true b eta (centeredLinearCap b eta beta) (Icc (-b) b) := by
  have hδ : 0 < (2*beta/9)/b^2 := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with eta heta
  exact centered_linear_covers hb hbeta.le heta.1
    ((lt_div_iff₀ (sq_pos_of_pos hb)).mp heta.2).le

theorem eventually_halfheight_square_covers {b beta : ℝ} (hb : 0 < b) (hbeta : 0 < beta) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,
      modelBody false b ⊆ upperSweepOn false b eta (squareCap b eta beta) (Icc (-b) b) ∪
        lowerSweepOn false b eta (squareCap b eta beta) (Icc (-b) b) := by
  obtain ⟨δ, hδ, hcover⟩ := RadialSqrtCap.exists_coverage_threshold hbeta
  have hδ' : 0 < δ/b^2 := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ'] with eta heta
  apply halfheight_coverage_of_canonical hb
  rw [physical_square_cap_profile]
  exact hcover (effectiveTilt b eta) (mul_pos heta.1 (sq_pos_of_pos hb))
    ((lt_div_iff₀ (sq_pos_of_pos hb)).mp heta.2)

theorem eventually_centered_square_covers {b beta : ℝ} (hb : 0 < b) (hbeta : 0 < beta) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,
      modelBody true b ⊆ upperSweepOn true b eta (fun s => 2*squareCap b eta beta s) (Icc (-b) b) ∪
        lowerSweepOn true b eta (fun s => 2*squareCap b eta beta s) (Icc (-b) b) := by
  obtain ⟨δ, hδ, hcover⟩ := RadialSqrtCap.exists_coverage_threshold hbeta
  have hδ' : 0 < δ/b^2 := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ'] with eta heta
  apply centered_coverage_of_canonical hb
  rw [physical_square_cap_profile]
  exact hcover (effectiveTilt b eta) (mul_pos heta.1 (sq_pos_of_pos hb))
    ((lt_div_iff₀ (sq_pos_of_pos hb)).mp heta.2)

lemma effectiveTilt_fractional_power {b eta : ℝ} (hb : 0 < b) (heta : 0 < eta) :
    effectiveTilt b eta ^ (5/2 : ℝ) = b^5 * eta^(5/2 : ℝ) := by
  unfold effectiveTilt
  rw [RadialCapCoverage.fractional_power _ (mul_pos heta (sq_pos_of_pos hb)),
    RadialCapCoverage.fractional_power eta heta,
    Real.sqrt_mul heta.le, Real.sqrt_sq hb.le]
  ring

lemma centered_cubic_cap_profile {b : ℝ} (hb : 0 < b) (eta c : ℝ) :
    (fun r => 1+eta^2*((b*r)^4+b^2*(b*r)^2)/2+c*eta^3) =
      RadialCaps.cubicCap (c/b^6) (effectiveTilt b eta) := by
  have hb0 := ne_of_gt hb
  funext r
  unfold RadialCaps.cubicCap RadialCaps.H effectiveTilt
  field_simp
  ring

lemma centered_fractional_cap_profile {b eta : ℝ} (hb : 0 < b) (heta : 0 < eta) (c : ℝ) :
    (fun r => 1+eta^2*((b*r)^4+b^2*(b*r)^2)/2+c*eta^(5/2:ℝ)) =
      RadialCaps.fractionalCap (c/b^5) (effectiveTilt b eta) := by
  have hb0 := ne_of_gt hb
  funext r
  unfold RadialCaps.fractionalCap RadialCaps.H
  rw [effectiveTilt_fractional_power hb heta]
  unfold effectiveTilt
  field_simp
  ring

theorem centered_cubic_covers {b eta c : ℝ} (hb : 0 < b) (heta : 0 < eta)
    (hc : (9/2 : ℝ)*b^6 ≤ c) :
    modelBody true b ⊆
      upperSweepOn true b eta (fun s => 1+eta^2*(s^4+b^2*s^2)/2+c*eta^3) (Icc (-b) b) ∪
      lowerSweepOn true b eta (fun s => 1+eta^2*(s^4+b^2*s^2)/2+c*eta^3) (Icc (-b) b) := by
  apply centered_coverage_of_canonical hb
  rw [centered_cubic_cap_profile hb]
  exact RadialCapCoverage.cubic_covers
    ((le_div_iff₀ (pow_pos hb 6)).mpr hc) (mul_pos heta (sq_pos_of_pos hb))

theorem eventually_centered_fractional_covers {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,
      modelBody true b ⊆
        upperSweepOn true b eta (fun s => 1+eta^2*(s^4+b^2*s^2)/2+c*eta^(5/2:ℝ)) (Icc (-b) b) ∪
        lowerSweepOn true b eta (fun s => 1+eta^2*(s^4+b^2*s^2)/2+c*eta^(5/2:ℝ)) (Icc (-b) b) := by
  have hc' : 0 < c/b^5 := div_pos hc (pow_pos hb 5)
  have hδ : 0 < ((2*(c/b^5)/9)^2)/b^2 := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with eta heta
  apply centered_coverage_of_canonical hb
  rw [centered_fractional_cap_profile hb heta.1]
  exact RadialCapCoverage.fractional_covers hc'
    (mul_pos heta.1 (sq_pos_of_pos hb))
    ((lt_div_iff₀ (sq_pos_of_pos hb)).mp heta.2).le

theorem halfheight_cubic_covers {b eta c : ℝ} (hb : 0 < b) (heta : 0 < eta)
    (hc : (9/2 : ℝ)*b^6 ≤ c) :
    modelBody false b ⊆
      upperSweepOn false b eta (fun s => (1+eta^2*(s^4+b^2*s^2)/2+c*eta^3)/2) (Icc (-b) b) ∪
      lowerSweepOn false b eta (fun s => (1+eta^2*(s^4+b^2*s^2)/2+c*eta^3)/2) (Icc (-b) b) := by
  apply halfheight_coverage_of_canonical hb
  have hcap : (fun r => 2*((1+eta^2*((b*r)^4+b^2*(b*r)^2)/2+c*eta^3)/2)) =
      RadialCaps.cubicCap (c/b^6) (effectiveTilt b eta) := by
    convert centered_cubic_cap_profile hb eta c using 1
    funext r
    ring
  rw [hcap]
  exact RadialCapCoverage.cubic_covers
    ((le_div_iff₀ (pow_pos hb 6)).mpr hc) (mul_pos heta (sq_pos_of_pos hb))

theorem eventually_halfheight_fractional_covers {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,
      modelBody false b ⊆
        upperSweepOn false b eta (fun s => (1+eta^2*(s^4+b^2*s^2)/2+c*eta^(5/2:ℝ))/2) (Icc (-b) b) ∪
        lowerSweepOn false b eta (fun s => (1+eta^2*(s^4+b^2*s^2)/2+c*eta^(5/2:ℝ))/2) (Icc (-b) b) := by
  have hc' : 0 < c/b^5 := div_pos hc (pow_pos hb 5)
  have hδ : 0 < ((2*(c/b^5)/9)^2)/b^2 := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with eta heta
  apply halfheight_coverage_of_canonical hb
  have hcap : (fun r => 2*((1+eta^2*((b*r)^4+b^2*(b*r)^2)/2+c*eta^(5/2:ℝ))/2)) =
      RadialCaps.fractionalCap (c/b^5) (effectiveTilt b eta) := by
    convert centered_fractional_cap_profile hb heta.1 c using 1
    funext r
    ring
  rw [hcap]
  exact RadialCapCoverage.fractional_covers hc'
    (mul_pos heta.1 (sq_pos_of_pos hb))
    ((lt_div_iff₀ (sq_pos_of_pos hb)).mp heta.2).le

end RadialPhysical

end

end OAI
