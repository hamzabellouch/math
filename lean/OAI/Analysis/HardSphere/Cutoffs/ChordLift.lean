import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff

variable (L : ℝ) [hL : Fact (0<L)]

def chordLift (x : ℝ) : ℝ := (L/Real.pi*Real.sin (Real.pi/L*x))^2

lemma chordLift_periodic : Function.Periodic (chordLift L) L := by
  intro x
  dsimp [chordLift]
  have h : Real.pi/L*(x+L)=Real.pi/L*x+Real.pi := by
    field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
  rw [h,Real.sin_add_pi]
  ring

def chord (x : AddCircle L) : ℝ := (chordLift_periodic L).lift x

@[simp] lemma chord_coe (x : ℝ) : chord L (x : AddCircle L)=chordLift L x :=
  (chordLift_periodic L).lift_coe x

omit hL in
lemma chordLift_smooth : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (chordLift L) := by
  change ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : ℝ ↦ (L/Real.pi*Real.sin (Real.pi/L*x))^2)
  fun_prop

lemma chord_continuous : Continuous (chord L) := by
  apply (QuotientAddGroup.isOpenMap_coe.isQuotientMap (AddCircle.continuous_mk' L) QuotientAddGroup.mk_surjective).continuous_iff.mpr
  simpa only [Function.comp_def,chord_coe] using (chordLift_smooth L).continuous

lemma chordLift_derivative (x : ℝ) : HasDerivAt (chordLift L)
    (2*(L/Real.pi*Real.sin (Real.pi/L*x))*Real.cos (Real.pi/L*x)) x := by
  have h := (((hasDerivAt_id x).const_mul (Real.pi/L)).sin.const_mul (L/Real.pi)).pow 2
  apply h.congr_deriv
  dsimp
  field_simp [ne_of_gt hL.out, Real.pi_ne_zero]

lemma chordLift_derivative_sq_le (x : ℝ) :
    (deriv (chordLift L) x)^2 ≤ 4*chordLift L x := by
  rw [(chordLift_derivative L x).deriv]
  have hc : Real.cos (Real.pi/L*x)^2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi/L*x),sq_nonneg (Real.sin (Real.pi/L*x))]
  simpa only [chordLift] using (show
    (2*(L/Real.pi*Real.sin (Real.pi/L*x))*Real.cos (Real.pi/L*x))^2≤
      4*(L/Real.pi*Real.sin (Real.pi/L*x))^2 by
        nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (2*(L/Real.pi*Real.sin (Real.pi/L*x))))])

lemma centered_representative (x : AddCircle L) :
    ∃ t : ℝ, (t : AddCircle L)=x ∧ |t|≤L/2 ∧ ‖x‖=|t| := by
  let t := (AddCircle.equivIco L (-L/2) x).val
  have ht : (t : AddCircle L)=x := AddCircle.coe_equivIco
  have hb : |t|≤L/2 := by
    apply abs_le.mpr
    constructor
    · simpa only [neg_div] using (AddCircle.equivIco L (-L/2) x).property.1
    · have hu := (AddCircle.equivIco L (-L/2) x).property.2
      dsimp [t]
      linarith
  exact ⟨t,ht,hb,ht ▸ ((AddCircle.norm_coe_eq_abs_iff L (ne_of_gt hL.out)).mpr
    (by simpa only [abs_of_pos hL.out] using hb))⟩

lemma chord_nonneg (x : AddCircle L) : 0≤chord L x := by
  obtain ⟨t,rfl,_,_⟩ := centered_representative L x
  exact sq_nonneg _

lemma chord_le_norm_sq (x : AddCircle L) : chord L x≤‖x‖^2 := by
  obtain ⟨t,rfl,ht,hx⟩ := centered_representative L x
  rw [chord_coe,hx]
  have h : |L/Real.pi*Real.sin (Real.pi/L*t)|≤|t| := by
    rw [abs_mul,abs_of_pos (div_pos hL.out Real.pi_pos)]
    calc
      L/Real.pi*|Real.sin (Real.pi/L*t)|≤L/Real.pi*|Real.pi/L*t| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (le_of_lt (div_pos hL.out Real.pi_pos))
      _ = |t| := by
        rw [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)]
        field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
  dsimp [chordLift]
  calc
    _ = |L/Real.pi*Real.sin (Real.pi/L*t)|^2 := (sq_abs _).symm
    _ ≤ |t|^2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr h

lemma norm_sq_le_chord (x : AddCircle L) : ‖x‖^2≤(Real.pi/2)^2*chord L x := by
  obtain ⟨t,rfl,ht,hx⟩ := centered_representative L x
  have ha : |Real.pi/L*t|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)]
    calc
      Real.pi/L*|t|≤Real.pi/L*(L/2) := mul_le_mul_of_nonneg_left ht (le_of_lt (div_pos Real.pi_pos hL.out))
      _ = Real.pi/2 := by field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
  have hb : |t|≤Real.pi/2*|L/Real.pi*Real.sin (Real.pi/L*t)| := by
    have h := mul_le_mul_of_nonneg_left (Real.mul_abs_le_abs_sin ha)
      (show 0≤L/2 from (div_pos hL.out (by norm_num)).le)
    simp only [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)] at h
    rw [abs_mul,abs_of_pos (div_pos hL.out Real.pi_pos)]
    have he : L/2*(2/Real.pi*(Real.pi/L*|t|))=|t| := by
      field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
    rw [he] at h
    convert h using 1; first | rfl | (field_simp [ne_of_gt hL.out, Real.pi_ne_zero])
  rw [chord_coe,hx]
  dsimp [chordLift]
  calc
    _ ≤ (Real.pi/2*|L/Real.pi*Real.sin (Real.pi/L*t)|)^2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).mpr hb
    _ = _ := by rw [mul_pow,sq_abs]

end PeriodicCutoff

end

end OAI
