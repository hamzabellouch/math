import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! An explicit ambient disk compression. Its radial formula is the
identity outside the unit disk, has parameter reciprocal as inverse,
and compresses every fixed smaller disk as the parameter increases. -/
open Set Metric Topology
noncomputable section
namespace CircleDomainRigidity

def diskCompressionDenom (a t : ℝ) : ℝ := 1 + (a-1) * max (1-t) 0

def diskCompression (a : ℝ) (z : ℂ) : ℂ :=
  (diskCompressionDenom a ‖z‖)⁻¹ • z

lemma diskCompressionDenom_pos {a t : ℝ} (ha : 0<a) (ht : 0≤t) :
    0 < diskCompressionDenom a t := by
  unfold diskCompressionDenom
  by_cases h : t≤1
  · rw [max_eq_left (by linarith)]
    by_cases hzero : t=0
    · simpa [hzero] using ha
    · have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm hzero)
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h)]
  · rw [max_eq_right (by linarith)]
    simp

lemma diskCompression_norm {a : ℝ} (ha : 0<a) (z : ℂ) :
    ‖diskCompression a z‖ = ‖z‖ / diskCompressionDenom a ‖z‖ := by
  rw [diskCompression,norm_smul,Real.norm_eq_abs,abs_of_pos
    (inv_pos.mpr (diskCompressionDenom_pos ha (norm_nonneg z)))]
  rw [div_eq_mul_inv,mul_comm]

lemma diskCompression_eq_self {a : ℝ} {z : ℂ} (hz : 1≤‖z‖) :
    diskCompression a z=z := by
  simp [diskCompression,diskCompressionDenom,max_eq_right (show 1-‖z‖≤0 by linarith)]

lemma diskCompressionDenom_inverse {a t : ℝ} (ha : 0<a) (ht : 0≤t) :
    diskCompressionDenom a⁻¹ (t / diskCompressionDenom a t) =
      (diskCompressionDenom a t)⁻¹ := by
  have hd := diskCompressionDenom_pos ha ht
  by_cases h : t≤1
  · have he : diskCompressionDenom a t=1+(a-1)*(1-t) := by
      simp [diskCompressionDenom,max_eq_left (show 0≤1-t by linarith)]
    have htd : t≤diskCompressionDenom a t := by
      rw [he]
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h)]
    have hh : 0≤1-t/diskCompressionDenom a t := by
      have := (div_le_one hd).mpr htd
      linarith
    have hd0 : 1+(a-1)*(1-t)≠0 := he ▸ hd.ne'
    rw [diskCompressionDenom,max_eq_left hh,he]
    field_simp [ha.ne',hd0]
    ring
  · have he : diskCompressionDenom a t=1 := by
      simp [diskCompressionDenom,max_eq_right (show 1-t≤0 by linarith)]
    rw [he,div_one]
    simp [diskCompressionDenom,max_eq_right (show 1-t≤0 by linarith)]

lemma diskCompression_inverse {a : ℝ} (ha : 0<a) (z : ℂ) :
    diskCompression a⁻¹ (diskCompression a z)=z := by
  rw [diskCompression,diskCompression_norm ha,
    diskCompressionDenom_inverse ha (norm_nonneg z),inv_inv]
  unfold diskCompression
  rw [smul_smul,mul_inv_cancel₀ (diskCompressionDenom_pos ha (norm_nonneg z)).ne',one_smul]

lemma diskCompression_continuous {a : ℝ} (ha : 0<a) : Continuous (diskCompression a) := by
  have hd : Continuous (fun z : ℂ => diskCompressionDenom a ‖z‖) := by
    unfold diskCompressionDenom
    fun_prop
  have hi : Continuous (fun z : ℂ => (diskCompressionDenom a ‖z‖)⁻¹) :=
    hd.inv₀ (fun z => (diskCompressionDenom_pos ha (norm_nonneg z)).ne')
  exact hi.smul (continuous_id : Continuous (fun z : ℂ => z))

def diskCompressionHomeomorph (a : ℝ) (ha : 0<a) : ℂ ≃ₜ ℂ where
  toFun := diskCompression a
  invFun := diskCompression a⁻¹
  left_inv := diskCompression_inverse ha
  right_inv := by
    intro z
    simpa only [inv_inv] using diskCompression_inverse (inv_pos.mpr ha) z
  continuous_toFun := diskCompression_continuous ha
  continuous_invFun := diskCompression_continuous (inv_pos.mpr ha)

lemma diskCompression_norm_bound {a R : ℝ} (ha : 0<a) (hR : R<1)
    {z : ℂ} (hz : ‖z‖≤R) :
    ‖diskCompression a z‖ ≤ R / (a*(1-R)) := by
  have hR0 : 0≤R := (norm_nonneg z).trans hz
  have hb : 0<a*(1-R) := mul_pos ha (sub_pos.mpr hR)
  have hdge : a*(1-R) ≤ diskCompressionDenom a ‖z‖ := by
    unfold diskCompressionDenom
    rw [max_eq_left (by linarith [norm_nonneg z])]
    nlinarith [norm_nonneg z, mul_nonneg ha.le (sub_nonneg.mpr hz)]
  rw [diskCompression_norm ha]
  exact div_le_div₀ hR0 hz hb hdge

lemma exists_disk_compression {R ε : ℝ} (hR0 : 0≤R) (hR : R<1) (hε : 0<ε) :
    ∃ a : ℝ, 0<a ∧ ∀ z : ℂ, ‖z‖≤R → ‖diskCompression a z‖<ε := by
  let a := (R+1)/(ε*(1-R))+1
  have hb : 0<ε*(1-R) := mul_pos hε (sub_pos.mpr hR)
  have ha : 0<a := by dsimp [a]; positivity
  have hab : R<a*(ε*(1-R)) := by
    dsimp [a]
    rw [add_mul,div_mul_cancel₀ _ hb.ne',one_mul]
    linarith
  refine ⟨a,ha,?_⟩
  intro z hz
  apply (diskCompression_norm_bound ha hR hz).trans_lt
  apply (div_lt_iff₀ (mul_pos ha (sub_pos.mpr hR))).mpr
  nlinarith [hab]

end CircleDomainRigidity

end

end OAI
