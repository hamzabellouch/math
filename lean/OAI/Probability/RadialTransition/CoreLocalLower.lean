import OAI.Probability.RadialTransition.TetraIntegral

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma partitionOn_one (φ : Potential) {b : ℝ} (hb : 0 ≤ b) (β : ℝ) :
    partitionOn φ (cube b) 1 β = b^3 := by
  simp [partitionOn, rawPartition, orderedEnergy, Measure.real, Measure.pi_univ,
    volume_cube, ENNReal.toReal_ofReal hb]

def blobTetraConstant (b : ℝ) : ℝ := (b/2)^3/((100000:ℝ)^9*24)

lemma blobTetraConstant_pos {b : ℝ} (hb : 0 < b) : 0 < blobTetraConstant b := by
  unfold blobTetraConstant
  positivity

lemma partitionOn_blob_tetra {t b β : ℝ} (hb : 0 ≤ b) (ht : 3*microLength t ≤ b/2) :
    blobTetraConstant b*Real.exp (-9*t) ≤ partitionOn (corePotential t) (cube b) 4 β := by
  have hsub : cube (b/2+3*microLength t) ⊆ cube b := by
    intro x hx k
    have hh := hx k
    exact ⟨hh.1, by linarith [hh.2]⟩
  have hp := partitionOn_mono (continuous_corePotential t) (bounded_corePotential t) β 4 hsub
    (by rw [volume_cube]; finiteness)
  have h1 := partitionOn_tetra_lower t (b/2) β (by positivity)
  have he : (b/2)^3*tetraEpsilon t^9/24 = blobTetraConstant b*Real.exp (-9*t) := by
    dsimp [tetraEpsilon, microLength, blobTetraConstant]
    rw [div_pow, div_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (9:ℝ)*(-t) = -9*t by ring]
    ring
  rw [he] at h1
  exact h1.trans hp

lemma core_local_grand_monomer {t b β h : ℝ} (hb : 0 ≤ b) (hβ : 0 ≤ β) :
    Real.exp (t*h)*b^3 ≤ grandOn (corePotential t) (cube b) β (t*h) := by
  have hs := grandOn_summable (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) hβ (by rw [volume_cube]; finiteness : volume (cube b) ≠ ⊤) (t*h)
  have hh := hs.le_tsum 1 (fun n _ => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg _ _ _ _))
  simpa only [Nat.cast_one, mul_one, partitionOn_one _ hb, grandOn] using hh

lemma core_local_grand_tetra {t b β h : ℝ} (hb : 0 ≤ b) (hβ : 0 ≤ β)
    (ht : 3*microLength t ≤ b/2) :
    blobTetraConstant b*Real.exp (t*(4*h-9)) ≤ grandOn (corePotential t) (cube b) β (t*h) := by
  have hs := grandOn_summable (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) hβ (by rw [volume_cube]; finiteness : volume (cube b) ≠ ⊤) (t*h)
  have hh := hs.le_tsum 4 (fun n _ => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg _ _ _ _))
  have hl := mul_le_mul_of_nonneg_left (partitionOn_blob_tetra hb ht (β := β)) (Real.exp_pos (t*h*4)).le
  have he : Real.exp (t*h*4)*(blobTetraConstant b*Real.exp (-9*t)) =
      blobTetraConstant b*Real.exp (t*(4*h-9)) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [he] at hl
  exact hl.trans hh

lemma core_local_log_monomer {t b β h : ℝ} (ht : 0 < t) (hb : 0 < b) (hβ : 0 ≤ β) :
    h+Real.log (b^3)/t ≤ Real.log (grandOn (corePotential t) (cube b) β (t*h))/t := by
  have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (pow_pos hb 3)) (core_local_grand_monomer hb.le hβ (t := t) (h := h))
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hb.ne'), Real.log_exp] at hh
  apply (le_div_iff₀ ht).mpr
  calc
    _ = t*h+Real.log (b^3) := by field_simp
    _ ≤ _ := hh

lemma core_local_log_tetra {t b β h : ℝ} (ht : 0 < t) (hb : 0 < b) (hβ : 0 ≤ β)
    (htb : 3*microLength t ≤ b/2) :
    4*h-9+Real.log (blobTetraConstant b)/t ≤ Real.log (grandOn (corePotential t) (cube b) β (t*h))/t := by
  have hh := Real.log_le_log (mul_pos (blobTetraConstant_pos hb) (Real.exp_pos _)) (core_local_grand_tetra hb.le hβ htb (h := h))
  rw [Real.log_mul (blobTetraConstant_pos hb).ne' (Real.exp_ne_zero _), Real.log_exp] at hh
  apply (le_div_iff₀ ht).mpr
  calc
    _ = Real.log (blobTetraConstant b)+t*(4*h-9) := by field_simp; ring
    _ ≤ _ := hh

end RadialTransition
end

end OAI
