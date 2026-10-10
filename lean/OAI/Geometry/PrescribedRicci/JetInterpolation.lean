import Mathlib
import OAI.Geometry.PrescribedRicci.DirectionalInterpolation

namespace OAI

/-! Jet Interpolation. -/

section

 
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def jet (e : ι → E) (f : E → ℝ) : {j : ℕ} → (Fin j → ι) → E → ℝ
  | 0,_ => f
  | _+1,w => dir (e (w 0)) (jet e f (w ∘ Fin.succ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Nonempty ι] in
lemma jet_smooth (e : ι → E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {j : ℕ} (w : Fin j → ι) : ContDiff ℝ ∞ (jet e f w) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact dir_smooth _ (ih _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Nonempty ι] in
lemma jet_compact (e : ι → E) {f : E → ℝ} (hf : HasCompactSupport f)
    {j : ℕ} (w : Fin j → ι) : HasCompactSupport (jet e f w) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact dir_compact _ (ih _)

def jetNorm (e : ι → E) (f : E → ℝ) (j : ℕ) (p : ℝ≥0∞) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun w : Fin j → ι => lpNorm (jet e f w) p volume)

lemma lpNorm_jet_le (e : ι → E) (f : E → ℝ) {j : ℕ} (w : Fin j → ι) (p : ℝ≥0∞) :
    lpNorm (jet e f w) p volume ≤ jetNorm e f j p := by
  exact Finset.le_sup' (fun w : Fin j → ι => lpNorm (jet e f w) p volume) (Finset.mem_univ w)

lemma jetNorm_nonneg (e : ι → E) (f : E → ℝ) (j : ℕ) (p : ℝ≥0∞) :
    0 ≤ jetNorm e f j p :=
  le_trans lpNorm_nonneg (lpNorm_jet_le e f (fun _ => Classical.choice ‹Nonempty ι›) p)

lemma jetNorm_attained (e : ι → E) (f : E → ℝ) (j : ℕ) (p : ℝ≥0∞) :
    ∃ w : Fin j → ι, jetNorm e f j p = lpNorm (jet e f w) p volume := by
  obtain ⟨w,_,hw⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ) Finset.univ_nonempty
    (fun w : Fin j → ι => lpNorm (jet e f w) p volume)
  exact ⟨w,hw⟩

lemma jetNorm_step (e : ι → E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (j : ℕ) {p : ℝ} (hp : 2 < p) (α β r s : ℝ≥0∞)
    [ENNReal.HolderTriple α β s] [ENNReal.HolderTriple s r 1]
    (hr : r * ENNReal.ofReal (p-2) = ENNReal.ofReal p) :
    (jetNorm e f (j+1) (ENNReal.ofReal p))^2 ≤
      (p-1)*jetNorm e f j α*jetNorm e f (j+2) β := by
  obtain ⟨w,hw⟩ := jetNorm_attained e f (j+1) (ENNReal.ofReal p)
  rw [hw]
  let w₀ : Fin j → ι := w ∘ Fin.succ
  have he : dir (e (w 0)) (dir (e (w 0)) (jet e f w₀)) =
      jet e f (Fin.cons (w 0) (Fin.cons (w 0) w₀)) := by
    simp only [jet,Fin.cons_zero,Fin.cons_succ,Function.comp_def]
  have h := directional_lp_interpolation hp α β r s hr (e (w 0))
    (jet_smooth e hf w₀) (jet_compact e hc w₀)
  rw [he] at h
  apply h.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (lpNorm_jet_le e f w₀ α) (by linarith only [hp])
  · exact lpNorm_jet_le e f _ β
  · exact lpNorm_nonneg
  · exact mul_nonneg (by linarith only [hp]) (jetNorm_nonneg e f j α)
end TameInterpolation

end
end

end OAI
