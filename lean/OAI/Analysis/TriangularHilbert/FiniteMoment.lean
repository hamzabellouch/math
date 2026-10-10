import OAI.Analysis.TriangularHilbert.SampledConvergence

namespace OAI

universe uκ

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

def complexMoment (z : ℂ) : ℝ := ‖z‖*Real.sqrt ‖z‖
lemma complexMoment_nonneg (z : ℂ) : 0 ≤ complexMoment z := by unfold complexMoment; positivity
@[simp] lemma complexMoment_zero : complexMoment 0 = 0 := by simp [complexMoment]
lemma continuous_complexMoment : Continuous complexMoment := continuous_norm.mul (Real.continuous_sqrt.comp continuous_norm)
lemma complexMoment_le {z : ℂ} {b : ℝ} (hz : ‖z‖ ≤ b) : complexMoment z ≤ b*Real.sqrt b :=
  mul_le_mul hz (Real.sqrt_le_sqrt hz) (Real.sqrt_nonneg _) ((norm_nonneg _).trans hz)

def finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k => complexMoment (f k))
lemma finiteMoment_eq {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    ∃ k, finiteMoment f = complexMoment (f k) := by
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => complexMoment (f k))
  exact ⟨k,hk⟩
lemma le_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) (k : κ) :
    complexMoment (f k) ≤ finiteMoment f  := by
  exact Finset.le_sup' (fun k => complexMoment (f k)) (Finset.mem_univ k)
lemma finiteMoment_nonneg {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) :
    0 ≤ finiteMoment f := by
  obtain ⟨k,hk⟩ := finiteMoment_eq f
  rw [hk]
  exact complexMoment_nonneg _
lemma finiteMoment_le {κ : Type uκ} [Fintype κ] [Nonempty κ] (f : κ → ℂ) {b : ℝ}
    (hb : ∀ k, ‖f k‖ ≤ b) : finiteMoment f ≤ b*Real.sqrt b :=
  Finset.sup'_le _ _ (fun k _ => complexMoment_le (hb k))
@[simp] lemma finiteMoment_zero {κ : Type uκ} [Fintype κ] [Nonempty κ] : finiteMoment (fun _ : κ => (0:ℂ)) = 0 := by
  simp [finiteMoment]
lemma continuous_finiteMoment {κ : Type uκ} [Fintype κ] [Nonempty κ] : Continuous (finiteMoment (κ := κ)) := by
  unfold finiteMoment
  exact Continuous.finset_sup'_apply _ (fun k _ => continuous_complexMoment.comp (continuous_apply k))
end
end TriangularHilbert
end

end OAI
