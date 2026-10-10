import OAI.Probability.InvariantIsing.Core.Model

namespace OAI

/-! Square extrema of finite nonnegative families. -/
noncomputable section
open scoped Classical
namespace InvariantIsing

lemma finite_sup_square {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (q : ℝ) (hq : 0 ≤ q) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => q*(f i)^2)=
      q*(Finset.univ.sup' Finset.univ_nonempty f)^2 := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  have hle (i : ι) : f i ≤ f a := by
    rw [← ha]
    exact Finset.le_sup' f (Finset.mem_univ i)
  rw [ha]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (hf i) (hf a) |>.mpr (hle i)) hq
  · exact Finset.le_sup' (fun i => q*(f i)^2) (Finset.mem_univ a)

lemma finite_sup_neg_square {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (q : ℝ) (hq : 0 ≤ q) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => -q*(f i)^2)=
      -q*(Finset.univ.inf' Finset.univ_nonempty f)^2 := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
  have hle (i : ι) : f a ≤ f i := by
    rw [← ha]
    exact Finset.inf'_le f (Finset.mem_univ i)
  rw [ha]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    exact mul_le_mul_of_nonpos_left (sq_le_sq₀ (hf a) (hf i) |>.mpr (hle i)) (neg_nonpos.mpr hq)
  · exact Finset.le_sup' (fun i => -q*(f i)^2) (Finset.mem_univ a)

end InvariantIsing

end

end OAI
