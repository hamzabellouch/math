import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceRetained
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupportPropagationBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem positive_reduced_tag_unique {v w H K : ℤ} (hH : 0 < H) (hK : 0 < K)
    (hv : IsCoprime v H) (hw : IsCoprime w K) (he : v*K=w*H) : H=K ∧ v=w := by
  have hdHK : H ∣ K := hv.symm.dvd_of_dvd_mul_left (by rw [he]; exact dvd_mul_left _ _)
  have hdKH : K ∣ H := hw.symm.dvd_of_dvd_mul_left (by rw [←he]; exact dvd_mul_left _ _)
  have hHK : H=K := Int.dvd_antisymm hH.le hK.le hdHK hdKH
  refine ⟨hHK,?_⟩
  rw [←hHK] at he
  exact mul_right_cancel₀ (ne_of_gt hH) he

namespace RetainedRow
section
variable (k j : ℕ) (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)

theorem term_current_support (P : ℕ+) (h : CopiedState k j) (y : OutsideState k j)
    (z : ℤ×HistoryReconstruction.Tree j) (phase : ℂ)
    (hf : term k j B V extra mask X Δ W P h y z phase≠0) :
    CurrentAtomSupport k j z.1 (sourceState k j (P:ℤ) h y) :=
  (retainedHistoryWeight_support (mul_ne_zero_iff.mp hf).1).current

theorem term_copiedProduct_pos (P : ℕ+) (h : CopiedState k j) (y : OutsideState k j)
    (z : ℤ×HistoryReconstruction.Tree j) (phase : ℂ)
    (hf : term k j B V extra mask X Δ W P h y z phase≠0) : 0 < ∏i,h i := by
  have hs := term_current_support k j B V extra mask X Δ W P h y z phase hf
  exact Finset.prod_pos (fun i _ => hs.copied_pos i)

theorem term_root_copiedProduct_coprime (P : ℕ+) (h : CopiedState k j) (y : OutsideState k j)
    (z : ℤ×HistoryReconstruction.Tree j) (phase : ℂ)
    (hf : term k j B V extra mask X Δ W P h y z phase≠0) : IsCoprime z.1 (∏i,h i) := by
  have hs := term_current_support k j B V extra mask X Δ W P h y z phase hf
  apply IsCoprime.prod_right
  intro i hi
  simpa only [sourceState_copied_value] using hs.root_coprime i.val

theorem term_exactTag_iff (P : ℕ+) (hL hR : CopiedState k j) (y : OutsideState k j)
    (z z' : ℤ×HistoryReconstruction.Tree j) (phaseL phaseR : ℂ)
    (hfL : term k j B V extra mask X Δ W P hL y z phaseL≠0)
    (hfR : term k j B V extra mask X Δ W P hR y z' phaseR≠0) :
    historyExactTag k j hL z.1=historyExactTag k j hR z'.1 ↔
      (∏i,hL i)=(∏i,hR i) ∧ z.1=z'.1 := by
  have hLp := term_copiedProduct_pos k j B V extra mask X Δ W P hL y z phaseL hfL
  have hRp := term_copiedProduct_pos k j B V extra mask X Δ W P hR y z' phaseR hfR
  constructor
  · intro he
    have hh := (historyExactTag_eq_iff k j hL hR z.1 z'.1 (ne_of_gt hLp) (ne_of_gt hRp)).mp he
    exact positive_reduced_tag_unique hLp hRp
      (term_root_copiedProduct_coprime k j B V extra mask X Δ W P hL y z phaseL hfL)
      (term_root_copiedProduct_coprime k j B V extra mask X Δ W P hR y z' phaseR hfR)
      (sub_eq_zero.mp hh)
  · rintro ⟨hp,hz⟩
    simp only [historyExactTag,hp,hz]

end
end RetainedRow
end Ostmann.Characters.Template

end

end OAI
