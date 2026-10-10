import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceDiagonal

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem history_offDiagonal_indicator (k j : ℕ) (P : ℕ+)
    (hL hR : CopiedState k j) (v w : ℤ) (fL fR : ℂ)
    (hL0 : (∏i,hL i)≠0) (hR0 : (∏i,hR i)≠0)
    (hLu : fL≠0 → IsUnit ((∏i,hL i:ℤ):ZMod (P:ℕ)))
    (hRu : fR≠0 → IsUnit ((∏i,hR i:ℤ):ZMod (P:ℕ))) :
    (if historyRowTag k j P hR w=historyRowTag k j P hL v ∧
        historyExactTag k j hR w≠historyExactTag k j hL v then fL*conj fR else 0) =
      if (P:ℤ)∣v*(∏i,hR i)-w*(∏i,hL i) ∧ v*(∏i,hR i)-w*(∏i,hL i)≠0
      then fL*conj fR else 0 := by
  by_cases hfl:fL=0
  · simp [hfl]
  by_cases hfr:fR=0
  · simp [hfr]
  have hr : historyRowTag k j P hR w=historyRowTag k j P hL v ↔
      (P:ℤ)∣v*(∏i,hR i)-w*(∏i,hL i) :=
    eq_comm.trans (historyRowTag_eq_iff k j P hL hR v w (hLu hfl) (hRu hfr))
  have he : historyExactTag k j hR w=historyExactTag k j hL v ↔
      v*(∏i,hR i)-w*(∏i,hL i)=0 :=
    eq_comm.trans (historyExactTag_eq_iff k j hL hR v w hL0 hR0)
  simp only [hr,ne_eq,he]

theorem historyRowOffDiagonal_expansion {α : Type*} [Fintype α] (k j : ℕ)
    (μ : FinitePrior α) (h : α → CopiedState k j) (y : OutsideState k j)
    (S : List Bool → Finset ℤ) (path : List Bool)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (P : ℕ+)
    (phase : α → SupportedHistory S j path → ℂ)
    (hprod : ∀x,(∏i,h x i)≠0)
    (hunit : ∀x z,historyRowTerm k j mask X Δ W P (h x) y z.val (phase x z)≠0 →
      IsUnit ((∏i,h x i:ℤ):ZMod (P:ℕ))) :
    historyRowOffDiagonal k j μ h y S path mask X Δ W P phase =
      μ.cmean (fun x => μ.cmean (fun x' =>
        ∑z:SupportedHistory S j path,∑z':SupportedHistory S j path,
          let N := z.val.1*(∏i,h x' i)-z'.val.1*(∏i,h x i)
          if (P:ℤ)∣N ∧ N≠0 then
            historyRowTerm k j mask X Δ W P (h x) y z.val (phase x z)*
              conj (historyRowTerm k j mask X Δ W P (h x') y z'.val (phase x' z'))
          else 0)) := by
  unfold historyRowOffDiagonal refinedRowOffDiagonal
  simp only [Fintype.sum_prod_type,FinitePrior.cmean,Finset.mul_sum,mul_ite,mul_zero]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' hx'
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro z' hz'
  have hh := history_offDiagonal_indicator k j P (h x) (h x') z.val.1 z'.val.1
    (historyRowTerm k j mask X Δ W P (h x) y z.val (phase x z))
    (historyRowTerm k j mask X Δ W P (h x') y z'.val (phase x' z'))
    (hprod x) (hprod x') (hunit x z) (hunit x' z')
  have hw := congrArg (fun a:ℂ => (μ.mass x:ℂ)*(μ.mass x':ℂ)*a) hh
  simp only [mul_ite,mul_zero] at hw
  convert hw using 1 <;> split_ifs <;> ring

end Ostmann.Characters.Template

end

end OAI
