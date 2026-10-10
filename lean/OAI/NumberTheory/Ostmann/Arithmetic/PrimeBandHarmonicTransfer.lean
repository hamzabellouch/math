import Mathlib.Order.Filter.AtTopBot.Basic
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeBandHarmonicTransferFinite

namespace OAI

noncomputable section
open Filter
open scoped BigOperators
namespace Ostmann.Arithmetic.PrimeBandHarmonicTransfer

theorem eventually_harmonic_band_le (f : ℕ→ℝ) (hf : ∀p,0≤f p)
    (hband : ∀δ:ℝ,0<δ → ∀ᶠ T:ℝ in atTop,
      ∀P:Finset ℕ,(∀p∈P,p.Prime) →
      (∀p∈P,T≤Real.log (p:ℝ) ∧ Real.log (p:ℝ)≤2*T) →
      (∑p∈P,(Real.log (p:ℝ)/(p:ℝ))*f p)≤δ*T)
    {α β : ℝ} (hα : 0<α) (hαβ : α<β) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ L:ℝ in atTop,∀P:Finset ℕ,(∀p∈P,p.Prime) →
      (∀p∈P,α*L≤Real.log (Real.log (p:ℝ)) ∧ Real.log (Real.log (p:ℝ))≤β*L) →
      (∑p∈P,f p/(p:ℝ))≤ε*L := by
  let C : ℝ := β/Real.log 2+1
  have hβ : 0<β := hα.trans hαβ
  have hC : 0<C := by dsimp only [C]; positivity
  let δ : ℝ := ε/C
  have hδ : 0<δ := div_pos hε hC
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (hband δ hδ)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((Real.log (max T₀ 1)+Real.log 2)/α)] with L hL hlarge
  intro P hprime hP
  have hstart : T₀≤Real.exp (α*L-Real.log 2) := by
    have hthreshold : Real.log (max T₀ 1)+Real.log 2≤L*α :=
      (div_le_iff₀ hα).mp hlarge
    have hp : (0:ℝ)<max T₀ 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    calc
      T₀ ≤ max T₀ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max T₀ 1)) := (Real.exp_log hp).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hh := finite_band_harmonic_bound f hf δ T₀ (α*L) (β*L) hδ.le
    (by positivity) (by positivity) hstart hT₀ P hprime hP
  have hcount : β*L/Real.log 2+1≤C*L := by
    dsimp only [C]
    rw [show β*L/Real.log 2=(β/Real.log 2)*L by ring]
    nlinarith
  have hδC : δ*C=ε := div_mul_cancel₀ ε hC.ne'
  calc
    _ ≤ δ*(β*L/Real.log 2+1) := hh
    _ ≤ δ*(C*L) := mul_le_mul_of_nonneg_left hcount hδ.le
    _ = ε*L := by rw [←mul_assoc,hδC]

end Ostmann.Arithmetic.PrimeBandHarmonicTransfer

end

end OAI
