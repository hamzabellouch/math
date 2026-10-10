import OAI.NumberTheory.TotientAsymptotic.CoordinateRealEndpoint

namespace OAI

/-! The effective row-deviation estimate for arbitrary real endpoints. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem real_coordinate_deviation : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ x : ℝ,512 ≤ x → 2*Real.exp (Real.exp 1) ≤ x → ∀ k : ℕ,
    ∀ ω : ℝ,0 < ω → ω ≤ 1 →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay ω k)^(4/3:ℝ)) ≤ B x-1 →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ x ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B x ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*x/Real.log x*Real.exp (-coordinateDecay ω k*B x) := by
  obtain ⟨C,F,hC,hF,hcount⟩ := effective_coordinate_count
  refine ⟨2*Real.exp 1*C,F,by positivity,hF,?_⟩
  intro x hx hxexp k ω hω hω1 hthreshold Q hQ
  have hx4 : 4 ≤ x := by linarith
  have hf := coordinate_floor_bounds hx4
  have hN : 256 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith : (256:ℝ) ≤ x)
  have hNexp : Real.exp (Real.exp 1) ≤ (⌊x⌋₊:ℝ) := by linarith only [hf.2.1,hxexp]
  have hNat := hcount ⌊x⌋₊ k hN hNexp ω hω hω1
    (hthreshold.trans hf.2.2.2.2.1) Q (by
      intro v hv
      obtain ⟨ht,hvX,n,hn,hφ,hscore⟩ := hQ v hv
      refine ⟨ht,Nat.le_floor hvX,n,hn,hφ,?_⟩
      have hh := mul_le_mul_of_nonneg_left hf.2.2.2.2.2 (show 0 ≤ 1+ω by linarith)
      exact hh.trans hscore)
  have hδ := coordinate_decay_bounds (k:=k) hω.le hω1
  have hround := coordinate_floor_normalization hx4 hδ.1 (hδ.2.1.trans (by norm_num))
  calc
    _ ≤ C*((⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ)*Real.exp (-coordinateDecay ω k*B (⌊x⌋₊:ℝ))) := by
      simpa only [div_eq_mul_inv,mul_assoc] using hNat
    _ ≤ C*(2*Real.exp 1*(x/Real.log x*Real.exp (-coordinateDecay ω k*B x))) :=
      mul_le_mul_of_nonneg_left hround hC.le
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
