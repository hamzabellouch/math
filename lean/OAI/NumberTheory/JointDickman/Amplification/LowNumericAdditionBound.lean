import OAI.NumberTheory.JointDickman.Amplification.LowNumericAdditionClass

namespace OAI

/-! # A uniform harmonic bound for a low-endpoint numeric-addition class -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- This is the numeric sum before choosing the Rankin parameter.  All
progression and squarefree-product hypotheses have been discharged for the
actual class.  Its only analytic inputs are the cited upper sieve and Mertens. -/
theorem low_numeric_addition_class_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {κ g ε : ℝ} (hκ : 0 < κ) (hg : 0 < g) (hg1 : g < 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (L k : ℕ) (τ C : ℝ) (e j b d : ℕ) (q W : ℝ),
        k ∈ Icc 1 L → g ≤ (k : ℝ)/L →
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
        (e*b : ℕ) ≤ Real.exp (κ*B) → 0 < q → q ≤ 1 → 2*(j : ℝ) ≤ W →
        (∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
          (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ)) ≤
          (((1/2 : ℝ)/q)^d*Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2))*
            (K/(j : ℝ)*Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B)+
              4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W) := by
  obtain ⟨K,hK,hbound⟩ := low_addition_window_harmonic_bound hFord hM hκ hg hg1 hε
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with B hB hB1
  intro L k τ C e j b d q W hk hgk he hb hj hcut hej hsize hq hq1 hW
  by_cases hne : (lowNumericAdditionClass B L τ C e j b d W).Nonempty
  · obtain ⟨Z,hZ⟩ := hne
    obtain ⟨_,_,_,_,c,_,hc,_⟩ := mem_lowNumericAdditionClass.mp hZ
    obtain ⟨z₀,c₀,_,hbase,hprogress⟩ := low_addition_equation_progression hj hej hc
    have hsum := low_numeric_addition_class_progression_bound hB1 hk hgk hq hq1 hprogress
      (τ := τ) (C := C) (d := d) (W := W)
    refine hsum.trans (mul_le_mul_of_nonneg_left
      (hB e j b z₀ c₀ q W he hb hj hcut hsize hbase hq.le hq1 hW) ?_)
    positivity
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne,sum_empty]
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hW0 : 0 < W := by linarith
    positivity

end JointDickman

end OAI
