import OAI.NumberTheory.Ostmann.Dirichlet.LogZeroFree
import OAI.NumberTheory.Ostmann.ZeroDensity.WeightedZeros

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem exists_actual_zero_gap_constant :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/4 ∧ ∀ (Q H : ℕ), 0 < Q → 0 < H →
      ∀ z : ZeroOccurrence Q (H : ℝ),
        c/Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ) ≤ 1-z.point.re := by
  obtain ⟨c0,hc0,hregion⟩ := Ostmann.Dirichlet.exists_nonprincipal_log_zero_free_region
  let c := min c0 (1/4)
  have hc : 0 < c := lt_min hc0 (by norm_num)
  have hcc : c ≤ c0 := min_le_left _ _
  refine ⟨c,hc,min_le_right _ _,?_⟩
  intro Q H hQ hH z
  let : NeZero Q := ⟨by omega⟩
  let q : ℕ := z.1.1.1.val+1
  have hqQ : q ≤ Q := by have ht := z.1.1.1.isLt; dsimp [q]; omega
  have hqp : (0 : ℝ) < q := by dsimp [q]; positivity
  have hglobal : Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight q z.point.im ≤
      Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ) := by
    unfold Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight
    apply add_le_add
    · exact Real.log_le_log hqp (by exact_mod_cast hqQ)
    · apply Real.log_le_log (by positivity)
      rw [abs_of_nonneg (show (0 : ℝ) ≤ (H : ℝ) from Nat.cast_nonneg H)]
      have ht : |z.point.im| ≤ (H : ℝ) := z.2.1.property.2
      linarith
  have hlocalpos : 0 < Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight q z.point.im :=
    lt_of_lt_of_le zero_lt_one (Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight_ge_one q z.point.im)
  have hglobalpos : 0 < Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ) :=
    lt_of_lt_of_le zero_lt_one (Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight_ge_one Q (H : ℝ))
  have hgap : c0/Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight q z.point.im < 1-z.point.re := by
    by_contra! hh
    exact hregion q z.1.1.2.val z.1.property z.point (by linarith) z.isNontrivialZero.1
  exact ((div_le_div_of_nonneg_right hcc hglobalpos.le).trans
    (div_le_div_of_nonneg_left hc0.le hlocalpos hglobal)).trans hgap.le

theorem exists_unconditional_weighted_zero_constants :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (Q H : ℕ)
      (exception : Option (PrimitiveFamily Q)) (M : ℝ),
      0 < Q → 0 < H → 0 < M →
      2*(10*Real.log ((Q^2*H : ℕ) : ℝ)) ≤ M →
      (∑ z ∈ retainedZeros Q exception (1/2) (H : ℝ),
        Real.exp (-M*(1-z.point.re))) ≤
        (⌊M/2⌋₊+1 : ℝ)*(C*(1+Real.log (Q*H : ℕ))^11)*
          Real.exp (1-M*(c/Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ))/2) := by
  obtain ⟨c,hc,hc4,hgap⟩ := exists_actual_zero_gap_constant
  obtain ⟨C,hC,hweighted⟩ := exists_actual_weighted_zero_constant
  refine ⟨c,C,hc,hC,?_⟩
  intro Q H exception M hQ hH hM hscale
  let : NeZero Q := ⟨by omega⟩
  have hheight := Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight_ge_one Q (H : ℝ)
  have hheightpos : 0 < Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ) := by linarith
  refine hweighted Q H exception M (c/Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ))
    hQ hH hM (div_nonneg hc.le hheightpos.le) ?_ hscale ?_
  · apply (div_le_iff₀ hheightpos).mpr
    linarith
  · intro z hz
    exact hgap Q H hQ hH z

end Ostmann.ZeroDensity

end

end OAI
