import OAI.NumberTheory.CubicMoment.Estimates.CubePairAsymptotic
import OAI.NumberTheory.CubicMoment.Estimates.CubeExclusions

namespace OAI

/-! Exact principal-frequency reindexing for the square-divisor sieve.
The factor d² disappears from the kernel before taking an asymptotic. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tsum_scaled_cubes (m : Eisenstein) (hm : m ≠ 0) (F : Eisenstein → ℂ) :
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, h = m*j^3) then F h else 0) =
      ∑' k : Eisenstein, if k ≠ 0 ∧ (∃ j : Eisenstein, j^3 = k) then F (m*k) else 0 := by
  let G := fun h : Eisenstein => if h ≠ 0 ∧ (∃ j : Eisenstein, h = m*j^3) then F h else 0
  have hG : (∑' h : Eisenstein, G h) = ∑' h : Eisenstein, if m ∣ h then G h else 0 := by
    apply tsum_congr
    intro h
    by_cases hh : h ≠ 0 ∧ (∃ j : Eisenstein, h = m*j^3)
    · obtain ⟨j,hj⟩ := hh.2
      rw [ite_eq_left (show m ∣ h from ⟨j^3,hj⟩)]
    · simp only [G,ite_eq_right hh,ite_self]
  rw [show (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, h = m*j^3) then F h else 0) =
    ∑' h : Eisenstein, G h from rfl,hG,tsum_divisible m hm]
  apply tsum_congr
  intro k
  have he : (∃ j : Eisenstein, m*k = m*j^3) ↔ ∃ j : Eisenstein, j^3 = k := by
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨j,(mul_left_cancel₀ hm hj).symm⟩
    · rintro ⟨j,rfl⟩
      exact ⟨j,rfl⟩
  have hn : m*k ≠ 0 ↔ k ≠ 0 := by
    constructor
    · intro h hk
      exact h (by rw [hk,mul_zero])
    · exact mul_ne_zero hm
  simp only [G,hn,he]

theorem divisor_cube_series {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hd : primary d)
    (had : IsCoprime a d) (hbd : IsCoprime b d)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, h = d^2*j^3) then
      mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h else 0) =
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
      gramDualTerm b a W A h else 0) := by
  rw [tsum_scaled_cubes (d^2) (pow_ne_zero _ (primary_ne_zero hd))]
  apply tsum_congr
  intro k
  by_cases hk : k ≠ 0 ∧ (∃ j : Eisenstein, j^3 = k)
  · rw [ite_eq_left hk,ite_eq_left hk]
    obtain ⟨j,rfl⟩ := hk.2
    rw [cube_gramDualTerm ha hb hd had hbd W hA,gramDualTerm_cube ha hb W hA]
  · rw [ite_eq_right hk,ite_eq_right hk]

theorem divisor_cube_series_effective {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hd : primary d) (hs : Squarefree d)
    (had : IsCoprime a d) (hbd : IsCoprime b d)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h) then
      mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h else 0) =
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
      gramDualTerm b a W A h else 0) := by
  have he (h : Eisenstein) : (∃ j : Eisenstein, j^3 = d*h) ↔
      ∃ j : Eisenstein, h = d^2*j^3 := by
    simpa only [eq_comm] using (squarefree_mul_cube_iff (h := h) (primary_ne_zero hd) hs)
  simp_rw [he]
  exact divisor_cube_series ha hb hd had hbd W hA

end CubicFirstMoment

end

end OAI
