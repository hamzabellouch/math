import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovOrthogonality

namespace OAI

/-! The complete Vinogradov solution count is exactly a torus moment of
the polynomial exponential sum. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped ComplexConjugate

noncomputable def halaszVinogradovPolynomial (k N : ℕ)
    (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  ∑ n : Fin N, halaszVinogradovCharacter
    (fun j => (((n.val+1)^(j.val+1):ℕ):ℤ)) α

def halaszVinogradovFrequency {s N : ℕ} (k : ℕ) (x : Fin s → Fin N) : Fin k → ℤ :=
  fun j => ∑ i, (((x i).val+1)^(j.val+1):ℕ)

lemma halasz_vinogradov_character_sum {s k : ℕ} (S : Finset (Fin s))
    (m : Fin s → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter (∑ i ∈ S, m i) α =
      ∏ i ∈ S, halaszVinogradovCharacter (m i) α := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [halaszVinogradovCharacter]
  | @insert i S hi ih =>
    rw [sum_insert hi,prod_insert hi,halasz_vinogradov_character_add,ih]

lemma halasz_vinogradov_power_expand (s k N : ℕ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovPolynomial k N α ^ s =
      ∑ x : Fin s → Fin N, halaszVinogradovCharacter (halaszVinogradovFrequency k x) α := by
  classical
  rw [halaszVinogradovPolynomial,Fintype.sum_pow]
  apply sum_congr rfl
  intro x _
  rw [← halasz_vinogradov_character_sum]
  congr 1
  ext j
  simp [halaszVinogradovFrequency]

lemma halasz_vinogradov_frequency_eq {s k N : ℕ} (x y : Fin s → Fin N) :
    halaszVinogradovFrequency k x = halaszVinogradovFrequency k y ↔
      y ∈ halaszVinogradovFiber x k := by
  classical
  constructor
  · intro h
    apply mem_halaszVinogradovFiber.mpr
    intro j hj
    have hj1 := (mem_Icc.mp hj).1
    have hjk := (mem_Icc.mp hj).2
    have hq := congrFun h (⟨j-1,by omega⟩ : Fin k)
    simp only [halaszVinogradovFrequency,Nat.sub_add_cancel hj1] at hq
    exact_mod_cast hq
  · intro h
    funext j
    have hj : j.val+1 ∈ Icc 1 k := mem_Icc.mpr ⟨by omega,by omega⟩
    have hq := (mem_halaszVinogradovFiber.mp h) (j.val+1) hj
    dsimp only [halaszVinogradovFrequency]
    exact_mod_cast hq

theorem halasz_vinogradov_moment (s k N : ℕ) :
    (∫ α, (halaszVinogradovPolynomial k N α)^s *
        conj ((halaszVinogradovPolynomial k N α)^s) ∂halaszVinogradovHaar k) =
      (halaszVinogradovCount s k N:ℂ) := by
  classical
  have hi (x y : Fin s → Fin N) :
      Integrable (fun α => halaszVinogradovCharacter (halaszVinogradovFrequency k x) α *
        conj (halaszVinogradovCharacter (halaszVinogradovFrequency k y) α))
        (halaszVinogradovHaar k) := by
    simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
    exact halasz_vinogradov_character_integrable _
  simp_rw [halasz_vinogradov_power_expand,map_sum,sum_mul,mul_sum]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  simp_rw [integral_finsetSum _ (fun y _ => hi _ y),halasz_vinogradov_character_inner,
    halasz_vinogradov_frequency_eq]
  simp only [sum_boole,filter_mem_eq_inter,univ_inter,halaszVinogradovCount,Nat.cast_sum]

end TwoPointCorrelations

end OAI
