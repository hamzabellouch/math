import OAI.NumberTheory.TotientAsymptotic.InitialPrimeFiber

namespace OAI

/-! The initial prime count summed over all rough cofactors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem initial_prime_count : ∃ C : ℝ,0 < C ∧ ∀ (a b d : ℕ) (y U L : ℝ),
    0 < d → Real.exp 2 ≤ y → 1 ≤ B y → 2 ≤ U → U ≤ y → 0 < L →
    ∀ E : Finset (ℕ × ℕ),(∀ e ∈ E,InitialPrimeData a b d y L e) →
    (∀ e ∈ E,Squarefree e.1 ∧ ∀ p ∈ e.1.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ y) →
    (E.card:ℝ) ≤ (C*(y/d)*(B y)^2/L^3)*(Real.log y/Real.log U) := by
  classical
  obtain ⟨A,hA,hcount⟩ := collision_prime_triple_count
  obtain ⟨R,hR,hrough⟩ := squarefree_rough_reciprocal_mass
  refine ⟨A*R,by positivity,?_⟩
  intro a b d y U L hd hy hBy hU hUy hL E hE hsq
  let V := E.image Prod.fst
  let K := A*(y/d)*(B y)^2/L^3
  have hy0 : 0 < y := (Real.exp_pos 2).trans_le hy
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmap : ∀ e ∈ E,e.1 ∈ V := fun e he => Finset.mem_image.mpr ⟨e,he,rfl⟩
  have heq : (E.card:ℝ)=∑ v ∈ V,((E.filter (fun e => e.1=v)).card:ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1:ℝ))
    simpa using hh.symm
  have hmass : (∑ v ∈ V,(v:ℝ)⁻¹) ≤ R*Real.log y/Real.log U := by
    apply hrough U y hU hUy V
    intro v hv
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    exact hsq e he
  calc
    _ = ∑ v ∈ V,((E.filter (fun e => e.1=v)).card:ℝ) := heq
    _ ≤ ∑ v ∈ V,K*(v:ℝ)⁻¹ := Finset.sum_le_sum (fun v hv =>
      initial_prime_fiber_bound hd hy hBy hL hA (hcount y L hy hBy hL) E hE v hv)
    _ = K*(∑ v ∈ V,(v:ℝ)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ K*(R*Real.log y/Real.log U) := mul_le_mul_of_nonneg_left hmass hK
    _ = _ := by dsimp [K]; ring

theorem initial_rough_count : ∃ C : ℝ,0 < C ∧ ∀ (a b d : ℕ) (y U : ℝ),
    0 < a → 0 < b → 0 < d → Real.exp 2 ≤ y → 1 ≤ B y → 2 ≤ U → U ≤ y →
    ∀ Q : Finset ℕ,(∀ n ∈ Q,InitialRoughConditions a b d y U n) →
    (Q.card:ℝ) ≤ (C*(y/d)*(B y)^2/(Real.log y/(6*B y))^3)*(Real.log y/Real.log U) := by
  classical
  obtain ⟨C,hC,hcount⟩ := initial_prime_count
  refine ⟨C,hC,?_⟩
  intro a b d y U ha hb hd hy hBy hU hUy Q hQ
  let E := Q.image initialRoughEncoding
  have hE : ∀ e ∈ E,InitialPrimeData a b d y (Real.log y/(6*B y)) e := by
    intro e he
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp he
    exact initial_rough_sieve_data ha hb hy hBy (hQ n hn)
  have hs : ∀ e ∈ E,Squarefree e.1 ∧ ∀ p ∈ e.1.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ y := by
    intro e he
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp he
    have hh := initial_rough_residual hy (hQ n hn)
    exact ⟨hh.2.2.1,hh.2.2.2⟩
  have hL : 0 < Real.log y/(6*B y) := by
    have hy1 : 1 < y := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 2)).trans_le hy
    exact div_pos (Real.log_pos hy1) (by positivity)
  have hh := hcount a b d y U (Real.log y/(6*B y)) hd hy hBy hU hUy hL E hE hs
  have he : E.card=Q.card := Finset.card_image_of_injOn (initial_rough_injOn hy Q hQ)
  rwa [he] at hh

end TotientAsymptotic

end

end OAI
