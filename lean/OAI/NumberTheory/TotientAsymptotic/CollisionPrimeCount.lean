import OAI.NumberTheory.TotientAsymptotic.CollisionSieveTails
import OAI.NumberTheory.TotientAsymptotic.UniformPrimeTripleBound

namespace OAI

/-! The height-uniform three-prime count used at the first collision band. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma collision_discriminant_ratio : ∃ K : ℝ,0 < K ∧ ∀ y : ℝ,
    Real.exp 2 ≤ y → 1 ≤ B y → ∀ a b : ℕ,0 < a → a < b →
    (a:ℝ) ≤ y → (b:ℝ) ≤ y →
    ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2 ≤ K*(B y)^2 := by
  obtain ⟨R,hR,hratio⟩ := totient_ratio_loglog_bound
  let K := R*(1+Real.log (3:ℝ))
  refine ⟨K^2,by dsimp [K]; positivity,?_⟩
  intro y hy hBy a b ha hab hay hby
  have hr := hratio (y^3) (cube_exp_two hy) (tripleDiscriminant a b)
    (tripleDiscriminant_pos ha hab) (tripleDiscriminant_le_cube hay hby)
  change (tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient ≤ R*B (y^3) at hr
  rw [B_cube hy] at hr
  have hlog3 : 0 ≤ Real.log (3:ℝ) := Real.log_nonneg (by norm_num)
  have hr' : (tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient ≤ K*B y := by
    apply hr.trans
    have hh : Real.log 3+B y ≤ (1+Real.log 3)*B y := by nlinarith
    simpa only [K,mul_assoc] using mul_le_mul_of_nonneg_left hh hR.le
  have hp := pow_le_pow_left₀ (show 0 ≤ (tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient by positivity) hr' 2
  simpa only [mul_pow] using hp

theorem collision_prime_triple_count_ordered : ∃ C : ℝ,0 < C ∧
    ∀ (y L : ℝ),Real.exp 2 ≤ y → 1 ≤ B y → 0 < L →
    ∀ a b N : ℕ,0 < a → a < b → (a:ℝ) ≤ y → (b:ℝ) ≤ y → L ≤ Real.log N →
    ∀ Q : Finset ℕ,(∀ q ∈ Q,q ≤ N ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
    (Q.card:ℝ) ≤ C*N*(B y)^2/L^3 := by
  obtain ⟨A,hA,hcount⟩ := uniform_prime_triple_bound
  obtain ⟨K,hK,hratio⟩ := collision_discriminant_ratio
  refine ⟨A*K,by positivity,?_⟩
  intro y L hy hBy hL a b N ha hab hay hby hLN Q hQ
  have hlog : 0 < Real.log N := hL.trans_le hLN
  have hN : 2 ≤ N := by
    have hnR : (1:ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp hlog
    exact_mod_cast hnR
  have hsub : Q ⊆ allPrimeTriples a b N := by
    intro q hq
    obtain ⟨hqN,hp,hap,hbp⟩ := hQ q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos,hqN⟩,hp,hap,hbp⟩
  have hs : (Q.card:ℝ) ≤ (allPrimeTriples a b N).card := by exact_mod_cast Finset.card_le_card hsub
  calc
    _ ≤ ((allPrimeTriples a b N).card:ℝ) := hs
    _ ≤ A*N*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log N)^3 :=
      hcount a b ha hab N hN
    _ ≤ A*N*(K*(B y)^2)/(Real.log N)^3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hratio y hy hBy a b ha hab hay hby)
        (by positivity)) (by positivity)
    _ ≤ A*N*(K*(B y)^2)/L^3 := div_le_div_of_nonneg_left (by positivity)
      (pow_pos hL 3) (pow_le_pow_left₀ hL.le hLN 3)
    _ = _ := by ring

theorem collision_prime_triple_count : ∃ C : ℝ,0 < C ∧
    ∀ (y L : ℝ),Real.exp 2 ≤ y → 1 ≤ B y → 0 < L →
    ∀ a b N : ℕ,0 < a → 0 < b → a ≠ b → (a:ℝ) ≤ y → (b:ℝ) ≤ y → L ≤ Real.log N →
    ∀ Q : Finset ℕ,(∀ q ∈ Q,q ≤ N ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
    (Q.card:ℝ) ≤ C*N*(B y)^2/L^3 := by
  obtain ⟨C,hC,hbound⟩ := collision_prime_triple_count_ordered
  refine ⟨C,hC,?_⟩
  intro y L hy hBy hL a b N ha hb hne hay hby hLN Q hQ
  rcases lt_or_gt_of_ne hne with hab|hba
  · exact hbound y L hy hBy hL a b N ha hab hay hby hLN Q hQ
  · exact hbound y L hy hBy hL b a N hb hba hby hay hLN Q
      (fun q hq => ⟨(hQ q hq).1,(hQ q hq).2.1,(hQ q hq).2.2.2,(hQ q hq).2.2.1⟩)

end TotientAsymptotic

end

end OAI
