import OAI.NumberTheory.TotientAsymptotic.PrimeReciprocalTails
import OAI.NumberTheory.TotientAsymptotic.TotientRatioLogLog

namespace OAI

/-! Height-uniform reciprocal sieve bounds for the two collision branches. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma tripleDiscriminant_le_cube {a b : ℕ} {y : ℝ} (ha : (a:ℝ) ≤ y) (hb : (b:ℝ) ≤ y) :
    (tripleDiscriminant a b:ℝ) ≤ y^3 := by
  have hy : 0 ≤ y := (Nat.cast_nonneg a).trans ha
  have hsub : ((b-a:ℕ):ℝ) ≤ y := (by exact_mod_cast Nat.sub_le b a : ((b-a:ℕ):ℝ) ≤ b).trans hb
  dsimp [tripleDiscriminant]
  push_cast
  calc
    _ ≤ (y*y)*y := mul_le_mul
      (mul_le_mul ha hb (Nat.cast_nonneg _) hy) hsub (Nat.cast_nonneg _) (mul_nonneg hy hy)
    _ = _ := by ring

lemma B_cube {y : ℝ} (hy : Real.exp 2 ≤ y) : B (y^3)=Real.log 3+B y := by
  have hy0 : 0 < y := (Real.exp_pos _).trans_le hy
  have hlog : 2 ≤ Real.log y := (Real.le_log_iff_exp_le hy0).mpr hy
  rw [B,Real.log_pow,Real.log_mul (by norm_num) (by linarith)]
  rfl

lemma cube_exp_two {y : ℝ} (hy : Real.exp 2 ≤ y) : Real.exp 2 ≤ y^3 := by
  have he := Real.add_one_le_exp (2:ℝ)
  have hy1 : 1 ≤ y := by linarith
  have hs : 1 ≤ y^2 := one_le_pow₀ hy1
  have hm := mul_le_mul_of_nonneg_left hs (zero_le_one.trans hy1)
  nlinarith

 theorem collision_triple_reciprocal_tail : ∃ C : ℝ,0 < C ∧
    ∀ (y : ℝ),Real.exp 2 ≤ y → 1 ≤ B y → ∀ (a b : ℕ),0 < a → a < b →
    (a:ℝ) ≤ y → (b:ℝ) ≤ y → ∀ (Q : Finset ℕ) (U : ℝ),1 < U →
    (∀ q ∈ Q,U ≤ q ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ C*(B y)^2/(Real.log U)^2 := by
  obtain ⟨A,hA,htail⟩ := prime_triple_reciprocal_tail
  obtain ⟨R,hR,hratio⟩ := totient_ratio_loglog_bound
  let K := R*(1+Real.log (3:ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨A*K^2,by positivity,?_⟩
  intro y hy hBy a b ha hab hay hby Q U hU hQ
  have hr := hratio (y^3) (cube_exp_two hy) (tripleDiscriminant a b)
    (tripleDiscriminant_pos ha hab) (tripleDiscriminant_le_cube hay hby)
  change (tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient ≤ R*B (y^3) at hr
  rw [B_cube hy] at hr
  have hb : 0 ≤ B y := by linarith
  have hlog3 : 0 ≤ Real.log (3:ℝ) := Real.log_nonneg (by norm_num)
  have hr' : (tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient ≤ K*B y := by
    apply hr.trans
    have hh : Real.log 3+B y ≤ (1+Real.log 3)*B y := by nlinarith
    simpa only [K,mul_assoc] using mul_le_mul_of_nonneg_left hh hR.le
  have hr0 : 0 ≤ (tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient := by positivity
  have hs := pow_le_pow_left₀ hr0 hr' 2
  calc
    _ ≤ A*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log U)^2 :=
      htail a b ha hab Q U hU hQ
    _ ≤ A*(K*B y)^2/(Real.log U)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hA.le) (sq_nonneg _)
    _ = _ := by ring

 theorem collision_pair_reciprocal_tail : ∃ C : ℝ,0 < C ∧
    ∀ (y : ℝ),Real.exp 2 ≤ y → ∀ (a : ℕ),0 < a → (a:ℝ) ≤ y →
    ∀ (Q : Finset ℕ) (U : ℝ),1 < U →
    (∀ q ∈ Q,U ≤ q ∧ q.Prime ∧ (a*q+1).Prime) →
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ C*B y/Real.log U := by
  obtain ⟨A,hA,htail⟩ := prime_pair_reciprocal_tail
  obtain ⟨R,hR,hratio⟩ := totient_ratio_loglog_bound
  refine ⟨A*R,by positivity,?_⟩
  intro y hy a ha hay Q U hU hQ
  have hr := hratio y hy a ha hay
  have hlogU : 0 < Real.log U := Real.log_pos hU
  calc
    _ ≤ A*((a:ℝ)/a.totient)/Real.log U := htail a ha Q U hU hQ
    _ ≤ A*(R*B y)/Real.log U :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hA.le) hlogU.le
    _ = _ := by ring

theorem collision_triple_reciprocal_tail_ne : ∃ C : ℝ,0 < C ∧
    ∀ (y : ℝ),Real.exp 2 ≤ y → 1 ≤ B y → ∀ (a b : ℕ),0 < a → 0 < b → a ≠ b →
    (a:ℝ) ≤ y → (b:ℝ) ≤ y → ∀ (Q : Finset ℕ) (U : ℝ),1 < U →
    (∀ q ∈ Q,U ≤ q ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ C*(B y)^2/(Real.log U)^2 := by
  obtain ⟨C,hC,hbound⟩ := collision_triple_reciprocal_tail
  refine ⟨C,hC,?_⟩
  intro y hy hB a b ha hb hab hay hby Q U hU hQ
  rcases lt_or_gt_of_ne hab with hlt|hgt
  · exact hbound y hy hB a b ha hlt hay hby Q U hU hQ
  · exact hbound y hy hB b a hb hgt hby hay Q U hU
      (fun q hq => ⟨(hQ q hq).1,(hQ q hq).2.1,(hQ q hq).2.2.2,(hQ q hq).2.2.1⟩)

end TotientAsymptotic

end

end OAI
