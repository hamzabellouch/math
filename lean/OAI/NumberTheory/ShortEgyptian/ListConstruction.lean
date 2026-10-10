import OAI.NumberTheory.ShortEgyptian.LevelSelection

namespace OAI

universe uJ uA uR

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

noncomputable def deterministicProduct {J : Type uJ} [Fintype J]
    (p : J → ℕ) (I : J → Bool) : ℕ := ∏ j, if I j then p j else 1

lemma deterministicProduct_pos {J : Type uJ} [Fintype J] (p : J → ℕ)
    (hp : ∀ j, 0 < p j) (I : J → Bool) : 0 < deterministicProduct p I := by
  apply prod_pos
  intro j _
  split <;> simp_all

lemma deterministicProduct_injective {J : Type uJ} [Fintype J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p) :
    Function.Injective (deterministicProduct p) := by
  have hd (I : J → Bool) (j : J) : p j ∣ deterministicProduct p I ↔ I j = true := by
    rw [deterministicProduct,(hp j).prime.dvd_finsetProd_iff]
    constructor
    · rintro ⟨k,_,hk⟩
      by_cases hI : I k = true
      · simp only [hI,ite_true] at hk
        have hjk : j = k := hinj ((Nat.prime_dvd_prime_iff_eq (hp j) (hp k)).mp hk)
        simpa [hjk] using hI
      · simp only [hI] at hk
        exact False.elim ((hp j).not_dvd_one hk)
    · intro hI
      exact ⟨j,mem_univ j,by simp [hI]⟩
  intro I K hIK
  funext j
  have heq : (I j = true) ↔ K j = true := by rw [←hd I j,←hd K j,hIK]
  cases hI : I j <;> cases hK : K j <;> simp_all

noncomputable def auxiliaryDenominator {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A) : ℕ :=
  2^a*(∏ j,p₀ j)*(∏ i,∏ j,p (f i (j,false))*p (f i (j,true)))

lemma auxiliaryDenominator_pos {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A)
    (h₀ : ∀ j, 0 < p₀ j) (hp : ∀ x, 0 < p x) :
    0 < auxiliaryDenominator a p₀ p f := by
  unfold auxiliaryDenominator
  exact mul_pos (mul_pos (by positivity) (prod_pos (fun j _ => h₀ j)))
    (prod_pos (fun _ _ => prod_pos (fun _ _ => mul_pos (hp _) (hp _))))

lemma two_pow_dvd_auxiliary {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A) :
    2^a ∣ auxiliaryDenominator a p₀ p f := by
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

lemma deterministic_dvd_auxiliary {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A) (I : J → Bool) :
    deterministicProduct p₀ I ∣ auxiliaryDenominator a p₀ p f := by
  have hd : deterministicProduct p₀ I ∣ ∏ j,p₀ j := by
    apply prod_dvd_prod_of_dvd
    intro j _
    split <;> simp
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

lemma sample_dvd_auxiliary {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A) (i : R) (I : J → Bool) :
    sampleProduct p I (f i) ∣ auxiliaryDenominator a p₀ p f := by
  have hd : sampleProduct p I (f i) ∣ ∏ j,p (f i (j,false))*p (f i (j,true)) := by
    unfold sampleProduct
    apply prod_dvd_prod_of_dvd
    intro j _
    cases hI : I j
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hb : (∏ j, p (f i (j,false))*p (f i (j,true))) ∣
      ∏ k : R, ∏ j, p (f k (j,false))*p (f k (j,true)) :=
    dvd_prod_of_mem (fun k : R => ∏ j, p (f k (j,false))*p (f k (j,true))) (mem_univ i)
  exact dvd_mul_of_dvd_right (hd.trans hb) _

lemma products_scale_bound {J : Type uJ} [Fintype J]
    (S : ℝ) (hS : 2 ≤ S) (hlog : 0 < Real.log S)
    (hm : (Fintype.card J:ℝ) ≤ S/Real.log S)
    (a : J → ℕ) (ha : ∀ j, (a j:ℝ) ≤ 2*S^100) :
    ((∏ j,a j : ℕ):ℝ) ≤ Real.exp (101*S) := by
  have hS0 : 0 < S := by linarith
  have hamp (j : J) : (a j:ℝ) ≤ Real.exp (101*Real.log S) := by
    calc
      _ ≤ 2*S^100 := ha j
      _ ≤ S*S^100 := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = S^101 := by ring
      _ = Real.exp (101*Real.log S) := by rw [←Real.exp_log (pow_pos hS0 101),Real.log_pow]; norm_num
  push_cast
  calc
    _ ≤ ∏ _j : J, Real.exp (101*Real.log S) := prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hamp j)
    _ = Real.exp ((Fintype.card J:ℝ)*(101*Real.log S)) := by simp only [prod_const,card_univ,Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by have hh := (le_div_iff₀ hlog).mp hm; nlinarith)

lemma deterministicProduct_bound {J : Type uJ} [Fintype J]
    (S : ℝ) (hS : 2 ≤ S) (hlog : 0 < Real.log S)
    (hm : (Fintype.card J:ℝ) ≤ S/Real.log S)
    (p : J → ℕ) (hp : ∀ j, (p j:ℝ) ≤ 2*S^100) (I : J → Bool) :
    (deterministicProduct p I:ℝ) ≤ Real.exp (101*S) := by
  apply products_scale_bound S hS hlog hm
  intro j
  split
  · exact hp j
  · simp only [Nat.cast_one]
    have hh : (1:ℝ) ≤ S^100 := one_le_pow₀ (by linarith)
    linarith

lemma sampleProduct_pos {J : Type uJ} {A : Type uA} [Fintype J]
    (p : A → ℕ) (hp : ∀ a, 0 < p a) (f : (J × Bool) → A) (I : J → Bool) :
    0 < sampleProduct p I f := prod_pos (fun _ _ => hp _)

lemma sampleProduct_bound {J : Type uJ} {A : Type uA} [Fintype J]
    (S : ℝ) (hS : 2 ≤ S) (hlog : 0 < Real.log S)
    (hm : (Fintype.card J:ℝ) ≤ S/Real.log S)
    (p : A → ℕ) (hp : ∀ a, (p a:ℝ) ≤ 2*S^100) (f : (J × Bool) → A) (I : J → Bool) :
    (sampleProduct p I f:ℝ) ≤ Real.exp (101*S) :=
  products_scale_bound S hS hlog hm _ (fun _ => hp _)

end ShortEgyptian

end OAI
