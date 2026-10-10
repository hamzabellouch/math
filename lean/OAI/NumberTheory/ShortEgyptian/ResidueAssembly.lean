import OAI.NumberTheory.ShortEgyptian.ScaleBounds

namespace OAI

universe uJ uA uR

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

lemma high_badLevel {J : Type uJ} [Fintype J]
    (S X : ℝ) (C : ℕ) (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (hcard : Fintype.card J = scaleM S) (hmax : ∀ j, (p j:ℝ) ≤ 2*S^100)
    (hS : 2 ≤ S) (hlog : 1 ≤ Real.log S) (hm100 : 100 ≤ (scaleM S:ℝ))
    (hP : (reciprocalPower (3*dimC):ℝ) ≤ Real.log S)
    (hconst : (reciprocalConstantNat (3*dimC):ℝ)*32^reciprocalPower (3*dimC) ≤ Real.exp (S/4))
    (hX : Real.exp S ≤ X) (hXD : X ≤ Real.exp ((dimX:ℝ)*S))
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) :
    ((badLevel (deterministicProduct p) C X (scaleRho S)).card:ℝ) ≤
      X*Real.exp (-(1/1000:ℝ)*scaleM S) := by
  have hS0 : 0 < S := by linarith
  have hl : 0 < Real.log S := by linarith
  have hm : (scaleM S:ℝ) ≤ S/Real.log S := Nat.floor_le (by positivity)
  have hJ : (Fintype.card J:ℝ) ≤ S/Real.log S := by simpa [hcard] using hm
  have hmoment (l : ℕ) (hlI : l ∈ Icc 1 ⌊1/(scaleRho S)^4⌋₊) :
      (∑ u ∈ scaleInterval X (scaleRho S), ‖phaseAverage (deterministicProduct p) C u l‖^2) ≤
      X*Real.exp (-(1/100:ℝ)*scaleM S) := by
    have hlhi : (l:ℝ) ≤ Real.exp ((1/2500:ℝ)*scaleM S) := by
      calc
        _ ≤ (⌊1/(scaleRho S)^4⌋₊:ℝ) := by exact_mod_cast (mem_Icc.mp hlI).2
        _ ≤ 1/(scaleRho S)^4 := Nat.floor_le (by positivity)
        _ = _ := by
          unfold scaleRho
          rw [←Real.exp_nat_mul,one_div,←Real.exp_neg]
          congr 1
          push_cast
          ring
    exact high_list_moment S X dimC (scaleM S) C l (deterministicProduct p)
      (deterministicProduct_injective p hp hinj) (by simp [hcard])
      (deterministicProduct_bound S hS hl hJ p hmax)
      hS0 hlog (by norm_num [dimC,dimX,dimM]) hm hm100 hP hconst hX
      (by simpa only [dimC,Nat.cast_mul,Nat.cast_ofNat,show (4:ℝ)*(dimX:ℝ)/4 = dimX by ring] using hXD)
      hClo hChi (mem_Icc.mp hlI).1 hlhi
  have hh := badLevel_of_moment (deterministicProduct p) C X (scaleRho S)
    (X*Real.exp (-(1/100:ℝ)*scaleM S)) (scaleRho_pos S)
    (mul_nonneg ((Real.exp_nonneg _).trans hX) (Real.exp_nonneg _)) hmoment
  apply hh.trans
  have heq : X*Real.exp (-(1/100:ℝ)*scaleM S)/(scaleRho S)^10 =
      X*Real.exp (-(9/1000:ℝ)*scaleM S) := by
    unfold scaleRho
    rw [←Real.exp_nat_mul,div_eq_mul_inv,←Real.exp_neg,mul_assoc,←Real.exp_add]
    congr 2
    push_cast
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) ((Real.exp_nonneg _).trans hX)
  have hm0 : (0:ℝ) ≤ scaleM S := Nat.cast_nonneg _
  nlinarith

lemma auxiliary_upper {J : Type uJ} {A : Type uA} [Fintype J]
    (S : ℝ) (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : Fin 1000 → (J × Bool) → A)
    (hS : 2 ≤ S) (hlog : 0 < Real.log S) (hm : (Fintype.card J:ℝ) ≤ S/Real.log S)
    (h₀ : ∀ j, (p₀ j:ℝ) ≤ 2*S^100) (hp : ∀ x, (p x:ℝ) ≤ 2*S^100)
    (ha : (2:ℝ)^a ≤ Real.exp S) :
    (auxiliaryDenominator a p₀ p f:ℝ) ≤ Real.exp ((dimM:ℝ)*S) := by
  have h₁ := products_scale_bound S hS hlog hm p₀ h₀
  have h₂ (i : Fin 1000) : ((∏ j,p (f i (j,false))*p (f i (j,true)) : ℕ):ℝ) ≤ Real.exp (202*S) := by
    rw [prod_mul_distrib,Nat.cast_mul]
    calc
      _ ≤ Real.exp (101*S)*Real.exp (101*S) := mul_le_mul
        (products_scale_bound S hS hlog hm _ (fun _ => hp _))
        (products_scale_bound S hS hlog hm _ (fun _ => hp _)) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have h₃ : ((∏ i : Fin 1000, ∏ j,p (f i (j,false))*p (f i (j,true)) : ℕ):ℝ) ≤ Real.exp (202000*S) := by
    push_cast
    calc
      _ ≤ ∏ _i : Fin 1000,Real.exp (202*S) := prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => by simpa only [Nat.cast_prod,Nat.cast_mul] using h₂ i)
      _ = _ := by rw [prod_const,card_univ,Fintype.card_fin,←Real.exp_nat_mul]; congr 1; push_cast; ring
  unfold auxiliaryDenominator
  push_cast
  calc
    _ ≤ Real.exp S*Real.exp (101*S)*Real.exp (202000*S) := by
      exact mul_le_mul (mul_le_mul ha (by simpa only [Nat.cast_prod] using h₁)
        (prod_nonneg (fun _ _ => Nat.cast_nonneg _)) (Real.exp_nonneg _))
        (by simpa only [Nat.cast_prod,Nat.cast_mul] using h₃)
        (prod_nonneg (fun _ _ => prod_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
        (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = Real.exp (202102*S) := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num [dimM]; nlinarith)

lemma auxiliary_lower {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (S : ℝ) (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A)
    (hS : 0 < S) (hlog : 0 < Real.log S) (hm : S/(2*Real.log S) ≤ (Fintype.card J:ℝ))
    (h₀ : ∀ j, S^100 ≤ (p₀ j:ℝ)) (h₀pos : ∀ j, 0 < p₀ j) (hp : ∀ x, 0 < p x) :
    Real.exp S < (auxiliaryDenominator a p₀ p f:ℝ) := by
  have hbase : Real.exp (50*S) ≤ ((∏ j,p₀ j : ℕ):ℝ) := by
    have hm' := (div_le_iff₀ (by positivity : (0:ℝ)<2*Real.log S)).mp hm
    calc
      _ ≤ Real.exp ((Fintype.card J:ℝ)*(100*Real.log S)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = (S^100)^Fintype.card J := by
        rw [Real.exp_nat_mul]
        congr 1
        rw [←Real.exp_log (pow_pos hS 100),Real.log_pow]
        norm_num
      _ = ∏ _j : J, S^100 := by simp
      _ ≤ _ := by push_cast; exact prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => h₀ j)
  have hMpos := auxiliaryDenominator_pos a p₀ p f h₀pos hp
  have hd : (∏ j,p₀ j) ∣ auxiliaryDenominator a p₀ p f :=
    dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  exact (Real.exp_lt_exp.mpr (by nlinarith : S < 50*S)).trans_le
    (hbase.trans (by exact_mod_cast Nat.le_of_dvd hMpos hd))

end ShortEgyptian

end OAI
