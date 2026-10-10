import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.BooleanRough01
import OAI.Combinatorics.SumProduct.Alignment.CoefficientPeeling01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
end
 
end

end
 

section
 
noncomputable section
open Finset
open scoped BigOperators
namespace BooleanPeeling
open BooleanRough CoefficientPeeling
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
 

theorem peel_cube (degree : ι → ℕ) (D q M : ℕ)
    (hdeg : ∀ i, 1 ≤ degree i ∧ degree i ≤ D) (hdim : 2*(q+D) < Fintype.card α)
    (a : ℤ) (b : α → ℤ) (θ : ι → Finset α → ℝ) (hθ : ∀ i, DegreeLE q (θ i))
    (htpos : ∀ S : Finset α, 0 < a + ∑ i ∈ S, b i)
    (htbound : ∀ S : Finset α, a + ∑ i ∈ S, b i ≤ (M : ℤ))
    (hrough : ∀ p : ℕ, p.Prime → (∃ S : Finset α, (p : ℤ) ∣ a + ∑ i ∈ S, b i) →
      Fintype.card α < p ∧ ∀ i, ¬ (p : ℤ) ∣ b i)
    (Z A₀ C₀ : ℝ) (hZ : 0 < Z) (hMZ : (M : ℝ) ≤ Z) (hA₀ : 0 < A₀) (hC₀ : 0 ≤ C₀)
    (p : Finset α → ℕ) (hp : ∀ S, p S = 1 ∨ p S = (a+∑ i ∈ S, b i).natAbs)
    (c : ι → ι → Finset α → ℤ)
    (hc : ∀ i j S, degree i < degree j →
      |(c i j S : ℝ)| ≤ C₀*(p S : ℝ)^(degree j-degree i))
    (ho : ∀ i S, NearInteger ((p S : ℝ)^degree i * (Eval (θ i) S +
      ∑ j ∈ univ.filter (fun j => degree i < degree j), (c i j S : ℝ)*Eval (θ j) S))
      (A₀*((p S : ℝ)/Z)^degree i))
    (hsmall : let β : ℝ := max 1 (A₀+(Fintype.card ι : ℝ)*C₀)
      (1+(M : ℝ)^D*(2^(Fintype.card α) : ℝ)^2)*(β^D*((M : ℝ)/Z))*
        (M : ℝ)^(D*2^(Fintype.card α)) < 1) :
    let β : ℝ := max 1 (A₀+(Fintype.card ι : ℝ)*C₀)
    ∃ f : ι → Finset α → ℚ, ∀ i, DegreeLE q (f i) ∧ IntegralCoeffs (f i) ∧
      ∀ S, |Eval (θ i) S - ((Eval (f i) S : ℚ) : ℝ)| *Z^(degree i) ≤ β^D := by
  classical
  let J : ℝ := (Fintype.card ι : ℝ)*C₀
  let β : ℝ := max 1 (A₀+J)
  change (1+(M : ℝ)^D*(2^(Fintype.card α) : ℝ)^2)*(β^D*((M : ℝ)/Z))*
      (M : ℝ)^(D*2^(Fintype.card α)) < 1 at hsmall
  change ∃ f : ι → Finset α → ℚ, ∀ i, DegreeLE q (f i) ∧ IntegralCoeffs (f i) ∧
    ∀ S, |Eval (θ i) S - ((Eval (f i) S : ℚ) : ℝ)| *Z^(degree i) ≤ β^D
  let t : Finset α → ℤ := fun S => a+∑ i ∈ S, b i
  have ht (S : Finset α) : 0 < t S := htpos S
  have htn (S : Finset α) : ((t S).natAbs : ℝ) = (t S : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast ht S)]
  have hM : (1 : ℝ) ≤ M := by
    have hh : (1 : ℤ) ≤ (M : ℤ) := (ht ∅).trans_le (htbound ∅)
    exact_mod_cast hh
  have hb : 1 ≤ β := le_max_left _ _
  have hbpos : 0 < β := zero_lt_one.trans_le hb
  have hJ : 0 ≤ J := mul_nonneg (Nat.cast_nonneg _) hC₀
  have hratio : 0 ≤ (M : ℝ)/Z ∧ (M : ℝ)/Z ≤ 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) hZ.le, (div_le_one hZ).mpr hMZ⟩
  have hbound (k : ℕ) : A₀+J*β^k ≤ β^(k+1) := by
    have hb1 : 1 ≤ β^k := one_le_pow₀ hb
    calc
      _ ≤ (A₀+J)*β^k := by nlinarith
      _ ≤ β*β^k := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hsmall_e (e : ℕ) (he : e ≤ D) :
      (1+(M : ℝ)^e*(2^(Fintype.card α) : ℝ)^2)*(β^D*((M : ℝ)/Z))*
        (M : ℝ)^(e*2^(Fintype.card α)) < 1 := by
    apply lt_of_le_of_lt _ hsmall
    gcongr
  have hpZ (S : Finset α) : (p S : ℝ) ≤ Z := by
    rcases hp S with hpS | hpS
    · rw [hpS, Nat.cast_one]
      exact hM.trans hMZ
    · rw [hpS, htn]
      exact (show (t S : ℝ) ≤ (M : ℝ) by exact_mod_cast htbound S).trans hMZ
  have hstage (k : ℕ) (hk : k ≤ D) :
      ∃ f : ι → Finset α → ℚ, ∀ i, D-k < degree i →
        DegreeLE q (f i) ∧ IntegralCoeffs (f i) ∧
        ∀ S, |Eval (θ i) S - ((Eval (f i) S : ℚ) : ℝ)| *Z^(degree i) ≤ β^k := by
    induction k with
    | zero =>
      exact ⟨fun _ _ => 0, fun i hi => by have := (hdeg i).2; omega⟩
    | succ k ih =>
      have hkD : k < D := by omega
      obtain ⟨f, hf⟩ := ih (by omega)
      have hlocal (i : ι) : ∃ fi : Finset α → ℚ, D-(k+1) < degree i →
          DegreeLE q fi ∧ IntegralCoeffs fi ∧
          ∀ S, |Eval (θ i) S - ((Eval fi S : ℚ) : ℝ)| *Z^(degree i) ≤ β^(k+1) := by
        by_cases hhi : D-k < degree i
        · refine ⟨f i, fun _ => ⟨(hf i hhi).1, (hf i hhi).2.1, fun S => ?_⟩⟩
          exact ((hf i hhi).2.2 S).trans (pow_le_pow_right₀ hb (by omega))
        by_cases hnew : D-(k+1) < degree i
        · have hei : degree i = D-k := by omega
          let T : Finset ι := univ.filter (fun j => degree i < degree j)
          have hT (j : ι) (hj : j ∈ T) : D-k < degree j := by
            have := (mem_filter.mp hj).2
            omega
          have hnear (S : Finset α) : NearInteger ((t S : ℝ)^degree i*Eval (θ i) S)
              ((A₀+J*β^k)*((t S : ℝ)/Z)^degree i) := by
            have him (j : ι) : ∃ v : ℤ, j ∈ T → Eval (f j) S = (v : ℚ) := by
              by_cases hj : j ∈ T
              · obtain ⟨v, hv⟩ := eval_integral_of_coeffs (f j) (hf j (hT j hj)).2.1 S
                exact ⟨v, fun _ => hv⟩
              · exact ⟨0, fun h => (hj h).elim⟩
            choose z hz using him
            have herr (j : ι) (hj : j ∈ T) :
                |Eval (θ j) S-(z j : ℝ)| *Z^degree j ≤ β^k := by
              have hz' : ((Eval (f j) S : ℚ) : ℝ) = (z j : ℝ) := by exact_mod_cast hz j hj
              rw [← hz']
              exact (hf j (hT j hj)).2.2 S
            have hp' := CoefficientPeeling.peel T degree (degree i)
              (fun j hj => (mem_filter.mp hj).2.le) (p S) hZ (hpZ S)
              (by positivity : 0 ≤ β^k) (Eval (θ i) S) (fun j => Eval (θ j) S) z
              (fun j => c i j S) (fun _ => C₀) (fun _ _ => hC₀)
              (fun j hj => hc i j S (mem_filter.mp hj).2) herr (ho i S)
            have hTJ : (∑ j ∈ T, C₀) ≤ J := by
              simp only [sum_const, nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr T.card_le_univ) hC₀
            have hp'' := hp'.mono (show
                (A₀+(∑ j ∈ T, C₀)*β^k)*((p S : ℝ)/Z)^degree i ≤
                (A₀+J*β^k)*((p S : ℝ)/Z)^degree i by gcongr)
            have hh := unit_or_rough hZ.ne' (hp S) hp''
            change NearInteger ((t S).natAbs ^ degree i * Eval (θ i) S)
              ((A₀+J*β^k)*((t S).natAbs / Z)^degree i) at hh
            simpa only [htn] using hh
          have hδ (S : Finset α) : (A₀+J*β^k)*((t S : ℝ)/Z)^degree i ≤ β^D*((M : ℝ)/Z) := by
            have hpow : ((t S : ℝ)/Z)^degree i ≤ (M : ℝ)/Z := by
              calc
                _ ≤ ((M : ℝ)/Z)^degree i := by
                  apply pow_le_pow_left₀ (div_nonneg (by exact_mod_cast (ht S).le) hZ.le)
                  exact div_le_div_of_nonneg_right (by exact_mod_cast htbound S) hZ.le
                _ ≤ ((M : ℝ)/Z)^1 := pow_le_pow_of_le_one hratio.1 hratio.2 (hdeg i).1
                _ = _ := pow_one _
            have hAb : A₀+J*β^k ≤ β^D :=
              (hbound k).trans (pow_le_pow_right₀ hb (by omega))
            exact mul_le_mul hAb hpow (pow_nonneg (div_nonneg (by exact_mod_cast (ht S).le) hZ.le) _) (by positivity)
          obtain ⟨fi, hfi, hfint, hferr⟩ := rough_rounding_local q (degree i) M
            (by have := (hdeg i).2; omega) a b (θ i) (hθ i) htpos htbound hrough
            (β^D*((M : ℝ)/Z)) (by positivity) (hsmall_e _ (hdeg i).2)
            (fun S => (A₀+J*β^k)*((t S : ℝ)/Z)^degree i) hδ hnear
          refine ⟨fi, fun _ => ⟨hfi, hfint, fun S => ?_⟩⟩
          have htne : (t S : ℝ) ≠ 0 := by exact_mod_cast (ht S).ne'
          have he : ((A₀+J*β^k)*((t S : ℝ)/Z)^degree i) / (t S : ℝ)^degree i * Z^degree i =
              A₀+J*β^k := by rw [div_pow]; field_simp
          have hh := mul_le_mul_of_nonneg_right (hferr S) (pow_nonneg hZ.le (degree i))
          change |Eval (θ i) S - ((Eval fi S : ℚ) : ℝ)| *Z^degree i ≤
            ((A₀+J*β^k)*((t S : ℝ)/Z)^degree i) / (t S : ℝ)^degree i * Z^degree i at hh
          exact (hh.trans_eq he).trans (hbound k)
        · exact ⟨fun _ => 0, fun h => (hnew h).elim⟩
      choose f' hf' using hlocal
      exact ⟨f', hf'⟩
  obtain ⟨f, hf⟩ := hstage D le_rfl
  exact ⟨f, fun i => hf i (by have := (hdeg i).1; omega)⟩

end BooleanPeeling

end

end
 

section
 
 

noncomputable section
namespace BooleanRough
open Finset
open scoped BigOperators
variable {α K : Type*} [DecidableEq α]

def BoolCoeffs [CommRing K] (p : MvPolynomial α K) (S : Finset α) : K :=
  ∑ m ∈ p.support, if m.support = S then p.coeff m else 0

omit [DecidableEq α] in
lemma support_card_le_sum [DecidableEq α] (m : α →₀ ℕ) :
    m.support.card ≤ m.sum (fun _ n => n) := by
  calc
    _ = ∑ _i ∈ m.support, 1 := by simp
    _ ≤ ∑ i ∈ m.support, m i := sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    _ = _ := rfl

lemma degree_boolCoeffs [CommRing K] (p : MvPolynomial α K) :
    DegreeLE p.totalDegree (BoolCoeffs p) := by
  intro S hS
  apply sum_eq_zero
  intro m hm
  have hmS : m.support ≠ S := by
    intro he
    have hd := (support_card_le_sum m).trans (MvPolynomial.le_totalDegree hm)
    rw [he] at hd
    omega
  simp [hmS]

lemma monomial_boolean_eval [CommRing K] (m : α →₀ ℕ) (c : K) (S : Finset α) :
    MvPolynomial.eval (fun i => if i ∈ S then 1 else 0) (MvPolynomial.monomial m c) =
      if m.support ⊆ S then c else 0 := by
  rw [MvPolynomial.eval_monomial]
  by_cases h : m.support ⊆ S
  · rw [ite_eq_left h]
    have hp : m.prod (fun i n => (if i ∈ S then (1 : K) else 0)^n) = 1 := by
      apply prod_eq_one
      intro i hi
      simp [h hi]
    rw [hp]
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi, hiS⟩ := not_subset.mp h
    have hp : m.prod (fun i n => (if i ∈ S then (1 : K) else 0)^n) = 0 := by
      apply prod_eq_zero hi
      simp [hiS, Finsupp.mem_support_iff.mp hi]
    rw [hp]
    simp

lemma eval_boolCoeffs [CommRing K] (p : MvPolynomial α K) (S : Finset α) :
    Eval (BoolCoeffs p) S = MvPolynomial.eval (fun i => if i ∈ S then 1 else 0) p := by
  unfold Eval BoolCoeffs
  rw [sum_comm]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, monomial_boolean_eval]
  apply sum_congr rfl
  intro m hm
  simp [mem_powerset]

theorem exists_boolean_coefficients [CommRing K] (p : MvPolynomial α K) :
    ∃ f : Finset α → K, DegreeLE p.totalDegree f ∧
      ∀ S, Eval f S = MvPolynomial.eval (fun i => if i ∈ S then 1 else 0) p :=
  ⟨BoolCoeffs p, degree_boolCoeffs p, eval_boolCoeffs p⟩

 
def AsPoly [Fintype α] [CommRing K] (f : Finset α → K) : MvPolynomial α K :=
  ∑ S : Finset α, MvPolynomial.C (f S) * ∏ i ∈ S, MvPolynomial.X i

omit [DecidableEq α] in
lemma asPoly_degree [DecidableEq α] [Fintype α] [CommRing K] [Nontrivial K]
    (d : ℕ) (f : Finset α → K)
    (hf : DegreeLE d f) : (AsPoly f).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro S _
  by_cases hS : S.card ≤ d
  · calc
      _ ≤ (MvPolynomial.C (f S) : MvPolynomial α K).totalDegree +
          (∏ i ∈ S, MvPolynomial.X i : MvPolynomial α K).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = (∏ i ∈ S, MvPolynomial.X i : MvPolynomial α K).totalDegree := by simp
      _ ≤ ∑ i ∈ S, (MvPolynomial.X i : MvPolynomial α K).totalDegree :=
        MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ S.card := by
        calc
          _ ≤ ∑ _i ∈ S, 1 := sum_le_sum (fun i _ => by simp [MvPolynomial.totalDegree_X])
          _ = _ := by simp
      _ ≤ d := hS
  · simp [hf S (by omega)]

lemma prod_boolean [CommRing K] (S T : Finset α) :
    (∏ i ∈ T, if i ∈ S then (1 : K) else 0) = if T ⊆ S then 1 else 0 := by
  by_cases h : T ⊆ S
  · simp only [ite_eq_left h]
    exact prod_eq_one (fun i hi => ite_eq_left (h hi))
  · rw [ite_eq_right h]
    obtain ⟨i, hi, hiS⟩ := not_subset.mp h
    exact prod_eq_zero hi (ite_eq_right hiS)

lemma eval_asPoly [Fintype α] [CommRing K] (f : Finset α → K) (S : Finset α) :
    MvPolynomial.eval (fun i => if i ∈ S then 1 else 0) (AsPoly f) = Eval f S := by
  simp only [AsPoly, map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X,
    prod_boolean]
  rw [show (∑ T : Finset α, f T * (if T ⊆ S then 1 else 0)) =
      ∑ T : Finset α, if T ∈ S.powerset then f T else 0 by
    apply sum_congr rfl
    intro T _
    simp only [mem_powerset]
    split_ifs <;> simp]
  change (∑ T : Finset α, if T ∈ S.powerset then f T else 0) = ∑ T ∈ S.powerset, f T
  rw [← sum_filter]
  congr 1
  ext T
  simp

end BooleanRough

end
end

end OAI
