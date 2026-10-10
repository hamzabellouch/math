import OAI.Geometry.TranslativeCovering.CrossDeployment

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3

namespace CrossDiagram
open MeasureTheory PoissonDiagrams
open scoped BigOperators

lemma small {Ω : Type u_1} {I : Type u_2} {J : Type u_3} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    {n : ℕ} (hn : 0 < n) (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω)
    (hI : Fintype.card I ≤ n^2) (hJ : Fintype.card J ≤ n^2)
    (hsmall : ∀ i j,μ.real (E i ∩ F j)/(μ.real (E i)*μ.real (F j)) ≤ (n:ℝ)⁻¹^8) :
    diagram μ E F ≤ (∏ i,μ.real (E i))*(∏ j,μ.real (F j))*(Real.exp ((n:ℝ)⁻¹^4)-1) := by
  have hI' : (Fintype.card I:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hI
  have hJ' : (Fintype.card J:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hJ
  have hprod := mul_le_mul hI' hJ' (Nat.cast_nonneg _) (sq_nonneg (n:ℝ))
  have hsum : ∑ i,∑ j,μ.real (E i ∩ F j)/(μ.real (E i)*μ.real (F j)) ≤ (n:ℝ)⁻¹^4 := by
    calc
      _ ≤ ∑ _i : I,∑ _j : J,(n:ℝ)⁻¹^8 := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsmall i j
      _ = ((Fintype.card I:ℝ)*(Fintype.card J:ℝ))*(n:ℝ)⁻¹^8 := by simp; ring
      _ ≤ (((n:ℝ)^2)*((n:ℝ)^2))*(n:ℝ)⁻¹^8 := mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = _ := by
        have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        field_simp

  exact (cross_bound μ E F).trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1) (by positivity))

lemma exp_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x-1 ≤ 2*x := by
  have hb := Real.norm_exp_sub_one_sub_id_le (x := x) (by simpa [Real.norm_of_nonneg hx] using hx1)
  have h := le_trans (le_abs_self (Real.exp x-1-x)) (by simpa [Real.norm_eq_abs,abs_of_nonneg hx] using hb)
  nlinarith only [h,mul_nonneg hx (sub_nonneg.mpr hx1)]

lemma inverse_scale {n : ℕ} (hn : 2 ≤ n) : Real.exp ((n:ℝ)⁻¹^4)-1 ≤ (n:ℝ)⁻¹^3 := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith only [hn']
  have h1 : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hn'])
  have h0 : 0 ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr hn0.le
  apply (exp_small (pow_nonneg h0 _) (pow_le_one₀ h0 h1)).trans
  have hi : 2*(n:ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hn0).mpr hn'
  calc
    _ = (2*(n:ℝ)⁻¹)*((n:ℝ)⁻¹^3) := by ring
    _ ≤ 1*((n:ℝ)⁻¹^3) := mul_le_mul_of_nonneg_right hi (by positivity)
    _ = _ := one_mul _
end CrossDiagram

end OAI
