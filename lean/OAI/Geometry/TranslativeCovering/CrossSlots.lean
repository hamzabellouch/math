import OAI.Geometry.TranslativeCovering.ShellCaps

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

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace CrossSlots
open MeasureTheory PoissonDiagrams
open scoped BigOperators Classical

lemma ratio {z c d x y p q A : ℝ} (hp : 0 < p) (hq : 0 < q) (hA : 0 ≤ A)
    (hc : p ≤ c) (hd : p ≤ d) (hx : q*c ≤ x) (hy : q*d ≤ y)
    (hz : z ≤ A*Real.sqrt (c*d)) : z/(x*y) ≤ A/(p*q^2) := by
  have hc0 := hp.trans_le hc
  have hd0 := hp.trans_le hd
  have hx0 := (mul_pos hq hc0).trans_le hx
  have hy0 := (mul_pos hq hd0).trans_le hy
  have hcd : p^2 ≤ c*d := by nlinarith only [mul_le_mul hc hd hp.le hc0.le]
  have hs : p ≤ Real.sqrt (c*d) := by
    apply (Real.le_sqrt hp.le (mul_nonneg hc0.le hd0.le)).mpr
    exact hcd
  have hs2 := Real.sq_sqrt (mul_nonneg hc0.le hd0.le)
  have hroot : p*Real.sqrt (c*d) ≤ c*d := by nlinarith only [mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (c*d)),hs2]
  have hxy : q^2*c*d ≤ x*y := by
    have hh := mul_le_mul hx hy (mul_nonneg hq.le hd0.le) hx0.le
    nlinarith only [hh]
  apply (div_le_div_iff₀ (mul_pos hx0 hy0) (by positivity)).mpr
  have h1 := mul_le_mul_of_nonneg_right hz (by positivity : 0 ≤ p*q^2)
  have h2 := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ A*q^2)
  have h3 := mul_le_mul_of_nonneg_left hxy hA
  nlinarith only [h1,h2,h3]

lemma diagrams {Ω : Type u_1} {I : Type u_2} {J : Type u_3} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω) {δ : ℝ}
    (_hδ : 0 ≤ δ) (hp : ∀ i j,μ.real (E i ∩ F j)/(μ.real (E i)*μ.real (F j)) ≤ δ) :
    diagram μ E F ≤ (∏ i,μ.real (E i))*(∏ j,μ.real (F j))*
      (Real.exp ((Fintype.card I:ℝ)*(Fintype.card J:ℝ)*δ)-1) := by
  have hb := cross_bound μ E F
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hp i j
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hh

lemma exp_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x-1 ≤ 2*x := by
  have hh := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
    (by linarith : 0 ≤ 1-x) hx (by ring : 1-x+x=1)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,Real.exp_zero] at hh
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  nlinarith only [hh,mul_le_mul_of_nonneg_right he.le hx]

lemma power_decay {Ω : Type u_4} {I : Type u_5} {J : Type u_6} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω) (n : ℕ) (hn : 2 ≤ n)
    (hI : Fintype.card I ≤ n^2) (hJ : Fintype.card J ≤ n^2)
    (hp : ∀ i j,μ.real (E i ∩ F j)/(μ.real (E i)*μ.real (F j)) ≤ (n:ℝ)⁻¹^8) :
    diagram μ E F ≤ (n:ℝ)⁻¹^3*(∏ i,μ.real (E i))*(∏ j,μ.real (F j)) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith only [hnR]
  have hi : (Fintype.card I:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hI
  have hj : (Fintype.card J:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hJ
  have hab : (Fintype.card I:ℝ)*(Fintype.card J:ℝ)*(n:ℝ)⁻¹^8 ≤ (n:ℝ)⁻¹^4 := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul hi hj (by positivity) (by positivity)) (by positivity : 0 ≤ (n:ℝ)⁻¹^8)
    convert hh using 1
    first | rfl | (field_simp)
  have hsmall : (n:ℝ)⁻¹^4 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  have hh := diagrams μ E F (by positivity : 0 ≤ (n:ℝ)⁻¹^8) hp
  have he := (Real.exp_le_exp.mpr hab)
  have hes := exp_small (by positivity : 0 ≤ (n:ℝ)⁻¹^4) hsmall
  have hc : 2*(n:ℝ)⁻¹^4 ≤ (n:ℝ)⁻¹^3 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hn0 4)).mp
    field_simp
    exact hnR
  have hpos : 0 ≤ (∏ i,μ.real (E i))*(∏ j,μ.real (F j)) := by positivity
  have hfinal := mul_le_mul_of_nonneg_left ((sub_le_sub_right he 1).trans (hes.trans hc)) hpos
  exact hh.trans hfinal |>.trans_eq (by ring)

end CrossSlots

end OAI
