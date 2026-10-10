import Mathlib

namespace OAI

                                   
section

/-! Source companion 04, Lemma denominators: the exact logarithmic denominator
family and its dimension-free simplex sum estimate. This is required to
instantiate the compact proportion tracker, not a new main theorem. -/
namespace UniformKServer.Denominators
noncomputable def regular (h a : ℝ) : ℝ := (h+Real.log (1/a))^2/h
noncomputable def height (u : ℝ) : ℝ := 1+Real.log (1/u)
noncomputable def marked (u a : ℝ) : ℝ := u+height u*Real.log (1/a)*(1+Real.log (1/a))
noncomputable def family {ι : Type*} [DecidableEq ι] (o : ι) (u : ℝ) (h a : ι → ℝ) (i : ι) : ℝ :=
  if i = o then marked u (a i) else regular (h i) (a i)

-- CANDIDATE PROOFS


theorem log_nonneg {a : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) : 0 ≤ Real.log (1/a) := by
  rcases ha.eq_or_lt with hz | hp
  · simp [← hz]
  · exact Real.log_nonneg ((le_div_iff₀ hp).mpr (by linarith))

theorem height_ge_one {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) : 1 ≤ height u := by
  unfold height
  linarith [log_nonneg hu.le hu₁]

theorem regular_pos {h a : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    0 < regular h a := by
  unfold regular
  exact div_pos (sq_pos_of_pos (add_pos_of_pos_of_nonneg hh (log_nonneg ha ha₁))) hh

theorem marked_pos {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    0 < marked u a := by
  unfold marked
  have hH := height_ge_one hu hu₁
  have hlog := log_nonneg ha ha₁
  have hp : 0 ≤ height u*Real.log (1/a)*(1+Real.log (1/a)) := by positivity
  linarith

theorem exp_sq_bound {y : ℝ} (hy : 0 ≤ y) : y^2 ≤ 8*Real.exp (y/2) := by
  have hh := Real.quadratic_le_exp_of_nonneg (show 0 ≤ y/2 by linarith)
  nlinarith

theorem regular_scalar {h a : ℝ} (hh : 1 ≤ h) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    a*regular h a ≤ 25*a*h+32*Real.exp (-h) := by
  have hhp : 0 < h := by linarith
  rcases ha.eq_or_lt with hz | hap
  · simp only [← hz, zero_mul]
    positivity
  let y := Real.log (1/a)
  have hy : 0 ≤ y := log_nonneg ha ha₁
  have hay : Real.exp (-y) = a := by simp [y, one_div, Real.log_inv, Real.exp_log hap]
  change a*((h+y)^2/h) ≤ _
  by_cases hnear : y ≤ 4*h
  · have hb : (h+y)^2/h ≤ 25*h := by
      apply (div_le_iff₀ hhp).mpr
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hb ha
    have hp := Real.exp_pos (-h)
    nlinarith
  · have hfar : 4*h < y := lt_of_not_ge hnear
    have hb : (h+y)^2/h ≤ 4*y^2 := by
      apply (div_le_iff₀ hhp).mpr
      have : y^2 ≤ y^2*h := by nlinarith [sq_nonneg y]
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hb ha
    have he := mul_le_mul_of_nonneg_left (exp_sq_bound hy) (Real.exp_nonneg (-y))
    have heq : Real.exp (-y)*Real.exp (y/2) = Real.exp (-y/2) := by
      rw [← Real.exp_add]
      congr 1; ring
    have heq' : Real.exp (-y)*(8*Real.exp (y/2)) = 8*Real.exp (-y/2) := by
      calc
        _ = 8*(Real.exp (-y)*Real.exp (y/2)) := by ring
        _ = _ := by rw [heq]
    rw [heq', hay] at he
    have htail : Real.exp (-y/2) ≤ Real.exp (-h) := Real.exp_le_exp.mpr (by linarith)
    have hab : 0 ≤ a*h := mul_nonneg ha hhp.le
    nlinarith

theorem marked_scalar {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    a*marked u a ≤ a*u+2*height u*(1-a) := by
  have hH := height_ge_one hu hu₁
  rcases ha.eq_or_lt with hz | hap
  · simp only [← hz, zero_mul, zero_add, sub_zero, mul_one]
    linarith
  let y := Real.log (1/a)
  have hy : 0 ≤ y := log_nonneg ha ha₁
  have he : Real.exp y = 1/a := Real.exp_log (div_pos zero_lt_one hap)
  have hb := mul_le_mul_of_nonneg_left (Real.quadratic_le_exp_of_nonneg hy) ha
  rw [he, mul_one_div_cancel hap.ne'] at hb
  have hp : 0 ≤ a*y := mul_nonneg ha hy
  have ht : a*y*(1+y) ≤ 2*(1-a) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ height u by linarith)
  change a*(u+height u*y*(1+y)) ≤ _
  nlinarith

theorem total_ge_one {ι : Type*} [Fintype ι] {h a : ι → ℝ}
    (hh : ∀ i, 1 ≤ h i) (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1) :
    1 ≤ ∑ i, a i*h i := by
  rw [← has]
  exact Finset.sum_le_sum fun i _ => by nlinarith [mul_nonneg (ha i) (sub_nonneg.mpr (hh i))]

theorem regular_simplex {ι : Type*} [Fintype ι] (h a : ι → ℝ) (Z : ℝ)
    (hh : ∀ i, 1 ≤ h i) (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1)
    (he : (∑ i, Real.exp (-h i)) ≤ Z) :
    (∑ i, a i*regular (h i) (a i)) ≤ (25+32*Z)*(∑ i, a i*h i) := by
  have hz : 0 ≤ Z := (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => Real.exp_nonneg (-h i))).trans he
  have ha₁ : ∀ i, a i ≤ 1 := fun i => by
    rw [← has]
    exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => regular_scalar (hh i) (ha i) (ha₁ i))
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hs
  have hT := total_ge_one hh ha has
  have hm := mul_le_mul_of_nonneg_left hT hz
  nlinarith

theorem marked_simplex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : ι) (u c Z : ℝ) (h a : ι → ℝ)
    (hu : 0 < u) (hu₁ : u ≤ 1) (hc : 0 < c) (hc₁ : c ≤ 1) (hZ : 0 ≤ Z)
    (ho : h o = u) (hh : ∀ i, i ≠ o → 1 ≤ h i)
    (hhc : ∀ i, i ≠ o → c*height u ≤ h i)
    (he : (∑ i ∈ Finset.univ.erase o, Real.exp (-h i)) ≤ Z*u)
    (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1) :
    (∑ i, a i*family o u h a i) ≤ (25+(2+32*Z)/c)*(∑ i, a i*h i) := by
  have ha₁ : ∀ i, a i ≤ 1 := fun i => by
    rw [← has]
    exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hH := height_ge_one hu hu₁
  have hal : (∑ i ∈ Finset.univ.erase o, a i) = 1-a o := by
    have heq := Finset.sum_erase_add Finset.univ a (Finset.mem_univ o)
    rw [has] at heq
    linarith
  have hT : (∑ i, a i*h i) = (∑ i ∈ Finset.univ.erase o, a i*h i)+a o*u := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o), ho]
  have hside : c*height u*(1-a o) ≤ ∑ i ∈ Finset.univ.erase o, a i*h i := by
    rw [← hal, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hb := mul_le_mul_of_nonneg_left (hhc i (Finset.ne_of_mem_erase hi)) (ha i)
    nlinarith
  have hR : 0 ≤ ∑ i ∈ Finset.univ.erase o, a i*h i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (ha i) (le_trans (by norm_num) (hh i (Finset.ne_of_mem_erase hi)))
  have hcu : c*u ≤ ∑ i, a i*h i := by
    rw [hT]
    have hhu : c*u*(1-a o) ≤ c*height u*(1-a o) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : u ≤ height u) hc.le)
        (sub_nonneg.mpr (ha₁ o))
    have hao : c*(a o*u) ≤ a o*u := mul_le_of_le_one_left (mul_nonneg (ha o) hu.le) hc₁
    nlinarith
  have hbase : (∑ i, a i*family o u h a i) ≤
      25*(∑ i ∈ Finset.univ.erase o, a i*h i)+32*Z*u+a o*u+2*height u*(1-a o) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o)]
    have hreg : (∑ i ∈ Finset.univ.erase o, a i*family o u h a i) ≤
        25*(∑ i ∈ Finset.univ.erase o, a i*h i)+32*Z*u := by
      have hs := Finset.sum_le_sum (fun i (hi : i ∈ Finset.univ.erase o) =>
        regular_scalar (hh i (Finset.ne_of_mem_erase hi)) (ha i) (ha₁ i))
      have eqn : (∑ i ∈ Finset.univ.erase o, a i*family o u h a i) =
          ∑ i ∈ Finset.univ.erase o, a i*regular (h i) (a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [family, Finset.ne_of_mem_erase hi]
      rw [eqn]
      simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hs
      linarith
    have hm := marked_scalar hu hu₁ (ha o) (ha₁ o)
    simp only [family, ↓reduceIte] at *
    linarith
  have hextra : 32*Z*u+2*height u*(1-a o) ≤ ((2+32*Z)/c)*(∑ i, a i*h i) := by
    apply (mul_le_mul_iff_right₀ hc).mp
    have eqn : c*(((2+32*Z)/c)*(∑ i, a i*h i)) = (2+32*Z)*(∑ i, a i*h i) := by
      field_simp
    rw [eqn]
    have hm := mul_le_mul_of_nonneg_left hcu (show 0 ≤ 32*Z by positivity)
    rw [hT] at hm ⊢
    nlinarith [mul_nonneg hc.le (mul_nonneg (ha o) hu.le)]
  rw [hT]
  rw [hT] at hextra
  nlinarith [mul_nonneg (ha o) hu.le]

end UniformKServer.Denominators

                                                                         
                                                                              

end

end OAI
