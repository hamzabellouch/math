import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Prob
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteProductPin

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteVariance

lemma sq_div_le_self {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hra : r ≤ a) :
    r^2/a ≤ r := by
  rcases eq_or_lt_of_le ha with hz | hp
  · have : r = 0 := by linarith
    simp [this]
  · apply (div_le_iff₀ hp).mpr
    nlinarith

lemma binary_split {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxa : x ≤ a) (hyb : y ≤ b) :
    x^2/a + y^2/b - (x+y)^2/(a+b) = a*b/(a+b)*(y/b-x/a)^2 := by
  rcases eq_or_lt_of_le ha with hz | hp
  · have hx0 : x = 0 := by linarith
    simp [← hz, hx0]
  · rcases eq_or_lt_of_le hb with hz | hq
    · have hy0 : y = 0 := by linarith
      simp [← hz, hy0]
    · have hab : a+b ≠ 0 := (add_pos hp hq).ne'
      field_simp
      ring

end CriticalPercolation.FiniteVariance

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_prop_mask_pin (w : E → Prop → ℝ) (e : E) (b : Prop) (f : (E → Prop) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  convert expect_mask_pin w e b f using 1
  congr 1
  funext ω
  by_cases h : ω e = b <;> simp [h]

lemma expect_split_pin (w : E → Prop → ℝ) (e : E) (f : (E → Prop) → ℝ) :
    expect w f = w e False*expect (pin w e False) f +
      w e True*expect (pin w e True) f := by
  calc
    expect w f = expect w (fun ω => (if ω e = False then f ω else 0) +
      (if ω e = True then f ω else 0)) := by
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
    _ = _ := by
      rw [expect_add]
      apply congrArg₂ (· + ·)
      · convert expect_prop_mask_pin w e False f using 1
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
      · convert expect_prop_mask_pin w e True f using 1
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]

lemma expect_congr_support (w : E → Prop → ℝ) (f g : Set E → ℝ)
    (h : ∀ ω, density w ω ≠ 0 → f ω = g ω) : expect w f = expect w g := by
  unfold expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hd : density w ω = 0
  · simp [hd]
  · rw [h ω hd]

lemma density_pin_support (w : E → Prop → ℝ) (e : E) (b : Prop) (ω : E → Prop)
    (h : density (pin w e b) ω ≠ 0) : ω e = b := by
  rw [density_pin] at h
  by_contra he
  simp [he] at h

lemma density_pin_old_support (w : E → Prop → ℝ) (e : E) (b : Prop) (ω : E → Prop)
    (hw : w e b ≠ 0) (h : density (pin w e b) ω ≠ 0) : density w ω ≠ 0 := by
  have hbit := density_pin_support w e b ω h
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),hbit]
  rw [density_pin,ite_eq_left hbit,one_mul] at h
  exact mul_ne_zero h hw

lemma expect_pin_mask (w : E → Prop → ℝ) (e : E) (b : Prop) (f : Set E → ℝ) :
    expect (pin w e b) (fun ω => if ω e = b then f ω else 0) =
      expect (pin w e b) f := by
  apply expect_congr_support
  intro ω h
  rw [ite_eq_left (density_pin_support w e b ω h)]

noncomputable def potential (w : E → Prop → ℝ) (U R : Set E → Prop) : ℝ :=
  prob w R - (prob w R)^2/prob w U

lemma potential_le (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b) (U R : Set E → Prop) :
    potential w U R ≤ prob w R := by
  have hU := prob_nonneg w hp U
  dsimp [potential]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) hU)

lemma potential_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (U R : Set E → Prop) (hRU : ∀ ω, R ω → U ω) : 0 ≤ potential w U R := by
  dsimp [potential]
  exact sub_nonneg.mpr (FiniteVariance.sq_div_le_self (prob_nonneg w hp U)
    (prob_nonneg w hp R) (prob_mono w hp hRU))

lemma potential_split (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (e : E) (U R : Set E → Prop) (hRU : ∀ ω, R ω → U ω)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hw0 : w e False = 1-p) (hw1 : w e True = p) :
    let U0 := prob (pin w e False) U
    let U1 := prob (pin w e True) U
    let R0 := prob (pin w e False) R
    let R1 := prob (pin w e True) R
    potential w U R - ((1-p)*potential (pin w e False) U R +
      p*potential (pin w e True) U R) =
      p*(1-p)*U0*U1/((1-p)*U0+p*U1)*(R1/U1-R0/U0)^2 := by
  dsimp only
  have hUn := fun b => prob_nonneg (pin w e b) (pin_nonneg w hp e b) U
  have hRn := fun b => prob_nonneg (pin w e b) (pin_nonneg w hp e b) R
  have hRU' := fun b => prob_mono (pin w e b) (pin_nonneg w hp e b) hRU
  have hU : prob w U = (1-p)*prob (pin w e False) U+p*prob (pin w e True) U := by
    have hh := expect_split_pin w e (fun ω => if U ω then 1 else 0)
    simpa only [prob,hw0,hw1] using hh
  have hR : prob w R = (1-p)*prob (pin w e False) R+p*prob (pin w e True) R := by
    have hh := expect_split_pin w e (fun ω => if R ω then 1 else 0)
    simpa only [prob,hw0,hw1] using hh
  have hq : 0 < 1-p := sub_pos.mpr hp1
  have hb := FiniteVariance.binary_split
    (mul_nonneg hq.le (hUn False)) (mul_nonneg hp0.le (hUn True))
    (mul_nonneg hq.le (hRn False)) (mul_nonneg hp0.le (hRn True))
    (mul_le_mul_of_nonneg_left (hRU' False) hq.le)
    (mul_le_mul_of_nonneg_left (hRU' True) hp0.le)
  have hscale : ∀ (c d : ℝ), (c*d)^2/c = c*d^2 := by
    intro c d
    by_cases hc : c = 0
    · simp [hc]
    · field_simp
  simp only [mul_div_mul_left _ _ hq.ne',mul_div_mul_left _ _ hp0.ne'] at hb
  have hx : ∀ (c d u : ℝ), (c*d)^2/(c*u) = c*d^2/u := by
    intro c d u
    rw [div_mul_eq_div_div,hscale]
  simp only [hx] at hb
  dsimp [potential]
  rw [hU,hR]
  convert hb using 1 <;> ring

end CriticalPercolation.FiniteProduct

end
end

end OAI
