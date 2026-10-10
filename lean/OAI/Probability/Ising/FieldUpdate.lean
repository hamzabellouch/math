import OAI.Probability.Ising.GibbsMeasure
import OAI.Probability.Ising.Interpolation

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

variable {V : Type*} [Fintype V]

/-- The spin at the removed site is inserted without discarding any edge interaction. -/
def insertSpin (v : V) (b : Bool) (η : {u : V // u ≠ v} → Bool) : V → Bool :=
  (Equiv.funSplitAt v Bool).symm (b, η)

omit [Fintype V] in
@[simp] lemma insertSpin_self (v : V) (b : Bool) (η : {u : V // u ≠ v} → Bool) :
    insertSpin v b η v = b := by simp [insertSpin, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype V] in
@[simp] lemma insertSpin_other (v : V) (b : Bool) (η : {u : V // u ≠ v} → Bool)
    (u : {u : V // u ≠ v}) : insertSpin v b η u = η u := by
  simp [insertSpin, Equiv.funSplitAt, Equiv.piSplitAt, u.property]

lemma sum_insert (v : V) (f : (V → Bool) → ℝ) :
    (∑ σ, f σ) =
      (∑ η, f (insertSpin v true η)) + ∑ η, f (insertSpin v false η) := by
  rw [← (Equiv.funSplitAt v Bool).symm.sum_comp f, Fintype.sum_prod_type]
  simp only [insertSpin, Fintype.sum_bool]

lemma sum_remove (v : V) (f : V → ℝ) :
    (∑ u, f u) = f v + ∑ u : {u : V // u ≠ v}, f u := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
  have he : (∑ u ∈ Finset.univ.erase v, f u) = ∑ u : {u : V // u ≠ v}, f u := by
    exact Finset.sum_subtype _ (fun _ => by simp) _
  rw [he, add_comm]

/-- Conditional field induced by an actual fixed spin. -/
def removedField (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool)
    (u : {u : V // u ≠ v}) : ℝ := h u + (J v u + J u v) * sgn b

def removedCoupling (J : V → V → ℝ) (v : V)
    (u w : {u : V // u ≠ v}) : ℝ := J u w

lemma hamiltonian_insert (J : V → V → ℝ) (h : V → ℝ) (v : V)
    (b : Bool) (η : {u : V // u ≠ v} → Bool) :
    hamiltonian J h (insertSpin v b η) = J v v + h v * sgn b +
      hamiltonian (removedCoupling J v) (removedField J h v b) η := by
  unfold hamiltonian
  rw [sum_remove v (fun u => ∑ w, J u w * sgn (insertSpin v b η u) * sgn (insertSpin v b η w))]
  rw [sum_remove v (fun u => h u * sgn (insertSpin v b η u))]
  simp_rw [sum_remove v (fun w => J _ w * sgn (insertSpin v b η _) * sgn (insertSpin v b η w))]
  simp only [insertSpin_self, insertSpin_other, mul_assoc, sgn_sq, mul_one,
    Finset.sum_add_distrib, removedCoupling, removedField, add_mul, Finset.sum_add_distrib]
  have he : (∑ u : {u : V // u ≠ v}, J v u * (sgn b * sgn (η u))) +
        (∑ u : {u : V // u ≠ v}, J u v * (sgn (η u) * sgn b)) =
      ∑ u : {u : V // u ≠ v}, (J v u + J u v) * sgn b * sgn (η u) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc] at he
  linarith

lemma mass_insert (J : V → V → ℝ) (h : V → ℝ) (v : V)
    (b : Bool) (η : {u : V // u ≠ v} → Bool) :
    mass J h (insertSpin v b η) = Real.exp (J v v + h v * sgn b) *
      mass (removedCoupling J v) (removedField J h v b) η := by
  simp only [mass, hamiltonian_insert, Real.exp_add]

/-- Conditional mean at a fixed-spin site; defined on actual remaining spins. -/
def pinMean (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) (o : V) : ℝ :=
  average (removedCoupling J v) (removedField J h v b) (fun η => sgn (insertSpin v b η o))

lemma pinMean_self (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) :
    pinMean J h v b v = sgn b := by
  simp only [pinMean, insertSpin_self, average_const]

lemma pinMean_other (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool)
    (o : V) (hov : o ≠ v) :
    pinMean J h v b o = mean (removedCoupling J v) (removedField J h v b) ⟨o, hov⟩ := by
  unfold pinMean mean
  congr 1
  funext η
  exact congrArg sgn (insertSpin_other v b η ⟨o, hov⟩)

lemma pinMean_mono (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h : V → ℝ) (v o : V) : pinMean J h v false o ≤ pinMean J h v true o := by
  by_cases hov : o = v
  · subst o
    simp [pinMean_self, sgn]
  · rw [pinMean_other _ _ _ _ _ hov, pinMean_other _ _ _ _ _ hov]
    apply mean_mono (removedCoupling J v) (fun u w => hJ u.val w.val)
    intro u
    dsimp [removedField, sgn]
    nlinarith [hJ v u, hJ u v]

lemma average_mul_part (J : V → V → ℝ) (h : V → ℝ) (f : (V → Bool) → ℝ) :
    average J h f * part J h = ∑ σ, mass J h σ * f σ := by
  exact div_mul_cancel₀ _ (part_pos J h).ne'

def pinPart (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) : ℝ :=
  Real.exp (J v v + h v * sgn b) * part (removedCoupling J v) (removedField J h v b)

lemma pinPart_pos (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) :
    0 < pinPart J h v b := mul_pos (Real.exp_pos _) (part_pos _ _)

lemma part_split (J : V → V → ℝ) (h : V → ℝ) (v : V) :
    part J h = pinPart J h v true + pinPart J h v false := by
  rw [part, sum_insert v]
  simp_rw [mass_insert, ← Finset.mul_sum]
  simp only [pinPart, part]
  congr!

lemma mean_split (J : V → V → ℝ) (h : V → ℝ) (v o : V) :
    mean J h o = (pinPart J h v true * pinMean J h v true o +
      pinPart J h v false * pinMean J h v false o) / part J h := by
  unfold mean average
  rw [sum_insert v]
  congr 1
  have H (b : Bool) : (∑ η, mass J h (insertSpin v b η) * sgn (insertSpin v b η o)) =
      pinPart J h v b * pinMean J h v b o := by
    simp_rw [mass_insert, mul_assoc, ← Finset.mul_sum]
    rw [pinPart, pinMean, mul_assoc, mul_comm (part _ _), average_mul_part]
    congr!
  rw [H, H]

lemma mean_self_split (J : V → V → ℝ) (h : V → ℝ) (v : V) :
    mean J h v = (pinPart J h v true - pinPart J h v false) /
      (pinPart J h v true + pinPart J h v false) := by
  rw [mean_split J h v v, pinMean_self, pinMean_self, part_split J h v]
  simp [sgn, sub_eq_add_neg]

lemma mean_affine (J : V → V → ℝ) (h : V → ℝ) (v o : V) :
    mean J h o = (pinMean J h v true o + pinMean J h v false o) / 2 +
      mean J h v * (pinMean J h v true o - pinMean J h v false o) / 2 := by
  rw [mean_split J h v o, mean_self_split J h v, part_split J h v]
  have hz : pinPart J h v true + pinPart J h v false ≠ 0 :=
    (add_pos (pinPart_pos _ _ _ _) (pinPart_pos _ _ _ _)).ne'
  field_simp
  ring

/-- A single finite field increment. -/
def fieldAt (v : V) (t : ℝ) : V → ℝ := fun u => if u = v then t else 0

omit [Fintype V] in
@[simp] lemma fieldAt_self (v : V) (t : ℝ) : fieldAt v t v = t := by simp [fieldAt]

omit [Fintype V] in
@[simp] lemma fieldAt_other (v : V) (t : ℝ) (u : V) (hu : u ≠ v) :
    fieldAt v t u = 0 := by simp [fieldAt, hu]

omit [Fintype V] in
lemma removedField_shift (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) (t : ℝ) :
    removedField J (h + fieldAt v t) v b = removedField J h v b := by
  ext u
  simp [removedField, u.property]

lemma pinMean_shift (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) (o : V) (t : ℝ) :
    pinMean J (h + fieldAt v t) v b o = pinMean J h v b o := by
  simp only [pinMean, removedField_shift]

lemma pinPart_shift (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) (t : ℝ) :
    pinPart J (h + fieldAt v t) v b = pinPart J h v b * Real.exp (t * sgn b) := by
  simp only [pinPart, removedField_shift, Pi.add_apply, fieldAt_self, add_mul,
    ← add_assoc, Real.exp_add]
  ring

lemma mean_field_update (J : V → V → ℝ) (h : V → ℝ) (v : V) (t : ℝ) :
    mean J (h + fieldAt v t) v = (mean J h v + Real.tanh t) /
      (1 + mean J h v * Real.tanh t) := by
  rw [mean_self_split J (h + fieldAt v t) v, mean_self_split J h v]
  simp only [pinPart_shift, sgn, ↓reduceIte, Bool.false_eq_true, mul_one, mul_neg_one]
  rw [Real.tanh_eq]
  have hp := pinPart_pos J h v true
  have hm := pinPart_pos J h v false
  have he := Real.exp_pos t
  have hf := Real.exp_pos (-t)
  have hsum : pinPart J h v true + pinPart J h v false ≠ 0 := (add_pos hp hm).ne'
  have hexp : Real.exp t + Real.exp (-t) ≠ 0 := (add_pos he hf).ne'
  field_simp
  ring_nf
  field_simp
  ring

lemma hamiltonian_flip (J : V → V → ℝ) (h : V → ℝ) (σ : V → Bool) :
    hamiltonian J (-h) (fun u => !(σ u)) = hamiltonian J h σ := by
  simp [hamiltonian, sgn_neg]

lemma mass_flip (J : V → V → ℝ) (h : V → ℝ) (σ : V → Bool) :
    mass J (-h) (fun u => !(σ u)) = mass J h σ := by
  simp only [mass, hamiltonian_flip]

def flipEquiv : (V → Bool) ≃ (V → Bool) where
  toFun σ u := !(σ u)
  invFun σ u := !(σ u)
  left_inv σ := by ext u; simp
  right_inv σ := by ext u; simp

lemma part_neg (J : V → V → ℝ) (h : V → ℝ) : part J (-h) = part J h := by
  rw [part, ← flipEquiv.sum_comp]
  simp only [flipEquiv, Equiv.coe_fn_mk, mass_flip]
  rfl

lemma mean_neg (J : V → V → ℝ) (h : V → ℝ) (v : V) :
    mean J (-h) v = -mean J h v := by
  rw [mean, average, part_neg, ← flipEquiv.sum_comp]
  simp only [flipEquiv, Equiv.coe_fn_mk, mass_flip, sgn_neg, mul_neg,
    Finset.sum_neg_distrib, neg_div]
  rfl

lemma mean_zero (J : V → V → ℝ) (v : V) : mean J 0 v = 0 := by
  have H := mean_neg J 0 v
  simp only [neg_zero] at H
  linarith

lemma mean_nonneg (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h : V → ℝ) (hh : 0 ≤ h) (v : V) : 0 ≤ mean J h v := by
  simpa only [mean_zero] using mean_mono J hJ 0 h hh v

omit [Fintype V] in
@[simp] lemma fieldAt_zero (v : V) : fieldAt v 0 = 0 := by
  ext u
  simp [fieldAt]

lemma mean_mixture_identity (J : V → V → ℝ) (h : V → ℝ) (v o : V)
    (t s α : ℝ) (b : Bool) :
    mean J (h + fieldAt v t) o -
      (α * mean J (h + fieldAt v s) o + (1 - α) * pinMean J h v b o) =
    (mean J (h + fieldAt v t) v -
      (α * mean J (h + fieldAt v s) v + (1 - α) * sgn b)) *
      (pinMean J h v true o - pinMean J h v false o) / 2 := by
  rw [mean_affine J (h + fieldAt v t) v o, mean_affine J (h + fieldAt v s) v o]
  simp only [pinMean_shift]
  cases b <;> norm_num [sgn] <;> ring

lemma mean_mixture_le (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h : V → ℝ) (v o : V) (t s α : ℝ) (b : Bool)
    (H : mean J (h + fieldAt v t) v ≤
      α * mean J (h + fieldAt v s) v + (1 - α) * sgn b) :
    mean J (h + fieldAt v t) o ≤
      α * mean J (h + fieldAt v s) o + (1 - α) * pinMean J h v b o := by
  have hh := mean_mixture_identity J h v o t s α b
  have hd := sub_nonneg.mpr (pinMean_mono J hJ h v o)
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr H) hd
  linarith

lemma mean_mixture_ge (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h : V → ℝ) (v o : V) (t s α : ℝ) (b : Bool)
    (H : α * mean J (h + fieldAt v s) v + (1 - α) * sgn b ≤
      mean J (h + fieldAt v t) v) :
    α * mean J (h + fieldAt v s) o + (1 - α) * pinMean J h v b o ≤
      mean J (h + fieldAt v t) o := by
  have hh := mean_mixture_identity J h v o t s α b
  have hd := sub_nonneg.mpr (pinMean_mono J hJ h v o)
  have hp := mul_nonneg (sub_nonneg.mpr H) hd
  linarith

lemma mean_mixture_eq (J : V → V → ℝ) (h : V → ℝ) (v o : V) (t s α : ℝ) (b : Bool)
    (H : mean J (h + fieldAt v t) v =
      α * mean J (h + fieldAt v s) v + (1 - α) * sgn b) :
    mean J (h + fieldAt v t) o =
      α * mean J (h + fieldAt v s) o + (1 - α) * pinMean J h v b o := by
  have hh := mean_mixture_identity J h v o t s α b
  rw [H, sub_self, zero_mul, zero_div] at hh
  exact sub_eq_zero.mp hh

end

end BufferedIsing.DSS

end OAI
