import OAI.MathematicalPhysics.AlternatingFlow.RecursiveBounds

namespace OAI

section JetNamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

noncomputable def direction (i : Fin 4) : ℝ × Space :=
  ![(1,0), (0,e 0), (0,e 1), (0,e 2)] i

lemma direction_norm (i : Fin 4) : ‖direction i‖ ≤ 1 := by
  fin_cases i <;> simp [direction, Prod.norm_def, Bounds.norm_e]

def shift (i : Fin 4) (h : ℚ) (q : RationalPoint) : RationalPoint :=
  if i = 0 then (q.1+h,q.2) else
  if i = 1 then (q.1,q.2.1+h,q.2.2) else
  if i = 2 then (q.1,q.2.1,q.2.2.1+h,q.2.2.2) else
  (q.1,q.2.1,q.2.2.1,q.2.2.2+h)

lemma shift_computable : Computable (fun z : Fin 4 × ℚ × RationalPoint => shift z.1 z.2.1 z.2.2) := by
  have h0 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have h1 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have h2 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have h3 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hh : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.1) := Computable.fst.comp Computable.snd
  have hi (i : Fin 4) : Computable (fun z : Fin 4 × ℚ × RationalPoint => decide (z.1 = i)) :=
    Primrec.eq.decide.to_comp.comp Computable.fst (Computable.const i)
  have hadd := Arithmetic.rat_add.to_comp
  exact (Computable.cond (hi 0) ((hadd.comp h0 hh).pair (h1.pair (h2.pair h3)))
    (Computable.cond (hi 1) (h0.pair ((hadd.comp h1 hh).pair (h2.pair h3)))
      (Computable.cond (hi 2) (h0.pair (h1.pair ((hadd.comp h2 hh).pair h3)))
        (h0.pair (h1.pair (h2.pair (hadd.comp h3 hh))))))).of_eq (by rintro ⟨i,h,q⟩; fin_cases i <;> rfl)

lemma shift_cast (i : Fin 4) (h : ℚ) (q : RationalPoint) :
    rationalPoint (shift i h q) = rationalPoint q + (h:ℝ) • direction i := by
  fin_cases i <;> ext j <;> simp [shift, rationalPoint, rationalVector, direction, e,
    EuclideanSpace.equiv] <;> fin_cases j <;> simp

noncomputable def wordJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × Space → E) : List (Fin 4) → ℝ × Space → E
  | [] => f
  | i::w => fun z => fderiv ℝ (wordJet f w) z (direction i)

lemma wordJet_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} (hf : ContDiff ℝ ∞ f) (w : List (Fin 4)) :
    ContDiff ℝ ∞ (wordJet f w) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma wordJet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} (hf : ContDiff ℝ ∞ f) (w : List (Fin 4)) (r : ℕ) (z : ℝ × Space) :
    ‖iteratedFDeriv ℝ r (wordJet f w) z‖ ≤ ‖iteratedFDeriv ℝ (r+w.length) f z‖ := by
  induction w generalizing r with
  | nil => simp [wordJet]
  | cons i w ih =>
    apply (Bounds.norm_directional_iterated _ (wordJet_smooth hf w) (direction i) r z).trans
    apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (direction_norm i))
    have hi : r + (i :: w).length = r + 1 + w.length := by simp only [List.length_cons]; omega
    rw [hi]
    exact ih (r+1)

lemma jet_lipschitz {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (C : ℝ)
    (hC : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C) (x y : E) :
    ‖f x - f y‖ ≤ C * ‖x-y‖ := by
  exact (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => by simpa only [norm_iteratedFDeriv_one] using hC x) (Set.mem_univ y) (Set.mem_univ x)

lemma difference_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C)
    (q v : E) (hv : ‖v‖ ≤ 1) {h : ℝ} (hh : 0 < h) :
    |fderiv ℝ f q v - (f (q+h•v)-f q)/h| ≤ C*h := by
  have hLip (x y : E) : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x-y‖ :=
    jet_lipschitz (hf.fderiv_right (by simp)) C (fun x => by
      simpa only [norm_iteratedFDeriv_fderiv] using hbound x) x y
  have hdist : ‖(q+h•v)-q‖ ≤ h := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hh] using mul_le_mul_of_nonneg_left hv hh.le
  have hmv := (convex_closedBall q h).norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f q) (x := q) (y := q+h•v)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x hx => (hLip x q).trans (mul_le_mul_of_nonneg_left
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx) hC))
    (Metric.mem_closedBall_self hh.le) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hdist)
  have hmv' : |f (q+h•v)-f q-h*fderiv ℝ f q v| ≤ C*h*h := by
    have hx := hmv.trans (mul_le_mul_of_nonneg_left hdist (mul_nonneg hC hh.le))
    simpa only [add_sub_cancel_left, map_smul, smul_eq_mul, Real.norm_eq_abs] using hx
  rw [← abs_neg, neg_sub, div_sub' hh.ne', abs_div, abs_of_pos hh, div_le_iff₀ hh]
  simpa only [one_mul, mul_comm] using hmv'

lemma tolerance_add (m n : ℕ) : (tolerance (m+n) : ℝ) = (tolerance m : ℝ)*(tolerance n : ℝ) := by
  simp [tolerance, pow_add]

lemma nat_mul_tolerance (n : ℕ) : (n:ℝ)*(tolerance n:ℝ) ≤ 1 := by
  have hn : (n:ℝ) ≤ 2^n := by exact_mod_cast n.lt_two_pow_self.le
  calc
    _ ≤ (2:ℝ)^n * (tolerance n:ℝ) := mul_le_mul_of_nonneg_right hn (tolerance_pos n).le
    _ = 1 := by simp [tolerance]

lemma difference_precision (C k : ℕ) : (C:ℝ)*(tolerance (k+1+C):ℝ) ≤ tolerance (k+1) := by
  rw [tolerance_add, mul_left_comm]
  exact mul_le_of_le_one_right (tolerance_pos _).le (nat_mul_tolerance C)

end AlternatingNS.Effective

end JetNamesDevelopment

end OAI
