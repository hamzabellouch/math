import Mathlib
import OAI.Computability.MinUncut.Model

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Box
variable {A : Type*} [Fintype A] [Nonempty A]

def vertex {m : ℕ} (b : Fin m → Bool) (x y : Fin m → A) : Fin m → A :=
  fun i => if b i then x i else y i

def moment {m : ℕ} (f : (Fin m → A) → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, ∏ b : Fin m → Bool, f (vertex b x y)

def correlation {m : ℕ} (f : (Fin m → A) → ℝ)
    (a : Fin m → (Fin m → A) → ℝ) : ℝ :=
  𝔼 x, f x * ∏ i, a i x

def Local {m : ℕ} (a : Fin m → (Fin m → A) → ℝ) : Prop :=
  ∀ i x z, a i (Function.update x i z) = a i x

omit [Nonempty A] in
lemma expect_cons {m : ℕ} (f : (Fin (m+1) → A) → ℝ) :
    (𝔼 x, f x) = 𝔼 z, 𝔼 x, f (Fin.cons z x) := by
  rw [← Finset.expect_product', Finset.univ_product_univ]
  exact Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (m+1) => A)).symm _ _ (fun x => congrArg f (Fin.cons_self_tail x).symm)

lemma prod_cons {m : ℕ} (f : (Fin (m+1) → Bool) → ℝ) :
    (∏ b, f b) = ∏ z : Bool, ∏ b, f (Fin.cons z b) := by
  rw [← Finset.prod_product' ]
  rw [Finset.univ_product_univ]
  exact Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).symm _ _ (fun x => congrArg f (Fin.cons_self_tail x).symm)

omit [Fintype A] [Nonempty A] in
@[simp] lemma vertex_cons {m : ℕ} (b : Bool) (bs : Fin m → Bool)
    (x y : A) (xs ys : Fin m → A) :
    vertex (Fin.cons b bs) (Fin.cons x xs) (Fin.cons y ys) =
      Fin.cons (if b then x else y) (vertex bs xs ys) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [vertex]

omit [Nonempty A] in
lemma moment_succ {m : ℕ} (f : (Fin (m+1) → A) → ℝ) :
    moment f = 𝔼 z, 𝔼 w, moment (fun x => f (Fin.cons z x) * f (Fin.cons w x)) := by
  unfold moment
  rw [expect_cons]
  conv_lhs => arg 2; ext z; arg 2; ext x; rw [expect_cons]
  simp_rw [prod_cons, Fintype.prod_bool, vertex_cons]
  simp only [Bool.false_eq_true, ↓reduceIte, Finset.prod_mul_distrib]
  apply Finset.expect_congr rfl
  intro z _
  rw [Finset.expect_comm]

lemma expect_pow_two_pow {T : Type*} [Fintype T] [Nonempty T] (f : T → ℝ) (m : ℕ) :
    (𝔼 t, f t)^(2^m) ≤ 𝔼 t, (f t)^(2^m) := by
  cases m with
  | zero => simp
  | succ m =>
      have he : Even (2^(m+1)) := ⟨2^m, by rw [pow_succ]; omega⟩
      have h := Real.pow_arith_mean_le_arith_mean_pow_of_even Finset.univ
        (fun _ : T => (Fintype.card T : ℝ)⁻¹) f (fun _ _ => by positivity)
        (by simp [Fintype.card_ne_zero]) he
      simpa only [Finset.expect_eq_sum_div_card, Finset.card_univ, ← Finset.mul_sum,
        ← Finset.sum_mul, div_eq_mul_inv, mul_comm] using h

lemma expect_sq_le {T : Type*} [Fintype T] [Nonempty T] (f : T → ℝ) :
    (𝔼 t, f t)^2 ≤ 𝔼 t, (f t)^2 := by
  simpa using expect_pow_two_pow f 1

omit [Fintype A] [Nonempty A] in
lemma face_zero {m : ℕ} (a : Fin (m+1) → (Fin (m+1) → A) → ℝ)
    (ha : Local a) (z w : A) (x : Fin m → A) :
    a 0 (Fin.cons z x) = a 0 (Fin.cons w x) := by
  simpa only [Fin.update_cons_zero] using ha 0 (Fin.cons w x) z

lemma first_step {m : ℕ} (f : (Fin (m+1) → A) → ℝ)
    (a : Fin (m+1) → (Fin (m+1) → A) → ℝ)
    (ha : Local a) (hb : ∀ i x, |a i x| ≤ 1) :
    (correlation f a)^2 ≤ 𝔼 z, 𝔼 w,
      correlation (fun x => f (Fin.cons z x)*f (Fin.cons w x))
        (fun i x => a i.succ (Fin.cons z x)*a i.succ (Fin.cons w x)) := by
  let z₀ := Classical.choice (inferInstance : Nonempty A)
  let g (x : Fin m → A) : ℝ := 𝔼 z, f (Fin.cons z x) * ∏ i : Fin m, a i.succ (Fin.cons z x)
  have hc : correlation f a = 𝔼 x, a 0 (Fin.cons z₀ x) * g x := by
    unfold correlation
    rw [expect_cons, Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro x _
    simp only [Fin.prod_univ_succ]
    simp_rw [face_zero a ha _ z₀ x]
    dsimp [g]
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro z _
    ring
  rw [hc]
  calc
    _ ≤ 𝔼 x, (a 0 (Fin.cons z₀ x)*g x)^2 := expect_sq_le _
    _ ≤ 𝔼 x, (g x)^2 := by
      apply Finset.expect_le_expect
      intro x _
      rw [mul_pow]
      have hs : (a 0 (Fin.cons z₀ x))^2 ≤ 1 := by
        nlinarith [sq_abs (a 0 (Fin.cons z₀ x)), hb 0 (Fin.cons z₀ x), abs_nonneg (a 0 (Fin.cons z₀ x))]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (g x))
    _ = _ := by
      dsimp [g, correlation]
      simp only [sq, Finset.expect_mul_expect]
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro z _
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro w _
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.prod_mul_distrib]
      ring

theorem box_cs (m : ℕ) (f : (Fin m → A) → ℝ)
    (a : Fin m → (Fin m → A) → ℝ) (ha : Local a) (hb : ∀ i x, |a i x|≤1) :
    (correlation f a)^(2^m) ≤ moment f := by
  induction m with
  | zero =>
      have hf : ∀ x : Fin 0 → A, f x = f (fun i => Fin.elim0 i) :=
        fun x => congrArg f (Subsingleton.elim _ _)
      simp [correlation, moment, hf]
  | succ m ih =>
      let g := fun z w (x : Fin m → A) => f (Fin.cons z x)*f (Fin.cons w x)
      let b := fun z w (i : Fin m) (x : Fin m → A) =>
        a i.succ (Fin.cons z x)*a i.succ (Fin.cons w x)
      have h₁ := first_step f a ha hb
      have hlocal (z w : A) : Local (b z w) := by
        intro i x t
        dsimp [b]
        simp only [Fin.cons_update, ha i.succ]
      have hbound (z w : A) (i : Fin m) (x : Fin m → A) : |b z w i x|≤1 := by
        dsimp [b]
        rw [abs_mul]
        simpa using mul_le_mul (hb i.succ (Fin.cons z x)) (hb i.succ (Fin.cons w x))
          (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
      calc
        _ = ((correlation f a)^2)^(2^m) := by rw [← pow_mul, pow_succ]; congr 1; omega
        _ ≤ (𝔼 z, 𝔼 w, correlation (g z w) (b z w))^(2^m) :=
          pow_le_pow_left₀ (sq_nonneg _) h₁ _
        _ ≤ 𝔼 z, (𝔼 w, correlation (g z w) (b z w))^(2^m) := expect_pow_two_pow _ m
        _ ≤ 𝔼 z, 𝔼 w, (correlation (g z w) (b z w))^(2^m) :=
          Finset.expect_le_expect (fun z _ => expect_pow_two_pow _ m)
        _ ≤ 𝔼 z, 𝔼 w, moment (g z w) := by
          apply Finset.expect_le_expect
          intro z _
          apply Finset.expect_le_expect
          intro w _
          exact ih _ _ (hlocal z w) (hbound z w)
        _ = _ := (moment_succ f).symm

lemma abs_correlation_cs {m : ℕ} (hm : 0 < m) (f : (Fin m → A) → ℝ)
    (a : Fin m → (Fin m → A) → ℝ) (ha : Local a) (hb : ∀ i x, |a i x|≤1) :
    |correlation f a|^(2^m) ≤ moment f := by
  have he : Even (2^m) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    exact ⟨2^k, by rw [pow_succ]; omega⟩
  simpa only [he.pow_abs] using box_cs m f a ha hb
end MinUncut.Box

end

end OAI
