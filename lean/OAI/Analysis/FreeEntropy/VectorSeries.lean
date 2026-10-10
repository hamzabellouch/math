import OAI.Analysis.FreeEntropy.SeriesNorm

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev VSeries (α E : Type) := List α → E
abbrev VDegreeSpace (α E : Type) [Fintype α] [NormedAddCommGroup E] (n : ℕ) :=
  PiLp 2 (fun _ : List.Vector α n => E)
def vdegreeVector (f : VSeries α E) (n : ℕ) : VDegreeSpace α E n :=
  WithLp.toLp 2 (fun w => f w.val)
def vdegreeNorm (f : VSeries α E) (n : ℕ) : ℝ := ‖vdegreeVector f n‖
@[simp] theorem vdegreeVector_apply {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : VSeries α E) (n : ℕ) (w : List.Vector α n) :
    vdegreeVector f n w = f w.val := rfl
@[simp] theorem vdegreeNorm_nonneg {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : VSeries α E) (n : ℕ) : 0 ≤ vdegreeNorm f n := norm_nonneg _
 theorem vdegreeNorm_sq {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : VSeries α E) (n : ℕ) :
    vdegreeNorm f n ^ 2 = ∑ w : List.Vector α n, ‖f w.val‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _
 theorem vdegreeNorm_scalar (f : Series α) (n : ℕ) : vdegreeNorm f n = degreeNorm f n := rfl
 theorem vdegreeNorm_congr {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : VSeries α E} (n : ℕ)
    (h : ∀ w, w.length = n → f w = g w) : vdegreeNorm f n = vdegreeNorm g n := by
  apply congrArg norm
  ext w : 1
  exact h w.val w.prop
 theorem vdegreeNorm_zero_degree (f : VSeries α E) : vdegreeNorm f 0 = ‖f []‖ := by
  apply (sq_eq_sq₀ (vdegreeNorm_nonneg _ _) (norm_nonneg _)).mp
  rw [vdegreeNorm_sq]
  simp only [show ∀ w : List.Vector α 0, w.val = [] from fun w => List.length_eq_zero_iff.mp w.prop]
  simp
 theorem vdegreeNorm_add_le {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f g : VSeries α E) (n : ℕ) :
    vdegreeNorm (f+g) n ≤ vdegreeNorm f n + vdegreeNorm g n := by
  change ‖vdegreeVector f n + vdegreeVector g n‖ ≤ _
  exact norm_add_le _ _
@[simp] theorem vdegreeNorm_zero {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (n : ℕ) : vdegreeNorm (0 : VSeries α E) n = 0 := norm_zero
 theorem vdegreeNorm_sum_le {ι : Type u1} (s : Finset ι) (f : ι → VSeries α E) (n : ℕ) :
    vdegreeNorm (∑ i ∈ s, f i) n ≤ ∑ i ∈ s, vdegreeNorm (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (vdegreeNorm_add_le _ _ _).trans (add_le_add_right ih _)
 theorem vdegreeNorm_tensor (f : Series α) (g : VSeries α E) (m n : ℕ) :
    vdegreeNorm (fun w => f (w.take m) • g (w.drop m)) (m+n) =
      degreeNorm f m * vdegreeNorm g n := by
  apply (sq_eq_sq₀ (vdegreeNorm_nonneg _ _) (mul_nonneg (degreeNorm_nonneg _ _) (vdegreeNorm_nonneg _ _))).mp
  rw [mul_pow, vdegreeNorm_sq, degreeNorm_sq, vdegreeNorm_sq]
  have h := (vectorSplit (α := α) m n).sum_comp
    (fun v : List.Vector α m × List.Vector α n => ‖f v.1.val‖ ^ 2 * ‖g v.2.val‖ ^ 2)
  calc
    _ = ∑ v : List.Vector α (m+n), ‖f (v.val.take m)‖^2 * ‖g (v.val.drop m)‖^2 := by
      simp only [norm_smul, mul_pow]
    _ = ∑ v : List.Vector α m × List.Vector α n, ‖f v.1.val‖^2 * ‖g v.2.val‖^2 := h
    _ = _ := by rw [Fintype.sum_prod_type, sum_mul_sum]

def vconv (M : Series α) (f : VSeries α E) : VSeries α E := fun w =>
  ∑ k ∈ range (w.length+1), M (w.take k) • f (w.drop k)
 theorem vdegreeNorm_conv_le (M : Series α) (f : VSeries α E) (n : ℕ) :
    vdegreeNorm (vconv M f) n ≤ ∑ k ∈ range (n+1), degreeNorm M k * vdegreeNorm f (n-k) := by
  have h : vdegreeNorm (vconv M f) n =
      vdegreeNorm (∑ k ∈ range (n+1), fun w => M (w.take k) • f (w.drop k)) n := by
    apply vdegreeNorm_congr
    intro w hw
    simp only [vconv, hw, Finset.sum_apply]
  rw [h]
  apply (vdegreeNorm_sum_le _ _ _).trans
  apply sum_le_sum
  intro k hk
  have hn : k + (n-k) = n := Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hk))
  simpa only [hn] using le_of_eq (vdegreeNorm_tensor M f k (n-k))

 def vsubst (M : Series α) (f : VSeries α E) : VSeries α E
  | [] => f []
  | a::w => ∑ k ∈ range (w.length+1), M (w.take k) • vsubst M (fun v => f (a::v)) (w.drop k)
termination_by w => w.length
@[simp] theorem vsubst_nil {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Series α) (f : VSeries α E) : vsubst M f [] = f [] := by rw [vsubst]
 theorem vsubst_cons {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Series α) (f : VSeries α E) (a : α) (w : List α) :
    vsubst M f (a::w) = vconv M (vsubst M (fun v => f (a::v))) w := by rw [vsubst, vconv]
 theorem vsubst_scalar (M f : Series α) : vsubst M f = subst M f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      rw [vsubst, subst]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      rfl

 def bundleDeriv (f : VSeries α E) : VSeries α (PiLp 2 (fun _ : α => E)) := fun w =>
  WithLp.toLp 2 (fun a => f (a::w))
@[simp] theorem bundleDeriv_apply {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : VSeries α E) (w : List α) (a : α) :
    bundleDeriv f w a = f (a::w) := rfl

def vectorCons (n : ℕ) : α × List.Vector α n ≃ List.Vector α (n+1) where
  toFun v := v.1 ::ᵥ v.2
  invFun w := (w.head,w.tail)
  left_inv v := by simp
  right_inv w := w.cons_head_tail

 theorem vdegreeNorm_bundleDeriv (f : VSeries α E) (n : ℕ) :
    vdegreeNorm (bundleDeriv f) n = vdegreeNorm f (n+1) := by
  apply (sq_eq_sq₀ (vdegreeNorm_nonneg _ _) (vdegreeNorm_nonneg _ _)).mp
  rw [vdegreeNorm_sq, vdegreeNorm_sq]
  simp only [PiLp.norm_sq_eq_of_L2, bundleDeriv_apply]
  rw [sum_comm]
  calc
    _ = ∑ v : α × List.Vector α n, ‖f (v.1 :: v.2.val)‖ ^ 2 :=
      (Fintype.sum_prod_type (fun v : α × List.Vector α n => ‖f (v.1 :: v.2.val)‖ ^ 2)).symm
    _ = _ := (vectorCons n).sum_comp (fun w : List.Vector α (n+1) => ‖f w.val‖^2)

 theorem vsubst_apply (M : Series α) (f : VSeries α (PiLp 2 (fun _ : α => E)))
    (w : List α) (a : α) :
    vsubst M f w a = vsubst M (fun v => f v a) w := by
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [vsubst, vsubst]
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
      apply sum_congr rfl
      intro k hk
      congr 1
      exact ih _ (by simp) _

 theorem vsubst_bundleDeriv (M : Series α) (f : VSeries α E) (w : List α) (a : α) :
    vsubst M (bundleDeriv f) w a = vsubst M (fun v => f (a::v)) w :=
  vsubst_apply M (bundleDeriv f) w a

 theorem vdegreeNorm_subst_succ (M : Series α) (f : VSeries α E) (n : ℕ) :
    vdegreeNorm (vsubst M f) (n+1) =
      vdegreeNorm (vconv M (vsubst M (bundleDeriv f))) n := by
  rw [← vdegreeNorm_bundleDeriv]
  apply vdegreeNorm_congr
  intro w hw
  ext a : 1
  simp only [bundleDeriv_apply, vsubst_cons, vconv, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    vsubst_bundleDeriv]

def substBound (b a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | n+1 => ∑ k ∈ range (n+1), b k * substBound b (fun j => a (j+1)) (n-k)
termination_by n => n

 theorem substBound_nonneg {b a : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (ha : ∀ k, 0 ≤ a k) (n : ℕ) :
    0 ≤ substBound b a n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases n with
    | zero => simpa only [substBound] using ha 0
    | succ n =>
      rw [substBound]
      exact sum_nonneg fun k hk => mul_nonneg (hb k) (ih (n-k) (by omega) (fun j => ha (j+1)))

 theorem vsubst_norm_le (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
      (M : Series α) (f : VSeries α E),
      vdegreeNorm (vsubst M f) n ≤ substBound (degreeNorm M) (vdegreeNorm f) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ M f
    cases n with
    | zero => simp [vdegreeNorm_zero_degree, substBound]
    | succ n =>
      rw [vdegreeNorm_subst_succ, substBound]
      apply (vdegreeNorm_conv_le _ _ _).trans
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (degreeNorm_nonneg _ _)
      have h := ih (n-k) (by omega) M (bundleDeriv f)
      have he : vdegreeNorm (bundleDeriv f) = fun j => vdegreeNorm f (j+1) :=
        funext (vdegreeNorm_bundleDeriv f)
      rw [he] at h
      exact h

end FiniteEntropySeparation.FreeSeries

end

end OAI
