import OAI.Dynamics.ConditionalShuffle.Disintegration

namespace OAI

noncomputable section
namespace Revealed.Instrument
open scoped Classical
open Thorp Thorp.Conditional Thorp.Fourier Revealed.Disintegration

lemma fairMass_bind {Ω Ω' X Y : Type*} [Fintype Ω] [Fintype Ω'] [Fintype X]
    (f : Ω → X) (k : X → Ω' → Y) (y : Y) :
    fairMass (fun z : Ω × Ω' => k (f z.1) z.2) y =
      ∑ x, fairMass f x * fairMass (k x) y := by
  rw [fairMass_test]
  rw [fairMass_eq_mean, mean_prod]
  rfl

lemma fairMass_snoc {Ω X : Type*} [Fintype Ω] {n : ℕ} (f : (Fin (n + 1) → Ω) → X) (x : X) :
    fairMass f x = fairMass (fun z : (Fin n → Ω) × Ω => f (Fin.snoc z.1 z.2)) x := by
  rw [fairMass_eq_mean, fairMass_eq_mean]
  exact (mean_equiv ((Equiv.prodComm (Fin n → Ω) Ω).trans (Fin.snocEquiv (fun _ : Fin (n + 1) => Ω))) _).symm

structure Data (E S G Ω : Type) where
  obs : E → Ω → S
  inc : E → Ω → G
  next : E → S → E

variable {E S G Ω : Type} [fintype_S : Fintype S] [fintype_G : Fintype G] [group_G : Group G] [Fintype Ω] [nonempty_Ω : Nonempty Ω]
variable (I : Data E S G Ω)

def joint (e : E) : S × G → ℝ := fairMass (fun ω => (I.obs e ω, I.inc e ω))
def probability (e : E) : S → ℝ := marginal (joint I e)
def kernel (e : E) : S → G → ℝ := conditional (joint I e)

lemma joint_nonneg (e : E) (x) : 0 ≤ joint I e x := by
  let retained_fintype_S := fintype_S
  let retained_fintype_G := fintype_G
  let retained_group_G := group_G
  let retained_nonempty_Ω := nonempty_Ω
  exact fairMass_nonneg _ _
lemma probability_nonneg (e : E) (s) : 0 ≤ probability I e s := marginal_nonneg _ (joint_nonneg I e) s
lemma probability_sum (e : E) : ∑ s, probability I e s = 1 := by
  rw [probability, marginal_sum]
  exact fairMass_sum _
lemma kernel_nonneg (e : E) (s g) : 0 ≤ kernel I e s g := conditional_nonneg _ (joint_nonneg I e) s g
lemma kernel_sum (e : E) (s) : ∑ g, kernel I e s g = 1 := by
  let retained_nonempty_Ω := nonempty_Ω
  exact conditional_sum _ s
lemma probability_mul_kernel (e : E) (s g) : probability I e s * kernel I e s g = joint I e (s,g) :=
  marginal_mul_conditional _ (joint_nonneg I e) s g

def base (e : E) : (n : ℕ) → (Fin n → S) → E
  | 0, _ => e
  | n + 1, p => I.next (base e n (Fin.init p)) (p (Fin.last n))

def weights (e : E) : (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => 1
  | n + 1, p => weights e n (Fin.init p) * probability I (base I e n (Fin.init p)) (p (Fin.last n))

def kernels (e : E) : (n : ℕ) → (Fin n → S) → (Fin n → G → ℝ)
  | 0, _ => Fin.elim0
  | n + 1, p => Fin.snoc (kernels e n (Fin.init p))
      (kernel I (base I e n (Fin.init p)) (p (Fin.last n)))

def observed (e : E) : (n : ℕ) → (Fin n → Ω) → (Fin n → S)
  | 0, _ => Fin.elim0
  | n + 1, ω => let p := observed e n (Fin.init ω)
      Fin.snoc p (I.obs (base I e n p) (ω (Fin.last n)))

def groupRun (e : E) : (n : ℕ) → (Fin n → Ω) → G
  | 0, _ => 1
  | n + 1, ω => I.inc (base I e n (observed I e n (Fin.init ω))) (ω (Fin.last n)) *
      groupRun e n (Fin.init ω)

def pathJoint (e : E) (n : ℕ) : (Fin n → S) × G → ℝ :=
  fairMass (fun ω : Fin n → Ω => (observed I e n ω, groupRun I e n ω))

lemma kernels_nonneg (e : E) (n : ℕ) (p : Fin n → S) : ∀ i g, 0 ≤ kernels I e n p i g := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i g
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [kernels, Fin.snoc_last] using kernel_nonneg I _ _ g
      · simpa only [kernels, Fin.snoc_castSucc] using ih (Fin.init p) j g

lemma kernels_sum (e : E) (n : ℕ) (p : Fin n → S) : ∀ i, ∑ g, kernels I e n p i g = 1 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [kernels, Fin.snoc_last] using kernel_sum I _ _
      · simpa only [kernels, Fin.snoc_castSucc] using ih (Fin.init p) j

lemma weights_nonneg (e : E) (n : ℕ) (p : Fin n → S) : 0 ≤ weights I e n p := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (ih _) (probability_nonneg I _ _)

lemma sum_snoc {M : Type*} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → S) → M) :
    (∑ p, f p) = ∑ p : Fin n → S, ∑ s : S, f (Fin.snoc p s) := by
  have h := (Equiv.sum_comp ((Equiv.prodComm (Fin n → S) S).trans
    (Fin.snocEquiv (fun _ : Fin (n + 1) => S))) f).symm
  change (∑ p, f p) = ∑ z : (Fin n → S) × S, f (Fin.snoc z.1 z.2) at h
  rw [Fintype.sum_prod_type] at h
  exact h

lemma weights_sum (e : E) (n : ℕ) : ∑ p, weights I e n p = 1 := by
  induction n with
  | zero => simp [weights]
  | succ n ih =>
      rw [sum_snoc]
      simp only [weights, Fin.init_snoc, Fin.snoc_last, ← Finset.mul_sum, probability_sum, mul_one]
      exact ih

lemma snoc_eq_iff {A : Type*} {n : ℕ} (p q : Fin n → A) (s t : A) :
    (Fin.snoc p s : Fin (n + 1) → A) = Fin.snoc q t ↔ p = q ∧ s = t := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg Fin.init h, by simpa using congrFun h (Fin.last n)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma realConv_right (μ ν : G → ℝ) (z : G) : realConv μ ν z = ∑ h, μ (z * h⁻¹) * ν h := by
  have h := Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft z))
    (fun a => μ a * ν (a⁻¹ * z))
  change (∑ a, μ (z * a⁻¹) * ν ((z * a⁻¹)⁻¹ * z)) = ∑ a, μ a * ν (a⁻¹ * z) at h
  simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one, realConv] using h.symm

lemma transition_mass (e : E) (n : ℕ) (p q : Fin n → S) (h z : G) (s : S) :
    fairMass (fun c : Ω => (Fin.snoc p (I.obs (base I e n p) c), I.inc (base I e n p) c * h))
      ((Fin.snoc q s : Fin (n + 1) → S), z) =
    if p = q then joint I (base I e n q) (s, z * h⁻¹) else 0 := by
  let retained_fintype_S := fintype_S
  let retained_fintype_G := fintype_G
  let retained_nonempty_Ω := nonempty_Ω
  by_cases hp : p = q
  · subst p
    simp [joint, fairMass, Prod.mk.injEq, eq_mul_inv_iff_mul_eq]
  · simp only [fairMass, Prod.mk.injEq, snoc_eq_iff, hp, false_and,
      ite_false, Finset.sum_const_zero, zero_div]

lemma pathJoint_succ (e : E) (n : ℕ) (p : Fin n → S) (s : S) (g : G) :
    pathJoint I e (n + 1) (Fin.snoc p s, g) =
      realConv (fun h => joint I (base I e n p) (s,h)) (fun h => pathJoint I e n (p,h)) g := by
  rw [pathJoint, fairMass_snoc]
  simp only [observed, groupRun, Fin.init_snoc, Fin.snoc_last]
  have h := fairMass_bind
    (fun ω : Fin n → Ω => (observed I e n ω, groupRun I e n ω))
    (fun x c => (Fin.snoc x.1 (I.obs (base I e n x.1) c), I.inc (base I e n x.1) c * x.2))
    ((Fin.snoc p s : Fin (n + 1) → S), g)
  rw [h, Fintype.sum_prod_type]
  simp only [transition_mass, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [realConv_right]
  apply Finset.sum_congr rfl
  intro h _
  rw [mul_comm]
  rfl

theorem pathJoint_factor (e : E) (n : ℕ) (p : Fin n → S) (g : G) :
    pathJoint I e n (p,g) = weights I e n p * realProduct n (kernels I e n p) g := by
  induction n generalizing g with
  | zero =>
      have hp : p = Fin.elim0 := Subsingleton.elim _ _
      subst p
      simp [pathJoint, observed, groupRun, weights, realProduct, fairMass, eq_comm]
  | succ n ih =>
      have hp : p = Fin.snoc (Fin.init p) (p (Fin.last n)) := (Fin.snoc_init_self p).symm
      conv_lhs => rw [hp]
      rw [pathJoint_succ, realConv_right]
      simp only [weights, kernels, realProduct, Fin.snoc_last, Fin.init_snoc, realConv_right]
      simp_rw [ih]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [← probability_mul_kernel]
      ring

end Revealed.Instrument

end

end OAI
