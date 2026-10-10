import OAI.Dynamics.ConditionalShuffle.ResetReverse

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter Topology
namespace Thorp.Conditional.Reset

abbrev Injection (D b : ℕ) := Fin b ↪ Position D

def act {α ι : Type*} (g : Equiv.Perm α) (x : ι ↪ α) : ι ↪ α := x.trans g.toEmbedding

@[simp] lemma act_apply {α ι : Type*} (g : Equiv.Perm α) (x : ι ↪ α) (i : ι) :
    act g x i = g (x i) := rfl

@[simp] lemma act_mul {α ι : Type*} (g h : Equiv.Perm α) (x : ι ↪ α) :
    act (g*h) x = act g (act h x) := rfl

@[simp] lemma act_one {α ι : Type*} (x : ι ↪ α) : act (1 : Equiv.Perm α) x = x := rfl

lemma act_eq_iff {α ι : Type*} (g : Equiv.Perm α) (x y : ι ↪ α) :
    act g x = y ↔ x = act g⁻¹ y := by
  constructor
  · intro h; rw [← h, ← act_mul, inv_mul_cancel, act_one]
  · intro h; rw [h, ← act_mul, mul_inv_cancel, act_one]

def actEquiv {α ι : Type*} (g : Equiv.Perm α) : (ι ↪ α) ≃ (ι ↪ α) where
  toFun := act g
  invFun := act g⁻¹
  left_inv x := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv x := by rw [← act_mul, mul_inv_cancel, act_one]

lemma uniform_injection {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]
    (e : ι ↪ α) : fairMass (fun g : Equiv.Perm α => act g e) =
      fun _ => (Fintype.card (ι ↪ α) : ℝ)⁻¹ := by
  funext y
  rw [fairMass_eq_mean, show (fun g : Equiv.Perm α => if act g e = y then (1:ℝ) else 0) =
      (fun g => (fun z : ι ↪ α => if z = y then (1:ℝ) else 0) (e.trans g.toEmbedding)) from rfl,
    mean_perm_embedding e (fun z : ι ↪ α => if z = y then (1:ℝ) else 0)]
  simp [mean]

def kernel (D b t : ℕ) (x y : Injection D b) : ℝ :=
  fairMass (fun ω : History D t => act (run D t ω) x) y

lemma kernel_nonneg (D b t : ℕ) (x y : Injection D b) : 0 ≤ kernel D b t x y :=
  fairMass_nonneg _ _

lemma kernel_row_sum (D b t : ℕ) (x : Injection D b) : ∑ y, kernel D b t x y = 1 :=
  fairMass_sum _

lemma kernel_column_sum (D b t : ℕ) (y : Injection D b) : ∑ x, kernel D b t x y = 1 := by
  unfold kernel
  simp only [fairMass_eq_mean]
  rw [← mean_sum]
  have he (ω : History D t) : (∑ x : Injection D b, if act (run D t ω) x = y then (1:ℝ) else 0) = 1 := by
    simp_rw [act_eq_iff]; simp
  simp only [he, mean_const]

def toInjection {α ι : Type*} (e : ι ↪ α) (f : ι → α) : ι ↪ α :=
  if h : Function.Injective f then ⟨f,h⟩ else e

@[simp] lemma toInjection_coe {α ι : Type*} (e x : ι ↪ α) : toInjection e x = x := by
  simp only [toInjection, dite_eq_left x.injective]; rfl

lemma injection_tv_le {α ι Ω Ω' : Type*} [Fintype α] [Fintype ι] [Fintype Ω] [Fintype Ω'] [DecidableEq ι]
    (e : ι ↪ α) (a : Ω → ι ↪ α) (b : Ω' → ι ↪ α) :
    tv (fairMass a) (fairMass b) ≤
      tv (fairMass (fun ω => (a ω : ι → α))) (fairMass (fun ω => (b ω : ι → α))) := by
  have hh := Trim.tv_push_le (fairMass (fun ω => (a ω : ι → α)))
    (fairMass (fun ω => (b ω : ι → α))) (toInjection e)
  rw [Trim.push_fairMass, Trim.push_fairMass] at hh
  simpa only [Function.comp_def, toInjection_coe] using hh

lemma kernel_row_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∀ᶠ d : ℕ in atTop, ∀ (b : ℕ), (b : ℝ) ≤ (1-ρ)*(2^(d+2) : ℝ) →
      ∀ x : Injection (d+2) b,
      tv (kernel (d+2) b (2*resetS ρ*(d+2)) x)
        (fun _ => (Fintype.card (Injection (d+2) b) : ℝ)⁻¹) ≤ (1/2 : ℝ)^(8*(d+2)) := by
  filter_upwards [reset_partial_mixing ρ hρ hρ₁] with d hd
  intro b hb x
  rw [← uniform_injection x]
  exact (injection_tv_le x (fun ω : History (d+2) (2*resetS ρ*(d+2)) =>
      act (run (d+2) (2*resetS ρ*(d+2)) ω) x) (fun g : State (d+2) => act g x)).trans
    (hd b x x.injective hb)

lemma reflection_column (d b t : ℕ) (x y : Injection (d+1) b) :
    kernel (d+1) b t x y =
      kernel (d+1) b t (act (reversePosition (d+1)) y) (act (reversePosition (d+1)) x) := by
  unfold kernel
  rw [fairMass_eq_mean, fairMass_eq_mean]
  rw [← mean_equiv (reverseHistory d t)]
  apply mean_congr; intro ω
  dsimp only [Function.comp_def]
  rw [reverse_run]
  have hr : reversePosition (d+1) * reversePosition (d+1) = 1 := by
    apply Equiv.ext; exact reversePosition_involutive (d+1)
  have iff : act (reversePosition (d+1) * (run (d+1) t ω)⁻¹ * reversePosition (d+1)) x = y ↔
      act (run (d+1) t ω) (act (reversePosition (d+1)) y) = act (reversePosition (d+1)) x := by
    rw [act_eq_iff, mul_inv_rev, mul_inv_rev]
    have hi : (reversePosition (d+1))⁻¹ = reversePosition (d+1) := by
      apply inv_eq_of_mul_eq_one_left; exact hr
    rw [hi, act_mul, act_mul, inv_inv]
    have hre (z : Injection (d+1) b) : act (reversePosition (d+1)) (act (reversePosition (d+1)) z) = z := by
      rw [← act_mul, hr, act_one]
    constructor
    · intro h; rw [h, hre]
    · intro h; rw [h, hre]
  simp only [iff]

lemma kernel_column_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∀ᶠ d : ℕ in atTop, ∀ (b : ℕ), (b : ℝ) ≤ (1-ρ)*(2^(d+2) : ℝ) →
      ∀ y : Injection (d+2) b,
      tv (fun x => kernel (d+2) b (2*resetS ρ*(d+2)) x y)
        (fun _ => (Fintype.card (Injection (d+2) b) : ℝ)⁻¹) ≤ (1/2 : ℝ)^(8*(d+2)) := by
  filter_upwards [kernel_row_bound ρ hρ hρ₁] with d hd
  intro b hb y
  have hh := hd b hb (act (reversePosition (d+2)) y)
  have hsum :
      (∑ x, |kernel (d+2) b (2*resetS ρ*(d+2)) x y - (Fintype.card (Injection (d+2) b) : ℝ)⁻¹|) =
      ∑ x, |kernel (d+2) b (2*resetS ρ*(d+2)) (act (reversePosition (d+2)) y) x -
        (Fintype.card (Injection (d+2) b) : ℝ)⁻¹| := by
    calc
      _ = ∑ x, |kernel (d+2) b (2*resetS ρ*(d+2)) (act (reversePosition (d+2)) y)
          (act (reversePosition (d+2)) x) - (Fintype.card (Injection (d+2) b) : ℝ)⁻¹| := by
        apply Finset.sum_congr rfl; intro x _
        rw [reflection_column (d+1) b (2*resetS ρ*(d+2)) x y]
      _ = _ := (actEquiv (ι := Fin b) (reversePosition (d+2))).sum_comp
        (fun x => |kernel (d+2) b (2*resetS ρ*(d+2)) (act (reversePosition (d+2)) y) x -
          (Fintype.card (Injection (d+2) b) : ℝ)⁻¹|)
  unfold tv at *; rwa [hsum]

end Thorp.Conditional.Reset

end

end OAI
