import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Information.GameDecoder
import OAI.Computability.BinPacking.PCP.CloudRounding

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := Finset.univ.expect f

def energy {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := mean (fun x => (f x) ^ 2)

def correlation {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  mean (fun x => f x * g x)

def averagingOperator {V D : Type*} [Fintype D] (G : PortGraph V D)
    (f : V → ℝ) (v : V) : ℝ := Finset.univ.expect (fun d => f (G.rot (v, d)).1)

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def edgeProfile {V D : Type*} [Fintype D] (bad : V × D → Bool) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then 1 else 0)

def edgeDensity {V D : Type*} [Fintype V] [Fintype D] (bad : V × D → Bool) : ℝ :=
  mean (edgeProfile bad)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

structure SpectralCertificate {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (lambda : ℝ) : Prop where
  nonnegative : 0 ≤ lambda
  lt_one : lambda < 1
  contraction : ∀ f : V → ℝ, mean f = 0 →
    energy (averagingOperator G f) ≤ lambda ^ 2 * energy f

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_eq_sum_div_card (f : A → ℝ) :
    mean f = (∑ x, f x) / (Fintype.card A : ℝ) :=
  Fintype.expect_eq_sum_div_card f

theorem mean_equiv (e : A ≃ B) (f : B → ℝ) :
    mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem mean_prod (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simpa only [mean, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

@[simp] theorem mean_const [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c :=
  Fintype.expect_const c

theorem mean_add (f g : A → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ f g

theorem mean_sub (f g : A → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ f g

theorem mean_mul_left (c : ℝ) (f : A → ℝ) :
    mean (fun x => c * f x) = c * mean f :=
  (Finset.mul_expect _ f c).symm

theorem mean_mul_right (f : A → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c :=
  (Finset.expect_mul _ f c).symm

theorem mean_nonnegative (f : A → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

theorem mean_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem energy_nonnegative (f : A → ℝ) : 0 ≤ energy f :=
  mean_nonnegative _ (fun x => sq_nonneg (f x))

theorem correlation_sq_le (f g : A → ℝ) :
    correlation f g ^ 2 ≤ energy f * energy g :=
  Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

theorem energy_sub_const [Nonempty A] (f : A → ℝ) (c : ℝ) :
    energy (fun x => f x - c) = energy f - 2 * c * mean f + c ^ 2 := by
  have h : (fun x => (f x - c) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * c) * f x + c ^ 2) := by
    funext x
    ring
  unfold energy
  rw [h, mean_add, mean_sub, mean_mul_left, mean_const]

theorem correlation_sub_const [Nonempty A] (f g : A → ℝ) (c d : ℝ) :
    correlation (fun x => f x - c) (fun x => g x - d) =
      correlation f g - d * mean f - c * mean g + c * d := by
  have h : (fun x => (f x - c) * (g x - d)) =
      (fun x => f x * g x - d * f x - c * g x + c * d) := by
    funext x
    ring
  unfold correlation
  rw [h, mean_add, mean_sub, mean_sub, mean_mul_left, mean_mul_left, mean_const]

end Averages

section Graph

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Nonempty V] in
theorem mean_operator (f : V → ℝ) : mean (averagingOperator G f) = mean f := by
  calc
    mean (averagingOperator G f) = mean (fun e : V × D => f (G.rot e).1) :=
      (mean_prod (fun e : V × D => f (G.rot e).1)).symm
    _ = mean (fun e : V × D => f e.1) := mean_equiv G.rot (fun e => f e.1)
    _ = mean (fun v : V => mean (fun _ : D => f v)) :=
      mean_prod (fun e : V × D => f e.1)
    _ = mean f := by simp only [mean_const]

omit [Fintype V] [Nonempty V] in
theorem operator_sub_const (f : V → ℝ) (c : ℝ) :
    averagingOperator G (fun v => f v - c) = fun v => averagingOperator G f v - c := by
  funext v
  change mean (fun d => f (G.rot (v, d)).1 - c) = _
  rw [mean_sub, mean_const]
  rfl

omit [Nonempty V] in
theorem mean_iterate (n : Nat) (f : V → ℝ) : mean (iterateOperator G n f) = mean f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, mean_operator, ih]

omit [Fintype V] [Nonempty V] in
theorem iterate_sub_const (n : Nat) (f : V → ℝ) (c : ℝ) :
    iterateOperator G n (fun v => f v - c) = fun v => iterateOperator G n f v - c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, ih, operator_sub_const]; rfl

omit [Nonempty V] [Nonempty D] in
theorem mean_markedStep (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (f : V → ℝ) :
    mean (markedStep G bad f) = correlation (edgeProfile bad) f := by
  calc
    mean (markedStep G bad f) =
        mean (fun e : V × D => if bad e then f (G.rot e).1 else 0) := by
      exact (mean_prod (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad (G.rot e)
          then f (G.rot (G.rot e)).1 else 0) :=
      (mean_equiv G.rot (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad e then f e.1 else 0) := by
      congr 1
      funext e
      rw [reversal e, G.rot_involutive e]
    _ = mean (fun v => mean (fun d => if bad (v, d) then f v else 0)) :=
      mean_prod (fun e : V × D => if bad e then f e.1 else 0)
    _ = correlation (edgeProfile bad) f := by
      unfold correlation
      congr 1
      funext v
      have h : (fun d => if bad (v, d) then f v else 0) =
          (fun d => (if bad (v, d) then (1 : ℝ) else 0) * f v) := by
        funext d
        cases bad (v, d) <;> simp
      rw [h, mean_mul_right]
      rfl

omit [Nonempty V] [Nonempty D] in
theorem returnMass_eq_correlation (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap = correlation (edgeProfile bad)
      (iterateOperator G gap (edgeProfile bad)) :=
  mean_markedStep G bad reversal _

omit [Nonempty V] in
theorem iterate_energy_bound (lambda : ℝ) (certificate : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) (n : Nat) :
    energy (iterateOperator G n f) ≤ (lambda ^ n) ^ 2 * energy f := by
  induction n with
  | zero => simp [iterateOperator]
  | succ n ih =>
      calc
        energy (iterateOperator G (n + 1) f) ≤
            lambda ^ 2 * energy (iterateOperator G n f) :=
          certificate.contraction _ ((mean_iterate G n f).trans hf)
        _ ≤ lambda ^ 2 * ((lambda ^ n) ^ 2 * energy f) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg lambda)
        _ = (lambda ^ (n + 1)) ^ 2 * energy f := by rw [pow_succ]; ring

omit [Nonempty V] in
theorem zero_mean_correlation_bound (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (f : V → ℝ)
    (hf : mean f = 0) (n : Nat) :
    correlation f (iterateOperator G n f) ≤ lambda ^ n * energy f := by
  have hsq : correlation f (iterateOperator G n f) ^ 2 ≤
      (lambda ^ n * energy f) ^ 2 := by
    calc
      _ ≤ energy f * energy (iterateOperator G n f) := correlation_sq_le _ _
      _ ≤ energy f * ((lambda ^ n) ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (iterate_energy_bound G lambda certificate f hf n)
          (energy_nonnegative f)
      _ = _ := by ring
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg certificate.nonnegative n) (energy_nonnegative f))

theorem correlation_centered (f : V → ℝ) (n : Nat) :
    correlation f (iterateOperator G n f) = mean f ^ 2 +
      correlation (fun v => f v - mean f)
        (iterateOperator G n (fun v => f v - mean f)) := by
  rw [iterate_sub_const, correlation_sub_const, mean_iterate]
  ring

end Graph

section Profiles

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_eq_edge_mean (bad : V × D → Bool) :
    edgeDensity bad = mean (fun e => if bad e then (1 : ℝ) else 0) :=
  (mean_prod (fun e : V × D => if bad e then (1 : ℝ) else 0)).symm

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_eq_card (bad : V × D → Bool) :
    edgeDensity bad =
      ((Finset.univ.filter (fun e => bad e = true)).card : ℝ) /
        (Fintype.card (V × D) : ℝ) := by
  rw [edgeDensity_eq_edge_mean, mean_eq_sum_div_card]
  simp only [Finset.sum_boole]

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeProfile_nonnegative (bad : V × D → Bool) (v : V) : 0 ≤ edgeProfile bad v :=
  mean_nonnegative _ (fun d => by cases bad (v, d) <;> norm_num)

omit [Fintype V] [Nonempty V] in
theorem edgeProfile_le_one (bad : V × D → Bool) (v : V) : edgeProfile bad v ≤ 1 := by
  change mean (fun d => if bad (v, d) then (1 : ℝ) else 0) ≤ 1
  calc
    _ ≤ mean (fun _ : D => (1 : ℝ)) := mean_mono (fun d => by
      cases bad (v, d) <;> norm_num)
    _ = 1 := mean_const _

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_nonnegative (bad : V × D → Bool) : 0 ≤ edgeDensity bad :=
  mean_nonnegative _ (edgeProfile_nonnegative bad)

theorem edgeDensity_le_one (bad : V × D → Bool) : edgeDensity bad ≤ 1 := by
  calc
    _ ≤ mean (fun _ : V => (1 : ℝ)) := mean_mono (edgeProfile_le_one bad)
    _ = 1 := mean_const _

omit [Nonempty V] in
theorem edgeProfile_energy_le_density (bad : V × D → Bool) :
    energy (edgeProfile bad) ≤ edgeDensity bad :=
  mean_mono (fun v => by
    have h0 := edgeProfile_nonnegative bad v
    have h1 := edgeProfile_le_one bad v
    nlinarith)

theorem edgeProfile_centered_energy (bad : V × D → Bool) :
    energy (fun v => edgeProfile bad v - edgeDensity bad) ≤
      edgeDensity bad * (1 - edgeDensity bad) := by
  rw [energy_sub_const]
  have h := edgeProfile_energy_le_density bad
  change energy (edgeProfile bad) - 2 * edgeDensity bad * edgeDensity bad +
    edgeDensity bad ^ 2 ≤ _
  nlinarith

theorem returnMass_le_sharp (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 +
      lambda ^ gap * (edgeDensity bad * (1 - edgeDensity bad)) := by
  rw [returnMass_eq_correlation G bad reversal, correlation_centered]
  have hzero : mean (fun v => edgeProfile bad v - edgeDensity bad) = 0 := by
    rw [mean_sub, mean_const]
    simp only [edgeDensity, sub_self]
  have hc := zero_mean_correlation_bound G lambda certificate
    (fun v => edgeProfile bad v - edgeDensity bad) hzero gap
  have hv := mul_le_mul_of_nonneg_left (edgeProfile_centered_energy bad)
    (pow_nonneg certificate.nonnegative gap)
  change edgeDensity bad ^ 2 + _ ≤ _
  exact add_le_add (le_refl _) (hc.trans hv)

theorem returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap := by
  have h := returnMass_le_sharp G lambda certificate bad reversal gap
  have hvar : edgeDensity bad * (1 - edgeDensity bad) ≤ edgeDensity bad := by
    nlinarith [sq_nonneg (edgeDensity bad)]
  have hm := mul_le_mul_of_nonneg_left hvar (pow_nonneg certificate.nonnegative gap)
  nlinarith

theorem adjacent_returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) :
    returnMass G bad 0 ≤ edgeDensity bad := by
  have h := returnMass_le_sharp G lambda certificate bad reversal 0
  norm_num at h
  nlinarith

end Profiles

theorem geometric_sum_le (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda < 1) (n : Nat) :
    (∑ k ∈ Finset.range n, lambda ^ k) ≤ 1 / (1 - lambda) := by
  have hsum : (∑ k ∈ Finset.range n, lambda ^ k) * (1 - lambda) = 1 - lambda ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hden : 0 < 1 - lambda := by linarith
  apply (le_div_iff₀ hden).2
  rw [hsum]
  linarith [pow_nonneg h0 n]

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

theorem sum_returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ gap ∈ Finset.range n, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda) := by
  calc
    _ ≤ ∑ gap ∈ Finset.range n,
        (edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap) :=
      Finset.sum_le_sum (fun gap _ => returnMass_le G lambda certificate bad reversal gap)
    _ = (n : ℝ) * edgeDensity bad ^ 2 +
        edgeDensity bad * (∑ gap ∈ Finset.range n, lambda ^ gap) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad * (1 / (1 - lambda)) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (geometric_sum_le lambda certificate.nonnegative certificate.lt_one n)
          (edgeDensity_nonnegative bad))
    _ = _ := by ring

theorem triangular_returnMass_sum_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
        (n : ℝ) * (edgeDensity bad / (1 - lambda)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hrow := sum_returnMass_le G lambda certificate bad reversal n
      have h := add_le_add ih hrow
      calc
        _ ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
            (n : ℝ) * (edgeDensity bad / (1 - lambda)) +
            ((n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda)) := h
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

theorem secondMoment_return_envelope (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (n : ℝ) * edgeDensity bad +
        2 * (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((n : ℝ) - 1) * edgeDensity bad) := by
  calc
    _ ≤ (n : ℝ) * edgeDensity bad +
        2 * (((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
          (n : ℝ) * (edgeDensity bad / (1 - lambda))) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (triangular_returnMass_sum_le G lambda certificate bad reversal n) (by norm_num))
    _ = _ := by ring

end BinPackingGames.Foundations.PCP.SpectralReturn

namespace BinPackingGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open BinPackingGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def zeroFrequency : Cube I := fun _ => false

theorem cubeXor_cancel_right (x y : Cube I) :
    cubeXor (cubeXor x y) y = x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

theorem cubeXor_assoc (x y z : Cube I) :
    cubeXor (cubeXor x y) z = cubeXor x (cubeXor y z) := by
  funext i
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [cubeXor, hx, hy, hz]

@[simp] theorem cubeXor_zeroFrequency (x : Cube I) :
    cubeXor x zeroFrequency = x := by
  funext i
  cases hx : x i <;> simp [cubeXor, zeroFrequency, hx]

def xorTranslation (y : Cube I) : Cube I ≃ Cube I where
  toFun x := cubeXor x y
  invFun x := cubeXor x y
  left_inv x := cubeXor_cancel_right x y
  right_inv x := cubeXor_cancel_right x y

def rotate (g : D → Cube I) (p : Cube I × D) : Cube I × D :=
  (cubeXor p.1 (g p.2), p.2)

theorem rotate_involutive (g : D → Cube I) : Function.Involutive (rotate g) := by
  rintro ⟨x, d⟩
  change (cubeXor (cubeXor x (g d)) (g d), d) = (x, d)
  rw [cubeXor_cancel_right]

def cayleyGraph (g : D → Cube I) : PortGraph (Cube I) D where
  rot :=
    { toFun := rotate g
      invFun := rotate g
      left_inv := rotate_involutive g
      right_inv := rotate_involutive g }
  rot_involutive := rotate_involutive g

@[simp] theorem cayleyGraph_rot (g : D → Cube I) (x : Cube I) (d : D) :
    (cayleyGraph g).rot (x, d) = (cubeXor x (g d), d) := rfl

def splitPortWord (n : Nat) : (Fin (n + 1) → D) ≃ D × (Fin n → D) where
  toFun p := (p 0, fun j => p j.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv p := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def powerGenerators (g : D → Cube I) : (n : Nat) → (Fin n → D) → Cube I
  | 0, _ => zeroFrequency
  | n + 1, p => cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ))

theorem wordEnd_eq_powerGenerators (g : D → Cube I) (n : Nat)
    (x : Cube I) (p : Fin n → D) :
    wordEnd (cayleyGraph g) n x p = cubeXor x (powerGenerators g n p) := by
  induction n generalizing x with
  | zero => simp [wordEnd, powerGenerators]
  | succ n ih =>
    change wordEnd (cayleyGraph g) n (cubeXor x (g (p 0))) (fun j => p j.succ) =
      cubeXor x (cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ)))
    rw [ih, cubeXor_assoc]

variable [Fintype I] [DecidableEq I] [Fintype D]

def cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  𝔼 d, f ((cayleyGraph g).rot (x, d)).1

def eigenvalue (g : D → Cube I) (s : Cube I) : ℝ :=
  𝔼 d, walsh s (g d)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem averagingOperator_cayleyGraph (g : D → Cube I) (f : Cube I → ℝ) :
    SpectralReturn.averagingOperator (cayleyGraph g) f = cayleyAverage g f := rfl

@[simp] theorem coefficient_zeroFrequency (f : Cube I → ℝ) :
    coefficient f zeroFrequency = 𝔼 x, f x := by
  simp [coefficient, zeroFrequency, walsh, bitSign]

theorem coefficient_xorTranslation (f : Cube I → ℝ) (s v : Cube I) :
    coefficient (fun x => f (cubeXor x v)) s = walsh s v * coefficient f s := by
  calc
    coefficient (fun x => f (cubeXor x v)) s =
        𝔼 x, f x * walsh s (cubeXor x v) := by
      unfold coefficient
      apply Fintype.expect_equiv (xorTranslation v)
      intro x
      change f (cubeXor x v) * walsh s x =
        f (cubeXor x v) * walsh s (cubeXor (cubeXor x v) v)
      rw [cubeXor_cancel_right]
    _ = 𝔼 x, (f x * walsh s x) * walsh s v := by
      apply Finset.expect_congr rfl
      intro x _
      rw [walsh_xor]
      ring
    _ = coefficient f s * walsh s v := by
      rw [← Finset.expect_mul]
      rfl
    _ = walsh s v * coefficient f s := mul_comm _ _

theorem cayleyAverage_walsh (g : D → Cube I) (s x : Cube I) :
    cayleyAverage g (walsh s) x = eigenvalue g s * walsh s x := by
  unfold cayleyAverage
  simp only [cayleyGraph_rot, walsh_xor]
  rw [← Finset.mul_expect]
  rw [mul_comm]
  rfl

theorem coefficient_cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (cayleyAverage g f) s = eigenvalue g s * coefficient f s := by
  calc
    coefficient (cayleyAverage g f) s =
        𝔼 x, 𝔼 d, f (cubeXor x (g d)) * walsh s x := by
      unfold coefficient cayleyAverage
      simp only [cayleyGraph_rot, Finset.expect_mul]
    _ = 𝔼 d, 𝔼 x, f (cubeXor x (g d)) * walsh s x := by
      rw [Finset.expect_comm]
    _ = 𝔼 d, walsh s (g d) * coefficient f s := by
      apply Finset.expect_congr rfl
      intro d _
      exact coefficient_xorTranslation f s (g d)
    _ = eigenvalue g s * coefficient f s := by
      rw [← Finset.expect_mul]
      rfl

theorem eigenvalue_powerGenerators (g : D → Cube I) (n : Nat) (s : Cube I) :
    eigenvalue (powerGenerators g n) s = eigenvalue g s ^ n := by
  induction n with
  | zero =>
    let : Nonempty (Fin 0 → D) := ⟨fun i => Fin.elim0 i⟩
    simp [eigenvalue, powerGenerators, zeroFrequency, walsh, bitSign]
  | succ n ih =>
    calc
      eigenvalue (powerGenerators g (n + 1)) s =
          𝔼 z : D × (Fin n → D),
            walsh s (cubeXor (g z.1) (powerGenerators g n z.2)) := by
        unfold eigenvalue
        apply Fintype.expect_equiv (splitPortWord n)
        intro p
        rfl
      _ = 𝔼 d, 𝔼 p : Fin n → D,
          walsh s (cubeXor (g d) (powerGenerators g n p)) := by
        exact SpectralReturn.mean_prod _
      _ = eigenvalue g s * eigenvalue (powerGenerators g n) s := by
        simp_rw [walsh_xor, ← Finset.mul_expect]
        rw [← Finset.expect_mul]
        rfl
      _ = eigenvalue g s ^ (n + 1) := by
        rw [ih, pow_succ, mul_comm]

theorem power_port_card (n : Nat) :
    Fintype.card (Fin n → D) = Fintype.card D ^ n := by
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem seven_power_port_card :
    Fintype.card (Fin 7 → Fin (2 ^ 16)) = (2 ^ 16) ^ 7 := by
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem cayley_energy_contraction (g : D → Cube I) (lambda : ℝ) (_hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (f : Cube I → ℝ) (hmean : (𝔼 x, f x) = 0) :
    (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2) := by
  classical
  have hzero : coefficient f zeroFrequency = 0 := by
    rw [coefficient_zeroFrequency]
    exact hmean
  calc
    (𝔼 x, cayleyAverage g f x ^ 2) =
        ∑ s, coefficient (cayleyAverage g f) s ^ 2 := (walsh_parseval _).symm
    _ = ∑ s, (eigenvalue g s * coefficient f s) ^ 2 := by
      simp only [coefficient_cayleyAverage]
    _ ≤ ∑ s, lambda ^ 2 * coefficient f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s = zeroFrequency
      · subst s
        simp [hzero]
      · have hb := hbias s hs
        have hlo : -lambda ≤ eigenvalue g s := (abs_le.mp hb).1
        have hhi : eigenvalue g s ≤ lambda := (abs_le.mp hb).2
        have hprod : 0 ≤ (lambda - eigenvalue g s) * (lambda + eigenvalue g s) :=
          mul_nonneg (sub_nonneg.mpr hhi) (by linarith)
        have hsq : eigenvalue g s ^ 2 ≤ lambda ^ 2 := by nlinarith
        calc
          (eigenvalue g s * coefficient f s) ^ 2 =
              eigenvalue g s ^ 2 * coefficient f s ^ 2 := by rw [mul_pow]
          _ ≤ lambda ^ 2 * coefficient f s ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = lambda ^ 2 * (𝔼 x, f x ^ 2) := by
      rw [← Finset.mul_sum, walsh_parseval]

theorem cayley_spectralCertificate (g : D → Cube I) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambdaone : lambda < 1)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda) :
    SpectralReturn.SpectralCertificate (cayleyGraph g) lambda where
  nonnegative := hlambda
  lt_one := hlambdaone
  contraction := by
    intro f hf
    change (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2)
    exact cayley_energy_contraction g lambda hlambda hbias f hf

theorem power_eigenvalue_bound (g : D → Cube I) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (n : Nat) (s : Cube I) (hs : s ≠ zeroFrequency) :
    |eigenvalue (powerGenerators g n) s| ≤ lambda ^ n := by
  rw [eigenvalue_powerGenerators, abs_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih (hbias s hs) (abs_nonneg _) (pow_nonneg hlambda _)

theorem sevenStep_halfCertificate (g : D → Cube I)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ)) :
    SpectralReturn.SpectralCertificate (cayleyGraph (powerGenerators g 7))
      ((1 / 2 : ℝ) ^ 7) := by
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact power_eigenvalue_bound g (1 / 2) (by norm_num) hbias 7 s hs

end BinPackingGames.Foundations.PCP.CayleySpectral

namespace BinPackingGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

@[simp] theorem square_rot_apply (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    (square G).rot (v, (d₁, d₂)) =
      let first := G.rot (v, d₁)
      let second := G.rot (first.1, d₂)
      (second.1, (second.2, first.2)) := rfl

@[simp] theorem square_next (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    next (square G) v (d₁, d₂) = next G (next G v d₁) d₂ := rfl

def cloudFirst (H : PortGraph D E) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) :=
  let step := H.rot (s.1.2, s.2.1)
  ((s.1.1, step.1), (step.2, s.2.2))

theorem cloudFirst_involutive (H : PortGraph D E) :
    Function.Involutive (cloudFirst (V := V) H) := by
  rintro ⟨⟨v, d⟩, ⟨e₁, e₂⟩⟩
  change ((v, (H.rot (H.rot (d, e₁))).1), ((H.rot (H.rot (d, e₁))).2, e₂)) =
    ((v, d), (e₁, e₂))
  rw [H.rot_involutive]

def crossCloud (G : PortGraph V D) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) := (G.rot s.1, (s.2.2, s.2.1))

theorem crossCloud_involutive (G : PortGraph V D) :
    Function.Involutive (crossCloud (E := E) G) := by
  rintro ⟨x, e₁, e₂⟩
  change (G.rot (G.rot x), (e₁, e₂)) = (x, (e₁, e₂))
  rw [G.rot_involutive]

def zigzag (G : PortGraph V D) (H : PortGraph D E) : PortGraph (V × D) (E × E) := by
  let B := involutionEquiv (cloudFirst (V := V) H) (cloudFirst_involutive H)
  let P := involutionEquiv (crossCloud (E := E) G) (crossCloud_involutive G)
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (cloudFirst_involutive H) (crossCloud_involutive G) }

@[simp] theorem zigzag_rot_apply (G : PortGraph V D) (H : PortGraph D E)
    (v : V) (d : D) (e₁ e₂ : E) :
    (zigzag G H).rot ((v, d), (e₁, e₂)) =
      let first := H.rot (d, e₁)
      let middle := G.rot (v, first.1)
      let last := H.rot (middle.2, e₂)
      ((middle.1, last.1), (last.2, first.2)) := rfl

theorem natCard_square_ports : Nat.card (D × D) = Nat.card D ^ 2 := by
  simp [Nat.card_prod, pow_two]

theorem natCard_square_edges :
    Nat.card (Edge V (D × D)) = Nat.card V * Nat.card D ^ 2 := by
  simp [Edge, Nat.card_prod, pow_two]

theorem natCard_zigzag_vertices :
    Nat.card (V × D) = Nat.card V * Nat.card D := Nat.card_prod V D

theorem natCard_zigzag_ports : Nat.card (E × E) = Nat.card E ^ 2 := by
  simp [Nat.card_prod, pow_two]

theorem natCard_zigzag_edges :
    Nat.card (Edge (V × D) (E × E)) =
      Nat.card V * Nat.card D * Nat.card E ^ 2 := by
  simp [Edge, Nat.card_prod, pow_two]

def cloudOperator [Fintype E] (H : PortGraph D E) (f : V × D → ℝ) (x : V × D) : ℝ :=
  SpectralReturn.mean (fun e => f (x.1, (H.rot (x.2, e)).1))

def graphPermutation (G : PortGraph V D) (f : V × D → ℝ) (x : V × D) : ℝ :=
  f (G.rot x)

theorem averagingOperator_square [Fintype D] (G : PortGraph V D) (f : V → ℝ) :
    SpectralReturn.averagingOperator (square G) f =
      SpectralReturn.averagingOperator G (SpectralReturn.averagingOperator G f) := by
  funext v
  let w : D × D → ℝ := fun ds => f (G.rot ((G.rot (v, ds.1)).1, ds.2)).1
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun d₁ => SpectralReturn.mean (fun d₂ => w (d₁, d₂)))
  exact SpectralReturn.mean_prod w

theorem averagingOperator_zigzag [Fintype E] (G : PortGraph V D)
    (H : PortGraph D E) (f : V × D → ℝ) :
    SpectralReturn.averagingOperator (zigzag G H) f =
      cloudOperator H (graphPermutation G (cloudOperator H f)) := by
  funext x
  rcases x with ⟨v, d⟩
  let w : E × E → ℝ := fun es =>
    let first := H.rot (d, es.1)
    let middle := G.rot (v, first.1)
    let last := H.rot (middle.2, es.2)
    f (middle.1, last.1)
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun e₁ => SpectralReturn.mean (fun e₂ => w (e₁, e₂)))
  exact SpectralReturn.mean_prod w

end BinPackingGames.Foundations.PCP.ZigzagGraphs

namespace BinPackingGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

theorem mean_indicator (S : Finset V) :
    mean (indicator S) = (S.card : ℝ) / (Fintype.card V : ℝ) := by
  have hf : Finset.univ.filter (fun v : V => v ∈ S) = S := by
    ext v
    simp
  rw [mean_eq_sum_div_card]
  simp only [indicator, Finset.sum_boole, hf]

theorem energy_indicator (S : Finset V) : energy (indicator S) = mean (indicator S) := by
  unfold energy
  congr 1
  funext v
  unfold indicator
  split_ifs <;> norm_num

omit [Fintype V] in
theorem indicator_nonnegative (S : Finset V) (v : V) : 0 ≤ indicator S v := by
  unfold indicator
  split_ifs <;> norm_num
end Indicators

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

def cut (G : PortGraph V D) (S : Finset V) : Finset (V × D) :=
  Finset.univ.filter (fun e => e.1 ∈ S ∧ (G.rot e).1 ∉ S)

section Nonempty
variable [Nonempty V] [Nonempty D] (G : PortGraph V D)

omit [Nonempty V] in
theorem cut_density_eq (S : Finset V) :
    ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) =
      mean (indicator S) - correlation (indicator S) (averagingOperator G (indicator S)) := by
  classical
  calc
    _ = mean (indicator (cut G S)) := (mean_indicator (cut G S)).symm
    _ = mean (fun e : V × D => indicator S e.1 -
        indicator S e.1 * indicator S (G.rot e).1) := by
      congr 1
      funext e
      by_cases hv : e.1 ∈ S <;> by_cases hw : (G.rot e).1 ∈ S <;>
        simp [indicator, cut, hv, hw]
    _ = mean (fun v => mean (fun d : D => indicator S v -
        indicator S v * indicator S (G.rot (v,d)).1)) := mean_prod _
    _ = mean (fun v => indicator S v -
        indicator S v * averagingOperator G (indicator S) v) := by
      congr 1
      funext v
      rw [mean_sub, mean_const, mean_mul_left]
      rfl
    _ = _ := mean_sub _ _

theorem cut_density_ge_variance
    (certificate : SpectralCertificate G (1/2)) (S : Finset V) :
    (1/2:ℝ) * mean (indicator S) * (1 - mean (indicator S)) ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  let f := indicator S
  have hz : mean (fun v => f v - mean f) = 0 := by
    rw [mean_sub, mean_const, sub_self]
  have he : energy (fun v => f v - mean f) = mean f - mean f ^ 2 := by
    rw [energy_sub_const, energy_indicator]
    ring
  have hb := zero_mean_correlation_bound G (1/2) certificate
    (fun v => f v - mean f) hz 1
  have hc := correlation_centered G f 1
  simp only [iterateOperator, pow_one, he] at hb hc
  rw [cut_density_eq]
  change (1/2:ℝ) * mean f * (1 - mean f) ≤
    mean f - correlation f (averagingOperator G f)
  nlinarith

theorem cut_density_ge_quarter
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    mean (indicator S) / 4 ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp0 : 0 ≤ mean (indicator S) := mean_nonnegative _ (indicator_nonnegative S)
  have hp : mean (indicator S) ≤ (1/2:ℝ) := by
    rw [mean_indicator]
    apply (div_le_iff₀ hN).mpr
    have hs : (2:ℝ) * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hsmall
    nlinarith
  have hv := cut_density_ge_variance G certificate S
  have hprod := mul_nonneg hp0 (sub_nonneg.mpr hp)
  nlinarith

theorem cut_card_ge_quarter_degree
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0:ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h := cut_density_ge_quarter G certificate S hsmall
  rw [Fintype.card_prod, Nat.cast_mul] at h
  have hh := (le_div_iff₀ (mul_pos hN hD)).mp h
  have he : mean (indicator S) / 4 *
      ((Fintype.card V : ℝ) * (Fintype.card D : ℝ)) =
        (Fintype.card D : ℝ) * (S.card : ℝ) / 4 := by
    rw [mean_indicator]
    field_simp [ne_of_gt hN]
  rw [he] at hh
  exact hh

theorem degree_mul_card_le_four_cut
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    Fintype.card D * S.card ≤ 4 * (cut G S).card := by
  have h := cut_card_ge_quarter_degree G certificate S hsmall
  have hr : (Fintype.card D : ℝ) * (S.card : ℝ) ≤ 4 * ((cut G S).card : ℝ) := by
    linarith
  exact_mod_cast hr

theorem cut_card_ge_quarter_degree_of_card_le_half
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : S.card ≤ Fintype.card V / 2) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) :=
  cut_card_ge_quarter_degree G certificate S (by omega)
end Nonempty

theorem cut_card_ge_twice (G : PortGraph V D)
    (certificate : SpectralCertificate G (1/2)) (hdegree : 8 ≤ Fintype.card D)
    (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    2 * S.card ≤ (cut G S).card := by
  let : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  rcases isEmpty_or_nonempty V with hV | hV
  · let := hV
    have hzero : Fintype.card V = 0 := Fintype.card_eq_zero
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · let := hV
    have h := degree_mul_card_le_four_cut G certificate S hsmall
    have hdeg := Nat.mul_le_mul_right S.card hdegree
    omega

end BinPackingGames.Foundations.PCP.SpectralCut

end

end OAI
