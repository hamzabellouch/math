import Mathlib

namespace OAI

section
namespace ElementaryPositivity
namespace PrimitiveStrings

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (D T : Module.End ℚ V)

abbrev Strings := ℕ →₀ LinearMap.ker D

noncomputable def evaluate : Strings D →ₗ[ℚ] V :=
  Finsupp.lsum ℚ fun n => (T ^ n).comp (LinearMap.ker D).subtype

@[simp] theorem evaluate_single (n : ℕ) (v : LinearMap.ker D) :
    evaluate D T (Finsupp.single n v) = (T ^ n) v.val := by
  simp [evaluate]

noncomputable def differentiate : Strings D →ₗ[ℚ] Strings D :=
  Finsupp.lsum ℚ fun n =>
    match n with
    | 0 => 0
    | k + 1 => (k + 1 : ℚ) • Finsupp.lsingle k

noncomputable def integrate : Strings D →ₗ[ℚ] Strings D :=
  Finsupp.lsum ℚ fun n => (n + 1 : ℚ)⁻¹ • Finsupp.lsingle (n + 1)

@[simp] theorem differentiate_single_zero (v : LinearMap.ker D) :
    differentiate D (Finsupp.single 0 v) = 0 := by simp [differentiate]

@[simp] theorem differentiate_single_succ (n : ℕ) (v : LinearMap.ker D) :
    differentiate D (Finsupp.single (n + 1) v) =
      Finsupp.single n ((n + 1 : ℚ) • v) := by simp [differentiate]

@[simp] theorem integrate_single (n : ℕ) (v : LinearMap.ker D) :
    integrate D (Finsupp.single n v) =
      Finsupp.single (n + 1) ((n + 1 : ℚ)⁻¹ • v) := by simp [integrate]

 theorem differentiate_apply (f : Strings D) (n : ℕ) :
    differentiate D f n = (n + 1 : ℚ) • f (n + 1) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, smul_add]
  | single k v =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases h : k = n
      · subst k; simp
      · simp [Ne.symm h]

@[simp] theorem differentiate_integrate (f : Strings D) :
    differentiate D (integrate D f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single k v => simp [smul_smul, show (k + 1 : ℚ) ≠ 0 by positivity]

variable (weyl : ∀ v, D (T v) = T (D v) + v)
include weyl

 theorem derivative_string (v : LinearMap.ker D) (n : ℕ) :
    D ((T ^ (n + 1)) v.val) = (n + 1 : ℚ) • (T ^ n) v.val := by
  induction n with
  | zero => simpa using (weyl v.val).trans (by simp)
  | succ n ih =>
    rw [pow_succ' T (n + 1), Module.End.mul_apply, weyl, ih, map_smul]
    rw [← Module.End.mul_apply, ← pow_succ' T n]
    simp only [Nat.cast_add, Nat.cast_one]
    simp only [add_smul, one_smul]

 theorem evaluate_differentiate (f : Strings D) :
    evaluate D T (differentiate D f) = D (evaluate D T f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single n v =>
    cases n with
    | zero => simp
    | succ n => simp [derivative_string D T weyl, map_smul]

theorem evaluate_injective_bounded (N : ℕ) (f : Strings D)
    (bound : ∀ n, N ≤ n → f n = 0) (hf : evaluate D T f = 0) : f = 0 := by
  induction N generalizing f with
  | zero => apply Finsupp.ext; intro n; exact bound n (Nat.zero_le n)
  | succ N ih =>
    have hd : differentiate D f = 0 := by
      apply ih
      · intro n hn
        rw [differentiate_apply, bound (n + 1) (Nat.succ_le_succ hn), smul_zero]
      · rw [evaluate_differentiate D T weyl, hf, map_zero]
    have hpos : ∀ n, f (n + 1) = 0 := by
      intro n
      have h := congrArg (fun g : Strings D => g n) hd
      rw [differentiate_apply] at h
      exact (smul_eq_zero.mp h).resolve_left (by positivity)
    have heq : f = Finsupp.single 0 (f 0) := by
      ext n
      cases n with
      | zero => simp
      | succ n => simp [hpos]
    rw [heq, evaluate_single, pow_zero, Module.End.one_apply] at hf
    rw [heq]
    have hzero : f 0 = 0 := Subtype.ext hf
    rw [hzero, Finsupp.single_zero]

 theorem evaluate_injective : Function.Injective (evaluate D T) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  apply evaluate_injective_bounded D T weyl (f.support.sup id + 1) f _ hf
  intro n hn
  by_contra hne
  have hn' : n ≤ f.support.sup id := Finset.le_sup (f := id) (f.mem_support_iff.mpr hne)
  omega

theorem exists_strings_of_pow_eq_zero (N : ℕ) (v : V) (hv : (D ^ N) v = 0) :
    ∃ f : Strings D, evaluate D T f = v := by
  induction N generalizing v with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hv
    subst v
    exact ⟨0, map_zero _⟩
  | succ N ih =>
    have hd : (D ^ N) (D v) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ]
      exact hv
    obtain ⟨f, hf⟩ := ih (D v) hd
    let g := integrate D f
    have hg : D (v - evaluate D T g) = 0 := by
      rw [map_sub, ← evaluate_differentiate D T weyl]
      simp only [g, differentiate_integrate, hf, sub_self]
    let c : LinearMap.ker D := ⟨v - evaluate D T g, hg⟩
    refine ⟨Finsupp.single 0 c + g, ?_⟩
    simp [c]

noncomputable def decomposition (nilpotent : ∀ v : V, ∃ N : ℕ, (D ^ N) v = 0) :
    Strings D ≃ₗ[ℚ] V :=
  LinearEquiv.ofBijective (evaluate D T)
    ⟨evaluate_injective D T weyl, fun v => by
      obtain ⟨N, hv⟩ := nilpotent v
      exact exists_strings_of_pow_eq_zero D T weyl N v hv⟩

end PrimitiveStrings
end ElementaryPositivity

end

end OAI
