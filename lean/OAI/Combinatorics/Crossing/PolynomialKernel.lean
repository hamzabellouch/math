import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Module
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

def Bounded (k : ℕ) (p : PolynomialModule ℝ W) : Prop :=
  ∀ n, k ≤ n → p.coeff n = 0

theorem bounded_zero (k : ℕ) : Bounded k (0 : PolynomialModule ℝ W) := by
  intro n hn
  simp

theorem bounded_mono {k l : ℕ} {p : PolynomialModule ℝ W}
    (hp : Bounded k p) (hkl : k ≤ l) : Bounded l p :=
  fun n hn => hp n (hkl.trans hn)

theorem bounded_add {k : ℕ} {p q : PolynomialModule ℝ W}
    (hp : Bounded k p) (hq : Bounded k q) : Bounded k (p + q) := by
  intro n hn
  simp [hp n hn, hq n hn]

theorem bounded_sub {k : ℕ} {p q : PolynomialModule ℝ W}
    (hp : Bounded k p) (hq : Bounded k q) : Bounded k (p - q) := by
  intro n hn
  change p.coeff n - q.coeff n = 0
  rw [hp n hn, hq n hn, sub_self]

theorem bounded_single {k n : ℕ} (hn : n < k) (w : W) :
    Bounded k (single ℝ n w) := by
  intro j hj
  simp [show n ≠ j by omega]

theorem bounded_zero_iff (p : PolynomialModule ℝ W) : Bounded 0 p ↔ p = 0 := by
  constructor
  · intro h
    ext n
    exact h n (Nat.zero_le n)
  · rintro rfl
    exact bounded_zero 0

def mulRoot (t : ℝ) (p : PolynomialModule ℝ W) : PolynomialModule ℝ W :=
  (Polynomial.X - Polynomial.C t) • p

theorem mulRoot_coeff_zero (t : ℝ) (p : PolynomialModule ℝ W) :
    (mulRoot t p).coeff 0 = -t • p.coeff 0 := by
  unfold mulRoot
  rw [sub_smul]
  change (((Polynomial.X : Polynomial ℝ) • p).coeff 0 -
    (Polynomial.C t • p).coeff 0) = _
  simp [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left]

theorem mulRoot_coeff_succ (t : ℝ) (p : PolynomialModule ℝ W) (n : ℕ) :
    (mulRoot t p).coeff (n+1) = p.coeff n - t • p.coeff (n+1) := by
  unfold mulRoot
  rw [sub_smul]
  change (((Polynomial.X : Polynomial ℝ) • p).coeff (n+1) -
    (Polynomial.C t • p).coeff (n+1)) = _
  simp [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left]

theorem eval_mulRoot (t u : ℝ) (p : PolynomialModule ℝ W) :
    eval u (mulRoot t p) = (u-t) • eval u p := by
  simp [mulRoot]

theorem bounded_mulRoot {k : ℕ} {p : PolynomialModule ℝ W}
    (t : ℝ) (hp : Bounded k p) : Bounded (k+1) (mulRoot t p) := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [mulRoot_coeff_succ, hp j (by omega), hp (j+1) (by omega)]
  simp

theorem eq_constant_of_bounded_one {p : PolynomialModule ℝ W} (hp : Bounded 1 p) :
    p = single ℝ 0 (p.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [hp (n+1) (by omega)]

theorem exists_mulRoot_of_eval_zero (t : ℝ) (k : ℕ) (p : PolynomialModule ℝ W)
    (hp : Bounded (k+1) p) (he : eval t p = 0) :
    ∃ q, Bounded k q ∧ mulRoot t q = p := by
  induction k generalizing p with
  | zero =>
    have hc := eq_constant_of_bounded_one hp
    have hz : p.coeff 0 = 0 := by
      rw [hc] at he
      simpa only [eval_single, pow_zero, one_smul] using he
    refine ⟨0, bounded_zero 0, ?_⟩
    have hp0 : p = 0 := hc.trans (by rw [hz, single_zero])
    simp [mulRoot, hp0]
  | succ k ih =>
    let q₀ := single ℝ k (p.coeff (k+1))
    have hq₀ : Bounded (k+1) q₀ := bounded_single (by omega) _
    let r := p - mulRoot t q₀
    have hr : Bounded (k+1) r := by
      intro n hn
      rcases eq_or_lt_of_le hn with rfl | hn'
      · change p.coeff (k+1) - (mulRoot t q₀).coeff (k+1) = 0
        rw [mulRoot_coeff_succ]
        simp [q₀]
      · exact bounded_sub hp (bounded_mulRoot t hq₀) n (by omega)
    have er : eval t r = 0 := by simp [r, eval_mulRoot, he]
    obtain ⟨q, hq, eq⟩ := ih r hr er
    refine ⟨q + q₀, bounded_add (bounded_mono hq (by omega)) hq₀, ?_⟩
    change (Polynomial.X - Polynomial.C t) • (q + q₀) = p
    rw [smul_add]
    change mulRoot t q + mulRoot t q₀ = p
    rw [eq]
    exact sub_add_cancel p _

theorem eq_zero_of_mulRoot_eq_zero (t : ℝ) (k : ℕ) (p : PolynomialModule ℝ W)
    (hp : Bounded k p) (he : mulRoot t p = 0) : p = 0 := by
  induction k with
  | zero => exact (bounded_zero_iff p).mp hp
  | succ k ih =>
    have hc : p.coeff k = 0 := by
      have hh := congrArg (fun q : PolynomialModule ℝ W => q.coeff (k+1)) he
      rw [mulRoot_coeff_succ, hp (k+1) (by omega)] at hh
      simpa using hh
    apply ih
    intro n hn
    rcases eq_or_lt_of_le hn with rfl | hn'
    · exact hc
    · exact hp n (by omega)

def mulRootLinear (t : ℝ) : PolynomialModule ℝ W →ₗ[ℝ] PolynomialModule ℝ W where
  toFun := mulRoot t
  map_add' _ _ := smul_add _ _ _
  map_smul' c p := smul_comm _ c p

variable {ι : Type*}

def constrained (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    (k : ℕ) : Submodule ℝ (PolynomialModule ℝ Z) where
  carrier := {p | Bounded k p ∧ ∀ i, Z.subtype (eval (node i) p) ∈ U i}
  zero_mem' := ⟨bounded_zero k, by simp⟩
  add_mem' := by
    intro p q hp hq
    refine ⟨bounded_add hp.1 hq.1, ?_⟩
    intro i
    simpa using (U i).add_mem (hp.2 i) (hq.2 i)
  smul_mem' := by
    intro c p hp
    refine ⟨?_, ?_⟩
    · intro n hn
      change c • p.coeff n = 0
      rw [hp.1 n hn, smul_zero]
    · intro i
      simpa using (U i).smul_mem c (hp.2 i)

variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

def constrainedEval (k : ℕ) (t : ℝ) : constrained U node Z k →ₗ[ℝ] Z :=
  (eval t).comp (constrained U node Z k).subtype

def toEvalKernel (k : ℕ) (t : ℝ) :
    constrained U node Z k →ₗ[ℝ] LinearMap.ker (constrainedEval U node Z (k+1) t) where
  toFun p := ⟨⟨mulRoot t p.val, bounded_mulRoot t p.property.1, by
    intro i
    have hi := (U i).smul_mem (node i-t) (p.property.2 i)
    simpa only [eval_mulRoot, _root_.map_smul] using hi⟩, by
      change eval t (mulRoot t p.val) = 0
      simp [eval_mulRoot]⟩
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact (mulRootLinear t).map_add p.val q.val
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (mulRootLinear t).map_smul c p.val

theorem toEvalKernel_injective (k : ℕ) (t : ℝ) :
    Function.Injective (toEvalKernel U node Z k t) := by
  intro p q he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_mulRoot_eq_zero t k (p.val-q.val)
  · exact bounded_sub p.property.1 q.property.1
  · have hh := congrArg (fun r : LinearMap.ker (constrainedEval U node Z (k+1) t) => r.val.val) he
    change mulRoot t p.val = mulRoot t q.val at hh
    change (mulRootLinear t) (p.val-q.val) = 0
    rw [map_sub, show mulRootLinear t p.val = mulRootLinear t q.val from hh, sub_self]

theorem toEvalKernel_surjective (k : ℕ) (t : ℝ) (ht : ∀ i, node i ≠ t) :
    Function.Surjective (toEvalKernel U node Z k t) := by
  intro p
  obtain ⟨q, hq, eq⟩ := exists_mulRoot_of_eval_zero t k p.val.val p.val.property.1 p.property
  have hqU : ∀ i, Z.subtype (eval (node i) q) ∈ U i := by
    intro i
    have hp := p.val.property.2 i
    rw [← eq, eval_mulRoot] at hp
    exact (U i).smul_mem_iff (sub_ne_zero.mpr (ht i)) |>.mp hp
  refine ⟨⟨q, hq, hqU⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact eq

def evalKernelEquiv (k : ℕ) (t : ℝ) (ht : ∀ i, node i ≠ t) :
    constrained U node Z k ≃ₗ[ℝ] LinearMap.ker (constrainedEval U node Z (k+1) t) :=
  LinearEquiv.ofBijective (toEvalKernel U node Z k t)
    ⟨toEvalKernel_injective U node Z k t, toEvalKernel_surjective U node Z k t ht⟩

def constrainedCoefficients (k : ℕ) : constrained U node Z k →ₗ[ℝ] (Fin k → Z) where
  toFun p n := p.val.coeff n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem constrainedCoefficients_injective (k : ℕ) :
    Function.Injective (constrainedCoefficients U node Z k) := by
  intro p q he
  apply Subtype.ext
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro n
  by_cases hn : n < k
  · exact congrFun he ⟨n, hn⟩
  · rw [p.property.1 n (by omega), q.property.1 n (by omega)]

instance constrained_finiteDimensional [FiniteDimensional ℝ W] (k : ℕ) :
    FiniteDimensional ℝ (constrained U node Z k) :=
  FiniteDimensional.of_injective (constrainedCoefficients U node Z k)
    (constrainedCoefficients_injective U node Z k)

def rankIncrement (h : ℕ) : ℕ :=
  Module.finrank ℝ (constrained U node Z (h+1)) - Module.finrank ℝ (constrained U node Z h)

theorem finrank_eval_range [FiniteDimensional ℝ W] (h : ℕ) (t : ℝ)
    (ht : ∀ i, node i ≠ t) :
    Module.finrank ℝ (LinearMap.range (constrainedEval U node Z (h+1) t)) =
      rankIncrement U node Z h := by
  have he := (evalKernelEquiv U node Z h t ht).finrank_eq
  have hr := (constrainedEval U node Z (h+1) t).finrank_range_add_finrank_ker
  unfold rankIncrement
  omega

end Zarankiewicz

end

end OAI
