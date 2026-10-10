import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

universe uV

/-!
# Polynomial zero counts over a finite prime field

The sample space contains every assignment of the finite variable set. In
particular, using a product variable type imposes no restriction on repeated
vector indices. The exact counting bound is obtained from the
Schwartz–Zippel theorem by renaming variables and clearing positive denominators.
-/

noncomputable section

namespace MetricEntropyDuality

variable {p : ℕ} [Fact p.Prime]

/-- The literal zero set in the full finite assignment space. -/
def polynomialZeros {V : Type uV} [Fintype V] (P : MvPolynomial V (ZMod p)) :
    Finset (V → ZMod p) := by
  classical
  exact Finset.univ.filter (fun x => MvPolynomial.eval x P = 0)

@[simp] theorem mem_polynomialZeros {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (x : V → ZMod p) :
    x ∈ polynomialZeros P ↔ MvPolynomial.eval x P = 0 := by
  classical
  simp [polynomialZeros]

private theorem polynomial_zero_card_mul_le_fin {n : ℕ}
    (P : MvPolynomial (Fin n) (ZMod p)) (hP : P ≠ 0) :
    p * (polynomialZeros P).card ≤ P.totalDegree * p ^ n := by
  have hSZ := MvPolynomial.schwartz_zippel_totalDegree hP
    (Finset.univ : Finset (ZMod p))
  have hzeros :
      (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod p)))).filter
        (fun x => MvPolynomial.eval x P = 0) = polynomialZeros P := by
    classical
    ext x
    simp [polynomialZeros]
  have hratio : ((polynomialZeros P).card : ℚ≥0) / (p : ℚ≥0) ^ n ≤
      (P.totalDegree : ℚ≥0) / (p : ℚ≥0) := by
    rw [hzeros] at hSZ
    simpa only [Finset.card_univ, ZMod.card] using hSZ
  have hp : (0 : ℚ≥0) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hcross := (div_le_div_iff₀ (pow_pos hp n) hp).mp hratio
  have hnat : (polynomialZeros P).card * p ≤ P.totalDegree * p ^ n := by
    exact_mod_cast hcross
  simpa only [Nat.mul_comm] using hnat

/-- Schwartz–Zippel as a natural-number inequality, for any finite variable
type, including the empty variable type. -/
theorem polynomial_zero_card_mul_le {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (hP : P ≠ 0) :
    p * (polynomialZeros P).card ≤ P.totalDegree * p ^ Fintype.card V := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let Q : MvPolynomial (Fin (Fintype.card V)) (ZMod p) :=
    MvPolynomial.renameEquiv (ZMod p) e P
  have hQ : Q ≠ 0 := by
    intro h
    apply hP
    apply (MvPolynomial.renameEquiv (ZMod p) e).injective
    simpa only [map_zero] using h
  have hcard : (polynomialZeros P).card = (polynomialZeros Q).card := by
    apply Finset.card_bij (fun x _ i => x (e.symm i))
    · intro x hx
      rw [mem_polynomialZeros] at hx ⊢
      simpa only [Q, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
        Function.comp_def, Equiv.symm_apply_apply] using hx
    · intro x hx y hy h
      funext v
      simpa only [Equiv.symm_apply_apply] using congrFun h (e v)
    · intro y hy
      refine ⟨fun v => y (e v), ?_, ?_⟩
      · rw [mem_polynomialZeros] at hy ⊢
        simpa only [Q, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
          Function.comp_def] using hy
      · funext i
        simp only [Equiv.apply_symm_apply]
  rw [hcard]
  have h := polynomial_zero_card_mul_le_fin Q hQ
  simpa only [Q, MvPolynomial.totalDegree_renameEquiv] using h

/-- A supplied upper bound for total degree gives the same exact zero count. -/
theorem polynomial_zero_card_mul_le_of_totalDegree_le {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (hP : P ≠ 0) {d : ℕ}
    (hdeg : P.totalDegree ≤ d) :
    p * (polynomialZeros P).card ≤ d * p ^ Fintype.card V :=
  (polynomial_zero_card_mul_le P hP).trans (Nat.mul_le_mul_right _ hdeg)

/-- The number of zeros is at most `d/p` times the number of assignments. -/
theorem polynomial_zero_card_real_le {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (hP : P ≠ 0) {d : ℕ}
    (hdeg : P.totalDegree ≤ d) :
    ((polynomialZeros P).card : ℝ) ≤
      (d : ℝ) / p * ((p ^ Fintype.card V : ℕ) : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hcross : (p : ℝ) * (polynomialZeros P).card ≤
      (d : ℝ) * ((p ^ Fintype.card V : ℕ) : ℝ) := by
    exact_mod_cast polynomial_zero_card_mul_le_of_totalDegree_le P hP hdeg
  calc
    ((polynomialZeros P).card : ℝ) ≤
        ((d : ℝ) * ((p ^ Fintype.card V : ℕ) : ℝ)) / p :=
      (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hcross)
    _ = (d : ℝ) / p * ((p ^ Fintype.card V : ℕ) : ℝ) := by ring

/-- The exact fraction of assignments on which the polynomial vanishes is
at most `d/p`; this is the uniform-product probability formulation. -/
theorem polynomial_zero_proportion_le {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (hP : P ≠ 0) {d : ℕ}
    (hdeg : P.totalDegree ≤ d) :
    ((polynomialZeros P).card : ℝ) / ((p ^ Fintype.card V : ℕ) : ℝ) ≤
      (d : ℝ) / p := by
  have htotal : (0 : ℝ) < ((p ^ Fintype.card V : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (Fact.out : p.Prime).pos (Fintype.card V)
  exact (div_le_iff₀ htotal).2 (polynomial_zero_card_real_le P hP hdeg)

end MetricEntropyDuality

end

end OAI
