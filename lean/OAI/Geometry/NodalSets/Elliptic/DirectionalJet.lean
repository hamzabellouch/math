import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import OAI.Geometry.NodalSets.Elliptic.PolynomialJet

namespace OAI

namespace Yau
namespace Jets
open MvPolynomial
noncomputable section
variable {σ K : Type*} [Field K] [DecidableEq σ]
abbrev Poly (σ K : Type*) [CommSemiring K] := MvPolynomial σ K

def direction (v : σ → K) : Derivation K (Poly σ K) (Poly σ K) :=
  mkDerivation K (fun j ↦ C (v j))

def transverse (v : σ → K) (i j : σ) : Poly σ K :=
  if j = i then C ((v i)⁻¹) * X i
  else X j + C (-(v j / v i)) * X i

def original (v : σ → K) (i j : σ) : Poly σ K :=
  if j = i then C (v i) * X i else X j + C (v j) * X i

omit [DecidableEq σ] in
lemma direction_C (v : σ → K) (a : K) : direction v (C a) = 0 := by
  simp [direction]

omit [DecidableEq σ] in
lemma direction_X (v : σ → K) (j : σ) : direction v (X j) = C (v j) := by
  simp [direction]

omit [DecidableEq σ] in
lemma direction_C_mul (v : σ → K) (a : K) (p : Poly σ K) :
    direction v (C a * p) = C a * direction v p := by
  rw [(direction v).leibniz]
  simp [smul_eq_mul]

lemma transverse_derivative (v : σ → K) (i : σ) (hi : v i ≠ 0) (j : σ) :
    direction v (transverse v i j) = if j = i then 1 else 0 := by
  by_cases hj : j = i
  · subst j
    simp [transverse, direction_X, ← map_mul, hi]
  · simp only [transverse, ite_eq_right hj, map_add, direction_C_mul, direction_X]
    have he : v j + -(v j / v i) * v i = 0 := by field_simp; ring
    simpa only [map_add, map_mul, map_neg, map_zero] using congrArg (C : K → Poly σ K) he

lemma transverse_inverse (v : σ → K) (i : σ) (hi : v i ≠ 0) (j : σ) :
    aeval (transverse v i) (original v i j) = X j := by
  by_cases hj : j = i
  · subst j
    simp only [original, map_mul, aeval_C, algebraMap_eq, aeval_X,
      transverse, ite_true]
    rw [← mul_assoc, ← map_mul]
    simp [hi]
  · simp only [original, map_add, map_mul, aeval_X, aeval_C,
      algebraMap_eq, transverse, ite_eq_right hj, ite_true]
    have he : C (-(v j / v i)) + C (v j) * C ((v i)⁻¹) = (0 : Poly σ K) := by
      rw [← map_mul, ← map_add]
      simp [div_eq_mul_inv]
    linear_combination (X i) * he

lemma substitution_inverse (v : σ → K) (i : σ) (hi : v i ≠ 0) (p : Poly σ K) :
    aeval (transverse v i) (aeval (original v i) p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp, transverse_inverse v i hi]

lemma directional_substitution (v : σ → K) (i : σ) (hi : v i ≠ 0) (p : Poly σ K) :
    direction v (aeval (transverse v i) p) =
      aeval (transverse v i) (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, (direction v).leibniz, hp, transverse_derivative v i hi,
      pderiv_mul, pderiv_X, map_add, smul_eq_mul]
    by_cases hj : j = i <;> simp [hj] <;> ring

lemma transverse_homogeneous (v : σ → K) (i j : σ) :
    (transverse v i j).IsHomogeneous 1 := by
  unfold transverse
  split_ifs
  · exact isHomogeneous_C_mul_X _ _
  · exact (isHomogeneous_X K j).add (isHomogeneous_C_mul_X _ _)

lemma original_homogeneous (v : σ → K) (i j : σ) :
    (original v i j).IsHomogeneous 1 := by
  unfold original
  split_ifs
  · exact isHomogeneous_C_mul_X _ _
  · exact (isHomogeneous_X K j).add (isHomogeneous_C_mul_X _ _)

theorem homogeneous_directional_primitive [CharZero K] (v : σ → K) (i : σ) (hi : v i ≠ 0)
    {p : Poly σ K} {m : ℕ} (hp : p.IsHomogeneous m) :
    ∃ q : Poly σ K, q.IsHomogeneous (m + 1) ∧ direction v q = p := by
  let r := aeval (original v i) p
  have hr : r.IsHomogeneous m := by
    simpa using hp.aeval (original v i) (original_homogeneous v i)
  refine ⟨aeval (transverse v i) (Yau.primitive i r), ?_, ?_⟩
  · simpa using (Yau.primitive_homogeneous i hr).aeval (transverse v i)
      (transverse_homogeneous v i)
  · rw [directional_substitution v i hi, Yau.pderiv_primitive]
    exact substitution_inverse v i hi p

lemma direction_eq_sum [Fintype σ] (v : σ → K) :
    direction v = ∑ i, v i • pderiv (R := K) i := by
  apply MvPolynomial.derivation_ext
  intro j
  have hs (s : Finset σ) :
      (∑ i ∈ s, v i • pderiv (R := K) i) (X j) =
        ∑ i ∈ s, v i • pderiv (R := K) i (X j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, Derivation.smul_apply, ih]
  rw [hs]
  simp [direction_X, pderiv_X, Algebra.smul_def, Pi.single_apply]

theorem complex_directional_primitive (v : Fin 4 → ℂ) (hv : v ≠ 0)
    {p : MvPolynomial (Fin 4) ℂ} {m : ℕ} (hp : p.IsHomogeneous m) :
    ∃ q : MvPolynomial (Fin 4) ℂ,
      q.IsHomogeneous (m + 1) ∧ direction v q = p := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv (funext hn)
  exact homogeneous_directional_primitive v i hi hp

end
end Jets
end Yau

end OAI
