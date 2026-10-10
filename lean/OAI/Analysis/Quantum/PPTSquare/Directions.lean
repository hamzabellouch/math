import OAI.Analysis.Quantum.PPTSquare.PencilPoints
import OAI.Analysis.Quantum.PPTSquare.QuadraticEvaluation

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Matrix PencilAlgebra PencilEvaluation PencilGeometry PencilPoints
namespace PencilDirections
variable {K : Type*} [Field K]
def point (t : Fin 3 → K) : Fin 4 → K := ![1,t 0,t 1,t 2]
lemma point_zero (t : Fin 3 → K) : point t 0 = 1 := rfl
lemma point_ne_zero (t : Fin 3 → K) : point t ≠ 0 := by
  intro hh
  have h := congrFun hh 0
  exact one_ne_zero h
lemma point_injective : Function.Injective (point (K := K)) := by
  intro s t h
  ext a
  fin_cases a
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 3
lemma scalar_unique (s t : Fin 3 → K) (c d : K) (h : c • point s = d • point t) : c = d := by
  have hh := congrFun h 0
  simpa only [Pi.smul_apply, point_zero, smul_eq_mul, mul_one] using hh
lemma distinct (t : Fin 20 → Fin 3 → K) (ht : Function.Injective t) :
    (∀ i, point (t i) ≠ 0) ∧
    ∀ i j, i ≠ j → ∀ c : K, c ≠ 0 → point (t i) ≠ c • point (t j) := by
  refine ⟨fun i => point_ne_zero (t i), ?_⟩
  intro i j hij c hc he
  have h1 : 1 = c := scalar_unique (t i) (t j) 1 c (by simpa using he)
  rw [← h1, one_smul] at he
  exact hij (ht (point_injective he))

variable [CharZero K]

lemma exact_points (t : Fin 20 → Fin 3 → K) (ht : Function.Injective t)
    (hmin : ∀ s : Fin 3 → K, minors (point s) = 0 ↔ ∃ i, s = t i) :
    (∀ i, (pencil (point (t i))).rank < 4) ∧
    (∀ x : Fin 4 → K, x ≠ 0 → ((pencil x).rank < 4 ↔
      ∃! i, ∃ c : K, c ≠ 0 ∧ x = c • point (t i))) := by
  have hi (i : Fin 20) : (pencil (point (t i))).rank < 4 :=
    (rank_lt_iff _).mpr ((hmin _).mpr ⟨i,rfl⟩)
  refine ⟨hi, ?_⟩
  intro x hx
  constructor
  · intro hr
    have hx0 : x 0 ≠ 0 := no_infinity x hx hr
    let s : Fin 3 → K := ![x 1 / x 0,x 2 / x 0,x 3 / x 0]
    have hy : (x 0)⁻¹ • x = point s := by
      ext a
      fin_cases a <;> simp [point,s,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,hx0,mul_comm]
      ring
    have hs : minors (point s) = 0 := by
      apply (rank_lt_iff _).mp
      rw [← hy, rank_smul _ (inv_ne_zero hx0)]
      exact hr
    obtain ⟨i,hsi⟩ := (hmin s).mp hs
    have he : x = x 0 • point (t i) := by
      rw [← hsi, ← hy, smul_smul, mul_inv_cancel₀ hx0, one_smul]
    refine ⟨i,⟨x 0,hx0,he⟩,?_⟩
    rintro j ⟨c,hc,hj⟩
    have hce : c = x 0 := scalar_unique (t j) (t i) c (x 0) (hj.symm.trans he)
    apply ht
    apply point_injective
    apply (smul_right_injective _ hx0)
    change x 0 • point (t j) = x 0 • point (t i)
    rw [← hce, ← hj, hce, ← he]
  · rintro ⟨i,⟨c,hc,rfl⟩,_⟩
    rw [rank_smul c hc]
    exact hi i
end PencilDirections

end

end OAI
