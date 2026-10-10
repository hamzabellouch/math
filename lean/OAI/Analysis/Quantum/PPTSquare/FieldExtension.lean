import OAI.Analysis.Quantum.PPTSquare.Evaluation

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Matrix Polynomial PencilAlgebra PencilEvaluation
namespace PencilExtension
variable {K F : Type*} [Field K] [Field F]
lemma action_map (φ : K →+* F) (a : Fin 3) : (action (K := K) a).map φ = action (K := F) a := by
  ext i j
  simp [action]
lemma lowMon_map (φ : K →+* F) (t : Fin 3 → K) (j : Fin 20) :
    φ (lowMon t j) = lowMon (fun a => φ (t a)) j := by
  simp [lowMon]
lemma evaluation_map (φ : K →+* F) (t : Fin 20 → Fin 3 → K) :
    (evaluation t).map φ = evaluation (fun i a => φ (t i a)) := by
  ext i j
  exact lowMon_map φ (t i) j
lemma diagonal_map (φ : K →+* F) (r : Fin 20 → K) :
    (diagonal r).map φ = diagonal (fun i => φ (r i)) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply, h]
lemma data_map (φ : K →+* F) (t : Fin 20 → Fin 3 → K) (r : Fin 20 → K)
    (hr : Function.Injective r)
    (hf : (action (K := K) 0).charpoly = ∏ i, (X-C (r i)))
    (hu : IsUnit (evaluation t))
    (he : ∀ a, evaluation t * action a = diagonal (fun i => (denominator : K)*t i a) * evaluation t)
    (ht : ∀ i, (denominator : K)*t i 0 = r i)
    (hm : ∀ j : Fin 10 → Fin 20, Function.Injective j →
      IsUnit ((evaluation t).submatrix j (fun k : Fin 10 => k.castLE (by decide)))) :
    Function.Injective (fun i => φ (r i)) ∧
    ((action (K := F) 0).charpoly = ∏ i, (X-C (φ (r i)))) ∧
    IsUnit (evaluation (fun i a => φ (t i a))) ∧
    (∀ a, evaluation (fun i a => φ (t i a)) * action a =
      diagonal (fun i => (denominator : F)*φ (t i a)) * evaluation (fun i a => φ (t i a))) ∧
    (∀ i, (denominator : F)*φ (t i 0) = φ (r i)) ∧
    (∀ j : Fin 10 → Fin 20, Function.Injective j →
      IsUnit ((evaluation (fun i a => φ (t i a))).submatrix j (fun k : Fin 10 => k.castLE (by decide)))) := by
  refine ⟨φ.injective.comp hr, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := congrArg (Polynomial.map φ) hf
    rw [← Matrix.charpoly_map, action_map] at hh
    simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using hh
  · rw [← evaluation_map φ t]
    exact hu.map φ.mapMatrix
  · intro a
    have hh := congrArg (fun A : Matrix (Fin 20) (Fin 20) K => A.map φ) (he a)
    rw [Matrix.map_mul, Matrix.map_mul, action_map, evaluation_map, diagonal_map] at hh
    simpa only [map_mul, map_intCast] using hh
  · intro i
    simpa only [map_mul, map_intCast] using congrArg φ (ht i)
  · intro j hj
    rw [← evaluation_map φ t]
    exact (hm j hj).map φ.mapMatrix
end PencilExtension

end

end OAI
