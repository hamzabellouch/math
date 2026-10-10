import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.IncidenceDisconnected

variable {V E : Type*}

def EndpointAdj (src dst : E → V) (u v : V) : Prop :=
  ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)

theorem reachable_endpoints_iff (src dst : E → V) (r : V) (e : E) :
    Relation.ReflTransGen (EndpointAdj src dst) r (src e) ↔
      Relation.ReflTransGen (EndpointAdj src dst) r (dst e) := by
  constructor
  · intro h
    exact h.tail ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  · intro h
    exact h.tail ⟨e, Or.inr ⟨rfl, rfl⟩⟩

variable [Fintype V] [DecidableEq V]

def reducedIncidence (r : V) (src dst : E → V) :
    Matrix {v : V // v ≠ r} E ℝ :=
  fun v e => (if v.1 = src e then 1 else 0) - (if v.1 = dst e then 1 else 0)

theorem sum_reduced_indicator (r : V) (f : V → ℝ) (hr : f r = 0) (v : V) :
    (∑ i : {v : V // v ≠ r}, f i.1 * (if i.1 = v then 1 else 0)) = f v := by
  by_cases hv : v = r
  · subst v
    rw [hr]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [ite_eq_right i.property, mul_zero]
  · have heq (i : {v : V // v ≠ r}) : i.1 = v ↔ i = ⟨v, hv⟩ :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [mul_ite, mul_one, mul_zero, heq]
    simp

theorem vecMul_reducedIncidence (r : V) (src dst : E → V)
    (f : V → ℝ) (hr : f r = 0) :
    (fun i : {v : V // v ≠ r} => f i.1) ᵥ* reducedIncidence r src dst =
      fun e => f (src e) - f (dst e) := by
  ext e
  simp only [Matrix.vecMul, dotProduct, reducedIncidence, mul_sub, Finset.sum_sub_distrib]
  rw [sum_reduced_indicator r f hr, sum_reduced_indicator r f hr]

theorem exists_nonzero_vecMul_reducedIncidence_eq_zero
    (r : V) (src dst : E → V)
    (hdis : ¬ ∀ v, Relation.ReflTransGen (EndpointAdj src dst) r v) :
    ∃ f : {v : V // v ≠ r} → ℝ, f ≠ 0 ∧ f ᵥ* reducedIncidence r src dst = 0 := by
  classical
  obtain ⟨v, hv⟩ := not_forall.mp hdis
  let f : V → ℝ := fun w => if Relation.ReflTransGen (EndpointAdj src dst) r w then 0 else 1
  have hr : f r = 0 := by simp [f, Relation.ReflTransGen.refl]
  have hvr : v ≠ r := by
    intro heq
    subst v
    exact hv Relation.ReflTransGen.refl
  refine ⟨fun w => f w.1, ?_, ?_⟩
  · intro hz
    have h := congr_fun hz ⟨v, hvr⟩
    simp [f, hv] at h
  · rw [vecMul_reducedIncidence r src dst f hr]
    funext e
    have heq := reachable_endpoints_iff src dst r e
    simp only [f, heq, sub_self, Pi.zero_apply]

theorem det_reducedIncidence_eq_zero_of_not_connected
    (r : V) (src dst : {v : V // v ≠ r} → V)
    (hdis : ¬ ∀ v, Relation.ReflTransGen (EndpointAdj src dst) r v) :
    (reducedIncidence r src dst).det = 0 := by
  exact Matrix.exists_vecMul_eq_zero_iff.mp
    (exists_nonzero_vecMul_reducedIncidence_eq_zero r src dst hdis)

theorem det_reindexed_reducedIncidence_eq_zero_of_not_connected
    (r : V) (src dst : E → V) (e : {v : V // v ≠ r} ≃ E)
    (hdis : ¬ ∀ v, Relation.ReflTransGen (EndpointAdj src dst) r v) :
    ((reducedIncidence r src dst).submatrix id e).det = 0 := by
  obtain ⟨f, hf, hkernel⟩ := exists_nonzero_vecMul_reducedIncidence_eq_zero r src dst hdis
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨f, hf, ?_⟩
  ext j
  exact congr_fun hkernel (e j)

theorem det_reducedLaplacian_eq_zero_of_not_connected
    [Fintype E] [DecidableEq E] (r : V) (src dst : E → V) (c : E → ℝ)
    (hdis : ¬ ∀ v, Relation.ReflTransGen (EndpointAdj src dst) r v) :
    (reducedIncidence r src dst * Matrix.diagonal c * (reducedIncidence r src dst).transpose).det = 0 := by
  obtain ⟨f, hf, hkernel⟩ := exists_nonzero_vecMul_reducedIncidence_eq_zero r src dst hdis
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨f, hf, ?_⟩
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hkernel]
  simp

theorem connected_of_det_reducedIncidence_ne_zero
    (r : V) (src dst : {v : V // v ≠ r} → V)
    (hdet : (reducedIncidence r src dst).det ≠ 0) :
    ∀ v, Relation.ReflTransGen (EndpointAdj src dst) r v := by
  by_contra hdis
  exact hdet (det_reducedIncidence_eq_zero_of_not_connected r src dst hdis)

end Problem336.IncidenceDisconnected

end

end OAI
