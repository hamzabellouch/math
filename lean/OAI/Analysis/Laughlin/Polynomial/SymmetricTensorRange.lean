import OAI.Analysis.Laughlin.Polynomial.SymmetricTensorOrbit

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem tensorWeight_le (Q : ℕ) (a : Fin Q → Fin 2) : tensorWeight Q a ≤ Q := by
  have h := Finset.card_le_card (Finset.filter_subset (fun i => a i=1) (Finset.univ : Finset (Fin Q)))
  simpa [tensorWeight,tensorBits] using h

 theorem tensorWeight_surjective (Q : ℕ) (p : Fin (Q+1)) : ∃ a : Fin Q → Fin 2, tensorWeight Q a=p.val := by
  by_contra h
  push Not at h
  have hc := tensorWeight_count Q p.val
  simp only [ite_eq_right (h _),Finset.sum_const_zero] at hc
  have hp : (0 : ℝ) < Q.choose p.val := by exact_mod_cast Nat.choose_pos (by omega : p.val ≤ Q)
  linarith

noncomputable def tensorWeightRepresentative (Q : ℕ) (p : Fin (Q+1)) : Fin Q → Fin 2 :=
  Classical.choose (tensorWeight_surjective Q p)
 theorem tensorWeightRepresentative_weight (Q : ℕ) (p : Fin (Q+1)) :
    tensorWeight Q (tensorWeightRepresentative Q p)=p.val := Classical.choose_spec (tensorWeight_surjective Q p)

noncomputable def symmetricTensorInclusion (Q : ℕ) : Matrix (Fin Q → Fin 2) (Fin (Q+1)) ℂ :=
  (symmetricTensorInclusionReal Q).map Complex.ofReal

theorem symmetricTensorInclusion_isometry (Q : ℕ) :
    (symmetricTensorInclusion Q)ᴴ * symmetricTensorInclusion Q=1 := by
  ext p q
  have h := congrArg Complex.ofReal (congrFun (congrFun (symmetricTensorInclusionReal_isometry Q) p) q)
  simpa [symmetricTensorInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
    Matrix.one_apply,apply_ite] using h

 theorem symmetricTensorInclusion_mulVec (Q : ℕ) (w : Fin (Q+1) → ℂ) (a : Fin Q → Fin 2) :
    (symmetricTensorInclusion Q *ᵥ w) a =
      ((Real.sqrt (Q.choose (tensorWeight Q a) : ℝ))⁻¹ : ℂ) *
        w ⟨tensorWeight Q a,by have := tensorWeight_le Q a; omega⟩ := by
  classical
  let p : Fin (Q+1) := ⟨tensorWeight Q a,by have := tensorWeight_le Q a; omega⟩
  change (∑ q, (symmetricTensorInclusion Q) a q * w q) = _
  rw [Finset.sum_eq_single p]
  · simp [symmetricTensorInclusion,symmetricTensorInclusionReal,p]
  · intro q hq hqp
    have hn : tensorWeight Q a ≠ q.val := by intro h; exact hqp (Fin.ext h.symm)
    simp [symmetricTensorInclusion,symmetricTensorInclusionReal,hn]
  · simp

theorem symmetricTensor_range (Q : ℕ) (v : (Fin Q → Fin 2) → ℂ)
    (hv : ∀ a b, tensorWeight Q a=tensorWeight Q b → v a=v b) :
    ∃ w : Fin (Q+1) → ℂ, symmetricTensorInclusion Q *ᵥ w=v := by
  let w : Fin (Q+1) → ℂ := fun p => (Real.sqrt (Q.choose p.val : ℝ) : ℂ) *
    v (tensorWeightRepresentative Q p)
  refine ⟨w,?_⟩
  funext a
  rw [symmetricTensorInclusion_mulVec]
  dsimp [w]
  have hn : (Real.sqrt (Q.choose (tensorWeight Q a) : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast Nat.choose_pos (tensorWeight_le Q a)
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
  apply hv
  exact tensorWeightRepresentative_weight Q _

 theorem symmetricTensor_projector_fixed (Q : ℕ) (v : (Fin Q → Fin 2) → ℂ)
    (hv : ∀ a b, tensorWeight Q a=tensorWeight Q b → v a=v b) :
    (symmetricTensorInclusion Q*(symmetricTensorInclusion Q)ᴴ) *ᵥ v=v := by
  obtain ⟨w,rfl⟩ := symmetricTensor_range Q v hv
  rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,symmetricTensorInclusion_isometry,Matrix.mul_one]

end Laughlin.Rotation

end OAI
