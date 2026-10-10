import OAI.Analysis.TracialSplitting.GNSRepresentations
import OAI.Analysis.OperatorAlgebra.CyclicStateNorm

namespace OAI

/-! The cyclic vector argument for the algebraic tracial multiplication
representation. -/

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a * b) = f (b * a))

@[irreducible] def traceTensor : A ⊗[ℂ] Aᵐᵒᵖ →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
  Pureness.commutingStarTensorHom f.gnsStarAlgHom
    (NuclearTrace.rightGNS f ht) (NuclearTrace.left_right_commute f ht)

lemma traceTensor_vector (a b : A) :
    traceTensor f ht (a ⊗ₜ[ℂ] MulOpposite.op b) (f.toPreGNS 1 : f.GNS) =
      (f.toPreGNS (a * b) : f.GNS) := by
  unfold traceTensor
  change f.gnsStarAlgHom a
    (NuclearTrace.rightGNS f ht (MulOpposite.op b) (f.toPreGNS 1 : f.GNS)) = _
  simp [PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.leftMulMapPreGNS]

lemma traceTensor_cyclic :
    DenseRange (fun z => traceTensor f ht z (f.toPreGNS 1 : f.GNS)) := by
  have hd : DenseRange (fun x : f.PreGNS => (x : f.GNS)) :=
    UniformSpace.Completion.denseRange_coe
  apply hd.mono
  rintro _ ⟨x, rfl⟩
  refine ⟨f.ofPreGNS x ⊗ₜ[ℂ] MulOpposite.op (1 : A), ?_⟩
  change traceTensor f ht (f.ofPreGNS x ⊗ₜ[ℂ] MulOpposite.op 1)
    (f.toPreGNS 1 : f.GNS) = (x : f.GNS)
  rw [traceTensor_vector, mul_one, PositiveLinearMap.toPreGNS_ofPreGNS]

omit [StarOrderedRing B] in
lemma traceTensor_vector_state (q : A ⊗[ℂ] Aᵐᵒᵖ →⋆ₐ[ℂ] B) (φ : B →ₚ[ℂ] ℂ)
    (hφ : ∀ a b : A, φ (q (a ⊗ₜ[ℂ] MulOpposite.op b)) = f (a * b))
    (w : A ⊗[ℂ] Aᵐᵒᵖ) :
    φ (q w) = inner ℂ (f.toPreGNS 1 : f.GNS)
      (traceTensor f ht w (f.toPreGNS 1)) := by
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
    have he : φ (q (a ⊗ₜ[ℂ] MulOpposite.op b.unop)) =
        inner ℂ (f.toPreGNS 1 : f.GNS)
          (traceTensor f ht (a ⊗ₜ[ℂ] MulOpposite.op b.unop) (f.toPreGNS 1)) := by
      rw [hφ, traceTensor_vector, UniformSpace.Completion.inner_coe,
        PositiveLinearMap.preGNS_inner_def]
      simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul]
    simpa only [MulOpposite.op_unop] using he
  | add x y hx hy =>
    simp only [map_add, add_apply, inner_add_right, hx, hy]

lemma traceTensor_vector_norm (q : A ⊗[ℂ] Aᵐᵒᵖ →⋆ₐ[ℂ] B) (φ : B →ₚ[ℂ] ℂ)
    (hφ : ∀ a b : A, φ (q (a ⊗ₜ[ℂ] MulOpposite.op b)) = f (a * b))
    (z : A ⊗[ℂ] Aᵐᵒᵖ) :
    ‖traceTensor f ht z (f.toPreGNS 1 : f.GNS)‖ = ‖φ.toPreGNS (q z)‖ := by
  rw [PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, ← map_star q, ← map_mul q,
    traceTensor_vector_state f ht q φ hφ]
  simp only [map_mul, map_star, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hn : (inner ℂ (traceTensor f ht z (f.toPreGNS 1 : f.GNS))
      (traceTensor f ht z (f.toPreGNS 1 : f.GNS))).re =
      ‖traceTensor f ht z (f.toPreGNS 1 : f.GNS)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hn, Real.sqrt_sq (norm_nonneg _)]

lemma traceTensor_norm_le (q : A ⊗[ℂ] Aᵐᵒᵖ →⋆ₐ[ℂ] B) (φ : B →ₚ[ℂ] ℂ)
    (hφ : ∀ a b : A, φ (q (a ⊗ₜ[ℂ] MulOpposite.op b)) = f (a * b))
    (z : A ⊗[ℂ] Aᵐᵒᵖ) : ‖traceTensor f ht z‖ ≤ ‖q z‖ := by
  have hn := traceTensor_vector_norm f ht q φ hφ
  have hm : ‖φ.leftMulMapPreGNS (q z)‖ ≤ ‖q z‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  apply (traceTensor f ht z).opNorm_le_bound (norm_nonneg _)
  refine isClosed_property (traceTensor_cyclic f ht)
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro b
  calc
    ‖traceTensor f ht z (traceTensor f ht b (f.toPreGNS 1 : f.GNS))‖ =
        ‖traceTensor f ht (z * b) (f.toPreGNS 1 : f.GNS)‖ := by rw [map_mul]; rfl
    _ = ‖φ.toPreGNS (q (z * b))‖ := hn (z * b)
    _ = ‖φ.leftMulMapPreGNS (q z) (φ.toPreGNS (q b))‖ := by
      simp only [map_mul, PositiveLinearMap.leftMulMapPreGNS_apply,
        PositiveLinearMap.ofPreGNS_toPreGNS]
    _ ≤ ‖φ.leftMulMapPreGNS (q z)‖ * ‖φ.toPreGNS (q b)‖ :=
      (φ.leftMulMapPreGNS (q z)).le_opNorm _
    _ ≤ ‖q z‖ * ‖φ.toPreGNS (q b)‖ :=
      mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ = ‖q z‖ * ‖traceTensor f ht b (f.toPreGNS 1 : f.GNS)‖ := by rw [hn b]

end WeakPureInfiniteness

end

end OAI
