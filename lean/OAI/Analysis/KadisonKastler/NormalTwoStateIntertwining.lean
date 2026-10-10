import OAI.Analysis.KadisonKastler.NormalTwoStatePartialIsometry

namespace OAI

/-! # The corner unitary intertwines the original representations -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
  (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))

def normalTwoStateDiagonal (a : Algebra M) :
    TwoStateMatrixHilbert H K →L[ℂ] TwoStateMatrixHilbert H K :=
  normalTwoStateSlot θ hθ 0 0 a + normalTwoStateSlot θ hθ 1 1 a

theorem normalTwoStateDiagonal_fst (a : Algebra M) (x : TwoStateMatrixHilbert H K) (r : Fin 2) :
    (normalTwoStateDiagonal θ hθ a x).fst r = a.val (x.fst r) := by
  change (normalTwoStateSlot θ hθ 0 0 a x).fst r +
    (normalTwoStateSlot θ hθ 1 1 a x).fst r = _
  rw [normalTwoStateSlot_fst, normalTwoStateSlot_fst]
  fin_cases r <;> simp

theorem normalTwoStateDiagonal_snd (a : Algebra M) (x : TwoStateMatrixHilbert H K) (r : Fin 2) :
    (normalTwoStateDiagonal θ hθ a x).snd r = (θ a).val (x.snd r) := by
  change (normalTwoStateSlot θ hθ 0 0 a x).snd r +
    (normalTwoStateSlot θ hθ 1 1 a x).snd r = _
  rw [normalTwoStateSlot_snd, normalTwoStateSlot_snd]
  fin_cases r <;> simp

theorem normalTwoStateDiagonal_source (a : Algebra M) (x : H) :
    normalTwoStateDiagonal θ hθ a (twoStateSourceEmbedding x) =
      twoStateSourceEmbedding (a.val x) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro r
  · change (normalTwoStateDiagonal θ hθ a (twoStateSourceEmbedding x)).fst r =
      tupleSingle 0 (a.val x) r
    rw [show (normalTwoStateDiagonal θ hθ a (twoStateSourceEmbedding x)).fst r =
      a.val ((twoStateSourceEmbedding x).fst r) from normalTwoStateDiagonal_fst θ hθ a _ r]
    change a.val (tupleSingle 0 x r) = tupleSingle 0 (a.val x) r
    fin_cases r <;> simp [tupleSingle_apply]
  · change (normalTwoStateDiagonal θ hθ a (twoStateSourceEmbedding x)).snd r = 0
    rw [show (normalTwoStateDiagonal θ hθ a (twoStateSourceEmbedding x)).snd r =
      (θ a).val ((twoStateSourceEmbedding x).snd r) from normalTwoStateDiagonal_snd θ hθ a _ r]
    change (θ a).val 0 = 0
    exact map_zero _

theorem normalTwoStateDiagonal_commutes_slot (a : Algebra M) :
    normalTwoStateDiagonal θ hθ a * normalTwoStateSlot θ hθ 1 0 1 =
      normalTwoStateSlot θ hθ 1 0 1 * normalTwoStateDiagonal θ hθ a := by
  ext x
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro r
  · change (normalTwoStateDiagonal θ hθ a (normalTwoStateSlot θ hθ 1 0 1 x)).fst r =
      (normalTwoStateSlot θ hθ 1 0 1 (normalTwoStateDiagonal θ hθ a x)).fst r
    rw [normalTwoStateDiagonal_fst, normalTwoStateSlot_fst,
      normalTwoStateSlot_fst, normalTwoStateDiagonal_fst]
    fin_cases r <;> simp
  · change (normalTwoStateDiagonal θ hθ a (normalTwoStateSlot θ hθ 1 0 1 x)).snd r =
      (normalTwoStateSlot θ hθ 1 0 1 (normalTwoStateDiagonal θ hθ a x)).snd r
    rw [normalTwoStateDiagonal_snd, normalTwoStateSlot_snd,
      normalTwoStateSlot_snd, normalTwoStateDiagonal_snd]
    fin_cases r <;> simp

variable (Ω : H) (ξ : K)
  (hcyc : DenseRange (algebraVectorMap (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ)))
  (d : ModularConjugationData (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ))

theorem normalTwoStateBridge_commutes (a : Algebra M) :
    normalTwoStateBridge θ hθ Ω ξ d * normalTwoStateDiagonal θ hθ a =
      normalTwoStateDiagonal θ hθ a * normalTwoStateBridge θ hθ Ω ξ d := by
  have hq := d.right_mem le_rfl (normalTwoStateEquiv θ hθ (matrixSlot 1 0 1))
  have hd : normalTwoStateDiagonal θ hθ a ∈ normalTwoStateAlgebra θ :=
    (normalTwoStateAlgebra θ).add_mem
      (normalTwoStateEquiv θ hθ (matrixSlot 0 0 a)).property
      (normalTwoStateEquiv θ hθ (matrixSlot 1 1 a)).property
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp hq _ hd
  change normalTwoStateDiagonal θ hθ a *
    conjugationOperator d.conjugation (normalTwoStateSlot θ hθ 1 0 1) =
      conjugationOperator d.conjugation (normalTwoStateSlot θ hθ 1 0 1) *
        normalTwoStateDiagonal θ hθ a at hc
  unfold normalTwoStateBridge
  rw [mul_assoc, ← hc, ← mul_assoc, ← normalTwoStateDiagonal_commutes_slot, mul_assoc]

include hcyc in
def normalTwoStateUnitary : H ≃ₗᵢ[ℂ] K :=
  partialIsometryCornerEquiv twoStateSourceEmbedding twoStateTargetEmbedding
    (normalTwoStateBridge θ hθ Ω ξ d)
    (normalTwoStateBridge_initial θ hθ Ω ξ hcyc d)
    (normalTwoStateBridge_final θ hθ Ω ξ hcyc d)

theorem normalTwoStateUnitary_intertwines (a : Algebra M) (x : H) :
    normalTwoStateUnitary θ hθ Ω ξ hcyc d (a.val x) =
      (θ a).val (normalTwoStateUnitary θ hθ Ω ξ hcyc d x) := by
  simp only [normalTwoStateUnitary, partialIsometryCornerEquiv_apply,
    twoStateTargetEmbedding_adjoint]
  change (normalTwoStateBridge θ hθ Ω ξ d
    (twoStateSourceEmbedding (a.val x))).snd 1 =
      (θ a).val ((normalTwoStateBridge θ hθ Ω ξ d (twoStateSourceEmbedding x)).snd 1)
  rw [← normalTwoStateDiagonal_source θ hθ a x]
  have hc := congrArg (fun T : TwoStateMatrixHilbert H K →L[ℂ] TwoStateMatrixHilbert H K =>
    T (twoStateSourceEmbedding x)) (normalTwoStateBridge_commutes θ hθ Ω ξ d a)
  change normalTwoStateBridge θ hθ Ω ξ d
      (normalTwoStateDiagonal θ hθ a (twoStateSourceEmbedding x)) =
    normalTwoStateDiagonal θ hθ a
      (normalTwoStateBridge θ hθ Ω ξ d (twoStateSourceEmbedding x)) at hc
  rw [hc, normalTwoStateDiagonal_snd]

end

end KadisonKastler

end OAI
