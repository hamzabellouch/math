import OAI.Analysis.KadisonKastler.MatrixCornerAutomorphism

namespace OAI

/-! # The cocycle obtained from an action fixing matrix corners -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
  (α : Multiplicative ℝ →* (CStarMatrix (Fin 2) (Fin 2) A ≃⋆ₐ[ℂ]
    CStarMatrix (Fin 2) (Fin 2) A))
  (hfix : ∀ t i, α t (matrixSlot i i 1) = matrixSlot i i 1)

def matrixCornerAction (i : Fin 2) : Multiplicative ℝ →* (A ≃⋆ₐ[ℂ] A) where
  toFun t := matrixCornerAut (α t) i (hfix t i)
  map_one' := by
    apply StarAlgEquiv.ext
    intro a
    change α 1 (matrixSlot i i a) i i = a
    rw [map_one]
    simp [matrixSlot]
  map_mul' s t := by
    apply StarAlgEquiv.ext
    intro a
    change α (s * t) (matrixSlot i i a) i i =
      α s (matrixSlot i i (α t (matrixSlot i i a) i i)) i i
    rw [map_mul]
    change α s (α t (matrixSlot i i a)) i i = _
    exact congrArg (fun x => α s x i i)
      (matrixSlot_image_reconstruct (α t) i i (hfix t i) (hfix t i) a)

def matrixActionCocycleValue (t : Multiplicative ℝ) : unitary A :=
  ⟨matrixOffDiagonalCoefficient (α t),
    matrixOffDiagonalCoefficient_unitary (α t) (hfix t 0) (hfix t 1)⟩

theorem matrixActionCocycleValue_mul (s t : Multiplicative ℝ) :
    (matrixActionCocycleValue α hfix (s * t) : A) =
      (matrixActionCocycleValue α hfix s : A) *
        matrixCornerAction α hfix 0 s (matrixActionCocycleValue α hfix t : A) := by
  let c (r : Multiplicative ℝ) := matrixOffDiagonalCoefficient (α r)
  have he (r : Multiplicative ℝ) : α r (matrixSlot 1 0 1) = matrixSlot 1 0 (c r) :=
    matrixSlot_image_reconstruct (α r) 1 0 (hfix r 1) (hfix r 0) 1
  have hx : matrixSlot 1 0 (c t) = matrixSlot 1 0 1 * matrixSlot 0 0 (c t) := by
    rw [matrixSlot_mul, one_mul]
  have h : α (s * t) (matrixSlot 1 0 1) =
      matrixSlot 1 0 (c s * (α s (matrixSlot 0 0 (c t)) 0 0)) := by
    rw [map_mul]
    change α s (α t (matrixSlot 1 0 1)) = _
    calc
      α s (α t (matrixSlot 1 0 1)) =
          matrixSlot 1 0 (c s) * α s (matrixSlot 0 0 (c t)) := by
        rw [he t, hx, map_mul, he s]
      _ = matrixSlot 1 0 (c s) *
          matrixSlot 0 0 (α s (matrixSlot 0 0 (c t)) 0 0) :=
        congrArg (fun x => matrixSlot 1 0 (c s) * x)
          (matrixSlot_image_reconstruct (α s) 0 0 (hfix s 0) (hfix s 0) (c t))
      _ = _ := matrixSlot_mul 1 0 0 _ _
  rw [he (s * t)] at h
  exact matrixSlot_injective 1 0 h

theorem matrixCornerAction_conjugate (t : Multiplicative ℝ) (a : A) :
    matrixCornerAction α hfix 1 t a =
      (matrixActionCocycleValue α hfix t : A) * matrixCornerAction α hfix 0 t a *
        star (matrixActionCocycleValue α hfix t : A) :=
  matrixCorner_actions_conjugate (α t) (hfix t 0) (hfix t 1) a

end

end KadisonKastler

end OAI
