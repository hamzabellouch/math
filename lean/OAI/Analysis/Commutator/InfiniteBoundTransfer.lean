import Mathlib
import OAI.Analysis.Commutator.CommutatorPerturbation
import OAI.Analysis.Commutator.InfiniteCenter
import OAI.Analysis.Commutator.RepresentationMatrixNorm
import OAI.Analysis.Commutator.IntertwinerMatrixTransfer

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

local instance infiniteBoundTransferDecidableEq {α : Sort*} : DecidableEq α := Classical.decEq α

open scoped InnerProductSpace ComplexOrder

namespace Kadison.InfiniteAmplification

open IntertwinerCompression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def single0 : H →ₗᵢ[ℂ] Space ℕ H :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 0).toLinearMap.isometryOfInner
    (fun x y => by
      change inner ℂ (lp.single (E:=fun _ : ℕ => H) 2 0 x)
        (lp.single (E:=fun _ : ℕ => H) 2 0 y)=inner ℂ x y
      rw [lp.inner_single_left,lp.single_apply,Pi.single_eq_same])

lemma single0_adjoint : (single0 (H:=H)).toContinuousLinearMap.adjoint=
    lp.evalCLM ℂ (fun _ : ℕ => H) 2 0 := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  exact (lp.inner_single_right (𝕜:=ℂ) 0 y x).symm

omit [CompleteSpace H] in
lemma single0_intertwines (T : H →L[ℂ] H) :
    (single0 (H:=H)).toContinuousLinearMap.comp T=(map T).comp single0.toContinuousLinearMap := by
  ext x i
  change lp.single (E:=fun _ : ℕ => H) 2 0 (T x) i=T (lp.single (E:=fun _ : ℕ => H) 2 0 x i)
  by_cases hi : i=0 <;> simp [lp.single_apply,hi]

lemma pullback_map (Y : H →L[ℂ] H) :
    transfer (single0 (H:=H)).toContinuousLinearMap.adjoint (map Y)=Y := by
  rw [transfer,ContinuousLinearMap.adjoint_adjoint,single0_adjoint]
  ext x
  change Y (lp.single (E:=fun _ : ℕ => H) 2 0 x 0)=Y x
  simp only [lp.single_apply,Pi.single_eq_same]

lemma seminorm_map_le (M : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    commutatorSeminorm (algebra M) (map Y)≤commutatorSeminorm M Y := by
  apply commutatorSeminorm_le
  rintro _ ⟨a,rfl⟩ ha
  change ‖diagonal (ι:=ℕ) (H:=H) Y*diagonal (ι:=ℕ) (H:=H) a.val-
    diagonal (ι:=ℕ) (H:=H) a.val*diagonal (ι:=ℕ) (H:=H) Y‖≤_
  rw [←map_mul,←map_mul,←map_sub]
  change ‖map (ι:=ℕ) (Y*a.val-a.val*Y)‖≤_
  rw [map_norm]
  exact commutator_bound_unitball M Y a.property (by
    change ‖map (ι:=ℕ) a.val‖≤1 at ha
    rwa [map_norm] at ha)

theorem bound_of_stable_bound (M : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M)
    {c : ℝ} (hc : 0≤c)
    (hb : ‖diagonalAmplification h (map Y)*matrixOperator h (fun i j => map (ι:=ℕ) (X i j))-
      matrixOperator h (fun i j => map (ι:=ℕ) (X i j))*diagonalAmplification h (map Y)‖≤
      c*commutatorSeminorm (algebra M) (map Y)*‖matrixOperator h (fun i j => map (ι:=ℕ) (X i j))‖) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm M Y*‖matrixOperator h X‖ := by
  let ψ := (diagonal (ι:=ℕ) (H:=H)).comp M.subtype
  have hT : ∀ a : M,single0.toContinuousLinearMap.comp (a:H →L[ℂ] H)=
      (ψ a).comp single0.toContinuousLinearMap := fun a => single0_intertwines a.val
  have hnorm : ‖(single0 (H:=H)).toContinuousLinearMap‖≤1 :=
    (single0 (H:=H)).norm_toContinuousLinearMap_le
  have hp := pullback_matrix_commutator_norm_le (A:=M) (H:=H) (G:=Space ℕ H)
    M.subtype ψ (single0 (H:=H)).toContinuousLinearMap hT
    hnorm h (fun i j => ⟨X i j,hX i j⟩) (map Y)
  rw [pullback_map] at hp
  apply hp.trans (hb.trans ?_)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (seminorm_map_le M Y) hc)
    (matrixOperator_subtype_norm_le M ψ h X hX) (norm_nonneg _)
    (mul_nonneg hc (commutatorSeminorm_nonneg M Y))

end Kadison.InfiniteAmplification

end

end
end

end OAI
