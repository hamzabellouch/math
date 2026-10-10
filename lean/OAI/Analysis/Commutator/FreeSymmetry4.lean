import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry
import OAI.Analysis.Commutator.FreeSymmetry2
import OAI.Analysis.Commutator.FreeSymmetry3

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {k l : ℕ} (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

include h1 in
theorem stageCoefficient_crossing (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c : (Fin k ≃ Fin l) → ℂ, ∀ n (a : Matrix (I n) (I n) ℂ)
      (v : TailSlots k l → Matrix (I n) (I n) ℂ), (∀ j, Matrix.trace (v j) = 0) →
      stageCoefficient τ Y (φ n) (fun o => o.elim a v) =
        ((Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace a) *
          ∑ b : Fin k ≃ Fin l, c b * ∏ i,
            ((Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace (v (.inl i) * v (.inr (b i)))) := by
  classical
  obtain ⟨d₀, hexp₀, hd₀⟩ := stageCoefficient_cycleCutoff τ hτ h1 Y I φ e he hsize hY hleft
  let d : Equiv.Perm (Option (TailSlots k l)) → ℂ := d₀
  have hexp (n) (v : Option (TailSlots k l) → Matrix (I n) (I n) ℂ) :
      stageCoefficient τ Y (φ n) v = ∑ σ, d σ * SchurWeyl.cycleTrace σ v := hexp₀ n v
  have hd (σ : Equiv.Perm (Option (TailSlots k l)))
      (hσ : 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (TailSlots k l)) + 1) :
      d σ = 0 := hd₀ σ hσ
  let c : Pairing (TailSlots k l) → ℂ := fun σ => d (SchurWeyl.endpointPairingPerm σ)
  have hc (n) (v : TailSlots k l → Matrix (I n) (I n) ℂ) (hv : ∀ j, (v j).trace = 0) :
      stageCoefficient τ Y (φ n) (fun o => o.elim (1 : Matrix (I n) (I n) ℂ) v) =
        ∑ σ, c σ * Pairing.contraction σ
          (fun X Z => (Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace (X * Z)) v :=
    stage_pairing_expansion τ Y (φ n) d hd (hexp n) v hv
  have hz (σ : Pairing (TailSlots k l)) (hσ : ¬ σ.Crosses) : c σ = 0 :=
    stage_pairing_same_side_zero τ hτ h1 Y I φ
      (fun q => let ⟨m, hm⟩ := hsize 0 q; ⟨m, hm.2⟩) c hc σ
      ((Pairing.not_crosses_iff_same_side σ).mp hσ)
  refine ⟨fun b => c (Pairing.crossPairing b), ?_⟩
  intro n a v hv
  have hh := SchurWeyl.centered_expansion_contractions d hd
    (fun o : Option (TailSlots k l) => o.elim a v) (fun j => hv j)
  have hs := Pairing.sum_contraction_crossing
    (fun X Z : Matrix (I n) (I n) ℂ => (Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace (X * Z)) v c hz
  have hh' : (∑ σ, d σ * SchurWeyl.cycleTrace σ (fun o : Option (TailSlots k l) => o.elim a v)) =
      ((Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace a) *
        ∑ σ, c σ * Pairing.contraction σ
          (fun X Z => (Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace (X * Z)) v := hh
  rw [hs] at hh'
  exact (hexp n (fun o : Option (TailSlots k l) => o.elim a v)).trans hh'

end Kadison.TracialGNS
end

end OAI
