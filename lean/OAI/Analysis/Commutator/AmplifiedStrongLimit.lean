import Mathlib
import OAI.Analysis.Commutator.Definitions
import OAI.Analysis.Commutator.StrongContractionLimit

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open Filter

namespace Kadison.StrongContractionLimit

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {l : Filter ι}

omit [CompleteSpace H] in
lemma piLp_tendsto {κ : Type*} [Fintype κ] (u : ι → PiLp 2 (fun _ : κ => H))
    (x : PiLp 2 (fun _ : κ => H)) (hu : ∀ k,Tendsto (fun i => u i k) l (𝓝 (x k))) :
    Tendsto u l (𝓝 x) := by
  have h := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => H)).symm.continuous.tendsto
    (fun k => x k)
  exact h.comp (tendsto_pi_nhds.mpr hu)

omit [CompleteSpace H] in
lemma diagonal_tendsto (P : ι → H →L[ℂ] H) (Y : H →L[ℂ] H)
    (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 (Y x)))
    (h : ℕ) (x : PiLp 2 (fun _ : Fin h => H)) :
    Tendsto (fun i => diagonalAmplification h (P i) x) l (𝓝 (diagonalAmplification h Y x)) := by
  apply piLp_tendsto
  intro k
  exact hstrong (x k)

omit [CompleteSpace H] in
lemma commutator_tendsto (P : ι → H →L[ℂ] H) (Y : H →L[ℂ] H)
    (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 (Y x)))
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : Fin h => H)) :
    Tendsto (fun i => (diagonalAmplification h (P i)*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h (P i)) x) l
      (𝓝 ((diagonalAmplification h Y*matrixOperator h X-
        matrixOperator h X*diagonalAmplification h Y) x)) := by
  exact (diagonal_tendsto P Y hstrong h (matrixOperator h X x)).sub
    (((matrixOperator h X).continuous.tendsto (diagonalAmplification h Y x)).comp
      (diagonal_tendsto P Y hstrong h x))

omit [CompleteSpace H] in
lemma commutator_bound_limit [l.NeBot] (P : ι → H →L[ℂ] H) (Y : H →L[ℂ] H)
    (hstrong : ∀ x,Tendsto (fun i => P i x) l (𝓝 (Y x)))
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (C : ℝ) (hC : 0≤C)
    (hbound : ∀ᶠ i in l,‖diagonalAmplification h (P i)*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h (P i)‖≤C) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤C :=
  norm_le_of_strong _ _ (commutator_tendsto P Y hstrong h X) hC hbound

end Kadison.StrongContractionLimit

end

end
end

end OAI
