import OAI.Analysis.KadisonKastler.KaplanskySelfAdjointBall
import OAI.Analysis.KadisonKastler.MatrixOperatorGeneration
import OAI.Analysis.KadisonKastler.BlockMatrices

namespace OAI

/-! # Discharging the finite-test Kaplansky density input

The self-adjoint contraction case was proved by the rational bounded
transform. The two-by-two self-adjoint matrix trick gives the general
case without a loss in the contraction bound.
-/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance kaplanskyOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance kaplanskyOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

private theorem norm_entry_le (S : FiniteHilbert (Fin 2) H →L[ℂ] FiniteHilbert (Fin 2) H)
    (i j : Fin 2) : ‖operatorEntry S i j‖ ≤ ‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖S (tupleSingle j x) i‖ ≤ ‖S‖ * ‖x‖
  have hs : ‖tupleSingle (H := H) j x‖ = ‖x‖ :=
    PiLp.norm_single 2 (fun _ : Fin 2 => H) j x
  exact (PiLp.norm_apply_le _ _).trans ((S.le_opNorm _).trans_eq (by rw [hs]))

/-- Kaplansky density in precisely the finite-test formulation used by
the conditional main theorem. This proof has no published hypotheses. -/
theorem publishedKaplanskyDensity : PublishedKaplanskyDensity.{u} := by
  intro H _ _ _ A T hT hn V ε hε
  classical
  let D := hilbertMatrix (blockOffDiagonal T (star T))
  have hDsa : IsSelfAdjoint D := by
    change star (hilbertMatrix (blockOffDiagonal T (star T))) = _
    rw [← hilbertMatrix_star]
    congr 1
    ext i j : 2
    simp only [CStarMatrix.star_apply]
    fin_cases i <;> fin_cases j <;> simp [blockOffDiagonal]
  have hDn : ‖D‖ ≤ 1 := by
    change ‖hilbertMatrix (blockOffDiagonal T (star T))‖ ≤ 1
    rw [norm_hilbertMatrix, norm_blockOffDiagonal, norm_star, max_self]
    exact hn
  have hD : D ∈ Set.centralizer (Set.centralizer
      (matrixOperatorAlgebra (ι := Fin 2) A : Set _)) := by
    rw [← generatedVonNeumannAlgebra_coe, generated_matrixOperatorAlgebra]
    change D ∈ matrixVonNeumann (generatedVonNeumannAlgebra A)
    apply (mem_matrixVonNeumann_iff_entries _ _).mpr
    intro i j
    change operatorEntry (hilbertMatrix (blockOffDiagonal T (star T))) i j ∈
      generatedVonNeumannAlgebra A
    rw [operatorEntry_hilbertMatrix]
    have ht : T ∈ generatedVonNeumannAlgebra A := by
      change T ∈ (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H))
      rwa [generatedVonNeumannAlgebra_coe]
    fin_cases i <;> fin_cases j
    · exact (generatedVonNeumannAlgebra A).zero_mem
    · exact ht
    · exact (generatedVonNeumannAlgebra A).toStarSubalgebra.star_mem' ht
    · exact (generatedVonNeumannAlgebra A).zero_mem
  obtain ⟨a, han, ha⟩ := selfAdjoint_bicommutant_unitBall_approx
    (matrixOperatorAlgebra (ι := Fin 2) A) D hD hDsa hDn
    (V.image (tupleSingle (H := H) (1 : Fin 2))) hε
  let b := operatorEntry (a : FiniteHilbert (Fin 2) H →L[ℂ] FiniteHilbert (Fin 2) H) 0 1
  refine ⟨⟨b, (mem_matrixOperatorAlgebra_iff A a.val).mp a.property 0 1⟩,
    (norm_entry_le _ 0 1).trans han, ?_⟩
  intro x hx
  have ha' := ha (tupleSingle (1 : Fin 2) x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hentry : (D (tupleSingle (1 : Fin 2) x) - a.val (tupleSingle (1 : Fin 2) x)) 0 =
      T x - b x := by
    change D (tupleSingle (1 : Fin 2) x) 0 - a.val (tupleSingle (1 : Fin 2) x) 0 = _
    congr 1
    change operatorEntry (hilbertMatrix (blockOffDiagonal T (star T))) 0 1 x = T x
    rw [operatorEntry_hilbertMatrix]
    rfl
  have hle := PiLp.norm_apply_le
    (D (tupleSingle (1 : Fin 2) x) - a.val (tupleSingle (1 : Fin 2) x)) (0 : Fin 2)
  rw [hentry] at hle
  exact hle.trans_lt ha'

end

end KadisonKastler

end OAI
