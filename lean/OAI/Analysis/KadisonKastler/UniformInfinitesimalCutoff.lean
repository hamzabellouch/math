import OAI.Analysis.KadisonKastler.InfinitesimalSequence

namespace OAI

/-! # A uniform infinitesimal cutoff for represented type III factors

The tolerance is chosen before the Hilbert space and factor. The estimate
uses a countable full matrix corner.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

structure MatrixTypeIIIFactorModel where
  H : Type u
  [normedH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℂ H]
  [completeH : CompleteSpace H]
  [separableH : TopologicalSpace.SeparableSpace H]
  M : VonNeumannAlgebra H
  isTypeIII : TypeIIIFactor M
  E : Submodule ℂ H
  [completeE : CompleteSpace E]
  matrixCorner : FullMatrixCorner E
  matrix_mem : ∀ i j, matrixCorner.entry i j ∈ M

attribute [instance] MatrixTypeIIIFactorModel.normedH MatrixTypeIIIFactorModel.innerH
  MatrixTypeIIIFactorModel.completeH MatrixTypeIIIFactorModel.separableH
  MatrixTypeIIIFactorModel.completeE

local instance uniformInfinitesimalSourceOrder (P : MatrixTypeIIIFactorModel.{u}) :
    PartialOrder (Algebra P.M) := CStarAlgebra.spectralOrder _
local instance uniformInfinitesimalSourceStarOrder (P : MatrixTypeIIIFactorModel.{u}) :
    StarOrderedRing (Algebra P.M) := CStarAlgebra.spectralOrderedRing _

theorem uniform_typeIII_infinitesimal_cutoff
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ P : MatrixTypeIIIFactorModel.{u},
      PublishedBlockCommutantApproximation (Algebra P.M) P.H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P : MatrixTypeIIIFactorModel.{u},
      ∀ T : P.H →L[ℂ] P.H, IsSelfAdjoint T → ‖T‖ ≤ 2 →
        (∀ x : Algebra P.M, ∃ y : Algebra P.M,
          ‖T * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * T -
            (y : P.H →L[ℂ] P.H)‖ ≤ ε * ‖x‖) →
        ∃ a b : P.H →L[ℂ] P.H, a ∈ P.M ∧ b ∈ P.M.commutant ∧
          ‖T - (a + b)‖ < 1 := by
  classical
  by_contra! hbad
  have hex (j : ℕ) := hbad (1 / (j + 1 : ℝ)) (by positivity)
  choose P t hself hnorm happrox hfar using hex
  let T : VaryingBoundedSequence (fun j => (P j).H →L[ℂ] (P j).H) :=
    ⟨t, memℓp_infty ⟨2, by rintro _ ⟨j, rfl⟩; exact hnorm j⟩⟩
  have hT : IsSelfAdjoint T := by
    apply Subtype.ext
    funext j
    exact (hself j).star_eq
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hε : Tendsto (fun j : ℕ => 1 / (j + 1 : ℝ)) (ω : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hω
  have hεbound (j : ℕ) : 1 / (j + 1 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (j + 1 : ℝ))).mpr
    norm_num
  have hevent := typeIII_eventually_approximate_algebra_add_commutant
    hSpectral hCompare hSakai (fun j => (P j).M) (fun j => (P j).isTypeIII)
    (fun j => hDistance (P j)) (fun j => (P j).E) (fun j => (P j).matrixCorner)
    (fun j => (P j).matrix_mem) ω T hT (fun j => 1 / (j + 1 : ℝ)) hε
    (fun j => by positivity) hεbound happrox 1 zero_lt_one
  obtain ⟨j, a, b, ha, hb, hab⟩ := hevent.exists
  exact (not_lt_of_ge (hfar j a b ha hb)) hab

end

end KadisonKastler

end OAI
