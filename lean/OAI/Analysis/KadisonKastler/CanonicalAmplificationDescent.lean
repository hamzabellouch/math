import OAI.Analysis.KadisonKastler.CanonicalAmplification
import OAI.Analysis.KadisonKastler.UCPDescent

namespace OAI

/-! # The coordinate slice and descent from the canonical amplification

Compression along the zeroth coordinate is an actual unital completely
positive retraction of the diagonal embedding. Matrix-entry membership
shows that it maps the amplified target algebra into the original one.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance canonicalSliceOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance canonicalSliceOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _
local instance canonicalSliceFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance canonicalSliceFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

def operatorCompressionLinear (S : H →L[ℂ] K) :
    (K →L[ℂ] K) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun T := S.adjoint.comp (T.comp S)
  map_add' T R := by ext x; simp
  map_smul' c T := by ext x; simp

@[simp] theorem operatorCompressionLinear_apply (S : H →L[ℂ] K)
    (T : K →L[ℂ] K) (x : H) :
    operatorCompressionLinear S T x = S.adjoint (T (S x)) := rfl

/-- Compression by any bounded operator is completely positive. -/
def operatorCompressionCP (S : H →L[ℂ] K) : (K →L[ℂ] K) →CP (H →L[ℂ] H) where
  toLinearMap := operatorCompressionLinear S
  map_cstarMatrix_nonneg' n X hX := by
    let : PartialOrder (Generator.FiniteHilbert (Fin n) K →L[ℂ]
        Generator.FiniteHilbert (Fin n) K) := ContinuousLinearMap.instLoewnerPartialOrder
    let : StarOrderedRing (Generator.FiniteHilbert (Fin n) K →L[ℂ]
        Generator.FiniteHilbert (Fin n) K) := ContinuousLinearMap.instStarOrderedRing
    let : PartialOrder (Generator.FiniteHilbert (Fin n) H →L[ℂ]
        Generator.FiniteHilbert (Fin n) H) := ContinuousLinearMap.instLoewnerPartialOrder
    let : StarOrderedRing (Generator.FiniteHilbert (Fin n) H →L[ℂ]
        Generator.FiniteHilbert (Fin n) H) := ContinuousLinearMap.instStarOrderedRing
    have hpos : (hilbertMatrix X).IsPositive := by
      have hp := map_nonneg (hilbertMatrixHom (H := K) (n := Fin n)) hX
      change (hilbertMatrix X - 0).IsPositive at hp
      simpa only [sub_zero] using hp
    have hcompressed : (hilbertMatrix (X.map (operatorCompressionLinear S))).IsPositive := by
      apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
      intro x
      let y : Generator.FiniteHilbert (Fin n) K := WithLp.toLp 2 (fun i => S (x i))
      have he : inner ℂ (hilbertMatrix (X.map (operatorCompressionLinear S)) x) x =
          inner ℂ (hilbertMatrix X y) y := by
        simp only [PiLp.inner_apply, hilbertMatrix_apply, CStarMatrix.map_apply,
          sum_inner, operatorCompressionLinear_apply, ContinuousLinearMap.adjoint_inner_left]
        rfl
      rw [he]
      exact (ContinuousLinearMap.isPositive_iff_complex _).mp hpos y
    apply (NonUnitalStarAlgHom.map_le_map_iff
      (hilbertMatrixHom (H := H) (n := Fin n)) hilbertMatrixHom_injective).mp
    rw [map_zero]
    change (hilbertMatrix (X.map (operatorCompressionLinear S)) - 0).IsPositive
    simpa only [sub_zero] using hcompressed

variable (H)

/-- The actual completely positive coordinate-zero slice. -/
def canonicalSlice :
    (CountableHilbertSum H →L[ℂ] CountableHilbertSum H) →CP (H →L[ℂ] H) :=
  operatorCompressionCP (canonicalSingle H 0)

@[simp] theorem canonicalSlice_apply
    (T : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (x : H) :
    canonicalSlice H T x = T (lp.single 2 0 x) 0 := by
  change (canonicalSingle H 0).adjoint (T (lp.single 2 0 x)) = _
  rw [canonicalSingle_adjoint]
  rfl

@[simp] theorem canonicalSlice_one : canonicalSlice H 1 = 1 := by
  ext x
  simp only [canonicalSlice_apply, one_apply_eq_self, lp.single_apply, Pi.single_eq_same]

@[simp] theorem canonicalSlice_l2Diagonal (T : H →L[ℂ] H) :
    canonicalSlice H (l2Diagonal T) = T := by
  ext x
  simp only [canonicalSlice_apply, l2Diagonal_apply, lp.single_apply, Pi.single_eq_same]

theorem canonicalSlice_mem {N : VonNeumannAlgebra H}
    {T : CountableHilbertSum H →L[ℂ] CountableHilbertSum H}
    (hT : T ∈ canonicalAmplifiedAlgebra H N) : canonicalSlice H T ∈ N := by
  have hentry : (canonicalMatrixCorner H).matrixEntry T 0 0 ∈ canonicalCornerAlgebra H N :=
    ((canonicalMatrixCorner H).mem_amplifiedAlgebra_iff _ T).mp hT 0 0
  have hm := (mem_spatialTransportAlgebra (canonicalInitialEquiv H) N
    ((canonicalMatrixCorner H).matrixEntry T 0 0)).mp hentry
  have he : (canonicalInitialEquiv H).conjStarAlgEquiv.symm
      ((canonicalMatrixCorner H).matrixEntry T 0 0) = canonicalSlice H T := by
    ext x
    change (canonicalInitialEquiv H).symm
      ((canonicalMatrixCorner H).matrixEntry T 0 0 (canonicalInitialEquiv H x)) =
        canonicalSlice H T x
    rw [canonicalMatrixCorner_matrixEntry, canonicalSlice_apply]
  rwa [he] at hm

/-- A near-identity conjugacy of the actual canonical amplifications
descends through the coordinate slice to a conjugacy on the original space. -/
theorem concrete_unitary_of_canonical_amplification {M N : VonNeumannAlgebra H}
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (z : unitary (CountableHilbertSum H →L[ℂ] CountableHilbertSum H))
    (hz : Conjugates z (canonicalAmplifiedAlgebra H M) (canonicalAmplifiedAlgebra H N))
    {g : ℝ} (hgap : kkDistance M N < g)
    (hsmall : 2 * ‖(z : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ < 1 / 1000)
    (hge : g + 2 * ‖(z : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ < 1) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤
        256 * ‖(z : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ := by
  apply concrete_unitary_of_retracted_conjugation hCorrection hCommutant
    (l2DiagonalHom (E := H)) (l2DiagonalHom_injective H)
    (canonicalSlice H) (canonicalSlice_one H) (canonicalSlice_l2Diagonal H) z
    (fun x => ?_) hgap hsmall hge
  apply canonicalSlice_mem H
  change unitaryConj z (l2Diagonal x.val) ∈
    (canonicalAmplifiedAlgebra H N : Set (CountableHilbertSum H →L[ℂ] CountableHilbertSum H))
  rw [← hz]
  exact ⟨l2Diagonal x.val, l2Diagonal_mem_canonicalAmplifiedAlgebra H x.property, rfl⟩

end

end KadisonKastler

end OAI
