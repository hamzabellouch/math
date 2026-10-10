import OAI.GroupTheory.PolycyclicRecognition.Algebra.BracketWords
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Spanning by conjugated generator directions

Products of adjoint exponentials applied to a Lie-generating family span the
whole algebra. This proves the linear nondegeneracy needed to construct a
submersive generator product scheme; it does not assume controllability or a
volume estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance generatorOrbitNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance generatorOrbitNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

/-- The adjoint operator, with its finite-dimensional continuous structure. -/
def continuousAd (x : L) : L →L[ℝ] L := Module.End.toContinuousLinearMap (𝕜 := ℝ) L (LieModule.toEnd ℝ L L x)

@[simp] theorem continuousAd_apply (x y : L) : continuousAd x y = ⁅x, y⁆ := rfl

/-- A finite product of actual operator exponentials of generator adjoints. -/
def generatorAdjointWord (X : I → L) (w : List (I × ℝ)) : L →L[ℝ] L :=
  (w.map (fun p => NormedSpace.exp (p.2 • continuousAd (X p.1)))).prod

@[simp] theorem generatorAdjointWord_nil (X : I → L) :
    generatorAdjointWord X [] = 1 := rfl

@[simp] theorem generatorAdjointWord_cons (X : I → L) (i : I) (t : ℝ)
    (w : List (I × ℝ)) :
    generatorAdjointWord X ((i, t) :: w) =
      NormedSpace.exp (t • continuousAd (X i)) * generatorAdjointWord X w := rfl

/-- The linear span of all conjugated generator directions. -/
def generatorOrbitSpan (X : I → L) : Submodule ℝ L :=
  Submodule.span ℝ (Set.range (fun p : List (I × ℝ) × I =>
    generatorAdjointWord X p.1 (X p.2)))

theorem generator_mem_orbitSpan (X : I → L) (i : I) : X i ∈ generatorOrbitSpan X := by
  apply Submodule.subset_span
  exact ⟨([], i), rfl⟩

/-- Each adjoint exponential preserves this span by prefixing a word. -/
theorem exp_ad_mem_orbitSpan (X : I → L) (i : I) (t : ℝ) {v : L}
    (hv : v ∈ generatorOrbitSpan X) :
    NormedSpace.exp (t • continuousAd (X i)) v ∈ generatorOrbitSpan X := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨w, j⟩, rfl⟩ := hv
    apply Submodule.subset_span
    exact ⟨((i, t) :: w, j), rfl⟩
  | zero => simp
  | add v u _ _ hv hu => simpa using (generatorOrbitSpan X).add_mem hv hu
  | smul c v _ hv => simpa using (generatorOrbitSpan X).smul_mem c hv

/-- Differentiating the genuine operator exponential recovers the adjoint. -/
theorem hasDerivAt_exp_ad_apply (x v : L) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • continuousAd x) v) ⁅x, v⁆ 0 := by
  have h := (hasDerivAt_exp_smul_const (continuousAd x) (0 : ℝ)).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  simpa using h

/-- A derivative of a curve in a closed linear subspace stays in that subspace. -/
theorem derivative_mem_submodule {f : ℝ → L} {v : L} {t : ℝ}
    (hf : HasDerivAt f v t) (U : Submodule ℝ L) (hU : ∀ s, f s ∈ U) : v ∈ U := by
  have h := range_deriv_subset_closure_span_image f dense_univ (Set.mem_range_self t)
  rw [hf.deriv] at h
  have hs : Submodule.span ℝ (f '' Set.univ) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, _, rfl⟩
    exact hU s
  have hc : IsClosed (U : Set L) := U.closed_of_finiteDimensional
  exact (closure_minimal hs hc) h

/-- Invariance under generator exponentials implies infinitesimal invariance. -/
theorem ad_mem_orbitSpan (X : I → L) (i : I) {v : L}
    (hv : v ∈ generatorOrbitSpan X) : ⁅X i, v⁆ ∈ generatorOrbitSpan X :=
  derivative_mem_submodule (hasDerivAt_exp_ad_apply (X i) v) (generatorOrbitSpan X)
    (fun t => exp_ad_mem_orbitSpan X i t hv)

/-- The elements whose adjoints preserve a fixed linear subspace form a Lie
subalgebra, by the Jacobi identity. -/
def submoduleAdjointStabilizer (U : Submodule ℝ L) : LieSubalgebra ℝ L where
  carrier := {x | ∀ v ∈ U, ⁅x, v⁆ ∈ U}
  zero_mem' := by intro v _; simpa only [zero_lie] using U.zero_mem
  add_mem' := by
    intro x y hx hy v hv
    simpa only [add_lie] using U.add_mem (hx v hv) (hy v hv)
  smul_mem' := by
    intro c x hx v hv
    simpa only [smul_lie] using U.smul_mem c (hx v hv)
  lie_mem' := by
    intro x y hx hy v hv
    rw [lie_lie]
    exact U.sub_mem (hx _ (hy v hv)) (hy _ (hx v hv))

/-- The conjugated generator directions span the entire generated Lie
algebra. No nilpotence assumption is needed for this nondegeneracy step. -/
theorem generatorOrbitSpan_eq_top (X : I → L)
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    generatorOrbitSpan X = ⊤ := by
  let U := generatorOrbitSpan X
  have hstab : submoduleAdjointStabilizer U = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩ v hv
    exact ad_mem_orbitSpan X i hv
  let K : LieSubalgebra ℝ L := { U with
    lie_mem' := by
      intro x y hx hy
      have hx' : x ∈ submoduleAdjointStabilizer U := by rw [hstab]; trivial
      exact hx' y hy }
  have hK : K = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact generator_mem_orbitSpan X i
  exact congrArg LieSubalgebra.toSubmodule hK

/-- Choose finitely many actual conjugated generator directions as a basis.
These are the differential columns in a conjugated generator scheme. -/
theorem exists_generatorOrbit_basis (X : I → L)
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    ∃ (b : Basis (Fin (finrank ℝ L)) ℝ L)
      (w : Fin (finrank ℝ L) → List (I × ℝ)) (i : Fin (finrank ℝ L) → I),
      ∀ k, generatorAdjointWord X (w k) (X (i k)) = b k := by
  classical
  have hspan : ⊤ ≤ generatorOrbitSpan X := (generatorOrbitSpan_eq_top X hX).ge
  let J := (linearIndepOn_empty ℝ (id : L → L)).extend
    (Set.empty_subset (Set.range (fun p : List (I × ℝ) × I =>
      generatorAdjointWord X p.1 (X p.2))))
  let b : Basis J ℝ L := Basis.ofSpan hspan
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin (finrank ℝ L) :=
    Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  have hb (k : Fin (finrank ℝ L)) : ∃ p : List (I × ℝ) × I,
      generatorAdjointWord X p.1 (X p.2) = (b.reindex e) k := by
    simpa only [Basis.coe_reindex, Function.comp_apply, Set.mem_range] using
      (Basis.ofSpan_subset hspan (show b (e.symm k) ∈ Set.range b from ⟨_, rfl⟩))
  choose p hp using hb
  exact ⟨b.reindex e, fun k => (p k).1, fun k => (p k).2, hp⟩

end PolycyclicRecognition

end

end OAI
