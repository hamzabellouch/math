import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallControlledSubspace
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicAveragingDimension

namespace OAI

/-! # From a good determinant ratio to a harmonic dimension bound -/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem wordBallQuadraticForm_posDef_of_gram (S : Finset G) (R : ℕ)
    (V : Submodule ℝ (G → ℝ)) (basis : Module.Basis ι ℝ V)
    (hgram : (wordBallGram S R (fun i => (basis i).val)).PosDef) :
    (wordBallQuadraticForm S R V).PosDef := by
  intro f hf
  have hv : basis.equivFun f ≠ 0 := by
    intro h
    exact hf (basis.equivFun.injective (by simpa using h))
  have hp := hgram.dotProduct_mulVec_pos hv
  have he : basisFunctionsLinearMap V basis (basis.equivFun f) = f.val := by
    change (basis.equivFun.symm (basis.equivFun f)).val = f.val
    rw [basis.equivFun.symm_apply_apply]
  change 0 < realMatrixQuadratic (wordBallGram S R (fun i => (basis i).val))
    (basis.equivFun f) at hp
  rw [wordBallGram_basis_quadratic, he] at hp
  simpa only [wordBallQuadraticForm_apply] using hp

omit [Fintype ι] [DecidableEq ι] in
theorem wordBallQuadraticForm_posDef_submodule (S : Finset G) (R : ℕ)
    {V W : Submodule ℝ (G → ℝ)} (hWV : W ≤ V)
    (hV : (wordBallQuadraticForm S R V).PosDef) :
    (wordBallQuadraticForm S R W).PosDef := by
  intro f hf
  let g : V := ⟨f.val, hWV f.property⟩
  have hg : g ≠ 0 := by
    intro h
    apply hf
    apply Subtype.ext
    exact congrArg (fun z : V => z.val) h
  simpa only [wordBallQuadraticForm_apply] using hV g hg

theorem harmonic_dimension_bound_from_gram (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (V : Submodule ℝ (G → ℝ)) (basis : Module.Basis ι ℝ V)
    (hharm : ∀ f : V, CayleyHarmonic S f.val)
    (C : Finset G) (r R t n : ℕ) (hRt : 0 < R + 3 * t)
    (hn : 2 * (R + 3 * t) ≤ n)
    (hdis : (C : Set G).Pairwise (fun x y =>
      Disjoint (translatedWordBall S r x) (translatedWordBall S r y)))
    (hC : C ⊆ wordBall S R)
    (hcover : ∀ x ∈ wordBall S R, ∃ y ∈ C, x ∈ translatedWordBall S t y)
    (hpos : (wordBallGram S R (fun i => (basis i).val)).PosDef)
    (K : ℝ) (hK : 1 < K)
    (hdet : (wordBallGram S n (fun i => (basis i).val)).det ≤
      K ^ Fintype.card ι * (wordBallGram S R (fun i => (basis i).val)).det)
    (hsmall : harmonicCoverFactor S r R t * K ^ 2 < 1) :
    Module.finrank ℝ V ≤ 2 * C.card := by
  obtain ⟨W, hWV, hdim, hgrowth⟩ := exists_wordBall_controlled_subspace S V basis
    (by omega : R ≤ n) hpos K hK hdet
  have hWp := wordBallQuadraticForm_posDef_submodule S R hWV
    (wordBallQuadraticForm_posDef_of_gram S R V basis hpos)
  have hWg : ∀ f : W, wordBallQuadraticValue S (2 * (R + 3 * t)) f.val ≤
      K ^ 2 * wordBallQuadraticValue S R f.val := by
    intro f
    exact (wordBallQuadraticValue_mono S f.val hn).trans (hgrowth f.val f.property)
  have hWd := (harmonic_subspace_dimension_le_cover S hS hgen C r R t hRt hdis hC
    hcover W (fun f => hharm ⟨f.val, hWV f.property⟩) hWp (K ^ 2) hWg hsmall).2
  exact hdim.trans (Nat.mul_le_mul_left 2 hWd)

end PolycyclicRecognition

end

end OAI
