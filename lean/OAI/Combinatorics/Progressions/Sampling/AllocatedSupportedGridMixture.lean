import OAI.Combinatorics.Progressions.Lattices.AllocatedSupportedResidueGrid
import OAI.Combinatorics.Progressions.Probability.FiniteSpatialReferenceMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem allocatedSupportedGrid_mixture_error
    (q : ℕ) (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (cells : Finset (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q))
    (hcells : ∀ v ∈ cells, 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = v)))
    (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (shift point : cells → rows → ℤ) (test : cells → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1) :
    let weight (v : cells) := (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = v.val))
    ‖(∑ v : cells, (weight v : ℂ) *
        (allocatedSupportedGridDensity B U basis hR hσ S q v.val (hcells v.val v.property)
          j i M rows (shift v) (point v) : ℂ) * test v) -
      (∑ v : cells, (weight v : ℂ) *
        allocatedSupportedGridApproximation B U basis hR S q v.val j i hactive hq hsize
          P C ε M rows (shift v) (point v) * test v)‖ ≤
      ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  intro weight
  let : NeZero q := ⟨hq.ne'⟩
  let p := principalTupleWeights (α := α) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
  have hE : 0 ≤ ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by positivity
  have he := norm_spatial_reference_sum_sub weight (fun _ : cells => 1)
    (fun v : cells => (allocatedSupportedGridDensity B U basis hR hσ S q v.val
      (hcells v.val v.property) j i M rows (shift v) (point v) : ℂ))
    (fun v : cells => allocatedSupportedGridApproximation B U basis hR S q v.val
      j i hactive hq hsize P C ε M rows (shift v) (point v)) test
    (A := 1) zero_lt_one hE (fun v => p.mass_nonneg _) htest
    (fun v => allocatedSupportedGridDensity_error B U basis hR hσ S q v.val
      (hcells v.val v.property) j i hactive hq hsize hgrid A hA P hcP hsP
      hC hMK rows hrows hB hε hε1 (shift v) (point v))
  simp only [div_one, Complex.ofReal_one, mul_one, abs_one] at he
  have hm : (∑ v : cells, weight v) ≤ 1 :=
    p.sum_fiber_masses_le_one (principalResidueLabel q) cells
  exact he.trans ((mul_le_mul_of_nonneg_left hm hE).trans_eq (mul_one _))

end Erdos3.VectorPolynomial

end

end OAI
