import OAI.Combinatorics.Progressions.Lattices.ResidueCoefficientFamily
import OAI.Combinatorics.Progressions.Linear.KernelJetExtendedControl

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem goodScalarKernelTuple_grid_tolerance {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    {L B : ℕ} {κ : ℝ} (hL : 0 < L) (selection : I → J) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple selection κ B x)
    (h : ℕ) (rows : O → Finset I) (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ s : O ↪ BoundedIntegerExponent J h,
      ∀ (H : ℝ) (hH : 0 < H), 1 ≤ H →
      ∀ (C : Matrix O N ℤ) (T : N → ℝ) (hT : ∀ n, 0 < T n),
      (∀ n, H / (L : ℝ) ^ h ≤ T n) →
      (∀ o n, |normalizedIntegerColumns C T (fun _ => H) o n| ≤
        kernelJetEntryAllowance (Fintype.card I) h) →
      ∀ (c w : BoundedIntegerExponent J h ⊕ N → ℝ) (hw : ∀ j, 0 < w j)
        (δ : ℝ≥0), 0 < δ → (∀ j, (δ : ℝ) ≤ w j) →
      ∀ (R b t ε : ℝ) (hR : 0 ≤ R) (hsupport : ∀ j, |c j| + w j ≤ R),
      0 ≤ b → 0 ≤ t → 0 < ε →
      (((B ^ h) ^ Fintype.card O : ℕ) : ℝ) ≤ Real.exp b →
      kernelJetInverseAllowance (Fintype.card I) (Fintype.card J) (Fintype.card O) h κ ≤ Real.exp b →
      kernelJetEntryAllowance (Fintype.card I) h ≤ Real.exp b → R ≤ Real.exp b →
      (δ : ℝ)⁻¹ ≤ Real.exp t →
      coefficientGridReplacementScale (J := BoundedIntegerExponent J h ⊕ N) (s.trans Function.Embedding.inl)
        (kernelJetEntryAllowance (Fintype.card I) h) R b t ε L h ≤ H →
      let A := Matrix.fromCols (scalarKernelIntegerJet x h rows) C
      let S := Sum.elim (kernelJetCoefficientScale J h L H) T
      let hS := Sum.rec (kernelJetCoefficientScale_pos J h (by exact_mod_cast hL) hH) hT
      ∃ hA : (A.submatrix id (s.trans Function.Embedding.inl)).det ≠ 0,
      ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) S,
        (∫ v, |(coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
            S hS (affineProductProfile_zero_outside c w hw hR hsupport) hZ v).toReal -
          coefficientGridProxy A (s.trans Function.Embedding.inl) hA S (fun _ => H) hS
            (fun _ => hH) (affineProductProfile c w) v| ∂Measure.count) ≤ ε := by
  obtain ⟨s, hs⟩ := goodScalarKernelTuple_extended_control (N := N)
    hL selection hκ x hx h rows hr hrows
  refine ⟨s, ?_⟩
  intro H hH hH1 C T hT hscale hentry c w hw δ hδ hwidth R b t ε hR hsupport
    hb ht hε hG hU hC hRb hi hlarge
  dsimp only
  let ctrl := hs H hH C T hscale hentry
  have hS : ∀ j, 0 < Sum.elim (kernelJetCoefficientScale J h L H) T j :=
    Sum.rec (kernelJetCoefficientScale_pos J h (by exact_mod_cast hL) hH) hT
  obtain ⟨hZ, herr⟩ := affineCoefficientGrid_tolerance
    (Matrix.fromCols (scalarKernelIntegerJet x h rows) C) (s.trans Function.Embedding.inl)
    (Sum.elim (kernelJetCoefficientScale J h L H) T) hS h ctrl (by exact_mod_cast hL) hH hH1
    (kernelJetEntryAllowance_pos _ _).le (kernelJetInverseAllowance_nonneg _ _ _ _ hκ)
    (Nat.cast_nonneg _) c w hw hδ hwidth hR hsupport hb ht hε hG hU hC hRb hi hlarge
  exact ⟨ctrl.det_ne_zero, hZ, herr⟩

end Erdos3

end

end OAI
