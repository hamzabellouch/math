import OAI.NumberTheory.Jacobsthal.Paths.OutsideExceptionsWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricTotalBoxMass
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualSafeBoxMass
open GeometricBoxImages SafeSubsetBoxGeometry CanonicalSubsetBox FilteredBoxWordMass
open LogarithmicBinScale ErdosSubsetWord


theorem uniform_geometric_box_mass (K : ℝ) (hK : 3 ≤ K) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
    ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ (hw : 1 < w) (htop : w < top),
    ∀ xi Clen : ℝ,∀ hxi : 0 < xi,1 ≤ Clen → Real.log B ≤ 2*Real.log w → 2*Clen*xi ≤ 1 →
    ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z →
      z.cutoff=B → z.closed=true → w^B=top → ∀ L alpha beta : ℝ,
    B^2*(∑ m∈geometricBoxes hw htop hxi Clen B K L alpha beta z,selectionMass (globalBins w top xi) m) ≤ C := by
  obtain ⟨C,B₀,W,hC,hB₀,hW,hTotal⟩ := uniform_safe_box_mass K hK
  refine ⟨C,B₀,max W (Real.exp 1),hC,hB₀,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ hw htop xi Clen hxi hClen hcomp hsmall z hi h199 h23 hz hcut hclosed hpower L alpha beta
  have hlog : 1 ≤ Real.log w := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hw₀)
    simpa only [Real.log_exp] using hh
  have hmesh : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  exact hTotal B w top hB ((le_max_left _ _).trans hw₀) hw htop xi Clen hxi
    (by linarith) hcomp hsmall z hi h199 h23 hz hcut hclosed hpower
    (geometricBoxes hw htop hxi Clen B K L alpha beta z)
    (geometric_box_anchor hw htop hxi (by linarith) hcomp hmesh z)

theorem unlisted_box_transfer {w top xi Cs C B K L alpha beta sigma A : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hsigma : 0 ≤ sigma)
    (a : ℕ → ℕ) (z : Node) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (F : Finset (List ℕ))
    (hTotal : B^2*(∑ m∈geometricBoxes hw htop hxi C B K L alpha beta z,selectionMass (globalBins w top xi) m) ≤ A)
    (hBox : ∀ m∈geometricBoxes hw htop hxi C B K L alpha beta z,
      selectedWordMass (globalBins w top xi) m
        (ExpandedCompactPartition.unlistedGeometric hw htop hxi Cs C B K L alpha beta a z Q F)
        ≤ sigma*selectionMass (globalBins w top xi) m) :
    B^2*(∑ ps∈ExpandedCompactPartition.unlistedGeometric hw htop hxi Cs C B K L alpha beta a z Q F,
      ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps) ≤ sigma*A := by
  rw [unlisted_geometric_box_mass hw htop hxi a z Q F]
  calc
    _ ≤ B^2*(∑ m∈geometricBoxes hw htop hxi C B K L alpha beta z,sigma*selectionMass (globalBins w top xi) m) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hBox) (sq_nonneg B)
    _ = sigma*(B^2*(∑ m∈geometricBoxes hw htop hxi C B K L alpha beta z,selectionMass (globalBins w top xi) m)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTotal hsigma
end NumberTheoryLean.GeometricTotalBoxMass


end Erdos970

end OAI
