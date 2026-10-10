import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormBound
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration

theorem rootSmallTest_bounds (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu : SmallUnitData D P q outerU xs v)
    (z : ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ) :
    0 ≤ rootSmallTest d h outerU xs hslots D P q v hu z ∧
      rootSmallTest d h outerU xs hslots D P q v hu z ≤ (rootModulus h:ℝ) := by
  have hh := actual_crtTest_bounds (smallPrime xs outerU) hu.coprime d (smallRetained xs outerU)
    (smallCoefficients D outerU xs v hu.frequency hu.denominator)
    (rootSmallEquiv h outerU xs hslots z)
  exact ⟨hh.1,hh.2.trans_eq (congrArg (fun n : ℕ=>(n:ℝ))
    (small_modulus_eq_root h outerU xs hslots))⟩

theorem rootSmallTest_norm_le (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu : SmallUnitData D P q outerU xs v)
    (z : ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ) :
    ‖(rootSmallTest d h outerU xs hslots D P q v hu z:ℂ)‖ ≤ (rootModulus h:ℝ) := by
  have hh := rootSmallTest_bounds d h outerU xs hslots D P q v hu z
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
