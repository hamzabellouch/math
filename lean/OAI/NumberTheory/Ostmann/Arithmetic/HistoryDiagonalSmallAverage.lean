import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallAverageRoot

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration
open ResidueHaar

theorem rootSmallTest_mixed_average (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    [NeZero (rootModulus h)] (hu : SmallUnitData D P q outerU xs v) :
    average (fun z : ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ =>
      rootResidueIndicator h (z.1,z.2) * (rootSmallTest d h outerU xs hslots D P q v hu z : ℂ)) =
      ((∏i : Fin outerU.length, (((outerU[i].value-1:ℕ):ℝ)/outerU[i].value) : ℝ) : ℂ) := by
  have hn : (∏i,smallPrime xs outerU i)≠0 := by
    rw [small_modulus_eq_root h outerU xs hslots]
    exact NeZero.ne _
  let : NeZero (∏i,smallPrime xs outerU i) := ⟨hn⟩
  simp_rw [rootResidueIndicator_mul_rootSmallTest]
  unfold rootSmallTest
  rw [average_equiv (rootSmallEquiv h outerU xs hslots)
    (fun z => (crtTest (smallPrime xs outerU) hu.coprime (smallRetained xs outerU)
      (fun i=>residueTransform d (smallPrime xs outerU i))
      (smallCoefficients D outerU xs v hu.frequency hu.denominator) z : ℂ))]
  have ha := actual_small_average d D P q outerU xs v hu
  have hc := congrArg (fun x : ℝ => (x:ℂ)) ha
  convert hc using 1;
    simp only [average,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_sum,Complex.ofReal_natCast,div_eq_mul_inv];
      ring

theorem norm_rootSmallTest_mixed_average_le_one (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    [NeZero (rootModulus h)] (hu : SmallUnitData D P q outerU xs v) :
    ‖average (fun z : ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ =>
      rootResidueIndicator h (z.1,z.2) * (rootSmallTest d h outerU xs hslots D P q v hu z : ℂ))‖ ≤ 1 := by
  have hn : (∏i,smallPrime xs outerU i)≠0 := by
    rw [small_modulus_eq_root h outerU xs hslots]
    exact NeZero.ne _
  let : NeZero (∏i,smallPrime xs outerU i) := ⟨hn⟩
  have hb := actual_small_average_le_one d D P q outerU xs v hu
  rw [actual_small_average d D P q outerU xs v hu] at hb
  rw [rootSmallTest_mixed_average]
  have hp : 0 ≤ ∏i : Fin outerU.length, (((outerU[i].value-1:ℕ):ℝ)/outerU[i].value) := by
    apply Finset.prod_nonneg
    intro i _
    positivity
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp] using hb

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
