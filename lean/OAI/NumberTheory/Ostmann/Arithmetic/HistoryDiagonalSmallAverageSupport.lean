import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallAverage

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration

theorem supportedSmallPrimeFacts {l : ℕ} (h : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs)) :
    ∀i,Fact (smallPrime xs outerU i).Prime := by
  have hprime : h.root.PrimeSmall := by
    rw [History.Supported.eq_def] at hs
    exact hs.2.1
  intro i
  constructor
  cases i with
  | inl i =>
    exact hprime xs[i] (hslots.mem_iff.mpr
      (List.mem_append_right _ (List.getElem_mem i.isLt)))
  | inr i =>
    exact hprime outerU[i] (hslots.mem_iff.mpr
      (List.mem_append_left _ (List.getElem_mem i.isLt)))

theorem supportedSmallUnitData {l : ℕ} (h : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs))
    (hlarge : ∀i : Fin xs.length,V l<xs[i].value) :
    letI := supportedSmallPrimeFacts h hs outerU xs hslots
    SmallUnitData outside.prod h.root.giantPlus h.root.giantMinus outerU xs h.root.frequency := by
  let := supportedSmallPrimeFacts h hs outerU xs hslots
  exact smallUnitData_of_state h.root outerU xs outside hslots
    (History.supported_root_coprime hs) (History.supported_root_frequency_ne_zero hs)
    (fun i => (History.supported_root_frequency_bound hs).trans_lt (hlarge i))

def supportedRootSmallTest (d : Decomposition) {l : ℕ} (h : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (hlarge : ∀i : Fin xs.length,V l<xs[i].value)
    (z : ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ) : ℝ :=
  letI := supportedSmallPrimeFacts h hs outerU xs hslots
  rootSmallTest d h outerU xs hslots outside.prod h.root.giantPlus h.root.giantMinus
    h.root.frequency (supportedSmallUnitData h hs outerU xs hslots hlarge) z

theorem supported_rootSmall_mixed_average_le_one (d : Decomposition) {l : ℕ} (h : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (hlarge : ∀i : Fin xs.length,V l<xs[i].value) :
    letI : NeZero (rootModulus h) := ⟨(rootModulus_pos h hs).ne'⟩
    ‖ResidueHaar.average (fun z : ZMod (rootModulus h) × (ZMod (rootModulus h))ˣ =>
      rootResidueIndicator h (z.1,z.2) *
         (supportedRootSmallTest d h hs outerU xs hslots hlarge z : ℂ))‖ ≤ 1 := by
  let : NeZero (rootModulus h) := ⟨(rootModulus_pos h hs).ne'⟩
  let := supportedSmallPrimeFacts h hs outerU xs hslots
  exact norm_rootSmallTest_mixed_average_le_one d h outerU xs hslots outside.prod
    h.root.giantPlus h.root.giantMinus h.root.frequency
    (supportedSmallUnitData h hs outerU xs hslots hlarge)

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
