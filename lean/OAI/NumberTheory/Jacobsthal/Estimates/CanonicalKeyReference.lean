import OAI.NumberTheory.Jacobsthal.Paths.FiniteBoxWordMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CanonicalKeyReference
open _root_.Filter PrimeHistories CanonicalStopKey CanonicalKeyWitness CanonicalKeyReplacement CanonicalKeyBands
open ActualStopGroupFiber StoppedCountVertex StoppedVertexHistory StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.MertensStrong
open scoped Topology


theorem moving_key_reference {Clen xi Kstop rho : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < Kstop) (hrho : 0 < rho) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,∀ Cs eta : ℝ,
      ∀ (a : ℕ → ℕ) (z : Node) (k : Key (binCount w top xi)),
      ∀ _d : Witness hw htop hxi Y Cs eta Clen B (Kstop*(Real.log w)^2)
        (rho*Kstop*(Real.log w)^2) ((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) a z k,
      ∀ p∈primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin),
      aligns (SourceStopPredicate.sourceClass a) k.tag.rational p →
      referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top)
        ((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊)) (k.pre++p::k.tail))
        ≤ (33/100)*primeProduct (k.tail.getLastD 0:ℝ)*
          ((Y:ℝ)/((p:ℝ)*(k.pre.prod*k.tail.prod:ℕ))) := by
  filter_upwards [ErdosStoppedReferenceUpper.actual_stopped_reference_upper hC hxi hxi1 hK hrho]
    with w hRef
  obtain ⟨hw,hRef⟩ := hRef
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y Cs eta a z k d p hp ha
  have hm := aligning_word_mem hw htop hxi d hC p hp ha
  rw [family,ErdosInverseEuler.smallEuler_eq_primeProduct] at hm
  have hh := (hRef top htop B hcomp Y Cs eta a z (k.pre++p::k.tail) hm).2
  rw [last_fixed_tail k.pre k.tail p d.tail_nonempty,
    TagBelowStopWindow.replacement_product,Nat.cast_mul] at hh
  rw [ErdosInverseEuler.smallEuler_eq_primeProduct]
  convert hh using 1; ring
end NumberTheoryLean.CanonicalKeyReference


end Erdos970

end OAI
