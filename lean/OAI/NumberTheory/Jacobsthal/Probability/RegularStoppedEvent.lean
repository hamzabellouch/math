import OAI.NumberTheory.Jacobsthal.Estimates.ActualRegularAdmission
import OAI.NumberTheory.Jacobsthal.Paths.FullWordHighAlignment

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RegularStoppedEvent
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ActualRegularAdmission ActualPrefixClearance RegularBadTagWords SourceMarkedStopping
open StoppedTraceSets StoppedCountAdapters PriorPrimeWindow MissingWindowPrimeMass
open StrongReferenceTransport StrongSourceFamilies ActualPrimeHigh ReferenceAdmission
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def hasSourceStop {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node) (ps : List ℕ) : Prop :=
  ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ∈ stopped w
    (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a z)
    (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) 1)

noncomputable def uncapturedTest {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (ps : List ℕ) : Prop :=
    (∃ q ∈ Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass a) q p) ∧
    ¬hasSourceStop hw htop hxi Y Cs eta Clen B b₀ b₁ a z ps

noncomputable def uncapturedRegular {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B K b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) : Finset (List ℕ) :=
  (regularWords hw htop hxi Clen B K z).filter (uncapturedTest hw htop hxi Y Cs eta Clen B b₀ b₁ a z Q)

theorem uncaptured_subset_exceptions {w top xi Cs eta Clen B K b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hmesh : 2*(xi/Real.log w) ≤ 6*(2*Clen*xi))
    (hb₀ : 0 < b₀) (hCs : Cs < 2*b₀) (hsearch : b₁ < w^((1/4:ℝ)))
    (hh : xi/Real.log w ≤ b₀) (hsmall : 2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*b₀)
    (Y : ℕ) (a : ℕ → ℕ) (z : Node) (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hg : StrongState z) (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (hroot : b₁/2 < z.cutoff)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) :
    uncapturedRegular hw htop hxi Y Cs eta Clen B K b₀ b₁ a z Q ⊆
      regularBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Clen B K z Q (sourceClass a) ∪
        missingWindowPrefixes w 1 K b₀ b₁ z := by
  intro ps hp
  obtain ⟨hr,⟨q,hq,ha⟩,hnotstop⟩ := Finset.mem_filter.mp hp
  have href := regular_word_reference hw htop hxi hC hcomp hmesh z ps hr
  by_cases hwin : hasPrimeWindow w b₀ b₁ z ps
  · by_cases hcorrect : ∃ t,ActualSourceTags.sourceTag Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps=some t ∧ t.rational=q
    · obtain ⟨t,ht,htq⟩ := hcorrect
      obtain ⟨pre,tail,heq,hwin⟩ := hwin
      have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hr).1
      have hreg := (Finset.mem_filter.mp hr).2
      have hsafe := clearance_supplies_safety hw htop hxi hC hcomp hmesh z ps hd.2 hreg.1 hreg.2.1
      have hcount := regular_tag_singleton hw htop hxi z ps hr (sourceClass a) t ht
      have halign : ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass a) t.rational p := by
        simpa only [htq] using ha
      exact False.elim (hnotstop (marked_prefix_forces_actual_stop Y hw htop hxi hC hcomp hb₀ hCs hsearch hh hsmall
        a ∅ 1 z ps pre tail heq hs hz hg hclosed hcap hroot href hreg.1 hsafe t ht hcount halign hwin))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr,q,hq,ha,hcorrect⟩)
  · have hu := (source_reference_transport hw htop z hs hz hg hclosed hcap ps href).1
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,(Finset.mem_filter.mp hr).2.2.2.1,hwin⟩)

end NumberTheoryLean.RegularStoppedEvent


end Erdos970

end OAI
