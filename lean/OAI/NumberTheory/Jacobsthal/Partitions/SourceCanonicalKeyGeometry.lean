import OAI.NumberTheory.Jacobsthal.Estimates.CanonicalKeyReference

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceCanonicalKeyGeometry
open _root_.Filter PrimeHistories CanonicalStopKey CanonicalStopPartition CanonicalKeyWitness
open CanonicalKeyBands CanonicalKeyReference SourceRootReference
open StoppedCountVertex StoppedVertexHistory StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.MertensStrong
open ErdosInverseBoxHeight ErdosCorrectionLimit ErdosSourceReferenceMargin
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem source_key_geometry {Clen xi Kstop rho : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < Kstop) (hrho : 0 < rho) (P0 : ℕ) :
    ∀ᶠ top : ℝ in atTop,
      let w := sourceW top
      let B := sourceB top
      let Y := sourceY top
      let z := sourceRootNode (1/100) top
      let mu := (Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊
      0 < Y ∧ ∃ hw : 1 < w,∃ htop : w < top,∀ Cs eta : ℝ,∀ a : ℕ → ℕ,
      ∀ k∈keys Y w top Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
        mu hw htop hxi a z,
      Nonempty (Witness hw htop hxi Y Cs eta Clen B (Kstop*(Real.log w)^2)
        (rho*Kstop*(Real.log w)^2) mu a z k) ∧
      P0 ≤ k.tail.getLastD 0 ∧
      Real.exp ((Kstop/2)*(Real.log w)^3) ≤ (k.tail.getLastD 0:ℝ) ∧
      (k.tail.getLastD 0:ℝ) ≤ Real.exp (rho*Kstop*(Real.log w)^3) ∧
      xi/4 ≤ width w top xi k.tag.bin ∧ width w top xi k.tag.bin ≤ 1 ∧
      (∀ p∈Set.Icc (lower w top xi k.tag.bin) ((1+width w top xi k.tag.bin)*lower w top xi k.tag.bin),
        203/100 ≤ Real.log ((Y:ℝ)/(p*(k.pre.prod*k.tail.prod:ℕ)))/Real.log (k.tail.getLastD 0:ℝ) ∧
        Real.log ((Y:ℝ)/(p*(k.pre.prod*k.tail.prod:ℕ)))/Real.log (k.tail.getLastD 0:ℝ) ≤ 219/100) ∧
      (∀ p∈(primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)).filter
          (aligns (SourceStopPredicate.sourceClass a) k.tag.rational),
        referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (k.pre++p::k.tail))
          ≤ (33/100)*primeProduct (k.tail.getLastD 0:ℝ)*
            ((Y:ℝ)/((p:ℝ)*(k.pre.prod*k.tail.prod:ℕ)))) := by
  filter_upwards [source_root_eventually_data,ErdosCofactorChoices.source_span_geometry,
    rootW_tendsto.eventually (moving_key_bands hC hxi hxi1 hK hrho),
    rootW_tendsto.eventually (moving_key_reference hC hxi hxi1 hK hrho),
    rootW_tendsto.eventually (TagBelowStopWindow.moving_window_below_search rho Kstop hrho hK),
    rootW_tendsto.eventually_ge_atTop (P0:ℝ)] with top hData hSpan hBands hRef hWindow hP0
  dsimp only
  obtain ⟨hY,_hB,hw,htop,hcomp,_hrlo,_hrhi,_hcons,_hpower⟩ := hData
  obtain ⟨_hwB,hBands⟩ := hBands
  obtain ⟨_hwR,hRef⟩ := hRef
  refine ⟨hY,hw,htop,?_⟩
  intro Cs eta a k hk
  obtain ⟨d⟩ := key_witness_exists hw htop hxi (sourceY top) Cs eta Clen (sourceB top)
    (Kstop*(Real.log (sourceW top))^2) (rho*Kstop*(Real.log (sourceW top))^2)
    ((sourceY top:ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) a
    (sourceRootNode (1/100) top) hWindow k hk
  have hBand := hBands top htop (sourceB top) hcomp (sourceY top) hY (1/100) Cs eta
    ((sourceY top:ℝ)*SmallSieveFinite.smallEuler ⌊sourceW top⌋₊) (by norm_num) (by norm_num)
    a (sourceRootNode (1/100) top) rfl k d
  have hTail : k.tail.getLastD 0∈k.tail := by
    have he : k.tail.getLastD 0=k.tail.getLast d.tail_nonempty := by
      conv_lhs => rw [← List.dropLast_append_getLast d.tail_nonempty]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem d.tail_nonempty
  have hPsource := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop (k.tail.getLastD 0)).mp
    (d.source _ (by simp only [List.mem_append,List.mem_cons]; exact Or.inr (Or.inr hTail)))
  have hPsize : P0 ≤ k.tail.getLastD 0 := by exact_mod_cast hP0.trans hPsource.2.1.le
  refine ⟨⟨d⟩,hPsize,hBand.1,hBand.2.1,?_,?_,hBand.2.2,?_⟩
  · exact effectiveWidth_ge_quarter (zero_lt_one.trans hw) htop hxi hxi1 (hSpan.2.2 xi hxi hxi1)
  · exact (effectiveWidth_le (zero_lt_one.trans hw) htop hxi).trans hxi1
  · intro p hp
    exact hRef top htop (sourceB top) hcomp (sourceY top) Cs eta a (sourceRootNode (1/100) top) k d
      p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
end NumberTheoryLean.SourceCanonicalKeyGeometry


end Erdos970

end OAI
