import OAI.NumberTheory.Jacobsthal.Estimates.StrongSourceFamilies
import OAI.NumberTheory.Jacobsthal.Paths.MovingStopMargins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedPrefixTools
open FinitePathGeometry PrimeHistories FiniteFirstTag ActualSourceTags PrimeBinRepresentatives
open ErdosPrimeInputs.HarmonicPrimeMeasure

private theorem tagFrom_none (n : ℕ) (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (ps : List ℕ)
    (h : ∀ p ∈ ps,F p=none) : firstTagFrom F k ps=none := by
  induction ps generalizing k with
  | nil => rfl
  | cons p ps ih =>
    rw [firstTagFrom,h p (by simp)]
    exact ih (k+1) (fun q hq => h q (by simp [hq]))

theorem tagFrom_append_none (n : ℕ) (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (pre tail : List ℕ)
    (h : ∀ p ∈ tail,F p=none) : firstTagFrom F k (pre++tail)=firstTagFrom F k pre := by
  induction pre generalizing k with
  | nil => exact tagFrom_none n F k tail h
  | cons p pre ih =>
    simp only [List.cons_append,firstTagFrom]
    cases hp : F p with
    | none => exact ih (k+1)
    | some bq => rfl

theorem terminal_cutoff_last (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ []) :
    (terminal w z ps).cutoff=primeExponent w (ps.getLast hne) := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [terminal_append]
  rfl

theorem terminal_lastD (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ []) :
    (terminal w z ps).cutoff=primeExponent w (ps.getLastD 0) := by
  have hh := terminal_cutoff_last w z ps hne
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rwa [he]

theorem prefix_exponent_lower {w : ℝ} (hw : 1 < w) (z : Node) (pre : List ℕ) (hne : pre ≠ [])
    (hD : pre.Pairwise (· > ·)) (hp : ∀ p ∈ pre,p.Prime) :
    ∀ p ∈ pre,(terminal w z pre).cutoff ≤ primeExponent w p := by
  let last := pre.getLast hne
  have hlast : last ∈ pre := List.getLast_mem hne
  have he : pre.dropLast++[last]=pre := List.dropLast_append_getLast hne
  have hdc : (pre.dropLast++[last]).Pairwise (· > ·) := by rwa [he]
  intro p hpre
  have hlp : last ≤ p := by
    have hm : p ∈ pre.dropLast++[last] := by rwa [he]
    rcases List.mem_append.mp hm with hm | hm
    · exact ((List.pairwise_append.mp hdc).2.2 p hm last (by simp)).le
    · have hh : p=last := Finset.mem_singleton.mp (by simpa using hm)
      exact hh.symm.le
  rw [terminal_cutoff_last w z pre hne]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast (hp last hlast).pos)
    (by exact_mod_cast hlp)) (Real.log_pos hw).le

theorem suffix_exponent_upper {w : ℝ} (hw : 1 < w) (z : Node) (pre tail : List ℕ) (hne : pre ≠ [])
    (hD : (pre++tail).Pairwise (· > ·)) (hp : ∀ p ∈ pre++tail,p.Prime) :
    ∀ p ∈ tail,primeExponent w p < (terminal w z pre).cutoff := by
  intro p hpt
  have hl := List.getLast_mem hne
  have hlt : p < pre.getLast hne := (List.pairwise_append.mp hD).2.2 _ hl p hpt
  rw [terminal_cutoff_last w z pre hne]
  exact div_lt_div_of_pos_right (Real.log_lt_log (by exact_mod_cast (hp p (by simp [hpt])).pos)
    (by exact_mod_cast hlt)) (Real.log_pos hw)

theorem no_candidate_below_search {n : ℕ} (Y w Cs eta : ℝ) (hw : 1 < w)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℤ)
    (hlo : ∀ b,0 < lower b) (hwidth : ∀ b,0 ≤ width b) (p : ℕ)
    (hx : primeExponent w p < w^((1/4:ℝ))) : tagCandidate Y w Cs eta lower width label a p=none := by
  cases ht : tagCandidate Y w Cs eta lower width label a p with
  | none => rfl
  | some bq =>
    rcases bq with ⟨b,q⟩
    have hh := candidate_witness Y w Cs eta lower width label a p ht
    have hlow := (bin_exponent_bounds hw (hlo _) (hwidth _) hh.2.1).1
    have hs := hh.2.2.1
    change w^((1/4:ℝ)) ≤ leftExponent w (lower (label p)) at hs
    exact False.elim ((not_lt_of_ge hs) (hlow.trans hx))

theorem sourceTag_prefix_eq {n : ℕ} (Y w Cs eta : ℝ) (hw : 1 < w)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℤ)
    (hlo : ∀ b,0 < lower b) (hwidth : ∀ b,0 ≤ width b) (pre tail : List ℕ)
    (htail : ∀ p ∈ tail,primeExponent w p < w^((1/4:ℝ))) :
    sourceTag Y w Cs eta lower width label a (pre++tail)=sourceTag Y w Cs eta lower width label a pre := by
  exact tagFrom_append_none n _ 0 pre tail (fun p hp =>
    no_candidate_below_search Y w Cs eta hw lower width label a hlo hwidth p (htail p hp))
end NumberTheoryLean.MarkedPrefixTools

end

section

namespace NumberTheoryLean.MarkedPrefixCandidate
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open StrongReferenceTransport StrongSourceFamilies SourceStopPredicate RepresentativeAdmission RepresentativeStopGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ActualSourceTags FiniteFirstTag MarkedPrefixTools SuccessfulMarkedCoordinates
open ReferenceAdmission ReferencePruning
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem marked_prefix_candidate (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hb₀ : 0 < b₀) (hCs : Cs < 2*b₀)
    (hsearch : b₁ < w^((1/4:ℝ))) (hh : xi/Real.log w ≤ b₀)
    (hsmall : 2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*b₀)
    (a : ℕ → ℕ) (z : Node) (ps pre tail : List ℕ) (heq : ps=pre++tail)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (hroot : b₁/2 < z.cutoff)
    (href : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hlen : (ps.length:ℝ) ≤ Clen*Real.log B)
    (hsafe : representativeSafe w (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z (2*Clen*xi) ps)
    (t : Tag (binCount w top xi))
    (htag : sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps=some t)
    (hcount : (ps.map (label (zero_lt_one.trans hw) htop hxi)).count t.bin=1)
    (halign : ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass a) t.rational p)
    (hwin : primeWindow b₀ b₁ (terminal w z pre)) :
    (terminal w z pre).side=.even ∧
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z pre := by
  let lab := label (zero_lt_one.trans hw) htop hxi
  let rep := representative w (lower w top xi) (width w top xi) lab
  have hne : pre ≠ [] := by
    intro hn
    have hh := hwin.2.2.2.2.1
    rw [hn,terminal_nil] at hh
    linarith
  have hsub : ∀ p ∈ pre,p ∈ ps := by
    intro p hp
    rw [heq]
    exact List.mem_append.mpr (Or.inl hp)
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp href).1
  have hdFull : (pre++tail).Pairwise (· > ·) := by simpa only [← heq] using hd.1
  have hdPre := (List.pairwise_append.mp hdFull).1
  have hsource : ∀ p ∈ ps,p ∈ sourcePrimeSet w top := hd.2
  have hsourcePre : ∀ p ∈ pre,p ∈ sourcePrimeSet w top := fun p hp => hsource p (hsub p hp)
  have hprimes : ∀ p ∈ pre++tail,p.Prime := by
    intro p hp
    exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p (by rwa [heq]))).1
  have hprimesPre : ∀ p ∈ pre,p.Prime := fun p hp => hprimes p (by simp [hp])
  have hlenPre : (pre.length:ℝ) ≤ Clen*Real.log B := by
    have hh : pre.length ≤ ps.length := by rw [heq,List.length_append]; omega
    exact (by exact_mod_cast hh : (pre.length:ℝ) ≤ ps.length).trans hlen
  have hb₁ : 0 < b₁ := by linarith [hwin.2.2.2.1,hwin.2.2.2.2.1]
  have htailSmall : ∀ p ∈ tail,primeExponent w p < w^((1/4:ℝ)) := by
    intro p hp
    have hh := suffix_exponent_upper hw z pre tail hne hdFull hprimes p hp
    linarith [hwin.2.2.2.2.1]
  have htEq := sourceTag_prefix_eq Y w Cs eta hw (lower w top xi) (width w top xi) lab (sourceClass a)
    (fun b => endpoint_pos (zero_lt_one.trans hw) _) (fun b => (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le)
    pre tail htailSmall
  have htagPre : sourceTag Y w Cs eta (lower w top xi) (width w top xi) lab (sourceClass a) pre=some t := by
    apply htEq.symm.trans
    simpa only [← heq] using htag
  have hcountPre : (pre.map lab).count t.bin=1 := by
    obtain ⟨u,p,v,hpre,_hidx,hbin,_hp,_hs,_ho,_ha,_hn⟩ :=
      sourceTag_witness Y w Cs eta (lower w top xi) (width w top xi) lab (sourceClass a) pre htagPre
    have hp : p ∈ pre := by rw [hpre]; simp
    have hm : t.bin ∈ pre.map lab := List.mem_map.mpr ⟨p,hp,hbin.symm⟩
    have hc := List.count_pos_iff.mpr hm
    change (ps.map lab).count t.bin=1 at hcount
    rw [heq,List.map_append,List.count_append] at hcount
    omega
  have halignPre : ∀ p ∈ pre,aligns (sourceClass a) t.rational p := by
    intro p hp
    have hh := prefix_exponent_lower hw z pre hne hdPre hprimesPre p hp
    exact halign p (hsub p hp) (by linarith [hwin.2.2.2.1])
  have hsafePre : representativeSafe w rep z (2*Clen*xi) pre := by
    intro qs hqs hneq heven
    have hpre : pre <+: ps := ⟨tail,heq.symm⟩
    have hall := (List.mem_inits _ _).mp hqs |>.trans hpre
    exact hsafe qs ((List.mem_inits _ _).mpr hall) hneq heven
  have hrefPre : pre ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap := by
    apply Finset.mem_filter.mpr
    have hdecfull : pre ++ tail ∈ decreasingPrefixes (sourcePrimeSet w top) := by
      simpa only [← heq] using (Finset.mem_filter.mp href).1
    refine ⟨decreasing_prefix_mem (pre := pre) (suf := tail) hdecfull,?_⟩
    exact ((admitted_append w z.gap z.side pre tail).mp (by simpa only [← heq] using (Finset.mem_filter.mp href).2)).1
  have htr := source_reference_transport hw htop z hs hz hg hclosed hcap pre hrefPre
  obtain ⟨U,_hU,hU⟩ := (uncapped_iff_exists_ceiling w 1 z pre).mp ((mem_uncappedPrefixes hw z pre).mp htr.1)
  have hr0 : 0 < z.gap := by linarith [hg.1]
  have hn := terminal_consistent (by norm_num : (0:ℝ)≤1) hr0 hs hz hU
  have hxpos : 0 < (terminal w z pre).cutoff := by linarith [hwin.2.2.2.1]
  have hspos : 0 < (terminal w z pre).ratio := by linarith [hwin.2.1]
  have hratio : (terminal w z pre).gap/(terminal w z pre).cutoff=(terminal w z pre).ratio := by
    apply (div_eq_iff hxpos.ne').mpr
    have hh := (eq_div_iff hspos.ne').mp hn
    nlinarith
  have hlast : pre.getLastD 0 ∈ pre := by
    have hh : pre.getLastD 0=pre.getLast hne := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      exact List.getLastD_concat
    rw [hh]
    exact List.getLast_mem hne
  have hxerr := source_representative_error hw htop hxi (hsourcePre _ hlast)
  change 0 ≤ rep (pre.getLastD 0)-primeExponent w (pre.getLastD 0) ∧
    rep (pre.getLastD 0)-primeExponent w (pre.getLastD 0) ≤ xi/Real.log w at hxerr
  rw [← terminal_lastD w z pre hne] at hxerr
  have hm := source_prefix_movement hw htop hxi hC hcomp z pre hsourcePre hlenPre
  change 0 ≤ (terminal w z pre).gap-representativeGap rep z.gap pre ∧
    (terminal w z pre).gap-representativeGap rep z.gap pre ≤ 2*Clen*xi at hm
  have hwindow : representativeWindow rep z b₀ b₁ pre := by
    exact actual_mark_to_representative_window
      (r := (terminal w z pre).gap) (rrep := representativeGap rep z.gap pre)
      (x := (terminal w z pre).cutoff) (xrep := rep (pre.getLastD 0))
      (Delta := 2*Clen*xi) (h := xi/Real.log w) hb₀ hwin.2.2.2.1 hwin.2.2.2.2.1
      (by linarith [hxerr.1]) (by linarith [hxerr.2]) (by linarith [hm.1]) (by linarith [hm.2])
      (by rw [hratio]; exact hwin.2.1) (by rw [hratio]; exact hwin.2.2.1) hh hsmall
  exact ⟨hwin.1,hne,hlenPre,source_list_boxed (zero_lt_one.trans hw) htop hxi pre hsourcePre,
    hsafePre,hwindow,t,htagPre,hcountPre,halignPre⟩
end NumberTheoryLean.MarkedPrefixCandidate

end

section

namespace NumberTheoryLean.SourceMarkedStopping
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open StrongReferenceTransport StrongSourceFamilies SourceStopPredicate RepresentativeAdmission RepresentativeStopGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ActualSourceTags FiniteFirstTag MarkedPrefixTools SuccessfulMarkedCoordinates
open ReferenceAdmission ReferencePruning
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass ErdosInverseAlignment
open MarkedPrefixCandidate StoppedPrefixExistence StoppedCountAdapters StoppedVertexHistory
open StoppedEvaluation StoppedTraceSets
attribute [local instance] Classical.propDecidable

theorem marked_prefix_forces_actual_stop (Y : ℕ) {w top Cs eta Clen B xi b₀ b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (hb₀ : 0 < b₀) (hCs : Cs < 2*b₀)
    (hsearch : b₁ < w^((1/4:ℝ))) (hh : xi/Real.log w ≤ b₀)
    (hsmall : 2*Clen*xi+(206/100)*(xi/Real.log w) ≤ (4/100)*b₀)
    (a : ℕ → ℕ) (H : Finset ℕ) (mu : ℝ) (z : Node) (ps pre tail : List ℕ) (heq : ps=pre++tail)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (hroot : b₁/2 < z.cutoff)
    (href : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hlen : (ps.length:ℝ) ≤ Clen*Real.log B)
    (hsafe : representativeSafe w (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z (2*Clen*xi) ps)
    (t : Tag (binCount w top xi))
    (htag : sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps=some t)
    (hcount : (ps.map (label (zero_lt_one.trans hw) htop hxi)).count t.bin=1)
    (halign : ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass a) t.rational p)
    (hwin : primeWindow b₀ b₁ (terminal w z pre)) :
    ∃ first rest : List ℕ,ps=first++rest ∧ first ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z H (sourcePrimeSet w top) mu) := by
  have hc := marked_prefix_candidate Y hw htop hxi hC hcomp hb₀ hCs hsearch hh hsmall
    a z ps pre tail heq hs hz hg hclosed hcap hroot href hlen hsafe t htag hcount halign hwin
  apply reference_candidate_forces_stop w _ (rootVertex z H (sourcePrimeSet w top) mu) ps href
  refine ⟨pre,tail,heq,?_⟩
  unfold lowerStop
  rw [after_node,after_past]
  simpa only [rootVertex,List.nil_append] using hc
end NumberTheoryLean.SourceMarkedStopping

end

end Erdos970

end OAI
