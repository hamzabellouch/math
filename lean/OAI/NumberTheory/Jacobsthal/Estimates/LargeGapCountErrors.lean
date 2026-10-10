import Mathlib
import OAI.NumberTheory.Jacobsthal.Paths.WordIntervalGeometry
import OAI.NumberTheory.Jacobsthal.Sieve.LiteralModulusEnvelope
import OAI.NumberTheory.Jacobsthal.Sieve.ReferenceExponentialTail

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FiniteErrorTelescoping


theorem endpoint_difference_le (E : List ℕ → ℝ) (pre ps : List ℕ) (delta : ℝ)
    (h : ∀ before p after,ps=before++p::after →
      |E ((pre++before)++[p])-E (pre++before)| ≤ delta) :
    |E (pre++ps)-E pre| ≤ (ps.length:ℝ)*delta := by
  induction ps generalizing pre with
  | nil => simp
  | cons p ps ih =>
    have hfirst := h [] p ps rfl
    simp only [List.append_nil] at hfirst
    have htail : ∀ before q after,ps=before++q::after →
        |E (((pre++[p])++before)++[q])-E ((pre++[p])++before)| ≤ delta := by
      intro before q after he
      have hh := h (p::before) q after (by rw [List.cons_append,he])
      simpa only [List.append_assoc,List.singleton_append] using hh
    have hh := ih (pre++[p]) htail
    have htri := abs_add_le (E ((pre++[p])++ps)-E (pre++[p])) (E (pre++[p])-E pre)
    have he : (pre++[p])++ps=pre++p::ps := by simp
    rw [he] at hh htri
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    have htel : E (pre++p::ps)-E (pre++[p])+(E (pre++[p])-E pre)=E (pre++p::ps)-E pre := by ring
    rw [htel] at htri
    nlinarith

theorem exists_large_edge (E : List ℕ → ℝ) (pre ps : List ℕ) (delta : ℝ)
    (h : (ps.length:ℝ)*delta < |E (pre++ps)-E pre|) :
    ∃ before p after,ps=before++p::after ∧ delta < |E ((pre++before)++[p])-E (pre++before)| := by
  by_contra! hn
  have hh := endpoint_difference_le E pre ps delta hn
  linarith

theorem witness_from_endpoints (E : List ℕ → ℝ) (pre ps : List ℕ) (H : ℕ) (hH : 0 < H)
    (eps : ℝ) (heps : 0 < eps) (hlen : ps.length ≤ H)
    (hstart : |E pre| ≤ eps/2) (hend : eps < |E (pre++ps)|) :
    ∃ before p after,ps=before++p::after ∧ eps/(4*H) < |E ((pre++before)++[p])-E (pre++before)| := by
  have hHr : 0 < (H:ℝ) := by exact_mod_cast hH
  have hdelta : 0 ≤ eps/(4*H) := by positivity
  have hm : (ps.length:ℝ)*(eps/(4*H)) ≤ eps/4 := by
    have hl : (ps.length:ℝ) ≤ H := by exact_mod_cast hlen
    have hh := mul_le_mul_of_nonneg_right hl hdelta
    have he : (H:ℝ)*(eps/(4*H))=eps/4 := by field_simp [hHr.ne']
    rwa [he] at hh
  have htri := abs_add_le (E (pre++ps)-E pre) (E pre)
  simp only [sub_add_cancel] at htri
  apply exists_large_edge E pre ps (eps/(4*H))
  linarith
end NumberTheoryLean.FiniteErrorTelescoping



namespace NumberTheoryLean.ActualCountErrorEdges
open ErdosInverseCounts


noncomputable def relativeCountError (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ) (d : ℕ) : ℝ :=
  (modulusCount Y small a d:ℝ)/(((Y:ℝ)/(d:ℝ))*V0)-1
noncomputable def wordCountError (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ) (ps : List ℕ) : ℝ :=
  relativeCountError Y small a V0 ps.prod

theorem relative_error_increment (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (d u : ℕ) (hd : 0 < d) (hu : 0 < u) :
    relativeCountError Y small a V0 (d*u)-relativeCountError Y small a V0 d=
      ((modulusCount Y small a (d*u):ℝ)-(modulusCount Y small a d:ℝ)/(u:ℝ))/
        ((Y:ℝ)*V0/((d:ℝ)*(u:ℝ))) := by
  have hYr : (Y:ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  have hdr : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hur : (u:ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold relativeCountError
  rw [Nat.cast_mul]
  field_simp [hYr,hdr,hur,hV.ne']
  ring

theorem relative_large_edge_iff (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 delta : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (d u : ℕ) (hd : 0 < d) (hu : 0 < u) :
    delta < |relativeCountError Y small a V0 (d*u)-relativeCountError Y small a V0 d| ↔
      NodeBadEdge Y small a delta V0 d u := by
  have hYr : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
  have hur : 0 < (u:ℝ) := by exact_mod_cast hu
  have hmu : 0 < (Y:ℝ)*V0/((d:ℝ)*(u:ℝ)) := by positivity
  rw [relative_error_increment Y small a V0 hY hV d u hd hu,abs_div,abs_of_pos hmu]
  rw [lt_div_iff₀ hmu]
  unfold NodeBadEdge
  simp only [mul_div_assoc,mul_assoc]

theorem word_large_edge_iff (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 delta : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (pre : List ℕ) (u : ℕ) (hd : 0 < pre.prod) (hu : 0 < u) :
    delta < |wordCountError Y small a V0 (pre++[u])-wordCountError Y small a V0 pre| ↔
      NodeBadEdge Y small a delta V0 pre.prod u := by
  unfold wordCountError
  rw [List.prod_append,List.prod_singleton]
  exact relative_large_edge_iff Y small a V0 delta hY hV pre.prod u hd hu
end NumberTheoryLean.ActualCountErrorEdges



namespace NumberTheoryLean.ActualCountErrorMass
open ErdosInverseCounts ActualCountErrorEdges
open ErdosPrimeInputs.PrimePrefixMass


theorem count_error_identity (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (d : ℕ) (hd : 0 < d) :
    |(modulusCount Y small a d:ℝ)-((Y:ℝ)/(d:ℝ))*V0|=
      ((Y:ℝ)/(d:ℝ))*V0*|relativeCountError Y small a V0 d| := by
  have hYr : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
  have hmu : 0 < ((Y:ℝ)/(d:ℝ))*V0 := by positivity
  have he : (modulusCount Y small a d:ℝ)-((Y:ℝ)/(d:ℝ))*V0=
      (((Y:ℝ)/(d:ℝ))*V0)*relativeCountError Y small a V0 d := by
    unfold relativeCountError
    field_simp [hmu.ne']
  rw [he,abs_mul,abs_of_pos hmu]

theorem word_count_error_weight (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (ps : List ℕ) (hd : 0 < ps.prod) :
    |(modulusCount Y small a ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|=
      ((Y:ℝ)*V0)*(prefixWeight ps*|wordCountError Y small a V0 ps|) := by
  rw [count_error_identity Y small a V0 hY hV ps.prod hd,StoppedVertexHistory.prefixWeight_product]
  unfold wordCountError
  ring

theorem finite_count_error_weight (B : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (hY : 0 < Y) (hV : 0 < V0) (F : Finset (List ℕ)) (hF : ∀ ps∈F,0 < ps.prod) :
    (B^2/((Y:ℝ)*V0))*(∑ ps∈F,|(modulusCount Y small a ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|)=
      B^2*(∑ ps∈F,prefixWeight ps*|wordCountError Y small a V0 ps|) := by
  have he := Finset.sum_congr rfl (fun ps hp => word_count_error_weight Y small a V0 hY hV ps (hF ps hp))
  rw [he,← Finset.mul_sum]
  have hYr : (Y:ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  field_simp [hYr,hV.ne']
end NumberTheoryLean.ActualCountErrorMass



namespace NumberTheoryLean.CountErrorClassification
open PrimeHistories ActualCountErrorEdges ErdosInverseCounts

attribute [local instance] Classical.propDecidable

noncomputable def errorSum (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ) (F : Finset (List ℕ)) : ℝ :=
  ∑ ps∈F,|(modulusCount Y small a ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|
noncomputable def largeGapWords (w K : ℝ) (z : Node) (F : Finset (List ℕ)) : Finset (List ℕ) :=
  F.filter (fun ps => K<(terminal w z ps).gap)
noncomputable def smallErrorWords (w K eps : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (z : Node) (F : Finset (List ℕ)) : Finset (List ℕ) :=
  F.filter (fun ps => (terminal w z ps).gap ≤ K ∧ |wordCountError Y small a V0 ps| ≤ eps)
noncomputable def badCompactWords (w K eps : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (z : Node) (F : Finset (List ℕ)) : Finset (List ℕ) :=
  F.filter (fun ps => (terminal w z ps).gap ≤ K ∧ eps < |wordCountError Y small a V0 ps|)

theorem error_sum_partition (w K eps : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (z : Node) (F : Finset (List ℕ)) :
    errorSum Y small a V0 F=
      errorSum Y small a V0 (largeGapWords w K z F)+
      errorSum Y small a V0 (smallErrorWords w K eps Y small a V0 z F)+
      errorSum Y small a V0 (badCompactWords w K eps Y small a V0 z F) := by
  simp only [errorSum,largeGapWords,smallErrorWords,badCompactWords,Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ps _hp
  by_cases hgap : K<(terminal w z ps).gap
  · simp [hgap,not_le_of_gt hgap]
  · have hg : (terminal w z ps).gap ≤ K := le_of_not_gt hgap
    by_cases he : |wordCountError Y small a V0 ps| ≤ eps
    · simp [hgap,hg,he,not_lt_of_ge he]
    · simp [hgap,hg,he,lt_of_not_ge he]
end NumberTheoryLean.CountErrorClassification



namespace NumberTheoryLean.LiteralCountErrorLedger
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedCountAdapters StoppedVertexHistory StoppedTraceSets
open StoppedModulusCount FlatStoppedIdentity ReferenceAdmission ErdosInverseCounts StoppedTraceAdmission

attribute [local instance] Classical.propDecidable

theorem negative_abs_le_signed (k : ℕ) (x : ℝ) : -|x| ≤ (-1:ℝ)^k*x := by
  have hh := neg_abs_le ((-1:ℝ)^k*x)
  simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hh

theorem literal_count_error_ledger (w : ℝ) (Y : ℕ) (small P : Finset ℕ) (residue : ℕ → ℕ)
    (z : Node) (V0 : ℝ) (stop : List ℕ → Prop) (hi : z.side=.even) (hP : ∀ p∈P,p.Prime) :
    ((Y:ℝ)*V0)*referencePolynomial w P z.side z.gap +
      (∑ ps∈stopped w stop P.card (rootVertex z ∅ P ((Y:ℝ)*V0)),
        (countSurvivors Y small residue (after w (rootVertex z ∅ P ((Y:ℝ)*V0)) ps)-
          referenceValue w (after w (rootVertex z ∅ P ((Y:ℝ)*V0)) ps))) -
      (∑ ps∈expanded w stop P.card (rootVertex z ∅ P ((Y:ℝ)*V0)),
        |(modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|) ≤
      countSurvivors Y small residue (rootVertex z ∅ P ((Y:ℝ)*V0)) := by
  let v := rootVertex z ∅ P ((Y:ℝ)*V0)
  have hRaw := actual_reference_error_lower_bound w Y small residue stop P.card v le_rfl hi
  have hErr : -(∑ ps∈expanded w stop P.card v,
      |(modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|) ≤
      ∑ ps∈expanded w stop P.card v,(-1:ℝ)^ps.length*(countMass Y small residue (after w v ps)-(after w v ps).scale) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro ps hps
    rw [trace_mass_eq_modulusCount w Y small P residue z ((Y:ℝ)*V0) stop P.card hP (Or.inl hps),after_scale_product]
    change -|(modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0| ≤
      (-1:ℝ)^ps.length*((modulusCount Y small residue ps.prod:ℝ)-((Y:ℝ)*V0)/(ps.prod:ℝ))
    have he : ((Y:ℝ)*V0)/(ps.prod:ℝ)=((Y:ℝ)/(ps.prod:ℝ))*V0 := by ring
    rw [he]
    exact negative_abs_le_signed ps.length _
  change ((Y:ℝ)*V0)*referencePolynomial w P z.side z.gap+_+_ ≤ _ at hRaw
  change ((Y:ℝ)*V0)*referencePolynomial w P z.side z.gap+_-_ ≤ _
  linarith

theorem expanded_reference_subset (w : ℝ) (P : Finset ℕ) (z : Node) (V : ℝ) (stop : List ℕ → Prop) (n : ℕ) :
    expanded w stop n (rootVertex z ∅ P V) ⊆ referencePrefixes w P z.side z.gap := by
  intro ps hps
  exact trace_reference_member w stop n (rootVertex z ∅ P V) (Or.inl hps)
end NumberTheoryLean.LiteralCountErrorLedger



namespace NumberTheoryLean.ReferenceCountEnvelope
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission StrongReferenceTransport StrongSourceFamilies
open ActualCountErrorEdges WordIntervalGeometry SourcePrimeProductData LogarithmicBinPartition ErdosModulusRelative
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem reference_count_envelope (aStar : ℝ) (ha : 0 < aStar) :
    ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧ ∀ B w top : ℝ,3 ≤ B → w₀ ≤ w → w < top →
      ∀ Y : ℕ,0 < Y → ∀ z : Node,z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      z.side=.even → 199/100 ≤ z.ratio → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ ps∈referencePrefixes w (sourcePrimeSet w top) z.side z.gap,
        |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| ≤
          C*Real.exp (-(1/192:ℝ)*(terminal w z ps).gap) := by
  obtain ⟨C,W,hC,hW,hEnvelope⟩ := modulus_error_envelope aStar ha
  refine ⟨C*Real.exp ((2-aStar)/192),W,mul_pos hC (Real.exp_pos _),hW,?_⟩
  intro B w top hB hw₀ htop Y hY z hroot hi h199 hz hcut hclosed hpower residue ps hps
  have hw : 1 < w := hW.trans_le hw₀
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  have hfloor := (source_reference_transport hw htop z hs hz hg hclosed hcap ps hps).2
  have hData := reference_word_product_data hw htop z.side z.gap ps hps
  have hsrc := (mem_decreasingPrefixes.mp (Finset.mem_filter.mp hps).1).2
  have hpos : ∀ p∈ps,0 < p := fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsrc p hp)).1.pos
  have hgap := word_interval_gap Y hY z hroot ps hpos
  have hv : aStar ≤ wordIntervalExponent w Y ps := by linarith
  have hh := hEnvelope w hw₀ Y ps.prod residue hY hData.1 hData.2.1 hData.2.2 hv
  change |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| ≤
    C*Real.exp (-wordIntervalExponent w Y ps/192) at hh
  rw [hgap] at hh
  have he : Real.exp (-((terminal w z ps).gap+aStar-2)/192)=
      Real.exp ((2-aStar)/192)*Real.exp (-(1/192:ℝ)*(terminal w z ps).gap) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [he,mul_assoc] using hh
end NumberTheoryLean.ReferenceCountEnvelope



namespace NumberTheoryLean.CountErrorFamilyMajorant
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission StrongReferenceTransport StrongSourceFamilies
open ReferenceCountEnvelope ActualCountErrorMass ActualCountErrorEdges SourcePrimeProductData
open LogarithmicBinPartition ErdosInverseCounts
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail


theorem count_error_family_majorant (aStar : ℝ) (ha : 0 < aStar) :
    ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧ ∀ B w top : ℝ,3 ≤ B → w₀ ≤ w → w < top →
      ∀ Y : ℕ,0 < Y → ∀ z : Node,z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      z.side=.even → 199/100 ≤ z.ratio → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ F : Finset (List ℕ),F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (B^2/((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊))*(∑ ps∈F,
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue ps.prod:ℝ)-
          ((Y:ℝ)/(ps.prod:ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊|) ≤ C*(B^2*(∑ ps∈F,prefixWeight ps)) := by
  obtain ⟨C,W,hC,hW,hEnvelope⟩ := reference_count_envelope aStar ha
  refine ⟨C,max W 2,hC,hW.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ htop Y hY z hroot hi h199 hz hcut hclosed hpower residue F hF
  have hw : 1 < w := hW.trans_le ((le_max_left _ _).trans hw₀)
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hw₀
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hp : ∀ ps∈F,0 < ps.prod := fun ps hps => (reference_word_product_data hw htop z.side z.gap ps (hF hps)).1
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  have hErr : ∀ ps∈F,|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| ≤ C := by
    intro ps hps
    have hh := hEnvelope B w top hB ((le_max_left _ _).trans hw₀) htop Y hY z hroot hi h199 hz hcut hclosed hpower residue ps (hF hps)
    have hfloor := (source_reference_transport hw htop z hs hz hg hclosed hcap ps (hF hps)).2
    have he : Real.exp (-(1/192:ℝ)*(terminal w z ps).gap) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact hh.trans ((mul_le_mul_of_nonneg_left he hC.le).trans_eq (mul_one C))
  rw [finite_count_error_weight B Y _ residue _ hY hV F hp]
  have hsum : (∑ ps∈F,prefixWeight ps*|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
      (SmallSieveFinite.smallEuler ⌊w⌋₊) ps|) ≤ C*(∑ ps∈F,prefixWeight ps) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ps hps
    have hh := mul_le_mul_of_nonneg_left (hErr ps hps) (prefixWeight_nonneg ps)
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg B)
  nlinarith
end NumberTheoryLean.CountErrorFamilyMajorant



namespace NumberTheoryLean.LargeGapCountErrors
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceAdmission
open ReferenceCountEnvelope ReferenceExponentialTail ActualCountErrorMass ActualCountErrorEdges SourcePrimeProductData
open LogarithmicBinPartition ErdosInverseCounts
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail


theorem uniform_large_gap_count_errors (aStar d eps : ℝ) (ha : 0 < aStar) (hd : 0 < d) (heps : 0 < eps) :
    ∃ K₀ B₀ w₀ : ℝ,3 ≤ K₀ ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ K B w top : ℝ,K₀ ≤ K → B₀ ≤ B → w₀ ≤ w → w < top → Real.log B ≤ d*Real.log w →
      ∀ Y : ℕ,0 < Y → ∀ z : Node,z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ residue : ℕ → ℕ,∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps∈F,K < (terminal w z ps).gap) →
      (B^2/((Y:ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊))*(∑ ps∈F,
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue ps.prod:ℝ)-
          ((Y:ℝ)/(ps.prod:ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊|) ≤ eps := by
  obtain ⟨C,WE,hC,hWE,hEnvelope⟩ := reference_count_envelope aStar ha
  obtain ⟨K₀,B₀,WT,hK₀,hB₀,hWT,hTail⟩ := uniform_reference_exponential_tail d (1/192) (eps/C) hd (by norm_num) (by positivity)
  refine ⟨K₀,B₀,max WE (max WT 2),hK₀,hB₀,hWE.trans_le (le_max_left _ _),?_⟩
  intro K B w top hK hB hw₀ htop hcomp Y hY z hroot hi h199 h23 hz hcut hclosed hpower residue F hF hGap
  have hw : 1 < w := hWE.trans_le ((le_max_left _ _).trans hw₀)
  have hw2 : 2 ≤ w := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hw₀
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hp : ∀ ps∈F,0 < ps.prod := fun ps hps => (reference_word_product_data hw htop z.side z.gap ps (hF hps)).1
  rw [finite_count_error_weight B Y _ residue _ hY hV F hp]
  have hErr : ∀ ps∈F,|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) ps| ≤
      C*Real.exp (-(1/192:ℝ)*(terminal w z ps).gap) := by
    intro ps hps
    exact hEnvelope B w top (hB₀.trans hB) ((le_max_left _ _).trans hw₀) htop Y hY z hroot hi h199 hz hcut hclosed hpower residue ps (hF hps)
  have hsum : (∑ ps∈F,prefixWeight ps*|wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue
      (SmallSieveFinite.smallEuler ⌊w⌋₊) ps|) ≤ C*(∑ ps∈F,prefixWeight ps*Real.exp (-(1/192:ℝ)*(terminal w z ps).gap)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ps hps
    have hh := mul_le_mul_of_nonneg_left (hErr ps hps) (prefixWeight_nonneg ps)
    nlinarith
  have htail := hTail K B w top hK hB ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀)
    htop hcomp z hi h199 h23 hz hcut hclosed hpower F hF hGap
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg B)
  have ht := mul_le_mul_of_nonneg_left htail hC.le
  have he : C*(eps/C)=eps := mul_div_cancel₀ eps hC.ne'
  rw [he] at ht
  nlinarith
end NumberTheoryLean.LargeGapCountErrors


end Erdos970

end OAI
