import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Estimates.CanonicalCorrectionSum
import OAI.NumberTheory.Jacobsthal.Partitions.TwoSingletonBins
import OAI.NumberTheory.Jacobsthal.Primes.StoppedReferencePrimes
import OAI.NumberTheory.Jacobsthal.Probability.PaperTagEventInclusion

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosSubsetWord
open ErdosCofactorChoices

attribute [local instance] Classical.decEq

noncomputable def descendingWord {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) : List ℕ :=
  (selectionPrimes f).sort (· ≥ ·)

theorem mem_descendingWord {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) (p : ℕ) :
    p ∈ descendingWord f ↔ ∃ i,p ∈ f i := by
  simp [descendingWord,selectionPrimes]

theorem descendingWord_nodup {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) :
    (descendingWord f).Nodup := Finset.sort_nodup _ _

theorem descendingWord_strict {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) :
    (descendingWord f).Pairwise (· > ·) := (Finset.sortedGT_sort _).pairwise

theorem descendingWord_toFinset {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) :
    (descendingWord f).toFinset=selectionPrimes f := Finset.sort_toFinset _ _

theorem descendingWord_length {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (mult : ι → ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (f : ι → Finset ℕ)
    (hf : f ∈ selections P mult) : (descendingWord f).length=∑ i,mult i := by
  have hmem := (mem_selections P mult f).mp hf
  rw [descendingWord,Finset.length_sort,selectionPrimes,Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun i _ => (hmem i).2)
  · intro i _ j _ hij
    exact selection_disjoint P hd f (fun b => (hmem b).1) hij

theorem descendingWord_product {ι : Type*} [Fintype ι] (P : ι → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (f : ι → Finset ℕ)
    (hf : ∀ i,f i ⊆ P i) : (descendingWord f).prod=selectionProduct f := by
  rw [selectionProduct_eq_union P hd f hf,← descendingWord_toFinset]
  simpa only [List.map_id'] using (List.prod_toFinset (fun p : ℕ => p) (descendingWord_nodup f)).symm

theorem descendingWord_primes {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (mult : ι → ℕ)
    (hP : ∀ i,∀ p ∈ P i,Nat.Prime p) (f : ι → Finset ℕ) (hf : f ∈ selections P mult) :
    ∀ p ∈ descendingWord f,Nat.Prime p := by
  intro p hp
  obtain ⟨i,hi⟩ := (mem_descendingWord f p).mp hp
  exact hP i p (((mem_selections P mult f).mp hf i).1 hi)

end ErdosSubsetWord



namespace ErdosSearchCount
open NumberTheoryLean FinitePathGeometry PrimeTiltGeometry PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure


noncomputable def selectedCount (P : ℕ → Bool) (ps : List ℕ) : ℕ := (ps.filter P).length
noncomputable def remainderSum (w : ℝ) (P : ℕ → Bool) (ps : List ℕ) : ℝ :=
  ((ps.filter (fun p => !(P p))).map (primeExponent w)).sum

theorem valid_half {i : Side} {s : ℝ} (hs : Valid i s) : (1:ℝ)/2 ≤ s := by
  cases i <;> dsimp [Valid] at hs <;> linarith

theorem child_gap_third {w ell S : ℝ} {z : Node} {p : ℕ}
    (hell : 0 ≤ ell) (hs : Valid z.side z.ratio)
    (hp : p ∈ nodeChildren w ell S z) : z.gap ≤ 3*(step w z p).gap := by
  have hx := child_exponent_positive hell hp
  have ht := valid_half (child_valid hs hp)
  change (1:ℝ)/2 ≤ z.gap/primeExponent w p-1 at ht
  have hh : (3:ℝ)/2 ≤ z.gap/primeExponent w p := by linarith
  have hm := (le_div_iff₀ hx).mp hh
  change z.gap ≤ 3*(z.gap-primeExponent w p)
  linarith

theorem initial_gap_le_search_power (w ell S : ℝ) (P : ℕ → Bool) (z : Node)
    (ps : List ℕ) (hell : 0 ≤ ell) (hs : Valid z.side z.ratio)
    (ha : allowed w ell S z ps) :
    z.gap ≤ (3:ℝ)^(selectedCount P ps)*((terminal w z ps).gap+remainderSum w P ps) := by
  induction ps generalizing z with
  | nil => simp [selectedCount,remainderSum]
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := (allowed_cons w ell S z p ps).mp ha
    have htail := ih (step w z p) (child_valid hs hp) ht
    have hx := (child_exponent_positive hell hp).le
    have hpow : (1:ℝ) ≤ 3^(selectedCount P ps) := one_le_pow₀ (by norm_num)
    cases he : P p with
    | true =>
      have hh := child_gap_third hell hs hp
      simp [selectedCount,remainderSum,he] at *
      rw [pow_succ]
      nlinarith
    | false =>
      simp [selectedCount,remainderSum,he] at *
      change z.gap-primeExponent w p ≤ _ at htail
      nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hx]

end ErdosSearchCount



namespace ErdosSearchCount
open NumberTheoryLean PrimeHistories PrimeBinRepresentatives ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

noncomputable def searchFlag {n : ℕ} (w : ℝ) (lower : Fin n → ℝ)
    (label : ℕ → Fin n) (p : ℕ) : Bool := decide (searchBin w (lower (label p)))
noncomputable def searchCount {n : ℕ} (w : ℝ) (lower : Fin n → ℝ)
    (label : ℕ → Fin n) (ps : List ℕ) : ℕ := selectedCount (searchFlag w lower label) ps

theorem searchCount_labels {n : ℕ} (w : ℝ) (lower : Fin n → ℝ)
    (label : ℕ → Fin n) (ps : List ℕ) :
    searchCount w lower label ps=(ps.map label).countP (fun b => decide (searchBin w (lower b))) := by
  rw [searchCount,selectedCount,← List.countP_eq_length_filter,List.countP_map]
  rfl

theorem searchCount_label_invariant {n : ℕ} (w : ℝ) (lower : Fin n → ℝ)
    (label : ℕ → Fin n) (ps qs : List ℕ) (he : ps.map label=qs.map label) :
    searchCount w lower label ps=searchCount w lower label qs := by
  rw [searchCount_labels,searchCount_labels,he]

theorem nonsearch_exponent_bound {w top xi : ℝ} (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) {p : ℕ} (hp : p ∈ sourcePrimeSet w top)
    (hn : searchFlag w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) p=false) :
    primeExponent w p ≤ w^((1/4:ℝ))+xi/Real.log w := by
  have hlo : leftExponent w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p)) < w^((1/4:ℝ)) := by
    have hh : ¬searchBin w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p)) := by
      simpa only [searchFlag,decide_eq_false_iff_not] using hn
    exact lt_of_not_ge hh
  have hsource := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp
  have hmem := label_prime_membership (zero_lt_one.trans hw) htop hxi hsource.1 hsource.2
  have hupper := (bin_exponent_bounds hw (endpoint_pos (zero_lt_one.trans hw) _)
    (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le hmem).2
  have hwidth := bin_exponent_width (w:=w)
    (R:=lower w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (xi:=width w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (endpoint_pos (zero_lt_one.trans hw) _)
    (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le
  have hlog : Real.log (1+width w top xi (label (zero_lt_one.trans hw) htop hxi p)) ≤ xi := by
    have hpos := effectiveWidth_pos (zero_lt_one.trans hw) htop hxi
    have he := Real.log_le_sub_one_of_pos (show 0 < 1+effectiveWidth w top xi by linarith)
    have hle := effectiveWidth_le (zero_lt_one.trans hw) htop hxi
    change Real.log (1+effectiveWidth w top xi) ≤ xi
    linarith
  have hd := div_le_div_of_nonneg_right hlog (Real.log_pos hw).le
  change primeExponent w p ≤ rightExponent w
    (lower w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (width w top xi (label (zero_lt_one.trans hw) htop hxi p)) at hupper
  linarith

theorem remainderSum_le_length_mul (w : ℝ) (P : ℕ → Bool) (ps : List ℕ) {A : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ p ∈ ps,P p=false → primeExponent w p ≤ A) :
    remainderSum w P ps ≤ (ps.length:ℝ)*A := by
  induction ps with
  | nil => simp [remainderSum]
  | cons p ps ih =>
    have ht := ih (fun q hq => hbound q (by simp [hq]))
    cases he : P p with
    | true => simp [remainderSum,he] at *; linarith
    | false =>
      have hp := hbound p (by simp) he
      simp [remainderSum,he] at *
      linarith

theorem source_remainder_bound {w top xi B Clen : ℝ} (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hlog : 1 ≤ Real.log w) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w) (ps : List ℕ)
    (hp : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) (hlen : (ps.length:ℝ) ≤ Clen*Real.log B) :
    remainderSum w (searchFlag w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi)) ps ≤
      2*Clen*Real.log w*(w^((1/4:ℝ))+1) := by
  have hxdiv : xi/Real.log w ≤ 1 := (div_le_one (Real.log_pos hw)).mpr (hxi1.trans hlog)
  have hA : 0 ≤ w^((1/4:ℝ))+1 := by positivity
  have hm := remainderSum_le_length_mul w
    (searchFlag w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi)) ps hA
    (fun p hps hn => (nonsearch_exponent_bound hw htop hxi (hp p hps) hn).trans (by linarith))
  have hl : (ps.length:ℝ) ≤ 2*Clen*Real.log w := by
    have hh := mul_le_mul_of_nonneg_left hcomp hC
    nlinarith
  exact hm.trans (mul_le_mul_of_nonneg_right hl hA)

end ErdosSearchCount



namespace ErdosSearchCount
open _root_.Filter _root_.Erdos970.Filter NumberTheoryLean FinitePathGeometry PrimeHistories
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition


theorem nonsearch_budget_le (K Clen epsilon : ℝ) (hC : 0 ≤ Clen) (hepsilon : 0 < epsilon) :
    ∀ᶠ w : ℝ in atTop,K+2*Clen*Real.log w*(w^((1/4:ℝ))+1) ≤ epsilon*w^((1/2:ℝ)) := by
  let eps : ℝ := epsilon/(8*(Clen+1))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hlog := (isLittleO_log_rpow_atTop (r := (1/4:ℝ)) (by norm_num)).bound heps
  have hpow : ∀ᶠ w : ℝ in atTop,2*K/epsilon ≤ w^((1/2:ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).eventually_ge_atTop (2*K/epsilon)
  filter_upwards [hlog,hpow,eventually_gt_atTop (1:ℝ)] with w hlog hK hw
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hL : 0 < Real.log w := Real.log_pos hw
  have hp : 0 < w^((1/4:ℝ)) := Real.rpow_pos_of_pos hw0 _
  have hp1 : 1 ≤ w^((1/4:ℝ)) := Real.one_le_rpow hw.le (by norm_num)
  have hlog' : Real.log w ≤ eps*w^((1/4:ℝ)) := by
    simpa only [Real.norm_eq_abs,abs_of_pos hL,abs_of_pos hp] using hlog
  have he : w^((1/4:ℝ))*w^((1/4:ℝ))=w^((1/2:ℝ)) := by
    rw [← Real.rpow_add hw0]; norm_num
  have hb : 4*Clen*eps ≤ epsilon/2 := by
    dsimp [eps]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have hden : 0 < 8*(Clen+1) := by positivity
    field_simp
    nlinarith
  have hs : 2*Clen*Real.log w*(w^((1/4:ℝ))+1) ≤ epsilon*w^((1/2:ℝ))/2 := by
    calc
      _ ≤ 4*Clen*Real.log w*w^((1/4:ℝ)) := by nlinarith [mul_nonneg (mul_nonneg hC hL.le) (sub_nonneg.mpr hp1)]
      _ ≤ 4*Clen*(eps*w^((1/4:ℝ)))*w^((1/4:ℝ)) := by gcongr
      _ = (4*Clen*eps)*w^((1/2:ℝ)) := by rw [← he]; ring
      _ ≤ (epsilon/2)*w^((1/2:ℝ)) := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hw0.le _)
      _ = _ := by ring
  have hK' := (div_le_iff₀ hepsilon).mp hK
  nlinarith

theorem nonsearch_budget_small (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,K+2*Clen*Real.log w*(w^((1/4:ℝ))+1) ≤ w^((1/2:ℝ)) := by
  simpa only [one_mul] using nonsearch_budget_le K Clen 1 hC (by norm_num)

theorem logarithmic_count_of_power {w R : ℝ} {k : ℕ} (hw : 1 < w)
    (hgap : w ≤ (3:ℝ)^k*R) (hsmall : R ≤ w^((1/2:ℝ))) :
    Real.log w/(2*Real.log 3) ≤ (k:ℝ) := by
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hpow : 0 < (3:ℝ)^k := by positivity
  have hm := hgap.trans (mul_le_mul_of_nonneg_left hsmall hpow.le)
  have hl := Real.log_le_log hw0 hm
  rw [Real.log_mul hpow.ne' (Real.rpow_pos_of_pos hw0 _).ne',Real.log_pow,
    Real.log_rpow hw0] at hl
  apply (div_le_iff₀ (show 0 < 2*Real.log 3 by positivity)).mpr
  nlinarith

theorem actual_search_count (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ (top B xi ell S : ℝ) (hw : 1 < w) (htop : w < top)
      (hxi : 0 < xi),xi ≤ 1 → Real.log B ≤ 2*Real.log w → 1 ≤ ell →
      ∀ (z : Node) (ps : List ℕ),Valid z.side z.ratio → w ≤ z.gap →
      allowed w ell S z ps → (terminal w z ps).gap ≤ K →
      (ps.length:ℝ) ≤ Clen*Real.log B → (∀ p ∈ ps,p ∈ sourcePrimeSet w top) →
      Real.log w/(2*Real.log 3) ≤
        (searchCount w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) ps:ℝ) := by
  filter_upwards [nonsearch_budget_small K Clen hC,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w hsmall hlog
  intro top B xi ell S hw htop hxi hxi1 hcomp hell z ps hs hstart ha hK hlen hp
  have hr := source_remainder_bound hw htop hxi hxi1 hlog hC hcomp ps hp hlen
  have hi := initial_gap_le_search_power w ell S
    (searchFlag w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi)) z ps
    (by linarith : 0 ≤ ell) hs ha
  apply logarithmic_count_of_power hw (hstart.trans hi)
  exact (add_le_add hK hr).trans hsmall

noncomputable def searchConstant : ℝ := 1/(4*Real.log 3)
theorem searchConstant_pos : 0 < searchConstant := by unfold searchConstant; positivity

theorem actual_search_count_uniform (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ (top B xi ell S : ℝ) (hw : 1 < w) (htop : w < top)
      (hxi : 0 < xi),xi ≤ 1 → Real.log B ≤ 2*Real.log w → 1 ≤ ell →
      ∀ (z : Node) (ps : List ℕ),Valid z.side z.ratio → w ≤ z.gap →
      allowed w ell S z ps → (terminal w z ps).gap ≤ K →
      (ps.length:ℝ) ≤ Clen*Real.log B → (∀ p ∈ ps,p ∈ sourcePrimeSet w top) →
      searchConstant*Real.log w ≤
        (searchCount w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) ps:ℝ) := by
  filter_upwards [actual_search_count K Clen hC] with w hwcount
  intro top B xi ell S hw htop hxi hxi1 hcomp hell z ps hs hstart ha hK hlen hp
  have hh := hwcount top B xi ell S hw htop hxi hxi1 hcomp hell z ps hs hstart ha hK hlen hp
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hwL : 0 ≤ Real.log w := (Real.log_pos hw).le
  apply le_trans _ hh
  unfold searchConstant
  field_simp
  nlinarith

end ErdosSearchCount



namespace ErdosSearchCount
open _root_.Filter _root_.Erdos970.Filter NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership JacobsthalSourceScale
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition


theorem paper_incoming_geometry : ∀ᶠ L : ℝ in atTop,
    1 < sourceW L ∧ sourceW L < Real.exp L ∧ Real.log (sourceB L) ≤ 2*Real.log (sourceW L) ∧
      ∀ z : Node,z.side=.even → Valid z.side z.ratio → Consistent z → z.cutoff=sourceB L →
        sourceW L ≤ z.gap := by
  filter_upwards [sourceW_bounds_eventually,source_scale_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hW hscale hL hlog
  have hLp : 0 < L := by linarith
  have hlogW : 0 < Real.log (sourceW L) := Real.log_pos hW.1
  have hd : Real.log (sourceW L) ≤ (Real.log L)^2 := by
    have hh := Real.log_le_log (zero_lt_one.trans hW.1) hW.2.2
    nlinarith
  have hWB : sourceW L ≤ sourceB L := div_le_div_of_nonneg_left hLp.le hlogW hd
  have htop : sourceW L < Real.exp L := hW.2.2.trans_lt (by linarith [Real.add_one_le_exp L])
  refine ⟨hW.1,htop,hscale.2.2.2.2,?_⟩
  intro z hi hs hc hcut
  have hr : 1 ≤ z.ratio := by rw [hi] at hs; change 198/100 ≤ z.ratio at hs; linarith
  have heq : sourceB L*z.ratio=z.gap := by
    have hh : z.cutoff=z.gap/z.ratio := hc
    rw [hcut] at hh
    exact (eq_div_iff (valid_pos hs).ne').mp hh
  exact hWB.trans (by nlinarith [hscale.2.1])

theorem paper_search_count (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ L : ℝ in atTop,∃ hw : 1 < sourceW L,∃ htop : sourceW L < Real.exp L,
      ∀ (xi ell S : ℝ) (hxi : 0 < xi),xi ≤ 1 → 1 ≤ ell → ∀ (z : Node) (ps : List ℕ),
      z.side=.even → Valid z.side z.ratio → Consistent z → z.cutoff=sourceB L →
      allowed (sourceW L) ell S z ps → (terminal (sourceW L) z ps).gap ≤ K →
      (ps.length:ℝ) ≤ Clen*Real.log (sourceB L) →
      (∀ p ∈ ps,p ∈ sourcePrimeSet (sourceW L) (Real.exp L)) →
      searchConstant*Real.log (sourceW L) ≤
        (searchCount (sourceW L) (lower (sourceW L) (Real.exp L) xi)
          (label (zero_lt_one.trans hw) htop hxi) ps:ℝ) := by
  filter_upwards [paper_incoming_geometry,sourceW_tendsto.eventually (actual_search_count_uniform K Clen hC)]
    with L hg hcount
  refine ⟨hg.1,hg.2.1,?_⟩
  intro xi ell S hxi hxi1 hell z ps hi hs hc hcut ha hK hlen hp
  exact hcount (Real.exp L) (sourceB L) xi ell S hg.1 hg.2.1 hxi hxi1 hg.2.2.1 hell z ps hs
    (hg.2.2.2 z hi hs hc hcut) ha hK hlen hp

theorem literal_source_search_count (K Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW (Real.log top),∃ htop : sourceW (Real.log top) < top,
      ∀ (xi ell S : ℝ) (hxi : 0 < xi),xi ≤ 1 → 1 ≤ ell → ∀ (z : Node) (ps : List ℕ),
      z.side=.even → Valid z.side z.ratio → Consistent z → z.cutoff=sourceB (Real.log top) →
      allowed (sourceW (Real.log top)) ell S z ps → (terminal (sourceW (Real.log top)) z ps).gap ≤ K →
      (ps.length:ℝ) ≤ Clen*Real.log (sourceB (Real.log top)) →
      (∀ p ∈ ps,p ∈ sourcePrimeSet (sourceW (Real.log top)) top) →
      searchConstant*Real.log (sourceW (Real.log top)) ≤
        (searchCount (sourceW (Real.log top)) (lower (sourceW (Real.log top)) top xi)
          (label (zero_lt_one.trans hw) htop hxi) ps:ℝ) := by
  filter_upwards [Real.tendsto_log_atTop.eventually paper_incoming_geometry,
    (sourceW_tendsto.comp Real.tendsto_log_atTop).eventually (actual_search_count_uniform K Clen hC),
    eventually_gt_atTop (0:ℝ)] with top hg hcount htopp
  have htop : sourceW (Real.log top) < top := by simpa only [Real.exp_log htopp] using hg.2.1
  refine ⟨hg.1,htop,?_⟩
  intro xi ell S hxi hxi1 hell z ps hi hs hc hcut ha hK hlen hp
  exact hcount top (sourceB (Real.log top)) xi ell S hg.1 htop hxi hxi1 hg.2.2.1 hell z ps hs
    (hg.2.2.2 z hi hs hc hcut) ha hK hlen hp

end ErdosSearchCount



namespace ErdosSearchCount
open _root_.Filter _root_.Erdos970.Filter NumberTheoryLean ActualSourceTags

attribute [local instance] Classical.propDecidable

theorem nonsearch_error_littleO (Clen : ℝ) (hC : 0 ≤ Clen) :
    Asymptotics.IsLittleO atTop (fun w : ℝ => 2*Clen*Real.log w*(w^((1/4:ℝ))+1))
      (fun w : ℝ => w^((1/2:ℝ))) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro c hc
  filter_upwards [nonsearch_budget_le 0 Clen c hC hc,eventually_gt_atTop (1:ℝ)] with w hb hw
  have hf : 0 ≤ 2*Clen*Real.log w*(w^((1/4:ℝ))+1) := by
    have hlog := (Real.log_pos hw).le
    positivity
  have hg : 0 ≤ w^((1/2:ℝ)) := Real.rpow_nonneg (by linarith) _
  simpa only [zero_add,Real.norm_eq_abs,abs_of_nonneg hf,abs_of_nonneg hg] using hb

theorem selectedCount_eq_sum (P : ℕ → Bool) (ps : List ℕ) :
    selectedCount P ps=(ps.map (fun p => if P p then (1:ℕ) else 0)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases he : P p <;> simp [selectedCount,he] at * <;> omega

noncomputable def searchIndexSet {m n : ℕ} (w : ℝ) (lower : Fin n → ℝ)
    (label : ℕ → Fin n) (f : Fin m → ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => searchBin w (lower (label (f i))))

theorem searchCount_ofFn {m n : ℕ} (w : ℝ) (lower : Fin n → ℝ)
    (label : ℕ → Fin n) (f : Fin m → ℕ) :
    searchCount w lower label (List.ofFn f)=(searchIndexSet w lower label f).card := by
  rw [searchCount,selectedCount_eq_sum,List.map_ofFn,List.sum_ofFn]
  rw [searchIndexSet,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [searchFlag,decide_eq_true_eq,Function.comp_def]

end ErdosSearchCount



namespace ErdosStoppedReferenceUpper
open _root_.Filter _root_.Erdos970.Filter
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceAdmission ReferencePruning ReferenceProductsBasics ReferenceSourcePrimeSets
open SourceStopPredicate StoppedCountVertex StoppedVertexHistory StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MovingCandidateBands MovingStopBandParameters MarkedSourceSmallness
open ErdosPrimeInputs.MertensStrong

theorem actual_stopped_reference_upper {Clen xi K rho : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < K) (hrho : 0 < rho) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,∀ Cs eta : ℝ,
      ∀ (residue : ℕ → ℕ) (z : Node) (ps : List ℕ),
      ps ∈ stopped w
        (stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) (rho*K*(Real.log w)^2)
          (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) residue z)
        (sourcePrimeSet w top).card
        (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)) →
      referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)) ps)
        ≤ (33/100)*((Y:ℝ)/(ps.prod:ℝ))*strictEuler (ps.getLastD 0:ℝ) ∧
      referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)) ps)
        ≤ (33/100)*((Y:ℝ)/(ps.prod:ℝ))*primeProduct (ps.getLastD 0:ℝ) := by
  obtain ⟨B₀,w₀,hB₀,_hw₀,hR⟩ := moving_vertex_reference_upper (rho*K) (mul_pos hrho hK)
  filter_upwards [moving_candidate_node_window hC hxi hxi1 hK,
    moving_stop_band_conditions Clen xi hxi.le hK,moving_compact_gap_small (12*B₀) hK,
    eventually_ge_atTop w₀,eventually_ge_atTop (100:ℝ)] with w hwin hcond hlarge hw₀ hw100
  obtain ⟨hw,hwin⟩ := hwin
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y Cs eta residue z ps hp
  let bins := label (zero_lt_one.trans hw) htop hxi
  let v := rootVertex z ∅ (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)
  have hf := ActualSourceStopBinding.actual_source_stops_first Y w Cs eta Clen B xi
    (K*(Real.log w)^2) (rho*K*(Real.log w)^2) ((Y:ℝ)*primeProduct w)
    (lower w top xi) (width w top xi) bins residue z (sourcePrimeSet w top) hp
  have hn := hwin top htop B hcomp Y Cs eta (rho*K*(Real.log w)^2) residue z ps hf.2.1
  obtain ⟨hlo,hhi,hrlo,hrhi,hcons,hclosed,_hPlower,hpower⟩ := hn
  have hhalf := hcond.2.2.2.2
  have hcut : B₀ ≤ (terminal w z ps).cutoff := by nlinarith
  have hcutscale : (terminal w z ps).cutoff ≤ (rho*K)*(Real.log w)^2 := hhi
  have hJ : 0 ≤ (Y:ℝ)/(ps.prod:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd := actual_stopped_vertex_data Y w top Cs eta Clen B xi
    (K*(Real.log w)^2) (rho*K*(Real.log w)^2) (zero_lt_one.trans hw) htop
    (lower w top xi) (width w top xi) bins residue z ps hp
  have hav : (after w v ps).available=sourcePrimes w (terminal w z ps).cutoff false := by
    rw [sourcePrimes,hpower]
    exact hd.2.2.2
  have hvnode : (after w v ps).node=terminal w z ps := after_node w v ps
  have href := hR w (terminal w z ps).cutoff ((Y:ℝ)/(ps.prod:ℝ)) hw₀ hcut hcutscale hJ
    (after w v ps) (by rw [hvnode]; exact hf.1) (by rw [hvnode]; linarith)
    (by rw [hvnode]; exact hrhi) (by rw [hvnode]; exact hcons) (by rw [hvnode])
    (by rw [hvnode]; exact hclosed) hav (after_original_scale w Y z (sourcePrimeSet w top) ps)
  rw [hpower] at href
  have hP100 : 100 ≤ (ps.getLastD 0:ℝ) := by
    have hsource := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp
      ((SourceStopWindow.candidate_source_primes Y hw htop hxi residue z ps hf.2.1) (ps.getLastD 0)
        (by
          have he : ps.getLastD 0=ps.getLast hf.2.1.1 := by
            conv_lhs => rw [← List.dropLast_append_getLast hf.2.1.1]
            exact List.getLastD_concat
          rw [he]
          exact List.getLast_mem hf.2.1.1))
    exact hw100.trans hsource.2.1.le
  have hstrict : 0 ≤ ((Y:ℝ)/(ps.prod:ℝ))*strictEuler (ps.getLastD 0:ℝ) :=
    mul_nonneg hJ (availableProduct_pos 0 _ false).le
  exact ⟨by dsimp [v] at href; nlinarith,reference_strict_to_closed hJ hP100 href⟩

theorem floored_source_stopped_reference_upper {Clen xi K rho : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < K) (hrho : 0 < rho) :
    ∀ᶠ top : ℝ in atTop,
      let w := ErdosInverseBoxHeight.sourceW top
      let B := ErdosInverseBoxHeight.sourceB top
      let Y := ErdosInverseBoxHeight.sourceY top
      ∃ hw : 1 < w,∃ htop : w < top,∀ alpha Cs eta : ℝ,
      ∀ (residue : ℕ → ℕ) (ps : List ℕ),
      ps ∈ stopped w
        (stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) (rho*K*(Real.log w)^2)
          (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi)
          residue (ErdosCorrectionLimit.sourceRootNode alpha top))
        (sourcePrimeSet w top).card
        (rootVertex (ErdosCorrectionLimit.sourceRootNode alpha top) ∅
          (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)) →
      referenceValue w (after w (rootVertex (ErdosCorrectionLimit.sourceRootNode alpha top) ∅
        (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)) ps)
        ≤ (33/100)*((Y:ℝ)/(ps.prod:ℝ))*strictEuler (ps.getLastD 0:ℝ) ∧
      referenceValue w (after w (rootVertex (ErdosCorrectionLimit.sourceRootNode alpha top) ∅
        (sourcePrimeSet w top) ((Y:ℝ)*primeProduct w)) ps)
        ≤ (33/100)*((Y:ℝ)/(ps.prod:ℝ))*primeProduct (ps.getLastD 0:ℝ) := by
  have ht : Tendsto ErdosInverseBoxHeight.sourceW atTop atTop :=
    JacobsthalSourceScale.sourceW_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (actual_stopped_reference_upper hC hxi hxi1 hK hrho),
    Real.tendsto_log_atTop.eventually ErdosSearchCount.paper_incoming_geometry,
    eventually_gt_atTop (1:ℝ)] with top hbound hgeometry htop1
  dsimp only
  obtain ⟨hw,hbound⟩ := hbound
  have htop : ErdosInverseBoxHeight.sourceW top < top := by
    simpa only [JacobsthalSourceScale.sourceW,ErdosInverseBoxHeight.sourceW,
      Real.exp_log (zero_lt_one.trans htop1)] using hgeometry.2.1
  have hcomp : Real.log (ErdosInverseBoxHeight.sourceB top) ≤
      2*Real.log (ErdosInverseBoxHeight.sourceW top) := hgeometry.2.2.1
  refine ⟨hw,htop,?_⟩
  intro alpha Cs eta residue ps hp
  exact hbound top htop (ErdosInverseBoxHeight.sourceB top) hcomp
    (ErdosInverseBoxHeight.sourceY top) Cs eta residue (ErdosCorrectionLimit.sourceRootNode alpha top) ps hp

end ErdosStoppedReferenceUpper



namespace ErdosSubsetWord
open ErdosCofactorChoices ErdosSearchCount ErdosTagEvent
open NumberTheoryLean ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

noncomputable def globalBins (w top xi : ℝ) : Fin (binCount w top xi) → Finset ℕ :=
  fun b => primeBin (lower w top xi b) (width w top xi b)
noncomputable def occupiedSearch (w top xi : ℝ) (mult : Fin (binCount w top xi) → ℕ) :
    Finset (Fin (binCount w top xi)) :=
  Finset.univ.filter (fun b => searchBin w (lower w top xi b) ∧ 0 < mult b)

theorem selected_prime_label {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) (b : Fin (binCount w top xi))
    {p : ℕ} (hp : p ∈ f b) : label (zero_lt_one.trans hw) htop hxi p=b := by
  have hmem := ((mem_selections _ mult f).mp hf b).1 hp
  exact ((bin_mem_iff_label (zero_lt_one.trans hw) htop hxi b p).mp hmem).2.2.2

theorem global_word_length {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) : (descendingWord f).length=∑ b,mult b :=
  descendingWord_length _ mult
    (fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i j hij) f hf

theorem word_source_membership {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) :
    ∀ p ∈ descendingWord f,p ∈ sourcePrimeSet w top := by
  intro p hp
  obtain ⟨b,hb⟩ := (mem_descendingWord f p).mp hp
  have hbin := ((mem_selections _ mult f).mp hf b).1 hb
  exact (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr
    (bin_prime_in_source (zero_lt_one.trans hw) htop hxi b hbin)

theorem word_search_count {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) :
    searchCount w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) (descendingWord f)=
      ∑ b,if searchBin w (lower w top xi b) then mult b else 0 := by
  have hmem := (mem_selections _ mult f).mp hf
  have hd : Pairwise (fun i j => Disjoint (globalBins w top xi i) (globalBins w top xi j)) :=
    fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i j hij
  rw [searchCount,selectedCount_eq_sum,← List.sum_toFinset _ (descendingWord_nodup f),
    descendingWord_toFinset,selectionPrimes,Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b _
    calc
      _ = ∑ _p ∈ f b,if searchBin w (lower w top xi b) then (1:ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hl := selected_prime_label hw htop hxi mult f hf b hp
        simp [searchFlag,hl]
      _ = _ := by split_ifs <;> simp [(hmem b).2]
  · intro i _ j _ hij
    exact selection_disjoint _ hd f (fun b => (hmem b).1) hij

theorem word_search_count_eq_occupied {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult)
    (hone : ∀ b ∈ occupiedSearch w top xi mult,mult b=1) :
    searchCount w (lower w top xi) (label (zero_lt_one.trans hw) htop hxi) (descendingWord f)=
      (occupiedSearch w top xi mult).card := by
  rw [word_search_count hw htop hxi mult f hf,occupiedSearch,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hs : searchBin w (lower w top xi b)
  · by_cases hm : 0 < mult b
    · have hh := hone b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs,hm⟩)
      simp [hs,hh]
    · have hz : mult b=0 := by omega
      simp [hs,hz]
  · simp [hs]

end ErdosSubsetWord



namespace ErdosSubsetWord
open ErdosCofactorChoices ErdosSearchCount
open NumberTheoryLean
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem global_label_mono {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p q : ℕ} (hp : p ∈ sourcePrimeSet w top) (hq : q ∈ sourcePrimeSet w top) (hqp : q ≤ p) :
    label (zero_lt_one.trans hw) htop hxi q ≤ label (zero_lt_one.trans hw) htop hxi p := by
  have hpb := label_value_bounds (zero_lt_one.trans hw) htop hxi ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp).2
  have hqb := label_value_bounds (zero_lt_one.trans hw) htop hxi ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop q).mp hq).2
  by_contra hn
  have hlt : label (zero_lt_one.trans hw) htop hxi p < label (zero_lt_one.trans hw) htop hxi q := lt_of_not_ge hn
  have he : upper w top xi (label (zero_lt_one.trans hw) htop hxi p) ≤
      lower w top xi (label (zero_lt_one.trans hw) htop hxi q) := by
    rw [upper_endpoint]
    exact endpoint_mono (zero_lt_one.trans hw) htop hxi (Nat.succ_le_of_lt hlt)
  have hreal : (q:ℝ) ≤ p := by exact_mod_cast hqp
  linarith

theorem word_label_count {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) (b : Fin (binCount w top xi)) :
    ((descendingWord f).map (label (zero_lt_one.trans hw) htop hxi)).count b=mult b := by
  have hmem := (mem_selections _ mult f).mp hf
  have hd : Pairwise (fun i j => Disjoint (globalBins w top xi i) (globalBins w top xi j)) :=
    fun i j hij => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi i j hij
  rw [List.count_eq_countP,List.countP_map,List.countP_eq_length_filter]
  change selectedCount (fun p => label (zero_lt_one.trans hw) htop hxi p == b) (descendingWord f)=mult b
  rw [selectedCount_eq_sum,← List.sum_toFinset _ (descendingWord_nodup f),
    descendingWord_toFinset,selectionPrimes,Finset.sum_biUnion]
  · calc
      _ = ∑ i,if i=b then mult i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ∑ _p ∈ f i,if i=b then (1:ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            have hl := selected_prime_label hw htop hxi mult f hf i hp
            simp [hl]
          _ = _ := by split_ifs <;> simp [(hmem i).2]
      _ = _ := by simp
  · intro i _ j _ hij
    exact selection_disjoint _ hd f (fun i => (hmem i).1) hij

theorem word_labels_ordered {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) :
    ((descendingWord f).map (label (zero_lt_one.trans hw) htop hxi)).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  apply (descendingWord_strict f).imp_of_mem
  intro p q hp hq hpq
  exact global_label_mono hw htop hxi (word_source_membership hw htop hxi mult f hf p hp)
    (word_source_membership hw htop hxi mult f hf q hq) hpq.le

theorem selection_label_word_eq {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f g : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) (hg : g ∈ selections (globalBins w top xi) mult) :
    (descendingWord f).map (label (zero_lt_one.trans hw) htop hxi)=
      (descendingWord g).map (label (zero_lt_one.trans hw) htop hxi) := by
  have hp : ((descendingWord f).map (label (zero_lt_one.trans hw) htop hxi)).Perm
      ((descendingWord g).map (label (zero_lt_one.trans hw) htop hxi)) := by
    apply List.perm_iff_count.mpr
    intro b
    rw [word_label_count hw htop hxi mult f hf,word_label_count hw htop hxi mult g hg]
  exact List.Perm.eq_of_pairwise' (word_labels_ordered hw htop hxi mult f hf)
    (word_labels_ordered hw htop hxi mult g hg) hp

theorem selection_prefix_labels_eq {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (f g : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) mult) (hg : g ∈ selections (globalBins w top xi) mult)
    (k : ℕ) :
    ((descendingWord f).take k).map (label (zero_lt_one.trans hw) htop hxi)=
      ((descendingWord g).take k).map (label (zero_lt_one.trans hw) htop hxi) := by
  rw [List.map_take,List.map_take,selection_label_word_eq hw htop hxi mult f g hf hg]

end ErdosSubsetWord



namespace NumberTheoryLean.FiniteBoxWordMass
open ErdosCofactorChoices ErdosSubsetWord CanonicalSubsetBox
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem word_injective {n : ℕ} (P : Fin n → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (f g : Fin n → Finset ℕ)
    (hf : ∀ i,f i ⊆ P i) (hg : ∀ i,g i ⊆ P i) (he : descendingWord f=descendingWord g) : f=g := by
  have hu : selectionPrimes f=selectionPrimes g := by
    rw [← descendingWord_toFinset f,← descendingWord_toFinset g,he]
  funext i
  rw [← recover_bin P hd f hf i,← recover_bin P hd g hg i,hu]

noncomputable def wordBox {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ) : Finset (List ℕ) :=
  (selections P mult).image descendingWord

theorem wordBox_mass {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    (∑ ps ∈ wordBox P mult,prefixWeight ps)=selectionMass P mult := by
  rw [wordBox,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f hf
    rw [StoppedVertexHistory.prefixWeight_product,
      descendingWord_product P hd f (fun i => ((mem_selections P mult f).mp hf i).1)]
  · intro f hf g hg he
    exact word_injective P hd f g (fun i => ((mem_selections P mult f).mp hf i).1)
      (fun i => ((mem_selections P mult g).mp hg i).1) he

theorem wordBoxes_disjoint {n : ℕ} (P : Fin n → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (mult mult' : Fin n → ℕ) (hne : mult ≠ mult') :
    Disjoint (wordBox P mult) (wordBox P mult') := by
  apply Finset.disjoint_left.mpr
  intro ps hp hp'
  obtain ⟨f,hf,hef⟩ := Finset.mem_image.mp hp
  obtain ⟨g,hg,heg⟩ := Finset.mem_image.mp hp'
  have hfP := (mem_selections P mult f).mp hf
  have hgP := (mem_selections P mult' g).mp hg
  have he := word_injective P hd f g (fun i => (hfP i).1) (fun i => (hgP i).1) (hef.trans heg.symm)
  subst g
  apply hne
  funext i
  exact (hfP i).2.symm.trans (hgP i).2

noncomputable def boxWords {n : ℕ} (P : Fin n → Finset ℕ) (M : Finset (Fin n → ℕ)) : Finset (List ℕ) :=
  M.biUnion (wordBox P)

theorem total_box_mass_eq {n : ℕ} (P : Fin n → Finset ℕ)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (M : Finset (Fin n → ℕ)) :
    (∑ mult ∈ M,selectionMass P mult) = ∑ ps ∈ boxWords P M,prefixWeight ps := by
  rw [boxWords,Finset.sum_biUnion (fun i _ j _ hij => wordBoxes_disjoint P hd i j hij)]
  apply Finset.sum_congr rfl
  intro mult _hm
  exact (wordBox_mass P mult hd).symm
end NumberTheoryLean.FiniteBoxWordMass


end Erdos970

end OAI
