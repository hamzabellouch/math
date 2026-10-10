import OAI.NumberTheory.Jacobsthal.Partitions.ActualRepeatedBinStep
import OAI.NumberTheory.Jacobsthal.Paths.ActualOwnerLocalComparison
import OAI.NumberTheory.Jacobsthal.Paths.CanonicalKeyWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CanonicalKeyReplacement
open PrimeHistories CanonicalStopKey CanonicalKeyWitness ActualStopGroupFiber
open SourceStopPredicate ActualTagFreezing ActualFrozenStopFamily BinReplacementOrder
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment


variable {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
  {Y : ℕ} {Cs eta Clen B b₀ b₁ mu : ℝ} {a : ℕ → ℕ} {z : Node}
  {k : Key (binCount w top xi)} (d : Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k)

include d

theorem whole_bin_words (p : ℕ) (hp : p∈primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)) :
    (k.pre++p::k.tail).Pairwise (· > ·) ∧
      ∀ q∈k.pre++p::k.tail,q∈sourcePrimeSet w top := by
  have hn := (bin_mem_iff_label (zero_lt_one.trans hw) htop hxi k.tag.bin p).mp hp
  have hpS : p∈sourcePrimeSet w top := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr
    ⟨hn.1,hn.2.1,hn.2.2.1⟩
  have hl : label (zero_lt_one.trans hw) htop hxi p=label (zero_lt_one.trans hw) htop hxi d.p₀ := hn.2.2.2.trans d.bin_eq
  have hc : ((k.pre++d.p₀::k.tail).map (label (zero_lt_one.trans hw) htop hxi)).count
      (label (zero_lt_one.trans hw) htop hxi d.p₀)=1 := by rw [← d.bin_eq]; exact d.singleton
  have hD := (decreasing_replacement (zero_lt_one.trans hw) htop hxi k.pre k.tail d.p₀ p d.source hpS hl hc).mp d.ordered
  have hS := (forall_mem_replacement_iff (fun q => q∈sourcePrimeSet w top) k.pre k.tail d.p₀ p
    (d.source d.p₀ (by simp)) hpS).mp d.source
  exact ⟨hD,hS⟩

theorem fixed_other_alignment : ∀ q∈k.pre++k.tail,aligns (sourceClass a) k.tag.rational q := by
  intro q hq
  apply d.aligned q
  simp only [List.mem_append,List.mem_cons] at hq ⊢
  tauto

theorem fixed_cofactor_pos : 0 < k.pre.prod*k.tail.prod := by
  have hs : ∀ q∈k.pre++k.tail,0 < q := by
    intro q hq
    have hm : q∈k.pre++d.p₀::k.tail := by
      simp only [List.mem_append,List.mem_cons] at hq ⊢
      tauto
    exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop q).mp (d.source q hm)).1.pos
  simpa only [List.prod_append] using List.prod_pos hs

theorem aligning_word_mem (hC : 0 ≤ Clen) (p : ℕ)
    (hp : p∈primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin))
    (ha : aligns (sourceClass a) k.tag.rational p) :
    k.pre++p::k.tail∈family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z :=
  actual_stopped_replacement Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z k.pre k.tail d.p₀ p
    d.mem_family d.tag d.prime_tag hp ha

theorem search_lower : Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ lower w top xi k.tag.bin := by
  have hR : 0 < lower w top xi k.tag.bin := endpoint_pos (zero_lt_one.trans hw) k.tag.bin.1
  have hs : w^((1:ℝ)/4) ≤ Real.log (lower w top xi k.tag.bin)/Real.log w := d.search
  have hh := Real.exp_le_exp.mpr ((le_div_iff₀ (Real.log_pos hw)).mp hs)
  simpa only [Real.exp_log hR] using hh
end NumberTheoryLean.CanonicalKeyReplacement



namespace NumberTheoryLean.MovingCandidateBands
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MovingStopBandParameters CandidateTerminalGeometry CandidateLengthBand


theorem moving_candidate_node_window {Clen xi K : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,∀ Cs eta b₁ : ℝ,
      ∀ (residue : ℕ → ℕ) (z : Node) (ps : List ℕ),
      stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) residue z ps →
      K*(Real.log w)^2-xi/Real.log w ≤ (terminal w z ps).cutoff ∧ (terminal w z ps).cutoff ≤ b₁ ∧
        204/100 ≤ (terminal w z ps).ratio ∧ (terminal w z ps).ratio ≤ 218/100 ∧
        Consistent (terminal w z ps) ∧ (terminal w z ps).closed=false ∧
        Real.exp ((K/2)*(Real.log w)^3) ≤ (ps.getLastD 0:ℝ) ∧
        w^(terminal w z ps).cutoff=(ps.getLastD 0:ℝ) := by
  filter_upwards [moving_stop_band_conditions Clen xi hxi.le hK] with w hcond
  obtain ⟨hw,hlog,hb₀,hsmall,hhalf⟩ := hcond
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y Cs eta b₁ residue z ps hc
  have hstep : xi/Real.log w ≤ 1 := (div_le_self hxi.le hlog).trans hxi1
  have hpos : 0 < K*(Real.log w)^2-xi/Real.log w := by linarith
  have hn := candidate_terminal_geometry Y hw htop hxi hC hcomp hpos hsmall residue z ps hc
  have hP := candidate_moving_last_prime_lower Y hw htop hxi hC hcomp hsmall hhalf residue z ps hc
  exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2,hP.1,hP.2⟩

theorem moving_candidate_J_band {Clen xi K : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,0 < Y →
      ∀ alpha Cs eta b₁ : ℝ,0 ≤ alpha → alpha ≤ 1 →
      ∀ (residue : ℕ → ℕ) (z : Node),z.gap=Real.log (Y:ℝ)/Real.log w-alpha+2 →
      ∀ ps : List ℕ,
      stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) residue z ps →
      ∀ p₀ q : ℕ,0 < q → ps.prod=p₀*q → ∀ R zeta : ℝ,0 < R → 0 ≤ zeta → zeta ≤ 1 →
      R ≤ (p₀:ℝ) → (p₀:ℝ) ≤ (1+zeta)*R → ∀ p : ℝ,R ≤ p → p ≤ (1+zeta)*R →
      Real.exp ((K/2)*(Real.log w)^3) ≤ (ps.getLastD 0:ℝ) ∧
        203/100 ≤ Real.log ((Y:ℝ)/(p*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ) ∧
        Real.log ((Y:ℝ)/(p*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ) ≤ 219/100 := by
  filter_upwards [moving_stop_band_conditions Clen xi hxi.le hK] with w hcond
  obtain ⟨hw,hlog,hb₀,hsmall,hhalf⟩ := hcond
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y hY alpha Cs eta b₁ ha0 ha1 residue z hroot ps hc p₀ q hq hprod R zeta hR hzeta hzeta1 hp₀lo hp₀hi p hplo hphi
  have hBand := candidate_whole_bin_length_band Y hY hw htop hxi hxi1 hC hcomp hlog hb₀ ha0 ha1 hsmall
    residue z hroot ps hc p₀ q hq hprod hR hzeta hzeta1 ⟨hp₀lo,hp₀hi⟩ p ⟨hplo,hphi⟩
  have hP := (candidate_moving_last_prime_lower Y hw htop hxi hC hcomp hsmall hhalf residue z ps hc).1
  exact ⟨hP,hBand⟩
end NumberTheoryLean.MovingCandidateBands



namespace NumberTheoryLean.CanonicalKeyBands
open _root_.Filter _root_.Erdos970.Filter FinitePathGeometry PrimeHistories CanonicalStopKey CanonicalKeyWitness CanonicalKeyReplacement
open SourceStopPredicate TagBelowStopWindow MovingCandidateBands
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin
open scoped Topology


theorem last_fixed_tail (pre tail : List ℕ) (p : ℕ) (htail : tail≠[]) :
    (pre++p::tail).getLastD 0=tail.getLastD 0 := by
  rw [← List.dropLast_append_getLast htail,← List.cons_append,← List.append_assoc]
  simp only [List.getLastD_concat]

theorem moving_key_bands {Clen xi Kstop rho : ℝ} (hC : 0 ≤ Clen)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hK : 0 < Kstop) (_hrho : 0 < rho) :
    ∀ᶠ w : ℝ in atTop,∃ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ B : ℝ,Real.log B ≤ 2*Real.log w → ∀ Y : ℕ,0 < Y →
      ∀ aStar Cs eta mu : ℝ,0 ≤ aStar → aStar ≤ 1 → ∀ (a : ℕ → ℕ) (z : Node),
      z.gap=Real.log (Y:ℝ)/Real.log w-aStar+2 →
      ∀ k : Key (binCount w top xi),
      ∀ _d : Witness hw htop hxi Y Cs eta Clen B (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2) mu a z k,
      Real.exp ((Kstop/2)*(Real.log w)^3) ≤ (k.tail.getLastD 0:ℝ) ∧
      (k.tail.getLastD 0:ℝ) ≤ Real.exp (rho*Kstop*(Real.log w)^3) ∧
      ∀ p∈Set.Icc (lower w top xi k.tag.bin) ((1+width w top xi k.tag.bin)*lower w top xi k.tag.bin),
        203/100 ≤ Real.log ((Y:ℝ)/(p*(k.pre.prod*k.tail.prod:ℕ)))/Real.log (k.tail.getLastD 0:ℝ) ∧
        Real.log ((Y:ℝ)/(p*(k.pre.prod*k.tail.prod:ℕ)))/Real.log (k.tail.getLastD 0:ℝ) ≤ 219/100 := by
  filter_upwards [moving_candidate_J_band hC hxi hxi1 hK,moving_candidate_node_window hC hxi hxi1 hK]
    with w hBand hNode
  obtain ⟨hw,hBand⟩ := hBand
  obtain ⟨_hwN,hNode⟩ := hNode
  refine ⟨hw,?_⟩
  intro top htop B hcomp Y hY aStar Cs eta mu ha0 ha1 a z hroot k d
  have hR : 0 < lower w top xi k.tag.bin := endpoint_pos (zero_lt_one.trans hw) k.tag.bin.1
  have htheta : 0 < width w top xi k.tag.bin := effectiveWidth_pos (zero_lt_one.trans hw) htop hxi
  have htheta1 : width w top xi k.tag.bin ≤ 1 :=
    (effectiveWidth_le (zero_lt_one.trans hw) htop hxi).trans hxi1
  have hp₀ := (mem_primeBin hR.le htheta.le d.p₀).mp d.prime_bin
  have hq := fixed_cofactor_pos hw htop hxi d
  have hprod := replacement_product k.pre k.tail d.p₀
  have hLast := last_fixed_tail k.pre k.tail d.p₀ d.tail_nonempty
  have hJ (p : ℝ) (hpL : lower w top xi k.tag.bin ≤ p)
      (hpU : p ≤ (1+width w top xi k.tag.bin)*lower w top xi k.tag.bin) :=
    hBand top htop B hcomp Y hY aStar Cs eta (rho*Kstop*(Real.log w)^2) ha0 ha1 a z hroot
      (k.pre++d.p₀::k.tail) d.candidate d.p₀ (k.pre.prod*k.tail.prod) hq hprod
      (lower w top xi k.tag.bin) (width w top xi k.tag.bin) hR htheta.le htheta1 hp₀.2.1.le hp₀.2.2 p hpL hpU
  have hJU : lower w top xi k.tag.bin ≤ (1+width w top xi k.tag.bin)*lower w top xi k.tag.bin := by nlinarith
  have hJR := hJ (lower w top xi k.tag.bin) (le_refl _) hJU
  rw [hLast] at hJR
  obtain ⟨_hlo,hcut,_hrlo,_hrhi,_hcons,_hclosed,_hPlo,hpower⟩ :=
    hNode top htop B hcomp Y Cs eta (rho*Kstop*(Real.log w)^2) a z (k.pre++d.p₀::k.tail) d.candidate
  rw [hLast] at hpower
  have hUpper : (k.tail.getLastD 0:ℝ) ≤ Real.exp (rho*Kstop*(Real.log w)^3) := by
    calc
      _ = w^(terminal w z (k.pre++d.p₀::k.tail)).cutoff := hpower.symm
      _ ≤ w^(rho*Kstop*(Real.log w)^2) := Real.rpow_le_rpow_of_exponent_le hw.le hcut
      _ = _ := by rw [Real.rpow_def_of_pos (zero_lt_one.trans hw)]; congr 1; ring
  refine ⟨hJR.1,hUpper,?_⟩
  intro p hp
  have hh := (hJ p hp.1 hp.2).2
  rwa [hLast] at hh
end NumberTheoryLean.CanonicalKeyBands



namespace ErdosStoppedArithmetic
open NumberTheoryLean NumberTheoryLean.FrozenPrimeGroup NumberTheoryLean.StoppedCountVertex
  NumberTheoryLean.StoppedVertexHistory NumberTheoryLean.StoppedCountAdapters
  NumberTheoryLean.LogarithmicBinPartition NumberTheoryLean.LargePrimeDeletion
  NumberTheoryLean.LastPrimeModulusCount
  ErdosInverseAlignment ErdosInversePrimeBin ErdosInverseCounts

attribute [local instance] Classical.propDecidable

theorem frozen_group_reward_sum (R theta : ℝ) (a : ℕ → ℤ) (r : ℚ)
    (pre tail : List ℕ) (reward : List ℕ → ℝ) :
    (∑ ps ∈ frozenGroup R theta a r pre tail,reward ps)=
      ∑ p ∈ (primeBin R theta).filter (aligns a r),reward (pre++p::tail) := by
  rw [frozenGroup,Finset.sum_image]
  intro p _ q _ he
  exact replacement_injective pre tail he

theorem frozen_correction_eq_original (Y : ℕ) (w top R theta : ℝ)
    (hw : 0 < w) (htop : w < top) (a : ℕ → ℕ) (z : PrimeHistories.Node)
    (mu : ℝ) (r : ℚ) (pre tail : List ℕ) (htail : tail ≠ [])
    (hWords : ∀ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
      (pre++p::tail).Pairwise (· > ·) ∧ ∀ q ∈ pre++p::tail,q ∈ sourcePrimeSet w top) :
    (∑ ps ∈ frozenGroup R theta (fun t => (a t : ℤ)) r pre tail,
      (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a
        (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)-
       referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)))=
    ∑ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
      ((modulusCount Y (ErdosStoppedTagSieve.smallPrimeSet (tail.getLastD 0 : ℝ)) a
        (p*(pre.prod*tail.prod)) : ℝ)-
       referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (pre++p::tail))) := by
  rw [frozen_group_reward_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [strict_smallPrimeSet_nat]
  rw [frozen_survivors_eq_modulusCount Y hw htop a z mu pre tail p htail
    (hWords p hp).1 (hWords p hp).2]

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open _root_.Filter _root_.Erdos970.Filter NumberTheoryLean NumberTheoryLean.PrimeHistories
  NumberTheoryLean.CanonicalKeyWitness NumberTheoryLean.CanonicalKeyReplacement
  NumberTheoryLean.CanonicalStopKey NumberTheoryLean.SourceStopPredicate
  NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints
  NumberTheoryLean.LogarithmicBinPartition
  ErdosInverseAlignment ErdosInversePrimeBin ErdosStoppedTagSieve ErdosHypotheticalTag


theorem canonical_key_arithmetic (Cs : ℝ) : ∀ᶠ w : ℝ in atTop,
    ∀ top xi : ℝ,∀ hw : 1 < w,∀ htop : w < top,∀ hxi : 0 < xi,
    ∀ Y : ℕ,∀ eta Clen B b₀ b₁ mu : ℝ,∀ a : ℕ → ℕ,∀ z : Node,
    ∀ k : Key (binCount w top xi),Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k →
      (k.tail.getLastD 0).Prime ∧ 0 < k.pre.prod*k.tail.prod ∧
      (∀ t ∈ smallPrimeSet (k.tail.getLastD 0 : ℝ),(k.pre.prod*k.tail.prod).Coprime t) ∧
      ∀ p ∈ primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin),
        Squarefree (p*(k.pre.prod*k.tail.prod)) ∧ k.tag.rational.den.Coprime p ∧
        p ∉ smallPrimeSet (k.tail.getLastD 0 : ℝ) ∧
        (∀ t ∈ (p*(k.pre.prod*k.tail.prod)).primeFactors,t ≠ p →
          aligns (sourceClass a) k.tag.rational t) ∧
        ∀ t ∈ (p*(k.pre.prod*k.tail.prod)).primeFactors,k.tail.getLastD 0 ≤ t := by
  filter_upwards [source_all_search_units Cs] with w hUnits
  intro top xi hw htop hxi Y eta Clen B b₀ b₁ mu a z k d
  have hFixed := fixed_other_alignment hw htop hxi d
  have hPrime0 : ∀ p ∈ k.pre++d.p₀::k.tail,p.Prime := by
    intro p hp
    exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (d.source p hp)).1
  obtain ⟨hP,hq,_hsq0,_hSupport0,_hSmall0,hqCoprime,_hOther0⟩ :=
    fixed_tail_arithmetic k.pre k.tail d.p₀ d.tail_nonempty d.ordered hPrime0 (sourceClass a) k.tag.rational hFixed
  refine ⟨hP,hq,hqCoprime,?_⟩
  intro p hp
  have hWord := whole_bin_words hw htop hxi d p hp
  have hPrime : ∀ t ∈ k.pre++p::k.tail,t.Prime := by
    intro t ht
    exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop t).mp (hWord.2 t ht)).1
  obtain ⟨_hP,_hq,hsq,hSupport,hSmall,_hqCo,hOther⟩ :=
    fixed_tail_arithmetic k.pre k.tail p d.tail_nonempty hWord.1 hPrime (sourceClass a) k.tag.rational hFixed
  have hR : 0 < lower w top xi k.tag.bin := endpoint_pos (zero_lt_one.trans hw) k.tag.bin.1
  have hWidth : 0 ≤ width w top xi k.tag.bin := (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le
  have hpBounds := (mem_primeBin hR.le hWidth p).mp hp
  have hUnit := hUnits.2 (lower w top xi k.tag.bin) k.tag.rational p hR d.eligible.1
    d.search hpBounds.2.1.le hpBounds.1
  exact ⟨hsq,hUnit,hSmall,hOther,hSupport⟩

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open _root_.Filter _root_.Erdos970.Filter NumberTheoryLean NumberTheoryLean.PrimeHistories
  NumberTheoryLean.CanonicalKeyWitness NumberTheoryLean.CanonicalKeyReplacement
  NumberTheoryLean.CanonicalStopKey NumberTheoryLean.ActualStopGroupFiber
  NumberTheoryLean.SourceStopPredicate NumberTheoryLean.StoppedCountVertex
  NumberTheoryLean.StoppedCountAdapters NumberTheoryLean.StoppedVertexHistory
  NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints
  NumberTheoryLean.LogarithmicBinPartition NumberTheoryLean.LargePrimeDeletion
  NumberTheoryLean.ReferenceProductsBasics
  ErdosInverseAlignment ErdosInversePrimeBin ErdosStoppedTagSieve
  ErdosPrimeInputs.MertensStrong
open ErdosCommonMInterval (lengthExponent)

attribute [local instance] Classical.propDecidable

theorem canonical_key_correction_nonnegative :
    ∃ eta0 : ℝ,0 < eta0 ∧ eta0 ≤ 1/4 ∧ ∃ P0 : ℕ,2 ≤ P0 ∧
      ∀ Cs : ℝ,0 ≤ Cs → ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → ∀ hxi : 0 < xi,
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ top : ℝ,
      ∀ hw : 1 < w,∀ htop : w < top,∀ Y : ℕ,0 < Y →
      ∀ eta Clen B b₀ b₁ mu : ℝ,0 ≤ eta → eta ≤ eta0 →
      ∀ a : ℕ → ℕ,∀ z : Node,∀ k : Key (binCount w top xi),
      Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k →
      let P := k.tail.getLastD 0
      let R := lower w top xi k.tag.bin
      let theta := width w top xi k.tag.bin
      let q := k.pre.prod*k.tail.prod
      P0 ≤ P → Real.exp (K*(Real.log w)^3) ≤ (P : ℝ) →
      (P : ℝ) ≤ Real.exp (rho*K*(Real.log w)^3) → xi/4 ≤ theta → theta ≤ 1 →
      (∀ x ∈ Set.Icc R ((1+theta)*R),
        203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) →
      (∀ p ∈ (primeBin R theta).filter (aligns (sourceClass a) k.tag.rational),
        referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (k.pre++p::k.tail)) ≤
          (33/100 : ℝ)*primeProduct (P : ℝ)*((Y : ℝ)/((p : ℝ)*q))) →
      0 ≤ ∑ ps ∈ keyGroup w top xi a k,
        (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)-
          referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)) := by
  obtain ⟨eta0,heta0,heta01,P0,hP0,hOwner⟩ := actual_owner_local_comparison
  refine ⟨eta0,heta0,heta01,P0,hP0,?_⟩
  intro Cs hCs
  obtain ⟨K,hK,hOwner⟩ := hOwner Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨wA,hwA,hA⟩ := hOwner rho xi hrho hxi
  obtain ⟨wU,hU⟩ := eventually_atTop.mp (canonical_key_arithmetic Cs)
  refine ⟨max wA wU,hwA.trans (le_max_left _ _),?_⟩
  intro w hw top hw1 htop Y hY eta Clen B b₀ b₁ mu heta hetaU a z k d
  dsimp only
  intro hPsize hPl hPu hWidthLo hWidthHi hBand hRef
  obtain ⟨hPrime,hq,hqSmall,hGeometry⟩ :=
    hU w ((le_max_right _ _).trans hw) top xi hw1 htop hxi Y eta Clen B b₀ b₁ mu a z k d
  let ref : ℕ → ℝ := fun p =>
    referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (k.pre++p::k.tail))
  have hNum : |(k.tag.rational.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using d.eligible.2
  have hMargin := hA w ((le_max_left _ _).trans hw) (k.tail.getLastD 0) hPrime hPsize
    (lower w top xi k.tag.bin) (width w top xi k.tag.bin) eta hPl hPu
    (search_lower hw1 htop hxi d) hWidthLo hWidthHi heta hetaU Y (k.pre.prod*k.tail.prod)
    hY hq k.tag.rational a d.eligible.1 hNum hBand hqSmall hGeometry d.near_full ref hRef
  have hNonneg : 0 ≤ (1/100 : ℝ)*primeProduct (k.tail.getLastD 0 : ℝ)*
      (∑ p ∈ primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin),
        (Y : ℝ)/((p : ℝ)*(k.pre.prod*k.tail.prod : ℕ))) := by
    apply mul_nonneg (mul_nonneg (by norm_num) (actual_primeProduct_pos _).le)
    exact Finset.sum_nonneg (fun p _ => by positivity)
  change 0 ≤ ∑ ps ∈ NumberTheoryLean.FrozenPrimeGroup.frozenGroup
    (lower w top xi k.tag.bin) (width w top xi k.tag.bin) (fun t => (a t : ℤ)) k.tag.rational k.pre k.tail,_
  rw [frozen_correction_eq_original Y w top (lower w top xi k.tag.bin) (width w top xi k.tag.bin)
    (zero_lt_one.trans hw1) htop a z mu k.tag.rational k.pre k.tail d.tail_nonempty
    (fun p hp => whole_bin_words hw1 htop hxi d p (Finset.mem_filter.mp hp).1)]
  exact hNonneg.trans hMargin

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open NumberTheoryLean NumberTheoryLean.PrimeHistories NumberTheoryLean.CanonicalStopPartition
  NumberTheoryLean.ActualStopGroupFiber NumberTheoryLean.SourceStopPredicate
  NumberTheoryLean.StoppedCountVertex NumberTheoryLean.StoppedCountAdapters
  NumberTheoryLean.StoppedVertexHistory NumberTheoryLean.StoppedTraceSets
  NumberTheoryLean.LogarithmicBinEndpoints NumberTheoryLean.LogarithmicBinLabels
  NumberTheoryLean.LogarithmicBinPartition NumberTheoryLean.LargePrimeDeletion


theorem stopped_correction_of_key_signs (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (a : ℕ → ℕ) (z : Node)
    (hKeys : ∀ k ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,
      0 ≤ ∑ ps ∈ keyGroup w top xi a k,
        (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)-
          referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps))) :
    0 ≤ ∑ ps ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu),
      (countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)-
        referenceValue w (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)) := by
  change 0 ≤ ∑ ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,_
  rw [sum_over_groups Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z]
  exact Finset.sum_nonneg hKeys

end ErdosStoppedArithmetic


end Erdos970

end OAI
