import OAI.NumberTheory.Ostmann.Construction.GiantSourceProducer
import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice
import OAI.NumberTheory.Ostmann.Construction.NominalCenterSelectionRanges
import OAI.NumberTheory.Ostmann.Construction.SourceWindowCoverage
import OAI.NumberTheory.Ostmann.Construction.StatisticScale
import OAI.NumberTheory.Ostmann.Preliminaries.Sizes

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Construction
open Filter Ostmann.Preliminaries
open scoped BigOperators

theorem initial_source_construction : ∃ δ : ℝ, 0<δ ∧
    ∀ (d : Decomposition) (Bs BD Bz : ℝ) (k : ℕ), 0<k →
      ∀ᶠ L : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 → ∀ spectator : PrimeSource,
        (∀p : spectator.Sample, Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
          Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
        (1/2:ℝ)≤ spectator.law.mean (fun p => balancedPrimeIndicator d p) →
        ∃ C : InitialSourceChoice d Bs BD Bz k L E,
          C.favorable⊆Supply.nonsparsePrimes d δ L ∧
          Real.exp ((1/20:ℝ)*L)≤C.blockBase ∧
          C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) ∧
          C.blockBase-2<(C.giantCenter:ℝ) ∧
          (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 ∧
          |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 ∧
          |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 ∧
          Real.sqrt C.scale*Real.exp (-27*(Conclusion.bulkSize k L:ℝ))≤C.statistic spectator := by
  classical
  obtain ⟨δ,hδ,hgiant⟩ := actual_positive_giant_prior
  refine ⟨δ,hδ,?_⟩
  intro d Bs BD Bz k hk
  let r : ℝ := (2:ℝ)^(k+1)
  have hr : 4≤r := by
    have h : (2:ℝ)^2≤(2:ℝ)^(k+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num only [pow_two,show (2:ℝ)*2=4 by norm_num] at h
    exact h
  let g := δ/(320*Real.sqrt 2)
  have hg : 0<g := by dsimp [g]; positivity
  obtain ⟨cψ,hcψ,hstat⟩ := halfListStatistic_lower
  obtain ⟨cA,CA,hcA,hCA,hsize⟩ := summand_sqrt_bounds d
  have hwin := eventually_upperWindow_card_lower d.A hcA hCA
    (hsize.mono fun X h => h.1) (hsize.mono fun X h => h.2.2.1)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hwin.and (eventually_ge_atTop (2:ℕ)))
  have hbsize := (Conclusion.bulkSize_tendsto_atTop hk).eventually_ge_atTop ((3+2*k:ℕ):ℝ)
  have hcell := logCell_sourceWindowCoverage_eventually d (by linarith : 0≤r) (2*(2:ℝ)^k)
  filter_upwards [hgiant d r hr,exists_bulk_prior_bin d hk (by norm_num : (0:ℝ)<1/16),
    exists_primeGroup_bin_eventually d hk (by norm_num : (1/2000:ℝ)≤1/1000)
      (by norm_num : (1/1000:ℝ)<1/100) (by norm_num : (0:ℝ)<1/16),
    exists_nominalCenterArray_with_bounds d Bs BD Bz hk,
    giantWindowScale_eventually r hr M,sourceWindowCoverage_eventually d (by linarith : 0≤r),
    hcell,statistic_scale_conditions_eventually hk hcψ (by positivity : 0<cA/2) hg,
    hbsize,eventually_ge_atTop (0:ℝ)] with L hG hbulk hspec hcenters hXscale hcover hcell hcost hslots hL
  intro E hE spectator hspecsupport hspecbal
  obtain ⟨G,c,P,hZg,hP,hGlo,hGhi,hclo,hchi,hPwindow,hgmean⟩ := hG
  obtain ⟨hZb,tb,htb,hbmean⟩ := hbulk E hE
  obtain ⟨td,htd,hsmean⟩ := hspec (Conclusion.bulkSize k L/2) (Nat.div_le_self _ _)
    spectator hspecsupport hspecbal
  have htb' : |(tb:ℝ)|≤favorableBlockWidth L/16 := by linarith
  have htd' : |(td:ℝ)|≤favorableBlockWidth L/16 := by linarith
  have hG0 : 0≤G := (Real.exp_pos _).le.trans hGlo
  obtain ⟨cells,hh,htop,hcomp⟩ := hcenters G c tb td hG0 ⟨hclo.le,hchi.le⟩ htb' htd'
  let C : InitialSourceChoice d Bs BD Bz k L E :=
    ⟨hE,G,c,P,hZg,hZb,tb,td,cells⟩
  refine ⟨C,hP,hGlo,hGhi,hclo,hchi,htb',htd',?_⟩
  have hXdata := hXscale G hGlo (by linarith [Real.exp_pos ((1/100:ℝ)*L)])
  have hMX : M≤C.scale := hXdata.1
  have hlog : 0<Real.log (C.scale:ℝ) := hXdata.2.1
  have hloglog : Real.log (Real.log (C.scale:ℝ))≤L := hXdata.2.2.1
  have hcard := (hM C.scale hMX).1
  have hXpos : 0<C.scale := by have := (hM C.scale hMX).2; omega
  have hcardpos : (0:ℝ)<(upperWindow d.A C.scale).card :=
    (div_pos (mul_pos (by positivity : 0<cA/2) (Real.sqrt_pos.mpr (by exact_mod_cast hXpos)))
      (pow_pos hlog 3)).trans_le hcard
  have hbulkcover : SourceWindowCoverage d C.bulk C.scale := by
    apply hcover G hGlo
    intro p
    have hp := (harmonicBand_log_support hZb p).2
    exact hp.trans ((Real.exp_le_exp.mpr (by nlinarith : (3/500:ℝ)*L≤(1/20:ℝ)*L)).trans hGlo)
  have hspeccover : SourceWindowCoverage d spectator C.scale := by
    apply hcover G hGlo
    intro p
    exact (hspecsupport p).2.trans ((Real.exp_le_exp.mpr (by nlinarith : (1/1000:ℝ)*L≤(1/20:ℝ)*L)).trans hGlo)
  have hauxcover : ∀i,SourceWindowCoverage d (C.auxiliary i) C.scale := by
    intro i
    cases i with
    | inl i =>
      apply hcell G hGlo (cells.top i) (by linarith [(htop i).1])
      · have hpow : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
        nlinarith [(htop i).2,Real.exp_pos ((1/100:ℝ)*L)]
    | inr ji =>
      exact hcell G hGlo (cells.comp ji.1 ji.2) (by linarith [(hcomp ji.1 ji.2).1])
        (hcomp ji.1 ji.2).2 E (cells.comp_balanced ji.1 ji.2 E hE).choose
  have hscalar : Real.exp (-10*(Conclusion.bulkSize k L:ℝ))≤
      nongiantScalar d C.bulk spectator C.auxiliary (Conclusion.bulkSize k L/2)
        (Conclusion.bulkSize k L/2) C.bulkBin C.spectatorBin := by
    apply nongiantScalar_exp_lower
    · exact Nat.div_le_self _ _
    · exact Nat.div_le_self _ _
    · rw [card_auxiliaryIndex]
      exact_mod_cast hslots
    · exact hbmean.le
    · exact hsmean.le
    · exact C.auxiliary_balanced
  have hI := hstat d P C.giant C.bulk spectator C.auxiliary
    (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L)
    C.scale tb td g hXpos hg.le (Finset.card_pos.mp (by exact_mod_cast hcardpos))
    hbulkcover hspeccover hauxcover hscalar hgmean.le
  exact statistic_scale_lower hcψ (by positivity : 0<cA/2) hg hlog
    (hloglog.trans hcost.1) hcost.2 hcard hI

end Ostmann.Construction

end

end OAI
