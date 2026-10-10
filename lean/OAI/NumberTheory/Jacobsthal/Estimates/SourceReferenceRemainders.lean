import OAI.NumberTheory.Jacobsthal.Analysis.RetainedNormalizedReward
import OAI.NumberTheory.Jacobsthal.Estimates.SourceCenteredGap
import OAI.NumberTheory.Jacobsthal.Partitions.ReferenceIntervalBound
import OAI.NumberTheory.Jacobsthal.Paths.ResidualHistoryGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.MovingGapHighRemoval

open _root_.Filter
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ErdosPrimeInputs.HighPrimeMass ErdosPrimeInputs.LongPrimePaths

theorem growing_gap_high_removal : ∃ w₀ : ℝ,1 < w₀ ∧ ∀ M : ℝ,∀ᶠ B : ℝ in atTop,
    ∀ w : ℝ,w₀ ≤ w → 2 ≤ B → ∀ z : Node,z.cutoff=B → 0 < z.gap → Valid z.side z.ratio → Consistent z →
      uncappedLowGapHighMass w 2 z ((Real.log B)^2) ((Real.log B)^2/2) ≤ B^(-M) := by
  obtain ⟨w₀,hw₀,h⟩ := long_prime_paths_superpolynomial
  refine ⟨w₀,hw₀,?_⟩
  intro M
  filter_upwards [h M] with B hB
  intro w hw hB2 z hcut hr hs hz
  have hw1 : 1 < w := hw₀.trans_le hw
  have hlow := uncapped_low_mass_le hw1 (by norm_num : (0:ℝ) ≤ 2) hr hs hz ((Real.log B)^2) ((Real.log B)^2/2)
  rw [hcut] at hlow
  have htail := lowGapHighMass_le_long (r₀:=z.gap) hw1 (by norm_num : (0:ℝ)<2) hB2
    (sq_nonneg (Real.log B)) (show (Real.log B)^2/2 ≤ (Real.log B)^2*2/2 by nlinarith [sq_nonneg (Real.log B)])
  exact (hlow.trans htail).trans (hB w hw 2 (by norm_num) hB2 _ (Nat.le_ceil _))

end NumberTheoryLean.MovingGapHighRemoval



namespace NumberTheoryLean.LargeCutoffResidual

open FinitePathGeometry PrimeHistories PrimeBinMembership ActualBoundaryDomain
open ReferenceLocalResidual ReferenceResidualErrors ReferenceResidualPointwise ReferenceProductErrorBounds
open ReferenceIntervalCutoff ReferenceIntervalBound GlobalResidualScale WeightPowerBounds

theorem large_cutoff_relative_power (d M : ℝ) (hd : 0 < d) (hM : 0 < M) :
    ∃ C T w₀ : ℝ,0 < C ∧ 2 ≤ T ∧ 1 < w₀ ∧ ∀ B w : ℝ,0 < B → T ≤ Real.log B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ z : Node,Valid z.side z.ratio → Consistent z →
        BoundaryDomain z.side z.gap → z.cutoff ≤ B → (Real.log B)^4 < z.cutoff →
        |sourceResidual w z| ≤ C*weight z.side z.ratio*(1+Real.log B)*powerDecay M B := by
  obtain ⟨cP,CP,wP,hcP,hCP,hwP,hP⟩ := source_residual_pointwise
  obtain ⟨cI,CI,wI,hcI,hCI,_hwI,hI⟩ := source_residual_split_bound
  obtain ⟨K,hK,hSave⟩ := linear_log_cutoff_saving hcI hd hM
  obtain ⟨CR,hCR,hRelative⟩ := relative_weight_power
  let T := max K (4*M+10)
  have hT : 2 ≤ T := by have h := le_max_right K (4*M+10); dsimp [T]; linarith
  refine ⟨CP*CR+CI,T,max wP wI,by positivity,hT,hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hBT hw hcomp z hs hz hdom hcap hbig
  have hL2 : 2 ≤ Real.log B := hT.trans hBT
  have hL : 0 ≤ Real.log B := by linarith
  have hKL : K ≤ Real.log B := (le_max_left _ _).trans hBT
  have hML : 4*M+10 ≤ Real.log B := (le_max_right _ _).trans hBT
  have hB1 : 1 ≤ B := (Real.log_nonneg_iff hB).mp hL
  have hKpos : 0 < K := by linarith
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwi : wI ≤ w := (le_max_right _ _).trans hw
  have hw1 : 1 < w := hwP.trans_le hwp
  let a := K*Real.log B
  have ha : 2 ≤ a := by dsimp [a]; nlinarith
  have hab : a < z.cutoff := by
    have ha2 : a ≤ (Real.log B)^2 := by dsimp [a]; nlinarith [mul_le_mul_of_nonneg_right hKL hL]
    have h24 : (Real.log B)^2 ≤ (Real.log B)^4 := by
      nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ (Real.log B)^2 by nlinarith) (sq_nonneg (Real.log B))]
    exact (ha2.trans h24).trans_lt hbig
  have hsHalf : (1/2:ℝ) ≤ z.ratio := by cases hi : z.side <;> simp only [hi,Valid] at hs <;> linarith
  have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
  have hr : 0 < z.gap := by rw [← he]; exact mul_pos (by linarith) (valid_pos hs)
  have hsep := rebased_ratio_separation hK hM.le hKL hML hsHalf hbig
  rw [he] at hsep
  obtain ⟨hvs,hzs⟩ := rebase_invariants hs hr hz (by linarith : 0 < a) hab.le
  have hφ := weight_pos hs
  have hφa := weight_pos hvs
  have hWeight : weight (rebase z a).side (rebase z a).ratio ≤ CR*weight z.side z.ratio*powerDecay M B :=
    hRelative M B z.side z.side z.ratio (z.gap/a) hs hsep.1 hsep.2
  have hLogA : Real.log a ≤ Real.log B := Real.log_le_log (by linarith) (hab.le.trans hcap)
  have hLogB : Real.log z.cutoff ≤ Real.log B := Real.log_le_log (by linarith) hcap
  have hLA : 0 ≤ 1+Real.log a := by have hh := Real.log_nonneg (show 1 ≤ a by linarith); linarith
  have hLb : 0 ≤ 1+Real.log z.cutoff := by have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith); linarith
  have hLB : 0 ≤ 1+Real.log B := by linarith
  have hPow := powerDecay_pos M B
  have hE2pos := primeError_pos cP w 2
  have hEApos := primeError_pos cI w a
  have hE2 := primeError_le_one hcP.le w 2
  have hEA := hSave B w hB1 hw1 hcomp
  have hLow : |sourceResidual w (rebase z a)| ≤ CP*CR*weight z.side z.ratio*(1+Real.log B)*powerDecay M B := by
    have hh := hP w hwp (rebase z a) hvs hzs ha hdom
    calc
      _ ≤ CP*weight (rebase z a).side (rebase z a).ratio*(1+Real.log a)*primeError cP w 2 := hh
      _ ≤ CP*(CR*weight z.side z.ratio*powerDecay M B)*(1+Real.log B)*1 := by gcongr
      _ = _ := by ring
  have hHigh : CI*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError cI w a ≤
      CI*weight z.side z.ratio*(1+Real.log B)*powerDecay M B := by gcongr
  have hh := hI w hwi z hs hz a ha hab
  calc
    _ ≤ CP*CR*weight z.side z.ratio*(1+Real.log B)*powerDecay M B+
        CI*weight z.side z.ratio*(1+Real.log B)*powerDecay M B := hh.trans (add_le_add hLow hHigh)
    _ = _ := by ring

end NumberTheoryLean.LargeCutoffResidual



namespace NumberTheoryLean.HighGapResidual

open FinitePathGeometry PrimeHistories PrimeBinMembership ActualBoundaryDomain
open ReferenceLocalResidual ReferenceResidualErrors ReferenceResidualPointwise ReferenceProductErrorBounds
open ReferenceIntervalCutoff ReferenceIntervalBound ReferenceResidualSum GlobalResidualScale WeightPowerBounds

theorem high_gap_residual_power (d M : ℝ) (hd : 0 < d) (hM : 0 < M) :
    ∃ C T w₀ : ℝ,0 < C ∧ 2 ≤ T ∧ 1 < w₀ ∧ ∀ B w : ℝ,0 < B → T ≤ Real.log B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ z : Node,Valid z.side z.ratio → Consistent z →
        BoundaryDomain z.side z.gap → 2 ≤ z.cutoff → z.cutoff ≤ B → (Real.log B)^2/2 ≤ z.gap →
        |sourceResidual w z| ≤ C*(1+Real.log B)*powerDecay M B := by
  obtain ⟨cP,CP,wP,hcP,hCP,hwP,hP⟩ := source_residual_pointwise
  obtain ⟨cI,CI,wI,hcI,hCI,_hwI,hI⟩ := source_residual_split_bound
  obtain ⟨K,hK,hSave⟩ := linear_log_cutoff_saving hcI hd hM
  have hKpos : 0 < K := by linarith
  obtain ⟨CA,TA,hCA,_hTA,hAbs⟩ := weight_power_at_ratio hKpos hM
  obtain ⟨W,hW,hWeight⟩ := uniform_weight_bound
  let T := max 2 TA
  refine ⟨CP*CA+CI*W,T,max wP wI,by positivity,le_max_left _ _,hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hBT hw hcomp z hs hz hdom hb hcap hgap
  have hL2 : 2 ≤ Real.log B := (le_max_left _ _).trans hBT
  have hL : 0 ≤ Real.log B := by linarith
  have hLA : TA ≤ Real.log B := (le_max_right _ _).trans hBT
  have hB1 : 1 ≤ B := (Real.log_nonneg_iff hB).mp hL
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwi : wI ≤ w := (le_max_right _ _).trans hw
  have hw1 : 1 < w := hwP.trans_le hwp
  let a := K*Real.log B
  have ha : 2 ≤ a := by dsimp [a]; nlinarith
  have hr : 0 < z.gap := by nlinarith
  have hφ := weight_pos hs
  have hRat := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hLogB : Real.log z.cutoff ≤ Real.log B := Real.log_le_log (by linarith) hcap
  have hLb : 0 ≤ 1+Real.log z.cutoff := by have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith); linarith
  have hLB : 0 ≤ 1+Real.log B := by linarith
  have hPow := powerDecay_pos M B
  have hE2pos := primeError_pos cP w 2
  have hEApos := primeError_pos cI w a
  have hE2 := primeError_le_one hcP.le w 2
  have hEA := hSave B w hB1 hw1 hcomp
  by_cases hba : z.cutoff ≤ a
  · have hRatio := gap_over_linear_cutoff hKpos hL (by linarith : 0 < z.cutoff) hba hgap
    rw [← hRat] at hRatio
    have hWt := hAbs B hLA z.side z.ratio hRatio
    have hpoint := hP w hwp z hs hz hb hdom
    have hBase : |sourceResidual w z| ≤ CP*CA*(1+Real.log B)*powerDecay M B := by
      calc
        _ ≤ CP*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError cP w 2 := hpoint
        _ ≤ CP*(CA*powerDecay M B)*(1+Real.log B)*1 := by gcongr
        _ = _ := by ring
    apply hBase.trans
    apply mul_le_mul_of_nonneg_right _ hPow.le
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hCI.le hW.le)) hLB
  · have hab : a < z.cutoff := lt_of_not_ge hba
    obtain ⟨hvs,hzs⟩ := rebase_invariants hs hr hz (by linarith : 0 < a) hab.le
    have hφa := weight_pos hvs
    have hRatio := gap_over_linear_cutoff hKpos hL (by linarith : 0 < a) (le_refl a) hgap
    have hWt := hAbs B hLA z.side (z.gap/a) hRatio
    have hLogA : Real.log a ≤ Real.log B := Real.log_le_log (by linarith) (hab.le.trans hcap)
    have hLa : 0 ≤ 1+Real.log a := by have hh := Real.log_nonneg (show 1 ≤ a by linarith); linarith
    have hLow : |sourceResidual w (rebase z a)| ≤ CP*CA*(1+Real.log B)*powerDecay M B := by
      have hpoint := hP w hwp (rebase z a) hvs hzs ha hdom
      calc
        _ ≤ CP*weight z.side (z.gap/a)*(1+Real.log a)*primeError cP w 2 := hpoint
        _ ≤ CP*(CA*powerDecay M B)*(1+Real.log B)*1 := by gcongr
        _ = _ := by ring
    have hWsource := hWeight _ _ hs
    have hHigh : CI*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError cI w a ≤
        CI*W*(1+Real.log B)*powerDecay M B := by gcongr
    have hh := hI w hwi z hs hz a ha hab
    calc
      _ ≤ CP*CA*(1+Real.log B)*powerDecay M B+CI*W*(1+Real.log B)*powerDecay M B :=
        hh.trans (add_le_add hLow hHigh)
      _ = _ := by ring

end NumberTheoryLean.HighGapResidual



namespace NumberTheoryLean.LowStateResidualBound

open FinitePathGeometry PrimeHistories PrimeBinMembership ActualBoundaryDomain
open ReferenceLocalResidual ReferenceResidualPointwise ReferenceProductErrorBounds GlobalResidualScale LargeCutoffResidual

theorem low_state_normalized_residual (d : ℝ) (hd : 0 < d) :
    ∃ c C T w₀ : ℝ,0 < c ∧ 0 < C ∧ 2 ≤ T ∧ 1 < w₀ ∧
      ∀ B w : ℝ,0 < B → T ≤ Real.log B → w₀ ≤ w → Real.log B ≤ d*Real.log w →
      ∀ z : Node,Valid z.side z.ratio → Consistent z → BoundaryDomain z.side z.gap →
        2 ≤ z.cutoff → z.cutoff ≤ B → z.gap ≤ (23/10:ℝ)*B → z.ratio ≤ (Real.log B)^2 →
        (z.gap^2/weight z.side z.ratio)*|sourceResidual w z| ≤
          C*((Real.log B)^13*primeError c w 2+1/B^7) := by
  obtain ⟨c,CP,wP,hc,hCP,hwP,hP⟩ := source_residual_pointwise
  obtain ⟨CL,TL,wL,hCL,hTL,_hwL,hLarge⟩ := large_cutoff_relative_power d 10 hd (by norm_num)
  let C := 2*CP+6*CL
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨c,C,TL,max wP wL,hc,hC,hTL,hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hT hw hcomp z hs hz hdom hb hcap hgap hratio
  have hL2 : 2 ≤ Real.log B := hTL.trans hT
  have hL : 0 ≤ Real.log B := by linarith
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwL : wL ≤ w := (le_max_right _ _).trans hw
  have hφ := weight_pos hs
  have hr : 0 < z.gap := by have hh := boundary_gap_ge_two hdom; linarith
  have hE := primeError_pos c w 2
  have hSmallC : 2*CP ≤ C := by dsimp [C]; linarith
  have hLargeC : 6*CL ≤ C := by dsimp [C]; linarith
  have hterm0 : 0 ≤ (Real.log B)^13*primeError c w 2 := by positivity
  have hinv0 : 0 ≤ (1:ℝ)/B^7 := by positivity
  by_cases hsmall : z.cutoff ≤ (Real.log B)^4
  · have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
    have hr6 : z.gap ≤ (Real.log B)^6 := by
      have hm := mul_le_mul hsmall hratio (valid_pos hs).le (pow_nonneg hL 4)
      rw [he] at hm
      nlinarith
    have hr12 : z.gap^2 ≤ (Real.log B)^12 := by
      have hm := pow_le_pow_left₀ hr.le hr6 2
      simpa only [← pow_mul] using hm
    have hlog := Real.log_le_log (by linarith : 0 < z.cutoff) hcap
    have hLf : 0 ≤ 1+Real.log z.cutoff := by have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith); linarith
    have hLup : 1+Real.log z.cutoff ≤ 2*Real.log B := by linarith
    have hp := hP w hwp z hs hz hb hdom
    have hm := mul_le_mul_of_nonneg_left hp (div_nonneg (sq_nonneg z.gap) hφ.le)
    have hn : (z.gap^2/weight z.side z.ratio)*|sourceResidual w z| ≤
        CP*z.gap^2*(1+Real.log z.cutoff)*primeError c w 2 := by
      convert! hm using 1
      field_simp
    calc
      _ ≤ CP*z.gap^2*(1+Real.log z.cutoff)*primeError c w 2 := hn
      _ ≤ CP*(Real.log B)^12*(2*Real.log B)*primeError c w 2 := by gcongr
      _ = (2*CP)*((Real.log B)^13*primeError c w 2) := by ring
      _ ≤ C*((Real.log B)^13*primeError c w 2) := mul_le_mul_of_nonneg_right hSmallC hterm0
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hinv0) hC.le
  · have hlarge := hLarge B w hB hT hwL hcomp z hs hz hdom hcap (lt_of_not_ge hsmall)
    have hr2 : z.gap^2 ≤ 6*B^2 := by
      have hm := pow_le_pow_left₀ hr.le hgap 2
      nlinarith [sq_nonneg B]
    have hLB : 1+Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hB]
    have hLB0 : 0 ≤ 1+Real.log B := by linarith
    have hPow := powerDecay_pos 10 B
    have hm := mul_le_mul_of_nonneg_left hlarge (div_nonneg (sq_nonneg z.gap) hφ.le)
    have hn : (z.gap^2/weight z.side z.ratio)*|sourceResidual w z| ≤
        CL*z.gap^2*(1+Real.log B)*powerDecay 10 B := by
      convert! hm using 1
      field_simp
    calc
      _ ≤ CL*z.gap^2*(1+Real.log B)*powerDecay 10 B := hn
      _ ≤ CL*(6*B^2)*B*powerDecay 10 B := by gcongr
      _ = (6*CL)*(1/B^7) := by
        have hpow10 := powerDecay_nat hB 10
        norm_num only [Nat.cast_ofNat] at hpow10
        rw [hpow10]
        field_simp
      _ ≤ C*(1/B^7) := mul_le_mul_of_nonneg_right hLargeC hinv0
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hterm0) hC.le

end NumberTheoryLean.LowStateResidualBound



namespace NumberTheoryLean.HighResidualSum

attribute [local instance] Classical.propDecidable
open _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh ActualBoundaryDomain SourceNodeCoordinates
open ReferenceSourceDecomposition ReferenceResidualPointwise ReferenceResidualSum ReferenceLocalResidual ReferenceProductErrorBounds
open GlobalResidualScale HighGapResidual MovingGapHighRemoval ResidualHistoryGeometry
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def highResidualAbsoluteSum (w B : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ (uncappedPrefixes w 2 start).filter (actualHasHigh w ((Real.log B)^2) start),
    prefixWeight ps*|sourceResidual w (terminal w start ps)|

theorem source_residual_crude : ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w →
    ∀ B : ℝ,∀ z : Node,Valid z.side z.ratio → Consistent z → BoundaryDomain z.side z.gap →
      2 ≤ z.cutoff → z.cutoff ≤ B → |sourceResidual w z| ≤ C*(1+Real.log B) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := source_residual_pointwise
  obtain ⟨W,hW,hWbound⟩ := uniform_weight_bound
  refine ⟨C*W,w₀,by positivity,hw₀,?_⟩
  intro w hw B z hs hz hdom hb hcap
  have hφ := weight_pos hs
  have hwb := hWbound _ _ hs
  have hlog := Real.log_le_log (by linarith : 0 < z.cutoff) hcap
  have hLb : 0 ≤ 1+Real.log z.cutoff := by have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith); linarith
  have hLB : 0 ≤ 1+Real.log B := by linarith
  have hEpos := primeError_pos c w 2
  have hE := primeError_le_one hc.le w 2
  calc
    _ ≤ C*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError c w 2 := h w hw z hs hz hb hdom
    _ ≤ C*W*(1+Real.log B)*1 := by gcongr
    _ = _ := by ring

theorem high_residual_sum_bound (d : ℝ) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff=B → B^2*highResidualAbsoluteSum w B start ≤ C/B^6 := by
  obtain ⟨CC,wC,hCC,hwC,hCrude⟩ := source_residual_crude
  obtain ⟨CH,TH,wH,hCH,hTH,_hwH,hHigh⟩ := high_gap_residual_power d 10 hd (by norm_num)
  obtain ⟨wT,_hwT,hTail⟩ := growing_gap_high_removal
  obtain ⟨BT,hBT⟩ := eventually_atTop.mp (hTail 10)
  obtain ⟨M,wM,hM,_hwM,hMass⟩ := total_prime_prefix_mass
  let B₀ := max 4 (max BT (Real.exp TH))
  let w₀ := max wC (max wH (max wT wM))
  refine ⟨CC+CH*M,B₀,w₀,by positivity,by dsimp [B₀]; have h := le_max_left (4:ℝ) (max BT (Real.exp TH)); linarith,
    hwC.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hB4 : 4 ≤ B := (le_max_left _ _).trans hB
  have hBT' : BT ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hBexp : Real.exp TH ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  have hBpos : 0 < B := by linarith
  have hBTlog : TH ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hBexp
  have hL2 : 2 ≤ Real.log B := hTH.trans hBTlog
  have hL : 0 ≤ 1+Real.log B := by linarith
  have hwC' : wC ≤ w := (le_max_left _ _).trans hw
  have hwH' : wH ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwT' : wT ≤ w := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  have hwM' : wM ≤ w := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  obtain ⟨hs,hr,_hstart,_hsize⟩ := source_node_bounds hBpos start hi h199 h23 hcons hcut
  let S := (Real.log B)^2
  let H := (uncappedPrefixes w 2 start).filter (actualHasHigh w S start)
  have hPow := powerDecay_pos 10 B
  have hDecay := powerDecay_nat hBpos 10
  norm_num only [Nat.cast_ofNat] at hDecay
  have hsmall : uncappedLowGapHighMass w 2 start S (S/2) ≤ powerDecay 10 B := by
    have hh := hBT B hBT' w hwT' (by linarith) start hcut hr hs hcons
    simpa only [S,Real.rpow_neg hBpos.le,Real.rpow_ofNat,hDecay] using hh
  have htotal : (∑ ps ∈ H,prefixWeight ps) ≤ M*B := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ps _ _ => prefixWeight_nonneg ps))
    calc
      _ ≤ ∑ ps ∈ decreasingPrefixes (primesBetween (w^(2:ℝ)) (w^start.cutoff)),prefixWeight ps :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ps _ _ => prefixWeight_nonneg ps)
      _ ≤ M*B := by rw [hcut]; have hh := hMass w hwM' 2 B (by norm_num) (by linarith); nlinarith [mul_pos hM hBpos]
  have hpoint : ∀ ps ∈ H,|sourceResidual w (terminal w start ps)| ≤
      CC*(1+Real.log B)*(if (terminal w start ps).gap ≤ S/2 then 1 else 0)+CH*(1+Real.log B)*powerDecay 10 B := by
    intro ps hp
    have hpA : uncappedAllowed w 2 start ps := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    obtain ⟨hvs,hcs,hdom,hlo,hup,_hrp,_hsizep⟩ := source_terminal_geometry hB4 start hi h199 h23 hcons hcut hpA
    by_cases hg : (terminal w start ps).gap ≤ S/2
    · rw [ite_eq_left hg,mul_one]
      exact (hCrude w hwC' B _ hvs hcs hdom hlo.le hup).trans (le_add_of_nonneg_right (by positivity))
    · rw [ite_eq_right hg,mul_zero,zero_add]
      exact hHigh B w hBpos hBTlog hwH' hcomp _ hvs hcs hdom hlo.le hup (le_of_lt (lt_of_not_ge hg))
  have hlowSum : (∑ ps ∈ H,prefixWeight ps*(if (terminal w start ps).gap ≤ S/2 then 1 else 0))=
      uncappedLowGapHighMass w 2 start S (S/2) := by
    unfold H uncappedLowGapHighMass
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ps _hp
    by_cases hh : actualHasHigh w S start ps <;>
      by_cases hg : (terminal w start ps).gap ≤ S/2 <;> simp [hh,hg]
  have hsum : highResidualAbsoluteSum w B start ≤
      CC*(1+Real.log B)*powerDecay 10 B+CH*(1+Real.log B)*powerDecay 10 B*(M*B) := by
    have hh := Finset.sum_le_sum (fun ps hp => mul_le_mul_of_nonneg_left (hpoint ps hp) (prefixWeight_nonneg ps))
    have he : (∑ ps ∈ H,prefixWeight ps*(CC*(1+Real.log B)*(if (terminal w start ps).gap ≤ S/2 then 1 else 0)+
        CH*(1+Real.log B)*powerDecay 10 B))=
      CC*(1+Real.log B)*(∑ ps ∈ H,prefixWeight ps*(if (terminal w start ps).gap ≤ S/2 then 1 else 0))+
      CH*(1+Real.log B)*powerDecay 10 B*(∑ ps ∈ H,prefixWeight ps) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ps _hp
      ring
    rw [he,hlowSum] at hh
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hsmall (by positivity))
      (mul_le_mul_of_nonneg_left htotal (by positivity)))
  have hB1 : 1 ≤ B := by linarith
  have hLB : 1+Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hBpos]
  have hcrudeB : CC*(1+Real.log B)*powerDecay 10 B ≤ CC*(1+Real.log B)*powerDecay 10 B*B :=
    le_mul_of_one_le_right (by positivity) hB1
  have hcombined : highResidualAbsoluteSum w B start ≤ (CC+CH*M)*B*(1+Real.log B)*powerDecay 10 B := by
    nlinarith only [hsum,hcrudeB]
  calc
    _ ≤ B^2*((CC+CH*M)*B*(1+Real.log B)*powerDecay 10 B) := mul_le_mul_of_nonneg_left hcombined (sq_nonneg B)
    _ ≤ B^2*((CC+CH*M)*B*B*powerDecay 10 B) := by gcongr
    _ = _ := by rw [hDecay]; field_simp

end NumberTheoryLean.HighResidualSum



namespace NumberTheoryLean.SharpRetainedResidual

attribute [local instance] Classical.propDecidable
open _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeKilledChain PrimeCorrectionFactor PrimeFamilyOccupation
open LowStateHorizon UniformBudgetRate ActualPrimeHigh SourceNodeCoordinates ResidualHistoryGeometry
open ReferenceLocalResidual ReferenceProductErrorBounds LowStateResidualBound
open ErdosPrimeInputs.PrimePrefixMass ErdosRetainedRewardTransfer

noncomputable def retainedResidualAbsoluteSum (w B : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ retainedPrefixes w 2 ((Real.log B)^2) start,prefixWeight ps*|sourceResidual w (terminal w start ps)|

theorem retained_residual_sum_bound (d : ℝ) (hd : 0 < d) :
    ∃ c C B₀ w₀ : ℝ,0 < c ∧ 0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff=B →
      B^2*retainedResidualAbsoluteSum w B start ≤ C*((Real.log w)^16*primeError c w 2+1/B^4) := by
  obtain ⟨c,CP,T,wP,hc,hCP,hT,hwP,hP⟩ := low_state_normalized_residual d hd
  obtain ⟨wBudget,hwBudget⟩ := eventually_atTop.mp
    ((correctionBudget_tendsto_zero d).eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)))
  let A := 5*transferConstant*CP
  have hA : 0 < A := by dsimp [A]; exact mul_pos (mul_pos (by norm_num) transferConstant_positive) hCP
  let C := A*(d^16+1)
  let B₀ := max 4 (Real.exp T)
  let w₀ := max wP (max normalizationThreshold (max wBudget (Real.exp (d^2))))
  refine ⟨c,C,B₀,w₀,hc,by dsimp [C]; positivity,by dsimp [B₀]; have hh := le_max_left (4:ℝ) (Real.exp T); linarith,
    hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hB4 : 4 ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := by linarith
  have hBexp : Real.exp T ≤ B := (le_max_right _ _).trans hB
  have hBT : T ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hBexp
  have hlogB : 2 ≤ Real.log B := hT.trans hBT
  have hL : 0 ≤ Real.log B := by linarith
  have hwP' : wP ≤ w := (le_max_left _ _).trans hw
  have hnorm : normalizationThreshold ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwBud : wBudget ≤ w := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  have hwExp : Real.exp (d^2) ≤ w := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwP.trans_le hwP'
  have hlogw : d^2 ≤ Real.log w := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hwExp
  have hS := (source_scale_bound hlogw hlogB hcomp).1
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hbudget := hwBudget w hwBud
  let delta := CP*((Real.log B)^13*primeError c w 2+1/B^7)
  have hE := primeError_pos c w 2
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have hF : ∀ ps ∈ retainedPrefixes w 2 ((Real.log B)^2) start,
      (terminal w start ps).gap^2*|sourceResidual w (terminal w start ps)|/
        weight (terminal w start ps).side (terminal w start ps).ratio ≤ delta := by
    intro ps hp
    have hpA := (mem_retainedPrefixes hw1 start ps).mp hp
    have hpU : uncappedAllowed w 2 start ps :=
      (uncapped_iff_exists_ceiling w 2 start ps).mpr ⟨(Real.log B)^2,hsS,hpA⟩
    obtain ⟨hvs,hcs,hdom,hlo,hup,_hrp,hgup⟩ := source_terminal_geometry hB4 start hi h199 h23 hcons hcut hpU
    have hratio := terminal_ratio_le hsS hpA
    have hh := hP B w hBpos hBT hwP' hcomp _ hvs hcs hdom hlo.le hup hgup hratio
    calc
      _ = ((terminal w start ps).gap^2/weight (terminal w start ps).side (terminal w start ps).ratio)*
          |sourceResidual w (terminal w start ps)| := by ring
      _ ≤ delta := hh
  have hTransfer := retained_normalized_reward_sum (d:=d) (w:=w) (ell:=2) (B:=B) (delta:=delta) (start:=start)
    hnorm (by norm_num) hS hsS hBpos hlogB hcomp hbudget hi h199 h23 hcons hcut hdelta
    (fun ps => sourceResidual w (terminal w start ps)) hF
  have hN := source_horizon_log_cube hlogB
  have hraw : B^2*retainedResidualAbsoluteSum w B start ≤
      A*((Real.log B)^16*primeError c w 2+(Real.log B)^3/B^7) := by
    calc
      _ ≤ transferConstant*(sourceHorizon ((Real.log B)^2) B:ℝ)*delta := hTransfer
      _ ≤ transferConstant*(5*(Real.log B)^3)*delta :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN transferConstant_positive.le) hdelta
      _ = _ := by dsimp [A,delta]; ring
  have hlogw0 : 0 ≤ Real.log w := (Real.log_pos hw1).le
  have hpower : (Real.log B)^16 ≤ d^16*(Real.log w)^16 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hL hcomp 16
  have hlogB_le : Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hBpos]
  have hfrac : (Real.log B)^3/B^7 ≤ 1/B^4 := by
    calc
      _ ≤ B^3/B^7 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hL hlogB_le 3) (by positivity)
      _ = _ := by field_simp
  have hterm := mul_le_mul_of_nonneg_right hpower hE.le
  have hx : 0 ≤ (Real.log w)^16*primeError c w 2 := by positivity
  have hy : 0 ≤ (1:ℝ)/B^4 := by positivity
  calc
    _ ≤ A*((Real.log B)^16*primeError c w 2+(Real.log B)^3/B^7) := hraw
    _ ≤ A*(d^16*((Real.log w)^16*primeError c w 2)+1/B^4) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      exact add_le_add (by simpa only [mul_assoc] using hterm) hfrac
    _ ≤ _ := by
      dsimp only [C]
      nlinarith only [mul_nonneg hA.le hx,mul_nonneg (mul_nonneg hA.le (pow_nonneg hd.le 16)) hy]

end NumberTheoryLean.SharpRetainedResidual



namespace NumberTheoryLean.SharpGlobalResidual

open _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeFamilyOccupation
open ReferenceLocalResidual ReferenceResidualSum ReferenceSourceDecomposition ReferenceLogScale
open SharpRetainedResidual HighResidualSum

theorem actual_residual_partition {w B : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ (Real.log B)^2) :
    residualAbsoluteSum w start=retainedResidualAbsoluteSum w B start+highResidualAbsoluteSum w B start :=
  uncapped_sum_partition hw hsS (fun ps => ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps*|sourceResidual w (terminal w start ps)|)

theorem sharp_source_residual_sum (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*residualAbsoluteSum w start ≤ ε := by
  obtain ⟨c,CL,BL,wL,hc,hCL,hBL,hwL,hLow⟩ := retained_residual_sum_bound d hd
  obtain ⟨CH,BH,wH,hCH,_hBH,_hwH,hHigh⟩ := high_residual_sum_bound d hd
  have hdec := log_power_primeError_tendsto CL 16 hc
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp
    (hdec.eventually (eventually_le_nhds (show (0:ℝ)<ε/2 by linarith)))
  let B₀ := max BL (max BH (max (Real.exp 2) (2*(CL+CH)/ε)))
  let w₀ := max wL (max wH wE)
  refine ⟨B₀,w₀,hBL.trans_le (le_max_left _ _),hwL.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBL' : BL ≤ B := (le_max_left _ _).trans hB
  have hBH' : BH ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hBexp : Real.exp 2 ≤ B := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hB
  have hBlarge : 2*(CL+CH)/ε ≤ B := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hB
  have hBpos : 0 < B := hBL.trans_le hBL'
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hB1 : 1 ≤ B := (Real.log_nonneg_iff hBpos).mp (by linarith)
  have hwL' : wL ≤ w := (le_max_left _ _).trans hw
  have hwH' : wH ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwE' : wE ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwL.trans_le hwL'
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hlow := hLow B w hBL' hwL' hcomp start hi h199 h23 hcons hcut
  have hhigh := hHigh B w hBH' hwH' hcomp start hi h199 h23 hcons hcut
  have hB4 : B ≤ B^4 := by simpa only [pow_one] using pow_le_pow_right₀ hB1 (show (1:ℕ) ≤ 4 by norm_num)
  have hB6 : B ≤ B^6 := by simpa only [pow_one] using pow_le_pow_right₀ hB1 (show (1:ℕ) ≤ 6 by norm_num)
  have htail : CL/B^4+CH/B^6 ≤ ε/2 := by
    have hfrac : CL/B^4+CH/B^6 ≤ (CL+CH)/B := by
      calc
        _ ≤ CL/B+CH/B := add_le_add
          (div_le_div_of_nonneg_left hCL.le hBpos hB4) (div_le_div_of_nonneg_left hCH.le hBpos hB6)
        _ = _ := by ring
    apply hfrac.trans
    apply (div_le_iff₀ hBpos).mpr
    have hh := (div_le_iff₀ hε).mp hBlarge
    nlinarith
  have hsmall := hwE w hwE'
  rw [mul_add,mul_one_div] at hlow
  rw [actual_residual_partition hw1 hsS,mul_add]
  nlinarith only [hlow,hhigh,htail,hsmall]

theorem sharp_signed_residual (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*|residualCorrection w start| ≤ ε := by
  obtain ⟨B₀,w₀,hB₀,hw₀,h⟩ := sharp_source_residual_sum d ε hd hε
  refine ⟨B₀,w₀,hB₀,hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  exact (mul_le_mul_of_nonneg_left (signed_residual_le_absolute w start) (sq_nonneg B)).trans
    (h B w hB hw hcomp start hi h199 h23 hcons hcut)

end NumberTheoryLean.SharpGlobalResidual



namespace NumberTheoryLean.GlobalReferenceApproximation

open FinitePathGeometry PrimeHistories PrimeBinMembership SourceNodeCoordinates
open ReferenceLocalResidual ReferenceSourceDecomposition UniformBoundaryCorrection SharpGlobalResidual

theorem global_reference_remainder (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        B^2*|sourceReference w start-nodeBenchmark w start-boundaryCorrection w 2 start| ≤ ε := by
  obtain ⟨B₁,w₀,hB₁,hw₀,h⟩ := sharp_signed_residual d ε hd hε
  refine ⟨max B₁ 4,w₀,hB₁.trans_le (le_max_left _ _),hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hB₁' : B₁ ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := by linarith
  obtain ⟨hs,hr,_h1,_h2⟩ := source_node_bounds hBpos start hi h199 h23 hcons hcut
  have he := actual_reference_decomposition (hw₀.trans_le hw) hs hr hcons (by rw [hcut]; linarith)
  have heq : sourceReference w start-nodeBenchmark w start-boundaryCorrection w 2 start=residualCorrection w start := by linarith
  rw [heq]
  exact h B w hB₁' hw hcomp start hi h199 h23 hcons hcut

end NumberTheoryLean.GlobalReferenceApproximation



open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit ErdosContinuousAnomaly
open NumberTheoryLean.ReferenceSourceDecomposition NumberTheoryLean.ReferenceLocalResidual
open NumberTheoryLean.UniformBoundaryCorrection NumberTheoryLean.GlobalReferenceApproximation

theorem root_source_remainder_tendsto (a : ℝ) :
    Tendsto (fun z => (ErdosInverseBoxHeight.sourceB z)^2*
      (sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode a z)-
        nodeBenchmark (ErdosInverseBoxHeight.sourceW z) (sourceRootNode a z)-
        boundaryCorrection (ErdosInverseBoxHeight.sourceW z) 2 (sourceRootNode a z))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨B₀,w₀,_hB₀,_hw₀,h⟩ := global_reference_remainder 2 (eps/2) (by norm_num) (by linarith)
  filter_upwards [actual_root_eventually a,rootB_tendsto.eventually (eventually_ge_atTop B₀),
    rootW_tendsto.eventually (eventually_ge_atTop w₀)] with z hs hB hw
  have hh := h (ErdosInverseBoxHeight.sourceB z) (ErdosInverseBoxHeight.sourceW z) hB hw hs.2.2.1
    (sourceRootNode a z) rfl hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.2 rfl
  rw [Real.dist_eq,sub_zero,abs_mul,abs_of_nonneg (sq_nonneg _)]
  exact hh.trans_lt (by linarith)

theorem root_anomaly_replacement_tendsto (a : ℝ) :
    Tendsto (fun z => (ErdosInverseBoxHeight.sourceB z)^2*
      (boundaryCorrection (ErdosInverseBoxHeight.sourceW z) 2 (sourceRootNode a z)-
        continuousBoundaryCorrection (ErdosInverseBoxHeight.sourceW z) 2 (sourceRootNode a z))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨B₀,w₀,_hB₀,_hw₀,h⟩ := actual_anomaly_replacement 2 2 (eps/2) le_rfl (by norm_num) (by linarith)
  filter_upwards [actual_root_eventually a,rootB_tendsto.eventually (eventually_ge_atTop B₀),
    rootW_tendsto.eventually (eventually_ge_atTop w₀)] with z hs hB hw
  have hh := h (ErdosInverseBoxHeight.sourceB z) (ErdosInverseBoxHeight.sourceW z) hB hw hs.2.2.1
    (sourceRootNode a z) rfl hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.2 rfl
  rw [Real.dist_eq,sub_zero,abs_mul,abs_of_nonneg (sq_nonneg _)]
  exact hh.trans_lt (by linarith)

end ErdosSourceReferenceMargin


end Erdos970

end OAI
