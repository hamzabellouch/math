import OAI.NumberTheory.Jacobsthal.Analysis.CorrectedCompactTransfer
import OAI.NumberTheory.Jacobsthal.Estimates.ScaledOriginalTail
import OAI.NumberTheory.Jacobsthal.Partitions.CompactSelectedPartition

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem removed_signed_reward_bound {w ell S c : ℝ} (hw : 1 < w)
    {start : Node} (hsS : start.ratio ≤ S) (F : List ℕ → ℝ)
    (hF : ∀ ps ∈ uncappedPrefixes w ell start,
      |F ps| ≤ Real.exp (-c*(terminal w start ps).gap)) :
    |(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps) -
      (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)| ≤
      uncappedRewardedHighMass w ell start S c := by
  classical
  have hp := uncapped_sum_partition (ell := ell) hw hsS (fun ps => prefixWeight ps*F ps)
  have he : (∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps) -
      (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps) =
      ∑ ps ∈ (uncappedPrefixes w ell start).filter (actualHasHigh w S start),prefixWeight ps*F ps := by
    linarith only [hp]
  rw [he]
  calc
    _ ≤ ∑ ps ∈ (uncappedPrefixes w ell start).filter (actualHasHigh w S start),
        |prefixWeight ps*F ps| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ps hps
      rw [abs_mul,abs_of_nonneg (prefixWeight_nonneg ps)]
      exact mul_le_mul_of_nonneg_left (hF ps (Finset.mem_filter.mp hps).1) (prefixWeight_nonneg ps)

theorem removed_signed_reward_every_power :
    ∃ M w₀ : ℝ,0 < M ∧ 1 < w₀ ∧ ∀ c : ℝ,0 < c → ∀ A : ℝ,∀ᶠ B : ℝ in atTop,
      ∀ w : ℝ,w₀ ≤ w → ∀ ell : ℝ,1 ≤ ell → ell ≤ B → ∀ start : Node,
        start.cutoff = B → 0 < start.gap → Valid start.side start.ratio → Consistent start →
        start.ratio ≤ (Real.log B)^2 → ∀ F : List ℕ → ℝ,
        (∀ ps ∈ uncappedPrefixes w ell start,|F ps| ≤ Real.exp (-c*(terminal w start ps).gap)) →
        |(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps) -
          (∑ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,prefixWeight ps*F ps)| ≤ M*B^(-A) := by
  obtain ⟨M,w₀,hM,hw₀,hbound⟩ := uncapped_rewarded_high_removal
  refine ⟨M,w₀,hM,hw₀,?_⟩
  intro c hc A
  filter_upwards [hbound c hc A] with B hB
  intro w hw ell hell hellB start hcut hr hs hcons hsS F hF
  exact (removed_signed_reward_bound (hw₀.trans_le hw) hsS F hF).trans
    (hB w hw ell hell hellB start hcut hr hs hcons)

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.LiteralPrimeOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeFamilyOccupation
open PrimeCompactWeights CompactInverseTest CompactNormalizationCorrection ScaledOriginalTail DerivativeWeights
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def nodeReward (H : Side → ℝ×ℝ → ℝ) (w : ℝ) (start : Node) (ps : List ℕ) : ℝ :=
  H (terminal w start ps).side ((terminal w start ps).gap,(terminal w start ps).ratio)

noncomputable def familyValue (H : Side → ℝ×ℝ → ℝ) (w ell S : ℝ) (start : Node) : ℝ :=
  (start.gap^2/weight start.side start.ratio)*
    (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*nodeReward H w start ps)

noncomputable def sourceFactor (B : ℝ) (start : Node) : ℝ :=
  B^2*weight start.side start.ratio/start.gap^2

theorem signed_weight_test_identity {w ell S B : ℝ} {start : Node}
    (hs : Valid start.side start.ratio) (H : Side → ℝ×ℝ → ℝ) (z : ChainState w ell S start) :
    scaledWeight w B start z*listReward (nodeReward H w start) z =
      sourceFactor B start*correctedTest (inverseTest H) z := by
  cases z with
  | none => simp [scaledWeight,listReward,correctedTest]
  | some h =>
    have hv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
    change scaledWeight w B start (some h)*H h.node.side (h.node.gap,h.node.ratio) =
      sourceFactor B start*((1+epsilon w)^h.primes.length*inverseTest H h.node.side (h.node.gap,h.node.ratio))
    rw [inverseTest_eq hv]
    unfold scaledWeight sourceFactor
    ring

theorem literal_corrected_occupation {w ell S B : ℝ} {start : Node}
    (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B) (H : Side → ℝ×ℝ → ℝ) :
    familyValue H w ell S start = correctedExpectation (inverseTest H) w ell S start (LowStateHorizon.sourceHorizon S B) := by
  have he := finite_signed_original_occupation hw hell hS0 hS hr hs hsS hB hsize (nodeReward H w start)
  simp_rw [signed_weight_test_identity hs H,integral_const_mul] at he
  rw [← Finset.mul_sum] at he
  have hf : 0 < sourceFactor B start := by unfold sourceFactor; have hp := weight_pos hs; positivity
  apply mul_left_cancel₀ hf.ne'
  calc
    _ = B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*nodeReward H w start ps) := by
      unfold sourceFactor familyValue
      field_simp [(weight_pos hs).ne',hr.ne']
    _ = _ := he.symm

noncomputable def tailListReward (c K w : ℝ) (start : Node) (ps : List ℕ) : ℝ :=
  if K < (terminal w start ps).gap then Real.exp (-c*(terminal w start ps).gap) else 0

theorem tailListReward_nonneg (c K w : ℝ) (start : Node) (ps : List ℕ) : 0 ≤ tailListReward c K w start ps := by
  unfold tailListReward
  split_ifs <;> positivity

theorem tail_weight_test_identity {w ell S B : ℝ} {start : Node} (c K : ℝ) (z : ChainState w ell S start) :
    ENNReal.ofReal (scaledWeight w B start z*listReward (tailListReward c K w start) z) = scaledTail c K w B start z := by
  cases z with
  | none => simp [scaledWeight,listReward,scaledTail]
  | some h =>
    change ENNReal.ofReal (scaledWeight w B start (some h)*(if K < h.node.gap then Real.exp (-c*h.node.gap) else 0)) = _
    change ENNReal.ofReal (scaledWeight w B start (some h)*(if K < h.node.gap then Real.exp (-c*h.node.gap) else 0)) =
      if K < h.node.gap then ENNReal.ofReal (scaledWeight w B start (some h)*Real.exp (-c*h.node.gap)) else 0
    by_cases hh : K < h.node.gap
    · rw [ite_eq_left hh,ite_eq_left hh]
    · rw [ite_eq_right hh,ite_eq_right hh,mul_zero,ENNReal.ofReal_zero]

theorem literal_scaled_tail {w ell S B : ℝ} {start : Node}
    (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B) (c K : ℝ) :
    ENNReal.ofReal (B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*tailListReward c K w start ps)) =
      ∑ n ∈ range (LowStateHorizon.sourceHorizon S B),∫⁻ z,scaledTail c K w B start z ∂pathLaw w ell S start n := by
  have he := finite_nonnegative_original_occupation hw hell hS0 hS hr hs hsS hB hsize
    (tailListReward c K w start) (fun ps _ => tailListReward_nonneg c K w start ps)
  simp_rw [tail_weight_test_identity c K] at he
  exact he.symm

end NumberTheoryLean.LiteralPrimeOccupation

end

section

namespace NumberTheoryLean.LiteralUniformPrimeTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualPrimeHigh PrimeFamilyOccupation LiteralPrimeOccupation ScaledOriginalTail
open UniformBudgetRate LowStateHorizon ErdosPrimeInputs.PrimePrefixMass

theorem tailListReward_envelope (c K w : ℝ) (start : Node) (ps : List ℕ) :
    |tailListReward c K w start ps| ≤ Real.exp (-c*(terminal w start ps).gap) := by
  unfold tailListReward
  split_ifs
  · rw [abs_of_pos (Real.exp_pos _)]
  · rw [abs_zero]; exact (Real.exp_pos _).le

theorem actual_uniform_original_prime_tail (d c ε : ℝ) (hd : 0 < d) (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₀ : ℕ,∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧
      ∀ M : ℕ,M₀ ≤ M → ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      ∀ ell : ℝ,1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      ∀ start : Node,start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        B^2*(∑ ps ∈ uncappedPrefixes w ell start,
          prefixWeight ps*tailListReward c (3*((M:ℝ)+1)) w start ps) ≤ ε := by
  obtain ⟨M₀,BL,wL,hBL,hwL,hlow⟩ := actual_uniform_scaled_tail d c (ε/2) hd hc (by linarith)
  obtain ⟨Crem,wH,hCrem,hwH,hremove⟩ := removed_signed_reward_every_power
  obtain ⟨BH,hBH⟩ := eventually_atTop.mp (hremove c hc 3)
  obtain ⟨wScale,hwScale⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  let B₀ := max BL (max BH (max (Real.exp 2) (2*Crem/ε)))
  let w₀ := max wL (max wH (max normalizationThreshold wScale))
  refine ⟨M₀,B₀,w₀,hBL.trans_le (le_max_left _ _),hwL.trans_le (le_max_left _ _),?_⟩
  intro M hM B w hB hw ell hell hellB hcomp start hi h199 h23 hcons hcut
  have hBL' : BL ≤ B := (le_max_left _ _).trans hB
  have hBH' : BH ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hB
  have hBexp : Real.exp 2 ≤ B :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBlarge : 2*Crem/ε ≤ B :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBpos : 0 < B := hBL.trans_le hBL'
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hwL' : wL ≤ w := (le_max_left _ _).trans hw
  have hwH' : wH ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hw
  have hwScale' : wScale ≤ w :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hw
  have hscale := source_scale_bound (hwScale w hwScale') hlogB hcomp
  let S := (Real.log B)^2
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hsS : start.ratio ≤ S := by linarith
  have he : B*start.ratio = start.gap := by
    have hh : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at hh
    exact (eq_div_iff (valid_pos hs).ne').mp hh
  have hr : 0 < start.gap := by rw [← he]; exact mul_pos hBpos (valid_pos hs)
  have hsize : start.gap ≤ (23/10:ℝ)*B := by nlinarith
  let F := tailListReward c (3*((M:ℝ)+1)) w start
  have hretained : B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps) ≤ ε/2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ ε/2)).mp
    rw [literal_scaled_tail hnorm hell hS0 hscale.1 hr hs hsS hBpos hsize]
    exact hlow M hM B w hBL' hwL' ell hell hellB hcomp start hi h199 h23 hcons hcut
  have hremoved := hBH B hBH' w hwH' ell hell hellB start hcut hr hs hcons hsS F
    (fun ps _ => tailListReward_envelope c (3*((M:ℝ)+1)) w start ps)
  have hremovedScaled : B^2*(Crem*B^(-(3:ℝ))) ≤ ε/2 := by
    have heq : B^2*(Crem*B^(-(3:ℝ))) = Crem/B := by
      rw [Real.rpow_neg hBpos.le,Real.rpow_ofNat]
      field_simp
    rw [heq]
    apply (div_le_iff₀ hBpos).mpr
    have hh := (div_le_iff₀ hε).mp hBlarge
    nlinarith
  have hdiff := mul_le_mul_of_nonneg_left hremoved (sq_nonneg B)
  have htriangle : B^2*(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps) ≤
      B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)+
        B^2*|(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps)-
          (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)| := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self
      ((∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*F ps)-
       (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps))) (sq_nonneg B)
    nlinarith
  linarith

end NumberTheoryLean.LiteralUniformPrimeTail

end

end Erdos970

end OAI
