import OAI.NumberTheory.Jacobsthal.Primes.ConditionalPrimeBins
import OAI.NumberTheory.Jacobsthal.Sieve.ExponentialMesh

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ConditionalBinRate

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ConditionalPrimeBins ExponentialMesh DerivativeWeights WeightFutureIntegrals

 theorem relative_error_rate {c C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) (hc : 4*κ ≤ c) :
    ∀ᶠ w : ℝ in atTop, ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 →
      C*(S+1)*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/mesh κ w ≤
        Real.exp (-(κ/2)*Real.sqrt (Real.log w)) := by
  filter_upwards [log_power_exp_absorption (4*C) 3 hκ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w hbound hlog
  intro S hS0 hS
  have hpow : 1 ≤ (Real.log w)^3 := one_le_pow₀ hlog
  have hSp : S+1 ≤ 2*(Real.log w)^3 := by linarith
  have herror := prime_error_over_mesh hκ.le hc (by linarith : 0 ≤ Real.log w)
  have hm := mesh_pos κ w
  calc
    _ = (C*(S+1))*(Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/mesh κ w) := by ring
    _ ≤ (C*(2*(Real.log w)^3))*(2*Real.exp (-κ*Real.sqrt (Real.log w))) := mul_le_mul
      (mul_le_mul_of_nonneg_left hSp hC) herror (by positivity) (by positivity)
    _ = (4*C)*(Real.log w)^3*Real.exp (-κ*Real.sqrt (Real.log w)) := by ring
    _ ≤ _ := hbound

theorem actual_conditional_bin_rate : ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
      ∀ ell S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio →
      ∀ g : History w ell S start, ∀ a : ℝ, Valid g.node.side.flip a → a ≤ S →
        chain w ell S start (some g) (ActualPrimeBins.liveBin a (a+mesh κ w)) ≤
          ENNReal.ofReal ((1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*
            mesh κ w*W a*(weight g.node.side.flip a/weight g.node.side g.node.ratio)) := by
  obtain ⟨c,C,wR,hc,hC,hwR,hraw⟩ := actual_conditional_bin
  refine ⟨c/4,by positivity,?_⟩
  intro κ hκ hκc
  have hcκ : 4*κ ≤ c := by linarith
  obtain ⟨W₀,hW₀⟩ := eventually_atTop.mp (relative_error_rate hC.le hκ hcκ)
  refine ⟨max wR W₀,hwR.trans_le (le_max_left _ _),?_⟩
  intro w hw ell S hS0 hS start hell hr hs g a ha haS
  have hm := mesh_pos κ w
  have hrel := hW₀ w ((le_max_right _ _).trans hw) S hS0 hS
  have hb := hraw w ((le_max_left _ _).trans hw) ell S start hell hr hs g a (mesh κ w) ha hm (mesh_le_one hκ.le w)
  have hv : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
  have hW := (W_pos (valid_pos ha)).le
  have hratio : 0 ≤ weight g.node.side.flip a/weight g.node.side g.node.ratio :=
    (div_pos (weight_pos ha) (weight_pos hv)).le
  have hδ : C*(a+1)*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/mesh κ w ≤
      Real.exp (-(κ/2)*Real.sqrt (Real.log w)) := by
    apply le_trans _ hrel
    apply div_le_div_of_nonneg_right _ hm.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : a+1 ≤ S+1) hC.le) (Real.exp_pos _).le
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (add_le_add_right hδ 1) hm.le) hW) hratio

end NumberTheoryLean.ConditionalBinRate

end

section

namespace NumberTheoryLean.GridWeightComparison

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open WeightGlobalBounds ConditionalBinRate ExponentialMesh DerivativeWeights WeightFutureIntegrals

theorem weight_local_ratio : ∃ L : ℝ, 0 < L ∧ ∀ S : ℝ, 3 ≤ S → ∀ i : Side, ∀ u s h : ℝ,
    Valid i u → Valid i s → s ≤ S → u ≤ s → s ≤ u+h →
      weight i u/weight i s ≤ Real.exp (L*(1+S)^3*h) := by
  obtain ⟨L,hL,hbound⟩ := weights_log_lipschitz
  refine ⟨L,hL,?_⟩
  intro S hS i u s h hu hs hsS hus hsu
  have hlog : |Real.log (weight i u)-Real.log (weight i s)| ≤ L*(1+S)^3*|u-s| := by
    cases i with
    | even => exact (hbound S hS).1 u s hu hs (hus.trans hsS) hsS
    | odd => exact (hbound S hS).2 u s hu hs (hus.trans hsS) hsS
  have habs : |u-s| ≤ h := by
    rw [abs_sub_comm u s,abs_of_nonneg (sub_nonneg.mpr hus)]
    linarith
  have hdiff : Real.log (weight i u)-Real.log (weight i s) ≤ L*(1+S)^3*h :=
    ((le_abs_self _).trans hlog).trans (mul_le_mul_of_nonneg_left habs (by positivity))
  have he := Real.exp_le_exp.mpr hdiff
  rwa [Real.exp_sub,Real.exp_log (weight_pos hu),Real.exp_log (weight_pos hs)] at he

theorem actual_parent_bin_upper : ∃ κ₀ L : ℝ, 0 < κ₀ ∧ 0 < L ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
      ∀ ell S : ℝ, 3 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio →
      ∀ g : History w ell S start, ∀ u a : ℝ,
      Valid g.node.side u → Valid g.node.side.flip a → g.node.ratio ≤ S → a ≤ S →
      u ≤ g.node.ratio → g.node.ratio ≤ u+mesh κ w →
        chain w ell S start (some g) (ActualPrimeBins.liveBin a (a+mesh κ w)) ≤
          ENNReal.ofReal ((1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*
            Real.exp (L*(1+S)^3*mesh κ w)*mesh κ w*W a*(weight g.node.side.flip a/weight g.node.side u)) := by
  obtain ⟨κ₀,hκ₀,hconditional⟩ := actual_conditional_bin_rate
  obtain ⟨L,hL,hlocal⟩ := weight_local_ratio
  refine ⟨κ₀,L,hκ₀,hL,?_⟩
  intro κ hκ hκle
  obtain ⟨w₀,hw₀,hrow⟩ := hconditional κ hκ hκle
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell S hS3 hS start hell hr hs g u a hu ha hgS haS hus hsu
  have hgv : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
  have hratio := hlocal S hS3 g.node.side u g.node.ratio (mesh κ w) hu hgv hgS hus hsu
  have htarget : weight g.node.side.flip a/weight g.node.side g.node.ratio ≤
      (weight g.node.side.flip a/weight g.node.side u)*Real.exp (L*(1+S)^3*mesh κ w) := by
    have heq : weight g.node.side.flip a/weight g.node.side g.node.ratio =
        (weight g.node.side.flip a/weight g.node.side u)*(weight g.node.side u/weight g.node.side g.node.ratio) := by
      field_simp [(weight_pos hu).ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hratio (div_pos (weight_pos ha) (weight_pos hu)).le
  have hm := mesh_pos κ w
  have hW := (W_pos (valid_pos ha)).le
  have hM : 0 ≤ (1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*mesh κ w*W a := by positivity
  refine (hrow w hw ell S (by linarith) hS start hell hr hs g a ha haS).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ ((1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*mesh κ w*W a)*
        ((weight g.node.side.flip a/weight g.node.side u)*Real.exp (L*(1+S)^3*mesh κ w)) :=
      mul_le_mul_of_nonneg_left htarget hM
    _ = _ := by ring

end NumberTheoryLean.GridWeightComparison

end

end Erdos970

end OAI
