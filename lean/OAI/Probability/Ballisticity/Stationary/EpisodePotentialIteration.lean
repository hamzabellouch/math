import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeCounterChain
import OAI.Probability.Ballisticity.Stationary.EpisodeExponential

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma potential_runFrom (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor K : ℝ) (N : ℕ)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b)))) (n : ℕ) :
    ∫⁻ ω, stagePotential (K*b)
      (J ω+episodeSteps e f hef r fexp g χ b sfloor N (q ω) ω n)
      (F ω+episodeCount e f hef r fexp g χ b sfloor N (q ω) ω
        (episodeStageFails e f r fexp g χ b N) n) ∂environmentLaw ν ≤
    ∫⁻ ω, stagePotential (K*b) (J ω) (F ω) ∂environmentLaw ν := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    have hh := (A.runFrom hef fexp g χ b sfloor N n).potential_advance ν
      (A.runFrom_partition hA hef fexp g χ b sfloor N n) fexp g χ b sfloor K N hH hbound
    apply le_trans _ ih
    simpa only [episodeSteps,episodeCount,Nat.add_assoc] using hh

end EpisodeRecordedAtlas

theorem actual_stage_exponential {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) (r : ℝ → ℝ)
    (fexp g χ b sfloor K : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b)))) (i : ℕ) :
    ∫⁻ ω, stagePotential (K*b)
      (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i)
      (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
        (episodeStageFails e f r fexp g χ b N) i) ∂environmentLaw ν ≤ 1 := by
  have hc : ∀ i : ℕ, ∫⁻ ω, stagePotential (K*b)
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).stages
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).failures ∂environmentLaw ν ≤ 1 := by
    intro i
    induction i with
    | zero => simp only [episodeCounterChain,stagePotential,Nat.cast_zero,mul_zero,sub_self,Real.exp_zero,
        ENNReal.ofReal_one,lintegral_one,measure_univ,le_refl]
    | succ i ih =>
      apply le_trans _ ih
      exact (episodeCounterAtlas (k:=k) e f hef r fexp g χ b sfloor hR N i).potential_runFrom ν
        (episodeCounterAtlas_partition (k:=k) e f hef r fexp g χ b sfloor hR N i)
        hef fexp g χ b sfloor K N hH hbound N
  have he : (fun ω => stagePotential (K*b)
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).stages
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).failures) =
      (fun ω => stagePotential (K*b)
        (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i)
        (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
          (episodeStageFails e f r fexp g χ b N) i)) := by
    funext ω
    have hh := episodeCounterChain_actual (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    rw [hh.2.2.1,hh.2.2.2]
  simpa only [he] using hc i

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

theorem actual_stage_entropy {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) (r : ℝ → ℝ)
    (fexp g χ b sfloor K : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b))))
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q] (C : ℝ) (hC : 0 ≤ C)
    (hkl : klDiv Q (environmentLaw ν) ≤ ENNReal.ofReal C) (i : ℕ) :
    K*b*(∫ ω, (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
        (episodeStageFails e f r fexp g χ b N) i:ℝ) ∂Q) ≤ C+Real.exp (-(K*b))*
      (∫ ω, (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i:ℝ) ∂Q) := by
  let J := fun ω => (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i:ℝ)
  let F := fun ω => (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
    (episodeStageFails e f r fexp g χ b N) i:ℝ)
  let Z := fun ω => K*b*F ω-Real.exp (-(K*b))*J ω
  have hm := EpisodeChainLedger.measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N i
  have hcast : Measurable (fun n : ℕ => (n:ℝ)) := measurable_of_countable _
  have hJ : Measurable J := hcast.comp hm.fst
  have hF : Measurable F := hcast.comp hm.snd
  have hZ : Measurable Z := (hF.const_mul _).sub (hJ.const_mul _)
  have hB : ∃ B : ℝ, ∀ ω, |Z ω| ≤ B := by
    refine ⟨(|K*b|+Real.exp (-(K*b)))*(i*N:ℕ),fun ω => ?_⟩
    have hh := EpisodeChainLedger.counts_bounded (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    have hj : |J ω| ≤ (i*N:ℕ) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      dsimp only [J]
      exact_mod_cast hh.1
    have hf : |F ω| ≤ (i*N:ℕ) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      dsimp only [F]
      exact_mod_cast hh.2
    calc
      |Z ω| ≤ |K*b*F ω|+|Real.exp (-(K*b))*J ω| := by
        simpa only [Z,sub_eq_add_neg,abs_neg] using abs_add_le (K*b*F ω) (-(Real.exp (-(K*b))*J ω))
      _ = |K*b| *|F ω|+Real.exp (-(K*b))*|J ω| := by
        simp only [abs_mul,abs_of_pos (Real.exp_pos _)]
      _ ≤ |K*b| *(i*N:ℕ)+Real.exp (-(K*b))*(i*N:ℕ) := by gcongr
      _ = _ := by ring
  have he := Entropy.exp_integrable_of_bounded (μ:=environmentLaw ν) hZ hB
  have hmgf := actual_stage_exponential ν e f hef r fexp g χ b sfloor K hR N hH hbound i
  have hint : (∫ ω, Real.exp (Z ω) ∂environmentLaw ν) ≤ 1 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ)≤1)).mp
    rw [ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    simpa only [stagePotential,Z,J,F,ENNReal.ofReal_one] using hmgf
  have hE := Entropy.expBudget_of_kl_le Q (environmentLaw ν) hC hkl Z hZ hB
  have hi := EpisodeChainLedger.counts_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q i
  have hze : (∫ ω, Z ω ∂Q) = K*b*(∫ ω, F ω ∂Q)-Real.exp (-(K*b))*(∫ ω, J ω ∂Q) := by
    rw [integral_sub (hi.2.const_mul _) (hi.1.const_mul _),integral_const_mul,integral_const_mul]
  rw [hze] at hE
  change K*b*(∫ ω, F ω ∂Q) ≤ C+Real.exp (-(K*b))*(∫ ω, J ω ∂Q)
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episode_count_absorption (j z L b g f K D β : ℝ)
    (hj : 0 ≤ j) (hL : 0 ≤ L) (hb : 0 < b) (hg : 0 < g) (hf : 0 ≤ f) (hK : 0 < K)
    (hc : 1/g+(1+f/g)*D/K ≤ β/32)
    (hs : (1+f/g)*Real.exp (-(K*b))/(K*b) ≤ 1/2)
    (hlarge : 32*b ≤ β*L)
    (hcount : j ≤ L/(g*b)+(1+f/g)*z+1)
    (hent : K*b*z ≤ D*L+Real.exp (-(K*b))*j) :
    2*b*j ≤ β/4*L := by
  have hkb : 0 < K*b := mul_pos hK hb
  have hcf : 0 ≤ 1+f/g := by positivity
  have hz : z ≤ (D*L+Real.exp (-(K*b))*j)/(K*b) := (le_div_iff₀ hkb).mpr (by nlinarith only [hent])
  have he : L/(g*b)+(1+f/g)*((D*L+Real.exp (-(K*b))*j)/(K*b))+1 =
      (L/b)*(1/g+(1+f/g)*D/K)+((1+f/g)*Real.exp (-(K*b))/(K*b))*j+1 := by
    field_simp
    ring
  have hh : j ≤ L/(g*b)+(1+f/g)*((D*L+Real.exp (-(K*b))*j)/(K*b))+1 := by
    have hx := mul_le_mul_of_nonneg_left hz hcf
    linarith only [hcount,hx]
  rw [he] at hh
  have ht := mul_le_mul_of_nonneg_left hc (div_nonneg hL hb.le)
  have hu := mul_le_mul_of_nonneg_right hs hj
  have hh' : j/2 ≤ (L/b)*(β/32)+1 := by linarith
  have hv := mul_le_mul_of_nonneg_left hh' hb.le
  have hEq : b*((L/b)*(β/32)+1)=β*L/32+b := by field_simp
  rw [hEq] at hv
  nlinarith only [hv,hlarge]

theorem actual_expected_stages {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) (r : ℝ → ℝ)
    (fexp g χ b sfloor K D β : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (hs : 1 ≤ sfloor) (hN : sfloor ≤ (N:ℝ))
    (hf : 0 ≤ fexp) (hg : 0 < g) (hb : 0 < b) (hK : 0 < K) (hD : 0 ≤ D)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s:ℝ))
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b))))
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hkl : klDiv Q (environmentLaw ν) ≤ ENNReal.ofReal (D*Real.log (N:ℝ)))
    (hc : 1/g+(1+fexp/g)*D/K ≤ β/32)
    (hsmall : (1+fexp/g)*Real.exp (-(K*b))/(K*b) ≤ 1/2)
    (hlarge : 32*b ≤ β*Real.log (N:ℝ)) :
    2*b*(∫ ω, (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω N:ℝ) ∂Q) ≤
      β/4*Real.log (N:ℝ) := by
  let J := fun ω => (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω N:ℝ)
  let F := fun ω => (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
    (episodeStageFails e f r fexp g χ b N) N:ℝ)
  have hi := EpisodeChainLedger.counts_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (hs.trans hN)
  have hH0 : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s := by
    intro s h
    have hp : 0 < s := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hs.trans h)
    exact_mod_cast (mul_pos hp (Real.exp_pos _)).trans_le (hH s h)
  have he := actual_stage_entropy ν e f hef r fexp g χ b sfloor K hR N hH0 hbound Q
    (D*Real.log (N:ℝ)) (mul_nonneg hD hlog) hkl N
  have hcount : (∫ ω, J ω ∂Q) ≤ Real.log (N:ℝ)/(g*b)+(1+fexp/g)*(∫ ω, F ω ∂Q)+1 := by
    have hh := integral_mono hi.1
      (((integrable_const (Real.log (N:ℝ)/(g*b))).add (hi.2.const_mul (1+fexp/g))).add (integrable_const 1))
      (fun ω => EpisodeChainLedger.stage_count_bound (k:=k) e f hef r fexp g χ b sfloor hR N ω hs hN hf hg hb hH)
    change (∫ ω, J ω ∂Q) ≤ (∫ ω, Real.log (N:ℝ)/(g*b)+(1+fexp/g)*F ω+1 ∂Q) at hh
    have hfi : Integrable F Q := hi.2
    rw [integral_add (f:=fun ω => Real.log (N:ℝ)/(g*b)+(1+fexp/g)*F ω) (g:=fun _ => (1:ℝ))
      ((integrable_const _).add (hfi.const_mul _)) (integrable_const _),
      integral_add (f:=fun _ => Real.log (N:ℝ)/(g*b)) (g:=fun ω => (1+fexp/g)*F ω)
        (integrable_const _) (hfi.const_mul _),integral_const_mul] at hh
    simpa only [integral_const,probReal_univ,one_smul] using hh
  exact episode_count_absorption _ _ _ _ _ _ _ _ _
    (integral_nonneg (fun ω => Nat.cast_nonneg _)) hlog hb hg hf hK hc hsmall hlarge hcount he

end DirectionalTransience

end

end OAI
