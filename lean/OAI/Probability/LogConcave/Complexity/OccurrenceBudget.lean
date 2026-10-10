import Mathlib
import OAI.Probability.LogConcave.Sampling.LogMeshCountRate

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature MeanTree
open scoped Topology Classical

def sourceOccurrenceBudget (a b : ℝ) (n m N nc Nc d : ℕ) : ℕ :=
  meanWork (Fintype.card (ProbabilityNode (sourceCorrelation a d) ((d:ℝ)^(-b)) (n+1)))
    (n+2) m N nc Nc 0 0 0+
  (Fintype.card (ProbabilityNode (sampleCorrelation ((d:ℝ)^(-a))) ((d:ℝ)^(-b)) (n+1))+1)^N

def occurrenceDegree (N Nc : ℕ) : ℕ := max (Nc*(2*N+2)) N

lemma sourceOccurrenceBudget_rate {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (n m N nc Nc : ℕ) :
    LogPowerRate (fun d => (sourceOccurrenceBudget a b n m N nc Nc d:ℝ))
      (-((occurrenceDegree N Nc:ℕ):ℝ)*b) := by
  have he := sourceCorrelation_eventually ha
  have hp := probabilityNode_card_rate hb.le (n+1)
    (he.mono (fun _ h => h.1)) (he.mono (fun _ h => h.2.1))
    (logMeshLength_rate a (he.mono (fun _ h => h.1))
      (he.mono (fun _ h => h.2.1)) (he.mono (fun _ h => h.2.2.le)))
  have hR : ∀ᶠ d : ℕ in atTop,0<(d:ℝ)^(-a) ∧ (d:ℝ)^(-a)≤1 := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
    exact ⟨Real.rpow_pos_of_pos (by linarith) _,Real.rpow_le_one_of_one_le_of_nonpos hd1 (by linarith)⟩
  have hs := hR.mono (fun d hd => sampleCorrelation_properties hd.1 hd.2)
  have hsp := probabilityNode_card_rate hb.le (n+1)
    (hs.mono (fun _ h => by linarith [h.1])) (hs.mono (fun _ h => h.2.1))
    (logMeshLength_sample_rate (hR.mono (fun _ h => ⟨le_rfl,h.2⟩)))
  have hsample := (hsp.add ((LogPowerRate.const 1).mono (by linarith))).pow N
  have hmean := meanWork_rate hb.le hp (n+2) m N nc Nc
  have hB₁ : ((Nc*(2*N+2):ℕ):ℝ)≤(occurrenceDegree N Nc:ℝ) := by
    exact_mod_cast le_max_left (Nc*(2*N+2)) N
  have hB₂ : (N:ℝ)≤(occurrenceDegree N Nc:ℝ) := by exact_mod_cast le_max_right (Nc*(2*N+2)) N
  have hm := hmean.mono (show -(occurrenceDegree N Nc:ℝ)*b≤-((Nc*(2*N+2):ℕ):ℝ)*b by nlinarith)
  have hp' := hsample.mono (show -(occurrenceDegree N Nc:ℝ)*b≤(N:ℝ)*(-b) by nlinarith)
  simpa only [sourceOccurrenceBudget,Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hm.add hp'

namespace OracleCompiler

lemma literalSample_cost_le_source {a b : ℝ} {d : ℕ} (hd : 0<d)
    (n m N nc Nc : ℕ) {η : ℝ} (hηR : (d:ℝ)^(-a)≤η) (hη1 : η≤1)
    (r : ℝ) (e : ProbabilityNode (sampleCorrelation η) ((d:ℝ)^(-b)) (n+1)) :
    cost (literalSample (d:=d) r (sampleCorrelation η) ((d:ℝ)^(-b)) (n+1) N e)≤
      sourceOccurrenceBudget a b n m N nc Nc d := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hR := Real.rpow_pos_of_pos hd0 (-a)
  have hη := lt_of_lt_of_le hR hηR
  have hR1 : (d:ℝ)^(-a)≤1 := hηR.trans hη1
  have hmono := logMeshCount_mono (sampleCorrelation_antitone hR.le hηR)
    (sampleCorrelation_properties hR hR1).2.1 (Real.rpow_pos_of_pos hd0 (-b))
  have hcard : Fintype.card (ProbabilityNode (sampleCorrelation η) ((d:ℝ)^(-b)) (n+1))≤
      Fintype.card (ProbabilityNode (sampleCorrelation ((d:ℝ)^(-a))) ((d:ℝ)^(-b)) (n+1)) := by
    simp only [probabilityNode_card]
    exact Nat.mul_le_mul_right _ hmono
  rw [cost_literalSample]
  have he := flowWork_bound (Fintype.card (ProbabilityNode (sampleCorrelation η) ((d:ℝ)^(-b)) (n+1))) N 0
  simp only [zero_add,one_mul] at he
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hcard 1) N
  unfold sourceOccurrenceBudget
  omega

theorem exists_cost_mesh_exponent {t κ : ℝ} (ht : 0<t) (hκ : 0<κ)
    (N Nc rank : ℕ) : ∃w : ℝ,0<w ∧ w<t ∧
      ∀n m nc,∀ᶠ d : ℕ in atTop,
        ((2*(40*sourceOccurrenceBudget (κ*t) (κ*w) n m N nc Nc d+40)^rank:ℕ):ℝ)≤
          (d:ℝ)^(κ*t) := by
  let H : ℝ := (rank:ℝ)*(occurrenceDegree N Nc:ℝ)+1
  have hH : 0<H := by dsimp [H]; positivity
  let w := t/(2*H)
  have hw : 0<w := div_pos ht (mul_pos (by norm_num) hH)
  have hHt : 1≤H := by
    dsimp [H]
    have : 0≤(rank:ℝ)*(occurrenceDegree N Nc:ℝ) := by positivity
    linarith
  have hwid : w*(2*H)=t := div_mul_cancel₀ t (ne_of_gt (mul_pos (by norm_num) hH))
  have hwt : w<t := by nlinarith
  refine ⟨w,hw,hwt,?_⟩
  intro n m nc
  have hc := sourceOccurrenceBudget_rate (mul_pos hκ ht) (mul_pos hκ hw) n m N nc Nc
  have hr := routineBudget_rate (show 0≤(occurrenceDegree N Nc:ℝ)*(κ*w) by positivity) (by simpa only [neg_mul] using hc) rank
  have hexp : -(κ*t)< -(rank:ℝ)*((occurrenceDegree N Nc:ℝ)*(κ*w)) := by
    have he : (rank:ℝ)*(occurrenceDegree N Nc:ℝ)*w<t := by dsimp [H] at hwid hH hHt; nlinarith
    nlinarith
  have he := hr.eventually_small hexp
  filter_upwards [he] with d hd
  exact (le_abs_self _).trans (by simpa only [neg_neg] using hd)

end OracleCompiler
end LogConcaveSampling

end

end

end OAI
