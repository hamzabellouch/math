import OAI.NumberTheory.OrdinaryCorrelations.Elliott.SubsetCost

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset

namespace OrdinaryCorrelations.RawDivisorBin
open OrdinaryAnalyticCentering ElliottReductions

def binIndex (τ : ℝ) (d : ℕ) : ℕ := ⌈Real.log (d:ℝ) / Real.log τ⌉₊ - 1

lemma binIndex_bounds {τ : ℝ} (hτ : 1 < τ) {d : ℕ} (hd : 1 < d) :
    τ^(binIndex τ d) < (d:ℝ) ∧ (d:ℝ) ≤ τ^(binIndex τ d+1) := by
  have hτpos : 0 < τ := by linarith
  have hdR : (1:ℝ) < d := by exact_mod_cast hd
  have hl := Real.log_pos hτ
  have hdp : 0 < (d:ℝ) := by linarith
  have hratio : 0 < Real.log (d:ℝ) / Real.log τ := div_pos (Real.log_pos hdR) hl
  have hceil : 0 < ⌈Real.log (d:ℝ) / Real.log τ⌉₊ := Nat.ceil_pos.mpr hratio
  have hs : binIndex τ d + 1 = ⌈Real.log (d:ℝ) / Real.log τ⌉₊ := by unfold binIndex; omega
  have hlower : (binIndex τ d : ℝ) < Real.log (d:ℝ) / Real.log τ := by
    apply Nat.lt_ceil.mp
    unfold binIndex
    omega
  have hupper : Real.log (d:ℝ) / Real.log τ ≤ (binIndex τ d+1:ℕ) := by
    rw [hs]
    exact Nat.le_ceil _
  constructor
  · apply (Real.log_lt_log_iff (pow_pos hτpos _) hdp).mp
    rw [Real.log_pow]
    exact (lt_div_iff₀ hl).mp hlower
  · apply (Real.log_le_log_iff hdp (pow_pos hτpos _)).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ hl).mp hupper

lemma binIndex_lt {τ C B : ℝ} (hτ : 1 < τ) {d : ℕ} (hd : 1 < d)
    (hsize : Real.log (d:ℝ) ≤ C*B) : binIndex τ d < ⌈C*B/Real.log τ⌉₊ := by
  have hratio : 0 < Real.log (d:ℝ) / Real.log τ :=
    div_pos (Real.log_pos (by exact_mod_cast hd)) (Real.log_pos hτ)
  have hceil := Nat.ceil_pos.mpr hratio
  have hle := Nat.ceil_mono (div_le_div_of_nonneg_right hsize (Real.log_pos hτ).le)
  unfold binIndex
  omega

theorem raw_bin (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hmf : Multiplicative f) (hmg : Multiplicative g) (h1f : f 1 = 1) (h1g : g 1 = 1)
    (hfd : Summable (primeDefect f)) (hgd : Summable (primeDefect g))
    (τ : ℝ) (hτ : 1 < τ) (hτ2 : τ < 2) :
    ∃ C₀ c : ℝ, 1 ≤ C₀ ∧ 0 < c ∧ ∀ᶠ B : ℝ in atTop,
      ∃ H : ℝ, ∃ D : Finset ℕ, Admissible B C₀ τ H D ∧
        (∀ d ∈ D, 1/2 ≤ ‖f d * g d‖) ∧ c * L₀ B / B ≤ ∑ d ∈ D, divisorWeight B d / d := by
  classical
  obtain ⟨C,hC,hCD⟩ := truncated_divisor_mass f g hf hg hmf hmg h1f h1g hfd hgd
  let K := 1 + C / Real.log τ
  have hl : 0 < Real.log τ := Real.log_pos hτ
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, 1/(4*K), hC, by positivity, ?_⟩
  filter_upwards [hCD] with B hB
  obtain ⟨hB, D, hD, hmass⟩ := hB
  have hB0 : 0 < B := by linarith
  let n := ⌈C*B/Real.log τ⌉₊
  have hn : 0 < n := Nat.ceil_pos.mpr (div_pos (mul_pos (by linarith) hB0) hl)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hfbin : ∀ d ∈ D, binIndex τ d ∈ range n := fun d hd =>
    mem_range.mpr (binIndex_lt hτ (hD d hd).2.2.1 (hD d hd).2.2.2.2.1)
  have hnn : (range n).Nonempty := ⟨0,mem_range.mpr hn⟩
  have hb : (range n).card • (L₀ B / (4*n)) ≤ ∑ d ∈ D, divisorWeight B d/d := by
    rw [card_range, nsmul_eq_mul]
    calc
      _ = L₀ B / 4 := by field_simp [hnR.ne']
      _ ≤ _ := hmass
  obtain ⟨r,hr,hbin⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hfbin hnn hb
  refine ⟨τ^r, D.filter (fun d => binIndex τ d = r), ?_, ?_, ?_⟩
  · refine ⟨one_le_pow₀ hτ.le, ?_, ?_⟩
    · have hrN : r < n := mem_range.mp hr
      have hrC : (r:ℝ) < C*B/Real.log τ := Nat.lt_ceil.mp hrN
      have hlog : Real.log (τ^r) ≤ C*B := by
        rw [Real.log_pow]
        exact ((lt_div_iff₀ hl).mp hrC).le
      exact (Real.log_le_iff_le_exp (pow_pos (by linarith : 0 < τ) r)).mp hlog
    · intro d hd
      obtain ⟨hd,hrd⟩ := mem_filter.mp hd
      obtain ⟨hsq,hsub,hd1,hcard,hsize,hmod⟩ := hD d hd
      obtain ⟨hlo,hhi⟩ := binIndex_bounds hτ hd1
      rw [hrd] at hlo hhi
      exact ⟨hsq,hsub,hd1,hlo,by simpa only [pow_succ, mul_comm] using hhi,hcard⟩
  · intro d hd
    exact (hD d (mem_filter.mp hd).1).2.2.2.2.2
  · have hnle : (n:ℝ) ≤ K*B := by
      have hn' : (n:ℝ) < C*B/Real.log τ+1 := Nat.ceil_lt_add_one (by positivity)
      have he : C*B/Real.log τ = (C/Real.log τ)*B := by ring
      dsimp [K]
      rw [he] at hn'
      nlinarith
    have hL : 0 ≤ L₀ B := L₀_nonneg B
    calc
      (1/(4*K))*L₀ B/B = L₀ B/(4*(K*B)) := by ring_nf
      _ ≤ L₀ B/(4*n) := div_le_div_of_nonneg_left hL (by positivity) (by nlinarith)
      _ ≤ _ := hbin

end OrdinaryCorrelations.RawDivisorBin

end

end OAI
