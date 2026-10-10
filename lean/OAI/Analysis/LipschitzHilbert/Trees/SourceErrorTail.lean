import OAI.Analysis.LipschitzHilbert.Trees.SourceErrorSupported
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceTailOrder

namespace OAI

/-! Polynomial thresholds for the actual positive convolution error.
Only the source bound and its logarithmic scale sum enter the constants. -/

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace LipschitzHilbert.LineErrorSources

variable {N : ℕ}

def momentBase (P : LineErrorSources N) (grid : FiniteLineGrid) : ℝ :=
  16*((((grid.branching:ℝ)+2)*(2*P.meanConstant+P.oscillationConstant+1))/
    Real.log (3/2)+P.meanConstant+1)

theorem momentBase_pos (P : LineErrorSources N) (grid : FiniteLineGrid) :
    0 < P.momentBase grid := by
  have hsum := P.sumBound_nonneg
  have hsource := P.sourceBound_nonneg
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold momentBase meanConstant oscillationConstant
  positivity

theorem majorant_moment_natural (P : LineErrorSources N) (grid : FiniteLineGrid)
    (hb : 1 < grid.branching) (hsource : ∀ j, grid.width < P.length j → P.source j = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ x, (ENNReal.ofReal (P.majorant x))^n ∂grid.lineMeasure) ≤
      ENNReal.ofReal ((P.momentBase grid*(n:ℝ))^n)*grid.lineMeasure univ := by
  have hmean : 0 ≤ P.meanConstant := by
    unfold meanConstant
    exact mul_nonneg (by positivity) P.sumBound_nonneg
  have hosc : 0 ≤ P.oscillationConstant := by
    unfold oscillationConstant
    exact mul_nonneg (by positivity) P.sourceBound_nonneg
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have h := ennreal_polynomial_moment_majorant
    ((((grid.branching:ℝ)+2)*(2*P.meanConstant+P.oscillationConstant+1))/Real.log (3/2))
    P.meanConstant (by positivity) hmean n hn
  have hm := P.majorant_moment_of_supported grid hb hsource (p := n) (Nat.cast_nonneg n)
  simp only [ENNReal.rpow_natCast] at hm
  exact hm.trans (mul_le_mul' (by simpa only [momentBase,mul_div_assoc,ENNReal.rpow_natCast] using h) le_rfl)

/-- A single order, chosen before the source family and interval, gives
the desired tail. No error majorant or concentration estimate is assumed. -/
theorem eventually_error_polynomial_tail (a J : ℝ) (ha : 0 ≤ a) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (P : LineErrorSources N)
      (grid : FiniteLineGrid), grid.branching = 2 →
      (∀ j, grid.width < P.length j → P.source j = 0) → P.sourceBound ≤ L^a → P.sumBound ≤ L^a →
      grid.lineMeasure {x | L^(a+4) ≤ P.majorant x} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ := by
  let K : ℝ := 16*((4*(2*(1024*Real.pi^2)+240*Real.pi+1))/Real.log (3/2)+
    1024*Real.pi^2+1)
  have hK : 0 < K := by
    have : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
    dsimp [K]
    positivity
  filter_upwards [eventually_source_reference_tail_order J hJ,
    eventually_ge_atTop (max 1 K)] with L hn hlarge
  obtain ⟨n,hn,hnL,hdecay⟩ := hn
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hKL : K ≤ L := (le_max_right _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hLa : 1 ≤ L^a := Real.one_le_rpow hL ha
  intro N P grid hb hsource hs hsum
  have hb' : 1 < grid.branching := by omega
  have hbase : P.momentBase grid ≤ K*L^a := by
    have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
    calc
      _ ≤ 16*((4*(2*((1024*Real.pi^2)*L^a)+(240*Real.pi)*L^a+L^a))/
          Real.log (3/2)+(1024*Real.pi^2)*L^a+L^a) := by
        unfold momentBase meanConstant oscillationConstant
        rw [hb]
        norm_num only [Nat.cast_ofNat]
        gcongr
      _ = _ := by dsimp [K]; ring
  have hthreshold : 4*(P.momentBase grid*(n:ℝ)) ≤ L^(a+4) := by
    calc
      _ = P.momentBase grid*(4*(n:ℝ)) := by ring
      _ ≤ (K*L^a)*L^2 := mul_le_mul hbase hnL (by positivity)
        (mul_nonneg hK.le (Real.rpow_nonneg hL0.le _))
      _ ≤ (L*L^a)*L^2 := by gcongr
      _ = L^(a+3) := by
        rw [Real.rpow_add hL0,show L^(3:ℝ) = L^(3:ℕ) from Real.rpow_natCast L 3]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hm := P.majorant_moment_natural grid hb' hsource n hn
  rw [ENNReal.ofReal_pow (mul_pos (P.momentBase_pos grid) hn0).le] at hm
  have ht := moment_superlevel_quarter grid.lineMeasure P.majorant P.majorant_continuous.measurable
    n (P.momentBase grid*(n:ℝ)) (mul_pos (P.momentBase_pos grid) hn0)
    (grid.lineMeasure univ) (by simpa only [abs_of_nonneg (P.majorant_nonneg _)] using hm)
  have hdecay' : (1/4:ℝ≥0∞)^n ≤ ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal hdecay
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at h
    norm_num only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat] at h
    simpa using h
  exact (measure_mono (fun x hx => by
    change 4*(P.momentBase grid*(n:ℝ)) ≤ |P.majorant x|
    rw [abs_of_nonneg (P.majorant_nonneg x)]
    exact hthreshold.trans hx)).trans (ht.trans (mul_le_mul' hdecay' le_rfl))

end LipschitzHilbert.LineErrorSources

end

end OAI
