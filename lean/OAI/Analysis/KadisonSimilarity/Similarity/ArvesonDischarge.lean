import OAI.Analysis.KadisonSimilarity.Similarity.ArvesonCompleteNorm

namespace OAI

/-! The Arveson commutant-distance identity follows from the sharp
implementation theorem for completely bounded derivations. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped ENNReal Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance arvesonDischarge_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

theorem twice_distance_le_of_complete_bound (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) {C : ℝ} (hC : 0 < C)
    (hb : completeCommutatorNorm M.commutant T ≤ ENNReal.ofReal C) :
    2 * Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ C := by
  let σ := M.commutant.toStarSubalgebra.subtype
  let δ := commutantDerivation M T
  obtain ⟨V, hV, hn⟩ := sharp_implementation_of_complete_bound σ δ
    (commutantDerivation_leibniz M T) hC (commutantDerivation_complete_bound M T hC.le hb)
  have hmem : T - V ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    have he := hV ⟨a, ha⟩
    change commutator T a = commutator V a at he
    have hz : commutator (T - V) a = 0 := by rw [commutator_sub_left, he, sub_self]
    exact (sub_eq_zero.mp hz).symm
  have hd := Metric.infDist_le_dist_of_mem hmem (x := T)
  have he : T - (T - V) = V := by abel
  rw [dist_eq_norm, he] at hd
  linarith

/-- The precise CSSW (2010), Equation (2.1), specialization is proved. -/
theorem arvesonDistanceFormula (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    ArvesonDistanceFormula M T := by
  let b := completeCommutatorNorm M.commutant T
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (completeCommutatorNorm_le_twice_distance M T)
  let r := b.toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have happrox (n : ℕ) : 2 * Metric.infDist T (M : Set (H →L[ℂ] H)) ≤
      r + (1 / 2 : ℝ) ^ n := by
    apply twice_distance_le_of_complete_bound M T (by positivity)
    change b ≤ ENNReal.ofReal (r + (1 / 2 : ℝ) ^ n)
    calc
      b = ENNReal.ofReal r := (ENNReal.ofReal_toReal hb).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))
  have hlim : Tendsto (fun n : ℕ => r + (1 / 2 : ℝ) ^ n) atTop (𝓝 r) := by
    have hc : Tendsto (fun _ : ℕ => r) atTop (𝓝 r) := tendsto_const_nhds
    have h := hc.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
    simpa only [add_zero] using h
  have hd : 2 * Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ r :=
    ge_of_tendsto hlim (Eventually.of_forall happrox)
  apply (arvesonDistanceFormula_iff_reverse_bound M T).mpr
  calc
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hd
    _ = b := ENNReal.ofReal_toReal hb

end KadisonSimilarity

end

end OAI
