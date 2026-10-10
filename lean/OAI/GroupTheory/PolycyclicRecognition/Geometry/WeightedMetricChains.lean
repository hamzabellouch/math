import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedChainMetric

namespace OAI

/-! # Explicit bounded-step chains for the weighted metric -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal Pointwise

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  (K : Set G) (hK : Subgroup.closure K = ⊤)
  (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K)
  (hbounded : ∀ x y : G, dist x y ≤ 1)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (hball : ∀ g : G, dist 1 g ≤ δ → g ∈ K)

def weightedMetricChains :
    letI := weightedGroupMetric K hK hsymm hbounded δ hδ hball
    LinearMetricChains G := by
  let n₀ := compactWeightedNorm K hK hbounded hsymm
  let P := compactWordGenerators K hK
  have hshort (g : G) (hg : g ∈ K) : n₀ g ≤ 1 := by
    have h := weightedWordNorm_le (compactWordCost K hK) g
    rw [compactWordCost_mem K hK g hg] at h
    have hreal : n₀ g ≤ dist 1 g := by exact_mod_cast h
    exact hreal.trans (hbounded 1 g)
  have hword (g : G) : (P.wordLength g : ℝ) ≤ (4 / δ) * n₀ g + (4 / δ) + 1 :=
    wordLength_le_weightedNorm_add K hK hbounded hsymm hδ hδ1 hball g
  let := weightedGroupMetric K hK hsymm hbounded δ hδ hball
  refine {
    step := 1
    step_pos := by norm_num
    slope := 4 / δ
    slope_nonneg := div_nonneg (by norm_num) hδ.le
    error := (4 / δ) + 1
    error_nonneg := by positivity
    chain := ?_ }
  intro x y
  obtain ⟨l, hl, he⟩ := P.exists_isGeodesic (x⁻¹ * y)
  refine ⟨l.length, fun i => x * P.wordProd (l.take i), by simp, by simp [he], ?_, ?_⟩
  · change (l.length : ℝ) ≤ (4 / δ) * n₀ (x⁻¹ * y) + ((4 / δ) + 1)
    have hh : l.length = P.wordLength (x⁻¹ * y) := by rw [← he, hl.eq]
    rw [hh]
    simpa only [add_assoc] using hword (x⁻¹ * y)
  · intro i hi
    change n₀ ((x * P.wordProd (l.take i))⁻¹ * (x * P.wordProd (l.take (i + 1)))) ≤ 1
    rw [← List.take_concat_get' l i hi, P.wordProd_append]
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    apply hshort
    simpa only [P, compactWordGenerators, List.length_singleton, pow_one] using
      generator_wordProd_mem_pow K hK hsymm [l[i]]

def weightedProperChainMetric [IsTopologicalGroup G] (hcompact : IsCompact K) :
    ProperChainMetric G where
  metric := weightedGroupMetric K hK hsymm hbounded δ hδ hball
  topology_eq := rfl
  proper := weightedGroupMetric_proper K hK hsymm hbounded δ hδ hδ1 hball hcompact
  leftInvariant := weightedGroupMetric_isometric K hK hsymm hbounded δ hδ hball
  chains := weightedMetricChains K hK hsymm hbounded δ hδ hδ1 hball

end PolycyclicRecognition

end

end OAI
