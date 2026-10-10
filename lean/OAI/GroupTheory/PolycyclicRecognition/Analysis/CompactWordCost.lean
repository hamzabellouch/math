import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedWordBound
import Mathlib.Geometry.Group.WordMetric
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-! # Weighted costs attached to a compact generating neighborhood

Inside the generating neighborhood use the original metric; outside it use
word length. This preserves the local topology while controlling word length.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]

def metricGroupNorm : GroupNorm G where
  toFun g := dist 1 g
  map_one' := dist_self 1
  inv' g := by simpa [dist_comm] using (dist_mul_left g (1 : G) g⁻¹).symm
  mul_le' g h := by
    calc
      dist 1 (g * h) ≤ dist 1 g + dist g (g * h) := dist_triangle _ _ _
      _ = dist 1 g + dist 1 h := by
        congr 1
        simpa only [mul_one] using dist_mul_left g (1 : G) h
  eq_one_of_map_eq_zero' g h := (dist_eq_zero.mp h).symm

variable (K : Set G) (hK : Subgroup.closure K = ⊤)

def compactWordGenerators : Group.Generators G K := Group.Generators.ofSet hK

def compactWordLength (g : G) : ℕ := (compactWordGenerators K hK).wordLength g

omit [MetricSpace G] [IsIsometricSMul G G] in
theorem compactWordLength_le_one (g : G) (hg : g ∈ K) : compactWordLength K hK g ≤ 1 := by
  have h := (compactWordGenerators K hK).wordLength_wordProd_le [(⟨g, hg⟩, true)]
  simpa [compactWordLength, compactWordGenerators] using h

omit [MetricSpace G] [IsIsometricSMul G G] in
@[simp] theorem compactWordLength_one : compactWordLength K hK 1 = 0 := by
  simp [compactWordLength]

omit [MetricSpace G] [IsIsometricSMul G G] in
@[simp] theorem compactWordLength_inv (g : G) :
    compactWordLength K hK g⁻¹ = compactWordLength K hK g := by
  simp [compactWordLength]

def compactWordCost (g : G) : ℝ≥0 := by
  classical
  exact if g ∈ K then nndist 1 g else compactWordLength K hK g

omit [IsIsometricSMul G G] in
theorem compactWordCost_mem (g : G) (hg : g ∈ K) :
    compactWordCost K hK g = nndist 1 g := by simp [compactWordCost, hg]

omit [IsIsometricSMul G G] in
theorem wordLength_le_cost (g : G) :
    (compactWordLength K hK g : ℝ) ≤ max 1 (compactWordCost K hK g : ℝ) := by
  classical
  by_cases hg : g ∈ K
  · have h : (compactWordLength K hK g : ℝ) ≤ 1 := by
      exact_mod_cast compactWordLength_le_one K hK g hg
    exact h.trans (le_max_left _ _)
  · simp only [compactWordCost, ite_eq_right hg, NNReal.coe_natCast]
    exact le_max_right _ _

variable (hbounded : ∀ x y : G, dist x y ≤ 1)

include hbounded in
omit [IsIsometricSMul G G] in
theorem metric_le_compactWordCost (g : G) : dist 1 g ≤ compactWordCost K hK g := by
  classical
  by_cases hg : g ∈ K
  · simp [compactWordCost, hg]
  · by_cases hgone : g = 1
    · simp [hgone, compactWordCost]
    · have hw : 1 ≤ compactWordLength K hK g := Nat.one_le_iff_ne_zero.mpr (by
        intro hz
        exact hgone ((compactWordGenerators K hK).wordLength_eq_zero_iff.mp hz))
      simpa [compactWordCost, hg] using
        (hbounded 1 g).trans (show (1 : ℝ) ≤ compactWordLength K hK g by exact_mod_cast hw)

theorem compactWordCost_inv (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K) (g : G) :
    compactWordCost K hK g⁻¹ = compactWordCost K hK g := by
  classical
  simp only [compactWordCost, hsymm, compactWordLength_inv]
  congr 1
  apply NNReal.eq
  exact (metricGroupNorm (G := G)).inv' g

def compactWeightedNorm (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K) : GroupNorm G :=
  weightedWordGroupNorm (compactWordCost K hK) (compactWordCost_inv K hK hsymm)
    metricGroupNorm (metric_le_compactWordCost K hK hbounded)

theorem wordLength_le_weightedNorm_add
    (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hball : ∀ g : G, dist 1 g ≤ δ → g ∈ K) (g : G) :
    (compactWordLength K hK g : ℝ) ≤
      (4 / δ) * compactWeightedNorm K hK hbounded hsymm g + (4 / δ) + 1 := by
  obtain ⟨l, hl, hcost⟩ := exists_productCost_lt (compactWordCost K hK) g 1 (by norm_num)
  have hbound := seminorm_product_cost_bound
    (metricGroupNorm (G := G)).toGroupSeminorm
    (compactWordGenerators K hK).groupNorm.toGroupSeminorm (compactWordCost K hK) hδ hδ1
    (metric_le_compactWordCost K hK hbounded)
    (fun x hx => by
      change (compactWordLength K hK x : ℝ) ≤ 1
      exact_mod_cast compactWordLength_le_one K hK x (hball x hx))
    (wordLength_le_cost K hK) l
  change (compactWordLength K hK l.prod : ℝ) ≤ _ at hbound
  rw [hl] at hbound
  have hcost' : (productCost (compactWordCost K hK) l : ℝ) <
      compactWeightedNorm K hK hbounded hsymm g + 1 := by exact_mod_cast hcost
  nlinarith [div_pos (show (0 : ℝ) < 4 by norm_num) hδ]

end PolycyclicRecognition

end

end OAI
