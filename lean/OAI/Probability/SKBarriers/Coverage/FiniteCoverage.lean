import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedMoments

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def finiteMass {α : Type*} (ν : α → ℝ) (S : Finset α) : ℝ := ∑ x ∈ S, ν x

def conditionalWeights {α : Type*} [DecidableEq α] (ν : α → ℝ)
    (S : Finset α) (x : α) : ℝ := if x ∈ S then ν x/finiteMass ν S else 0

theorem finiteMass_nonneg {α : Type*} (ν : α → ℝ) (hν : ∀ x, 0 ≤ ν x) (S : Finset α) :
    0 ≤ finiteMass ν S := Finset.sum_nonneg (fun x _ => hν x)

theorem finiteMass_mono {α : Type*} (ν : α → ℝ) (hν : ∀ x, 0 ≤ ν x)
    {S T : Finset α} (hST : S ⊆ T) : finiteMass ν S ≤ finiteMass ν T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST (fun x _ _ => hν x)

theorem conditionalWeights_nonneg {α : Type*} [DecidableEq α] (ν : α → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (S : Finset α) (x : α) : 0 ≤ conditionalWeights ν S x := by
  unfold conditionalWeights
  split_ifs
  · exact div_nonneg (hν x) (finiteMass_nonneg ν hν S)
  · rfl

theorem conditionalWeights_sum {α : Type*} [Fintype α] [DecidableEq α]
    (ν : α → ℝ) (S : Finset α) (hS : 0 < finiteMass ν S) :
    ∑ x, conditionalWeights ν S x = 1 := by
  unfold conditionalWeights
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,← Finset.sum_div]
  exact div_self hS.ne'

def finiteOverlapMass {n : ℕ} (ν : Config n → ℝ) (S : Finset (Config n)) (q : ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, if q ≤ |overlap x y| then ν x*ν y else 0

theorem weightedOverlapMass_conditional {n : ℕ} (ν : Config n → ℝ)
    (S : Finset (Config n)) (q : ℝ) :
    weightedOverlapMass (conditionalWeights ν S) q =
      finiteOverlapMass ν S q/(finiteMass ν S)^2 := by
  unfold weightedOverlapMass conditionalWeights finiteOverlapMass
  rw [Finset.sum_div]
  have H (x : Config n) :
      (∑ y : Config n, if q ≤ |overlap x y| then
        (if x ∈ S then ν x/finiteMass ν S else 0)*
        (if y ∈ S then ν y/finiteMass ν S else 0) else 0) =
      if x ∈ S then (∑ y ∈ S, if q ≤ |overlap x y| then ν x*ν y else 0)/
        (finiteMass ν S)^2 else 0 := by
    by_cases hx : x ∈ S
    · rw [ite_eq_left hx,ite_eq_left hx,Finset.sum_div]
      calc
        _ = ∑ y : Config n, if y ∈ S then
            (if q ≤ |overlap x y| then ν x*ν y else 0)/(finiteMass ν S)^2 else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          split_ifs <;> ring
        _ = _ := by
          rw [← Finset.sum_filter]
          simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    · simp [hx]
  simp_rw [H]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem finiteOverlapMass_eq_rows {n : ℕ} (ν : Config n → ℝ)
    (S : Finset (Config n)) (q : ℝ) :
    finiteOverlapMass ν S q =
      ∑ x ∈ S, ν x*finiteMass ν (S.filter (fun y => q ≤ |overlap x y|)) := by
  unfold finiteOverlapMass finiteMass
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum,Finset.sum_filter]

theorem finite_coverage_of_pair_bound {n : ℕ} (ν : Config n → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {a b q : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hpair : ∀ S : Finset (Config n), a ≤ finiteMass ν S →
      b ≤ weightedOverlapMass (conditionalWeights ν S) q) :
    ∀ S : Finset (Config n),
      finiteMass ν (S.filter (fun x =>
        finiteMass ν (S.filter (fun y => q ≤ |overlap x y|)) < a*b)) < a := by
  intro S
  let B := S.filter (fun x => finiteMass ν (S.filter (fun y => q ≤ |overlap x y|)) < a*b)
  change finiteMass ν B < a
  by_contra h
  have hB : a ≤ finiteMass ν B := not_lt.mp h
  have hBpos : 0 < finiteMass ν B := ha.trans_le hB
  have hlow := hpair B hB
  rw [weightedOverlapMass_conditional] at hlow
  have hraw : b*(finiteMass ν B)^2 ≤ finiteOverlapMass ν B q :=
    (le_div_iff₀ (sq_pos_of_pos hBpos)).mp hlow
  have hrow (x : Config n) (hx : x ∈ B) :
      finiteMass ν (B.filter (fun y => q ≤ |overlap x y|)) < a*b := by
    have hSx := (Finset.mem_filter.mp hx).2
    apply lt_of_le_of_lt _ hSx
    exact finiteMass_mono ν hν (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
  have hstrict : finiteOverlapMass ν B q < a*b*finiteMass ν B := by
    rw [finiteOverlapMass_eq_rows]
    unfold finiteMass
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro x hx
      simpa only [finiteMass,mul_comm] using mul_le_mul_of_nonneg_left (hrow x hx).le (hν x)
    · obtain ⟨x,hx,hxpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => hν x)).mp hBpos
      exact ⟨x,hx,by simpa only [finiteMass,mul_comm] using mul_lt_mul_of_pos_left (hrow x hx) hxpos⟩
  have hcompare := mul_le_mul_of_nonneg_left hB
    (mul_nonneg hb hBpos.le)
  nlinarith
end SK.Analytic

end
end

end

end OAI
