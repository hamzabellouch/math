import OAI.Probability.ContinuumTransition.InitialTriple

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def geometricBudget (n : ℕ) : ℝ := (1/2)^n
def groupRadius (τ : ℝ) (n : ℕ) : ℝ := τ*(1-geometricBudget (n+1))
def locationRadius (n : ℕ) : ℝ := 1/8-geometricBudget n/16

lemma geometricBudget_pos (n : ℕ) : 0 < geometricBudget n := pow_pos (by norm_num) _
lemma geometricBudget_succ (n : ℕ) : geometricBudget (n+1) = geometricBudget n/2 := by
  unfold geometricBudget
  rw [pow_succ]
  ring
lemma groupRadius_le {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) : groupRadius τ n ≤ τ := by
  dsimp [groupRadius]
  nlinarith only [mul_nonneg hτ (geometricBudget_pos (n+1)).le]
lemma groupRadius_succ (τ : ℝ) (n : ℕ) :
    groupRadius τ (n+1) = groupRadius τ n+τ*geometricBudget n/4 := by
  simp only [groupRadius,geometricBudget_succ]
  ring
lemma locationRadius_lt (n : ℕ) : locationRadius n < 1/8 := by
  dsimp [locationRadius]
  linarith only [geometricBudget_pos n]
lemma locationRadius_succ (n : ℕ) : locationRadius (n+1)=locationRadius n+geometricBudget n/32 := by
  simp only [locationRadius,geometricBudget_succ]
  ring

structure ConstructionStage (t p τ : ℝ) (n : ℕ) where
  σ : ℕ → ℝ
  R : ℕ → ℝ
  a : ℝ
  x : Parameter
  σ_nonneg : ∀ k, 0 ≤ σ k
  R_one : ∀ k, 1 ≤ R k
  σ_summable : Summable σ
  a_pos : 0 < a
  mass : a+∑' k, σ k ≤ firstMass p+1-geometricBudget n
  referenceBounded : ∃ B ≥ 0, ∀ k, σ k ≠ 0 → R k ≤ B
  location : dist x initialPoint < locationRadius n
  triple : HasVertexTriple (meanField (physicalPressure (physicalProfile t σ R) t) a) x p (groupRadius τ n)

def ConstructionStage.pressure {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) : Parameter → ℝ :=
  physicalPressure (physicalProfile t s.σ s.R) t

def ConstructionStage.ideal {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) : Parameter → ℝ :=
  meanField s.pressure s.a

lemma ConstructionStage.mass_total {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    s.a+∑' k, s.σ k ≤ firstMass p+1 :=
  s.mass.trans (sub_le_self _ (geometricBudget_pos n).le)

lemma ConstructionStage.base_mass {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    ∑' k, s.σ k ≤ firstMass p+1 := by
  linarith only [s.mass_total,s.a_pos]

lemma ConstructionStage.a_le {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    s.a ≤ firstMass p+1 := by
  have hh : 0 ≤ ∑' k, s.σ k := tsum_nonneg s.σ_nonneg
  linarith only [s.mass_total,hh]

lemma ConstructionStage.x_near {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    s.x ∈ ball initialPoint (1/8) := s.location.trans (locationRadius_lt n)

lemma ConstructionStage.near_moderate {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    ball s.x (1/8) ⊆ closedBall initialPoint (1/4) := by
  intro y hy
  exact le_of_lt (calc
    dist y initialPoint ≤ dist y s.x+dist s.x initialPoint := dist_triangle _ _ _
    _ < 1/4 := by have hh := s.x_near; change dist s.x initialPoint < 1/8 at hh; change dist y s.x < 1/8 at hy; linarith)

lemma ConstructionStage.convex {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n)
    (hcap : ConstructionCap t (firstMass p+1)) : ConvexOn ℝ pressureDomain s.ideal := by
  exact meanField_convex (physical_convex_bounded hcap.t_large s.σ_nonneg s.R_one s.σ_summable (hcap.weak s.base_mass))
    (physical_meanField_bounded hcap.t_large s.a_pos s.σ_nonneg s.R_one s.σ_summable
      (hcap.weak s.base_mass) (hcap.lt_gap s.a_le)).1

end ContinuumTemperature
end
end

end OAI
