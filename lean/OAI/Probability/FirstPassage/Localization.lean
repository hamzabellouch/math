import OAI.Probability.FirstPassage.UniformShape
import OAI.Probability.FirstPassage.Translation
import Mathlib.Topology.Order.Compact

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

theorem timeConstantNorm_continuous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    Continuous μ := by
  obtain ⟨B, hB, hb⟩ := timeConstantNorm_lipschitz_bound μ hμ
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε/B, div_pos hε hB, ?_⟩
  intro w hw
  have hd : ‖w-v‖ < ε/B := hw
  have he := (lt_div_iff₀ hB).mp hd
  have hl := hb w v
  change |μ w-μ v| < ε
  nlinarith

theorem timeConstantNorm_lower_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∃ α : ℝ, 0 < α ∧ ∀ v, α * ‖v‖ ≤ μ v := by
  have hs : (Metric.sphere (0 : Plane) 1).Nonempty := by
    refine ⟨PiLp.single 2 0 1, ?_⟩
    simp
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : Plane) 1).exists_isMinOn hs
    (timeConstantNorm_continuous μ hμ).continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa using hv
  have hvne : v ≠ 0 := by intro he; simp [he] at hvnorm
  have hpos : 0 < μ v := lt_of_le_of_ne (hμ.nonneg v) (by
    intro he; exact hvne ((hμ.zero_iff v).mp he.symm))
  refine ⟨μ v,hpos,?_⟩
  intro w
  by_cases hw : w = 0
  · simp [hw, (hμ.zero_iff 0).mpr rfl]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hunit : (1/‖w‖) • w ∈ Metric.sphere (0 : Plane) 1 := by
    simp [norm_smul, hn.ne']
  have hle : μ v ≤ μ ((1/‖w‖) • w) := hmin hunit
  rw [hμ.homogeneous, abs_of_pos (one_div_pos.mpr hn)] at hle
  have ht := mul_le_mul_of_nonneg_right hle hn.le
  simpa only [one_div, mul_assoc, mul_comm, mul_left_comm,
    inv_mul_cancel₀ hn.ne', mul_inv_cancel₀ hn.ne', one_mul, mul_one] using ht

theorem pathCost_take_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (i : ℕ) :
    pathCost w p (ds.take i) ≤ pathCost w p ds := by
  have he := pathCost_append w p (ds.take i) (ds.drop i)
  rw [List.take_append_drop] at he
  have hn := pathCost_nonneg hw (p+displacement (ds.take i)) (ds.drop i)
  linarith

def PathIn (p : Vertex) (ds : List Step) (S : Set Vertex) : Prop :=
  ∀ i ≤ ds.length, p+displacement (ds.take i) ∈ S

theorem path_confined_of_escape (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (R a : ℝ)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hcost : pathCost w p ds < a) :
    PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  intro i _
  change ‖latticeEmbed (p+displacement (ds.take i)-p)‖ < R
  by_contra hn
  have he := hescape (p+displacement (ds.take i)) (le_of_not_gt hn)
  have hp := passageTime_le_cost w hw p (p+displacement (ds.take i)) (ds.take i) rfl
  have ht := pathCost_take_le w hw p ds i
  linarith

theorem exists_confined_near_optimal (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R a ε : ℝ) (hε : 0 < ε)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hshort : passageTime w p q + ε ≤ a) :
    ∃ ds, p+displacement ds=q ∧ pathCost w p ds < passageTime w p q+ε ∧
      PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  exact ⟨ds,hend,hcost,path_confined_of_escape w hw p ds R a hescape (hcost.trans_le hshort)⟩

theorem UniformShape.eventually_escape (w : Edge → ℝ) (μ : Plane → ℝ)
    (hu : UniformShape w μ) (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ)
    (hlower : ∀ v, α*‖v‖ ≤ μ v) :
    ∀ᶠ s : ℝ in atTop, ∀ z : Vertex, δ*s/3 ≤ ‖latticeEmbed z‖ →
      α*δ*s/6 ≤ passageTime w 0 z := by
  obtain ⟨R,hR,hr⟩ := hu (α/2) (by linarith)
  filter_upwards [eventually_ge_atTop (3*R/δ)] with s hs
  intro z hz
  have hRz : R ≤ ‖latticeEmbed z‖ := by
    have ht := (div_le_iff₀ hδ).mp hs
    nlinarith
  have he := (abs_le.mp (hr z hRz)).1
  have hl := hlower (latticeEmbed z)
  have ht := mul_le_mul_of_nonneg_left hz hα.le
  nlinarith

end PlanarFPP

end OAI
