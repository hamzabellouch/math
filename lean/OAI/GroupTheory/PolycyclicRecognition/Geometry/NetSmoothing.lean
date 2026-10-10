import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteSupportInterpolation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitNetPartition
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LocalLipschitzMinimizing

namespace OAI

/-! # Uniformly close Lipschitz interpolation of coarse maps -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal BigOperators

variable {X Y : Type*} [Group X] [MetricSpace X] [ProperSpace X]
  [IsIsometricSMul X X] [MetricSpace Y]
  {V : Set X} (hV : V.Pairwise (fun x y => 1 < dist x y)) [LinearOrder V]

def netSmoothedMap (c : ControlledContraction Y) (p₀ : Y) (f : X → Y) (x : X) : Y :=
  finiteSupportCenter c p₀ (fun v : V => f v) (unitNetPartition hV x)

omit [Group X] [IsIsometricSMul X X] in
theorem net_union_support_diameter {x y : X} (hxy : dist x y ≤ 1)
    {v w : V}
    (hv : v ∈ (unitNetMass hV x).support ∪ (unitNetMass hV y).support)
    (hw : w ∈ (unitNetMass hV x).support ∪ (unitNetMass hV y).support) :
    dist (v : X) (w : X) ≤ 6 := by
  have hb (u : V) (hu : u ∈ (unitNetMass hV x).support ∪ (unitNetMass hV y).support) :
      dist x (u : X) ≤ 3 := by
    rcases Finset.mem_union.mp hu with hu | hu
    · have h := (mem_support_unitNetMass_iff hV x u).mp hu
      linarith
    · have h := (mem_support_unitNetMass_iff hV y u).mp hu
      have ht := dist_triangle x y (u : X)
      linarith
  have hv' := hb v hv
  have hw' := hb w hw
  have ht := dist_triangle (v : X) x (w : X)
  rw [dist_comm (v : X) x] at ht
  linarith

/-- The same constants work for every map with the prescribed coarse
upper bound. All interpolation data are constructed from the fixed net. -/
theorem exists_uniform_net_smoothing (c : ControlledContraction Y) (p₀ : Y)
    (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1)
    (hpath : ∀ g : X, ∃ γ : ℝ → X, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ L : ℝ≥0, ∃ E : ℝ, 0 ≤ E ∧ ∀ f : X → Y,
      (∀ x y, dist (f x) (f y) ≤ K * dist x y + C) →
      LipschitzWith L (netSmoothedMap hV c p₀ f) ∧
        ∀ x, dist (netSmoothedMap hV c p₀ f x) (f x) ≤ E := by
  obtain ⟨M, hM⟩ := exists_uniform_unit_net_card (G := X) 2
  have hMv := hM V hV
  let D := 6 * K + C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨R, hR, hrad⟩ := exists_interpolation_radius (I := V) c hD (2 * M)
  obtain ⟨Q, hQ, hweight⟩ := exists_interpolation_weight_control (I := V) c hD (2 * M)
  let L : ℝ≥0 := ⟨Q * (4 * (M : ℝ)), mul_nonneg hQ (by positivity)⟩
  refine ⟨L, R, hR, ?_⟩
  intro f hf
  constructor
  · apply lipschitzWith_of_unit_local_bound hpath
    intro x y hxy
    let s := (unitNetMass hV x).support ∪ (unitNetMass hV y).support
    have hs : s.card ≤ 2 * M := by
      have h := (Finset.card_union_le (unitNetMass hV x).support (unitNetMass hV y).support).trans
        (Nat.add_le_add (unitNetMass_support_card_le hV hMv x) (unitNetMass_support_card_le hV hMv y))
      simpa only [two_mul] using h
    have hx : (unitNetMass hV x).support ⊆ s := Finset.subset_union_left
    have hy : (unitNetMass hV y).support ⊆ s := Finset.subset_union_right
    have hpx : (unitNetPartition hV x).support ⊆ s := Finset.Subset.trans Finsupp.support_smul hx
    have hpy : (unitNetPartition hV y).support ⊆ s := Finset.Subset.trans Finsupp.support_smul hy
    have hd : ∀ v ∈ s, ∀ w ∈ s, dist (f (v : X)) (f (w : X)) ≤ D := by
      intro v hv w hw
      exact (hf v w).trans (by dsimp [D]; nlinarith only [net_union_support_diameter hV hxy hv hw, hK])
    have h := finiteSupportCenter_dist_le c hweight p₀ (fun v : V => f v)
      (unitNetPartition hV x) (unitNetPartition hV y) s hpx hpy hs
      (unitNetPartition_nonneg hV x) (unitNetPartition_nonneg hV y)
      (unitNetPartition_total hV hcover x) (unitNetPartition_total hV hcover y) hd
    have hv := unitNetPartition_variation_on_finset hV hcover x y s hx hy
    have hsr : (s.card : ℝ) ≤ 2 * M := by exact_mod_cast hs
    change dist (finiteSupportCenter c p₀ _ _) (finiteSupportCenter c p₀ _ _) ≤ _
    apply h.trans
    have hv' : (∑ v ∈ s, |unitNetPartition hV x v - unitNetPartition hV y v|) ≤
        4 * (M : ℝ) * dist x y := by
      nlinarith only [hv, mul_le_mul_of_nonneg_right hsr (dist_nonneg (x := x) (y := y))]
    exact (mul_le_mul_of_nonneg_left hv' hQ).trans_eq (by change _ = (Q * (4 * (M : ℝ))) * dist x y; ring)
  · intro x
    have hs : (unitNetPartition hV x).support ⊆ (unitNetMass hV x).support := Finsupp.support_smul
    have hcard : (unitNetPartition hV x).support.card ≤ 2 * M :=
      (Finset.card_le_card hs).trans ((unitNetMass_support_card_le hV hMv x).trans (by omega))
    have hd : ∀ v ∈ (unitNetPartition hV x).support,
        ∀ w ∈ (unitNetPartition hV x).support, dist (f (v : X)) (f (w : X)) ≤ D := by
      intro v hv w hw
      have h := net_union_support_diameter hV (x := x) (y := x) (by simp)
        (Finset.mem_union_left _ (hs hv)) (Finset.mem_union_left _ (hs hw))
      exact (hf v w).trans (by dsimp [D]; nlinarith only [h, hK])
    apply finiteSupportCenter_dist_anchor_le c hrad p₀ (fun v : V => f v)
      (unitNetPartition hV x) (unitNetPartition_nonneg hV x)
      (unitNetPartition_total hV hcover x) hcard hd (f x)
    intro v hv
    have h := ((mem_support_unitNetMass_iff hV x v).mp (hs hv)).le
    rw [dist_comm x (v : X)] at h
    exact (hf v x).trans (by dsimp [D]; nlinarith only [h, hK])

end PolycyclicRecognition

end

end OAI
