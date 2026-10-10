import OAI.Geometry.RCD.Coordinates.InitialSplittingSequence

namespace OAI

/-! # The local initial splitting input from the actual RCD constructions

This proves the specialization of Huang--Huang, Theorem 2.9(1), retained
by `LocalInitialSplittingInput`. The contradiction sequence keeps the
original measured approximations and the original physical radii.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.initialSplittingInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] : LocalInitialSplittingInput hX := by
  intro hn β hβ
  by_contra hnot
  push Not at hnot
  let ε := fun k : ℕ => (1/256:ℝ)*(1/((k:ℝ)+1))
  have hε (k : ℕ) : 0<ε k := by dsimp only [ε]; positivity
  have hεsmall (k : ℕ) : ε k≤1/256 := by
    have hh : (1:ℝ)/((k:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by
      linarith [Nat.cast_nonneg (α:=ℝ) k])
    exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤1/256)).trans_eq (mul_one _)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1/256:ℝ)
  have hbad (k : ℕ) : ∃ (p : X) (r : ℝ) (V : X → Euclidean n),
      0<r ∧ -ε k≤K*r^2 ∧
      IsMeasuredEuclideanApproximation (hausdorff n X) n p r 16 (ε k) V ∧
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        ¬FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*r) β u v := by
    obtain ⟨p,r,hr,hK,⟨V,hV⟩,hfail⟩ := hnot (ε k) (hε k)
    exact ⟨p,r,V,hr,hK,hV,hfail⟩
  choose p r V hr hK hV hfail using hbad
  have hcurv (k : ℕ) : -1≤K*(16*r k)^2 := by
    have hh := mul_le_mul_of_nonneg_left (hK k) (by norm_num : (0:ℝ)≤256)
    have he := hεsmall k
    nlinarith
  obtain ⟨α,_,hgood⟩ := hX.initial_splitting_sequence hn p r ε V hr hcurv
    (fun k => (hε k).le) (fun k => (hεsmall k).trans (by norm_num)) hεlim hV
  obtain ⟨k,u,v,huv⟩ := (hgood β hβ).exists
  exact hfail (α k) u v huv

end RegularPointCoordinates

end

end OAI
