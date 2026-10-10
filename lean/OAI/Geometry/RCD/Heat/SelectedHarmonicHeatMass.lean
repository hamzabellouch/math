import OAI.Geometry.RCD.Heat.HeatHarmonicMassControl
import OAI.Geometry.RCD.Heat.HeatMassDiagonalSelection

namespace OAI

/-! # Actual heat times with simultaneous value and local Bochner mass control -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem selected_harmonic_heat_mass (hK : K ≤ 0)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) {C : ℝ} (hC : 0 ≤ C)
    (χ : ∀ k, GoodLaplacianCutoff (hausdorff n X) hX.quadratic (p k) (2*r k) C)
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (d : ℕ → Lp ℝ 2 (hausdorff n X))
    (hd : ∀ k, IsWeakLaplacian (hausdorff n X) hX.quadratic (u k) (d k))
    (U : ℕ → X → ℝ) (L A : ℕ → ℝ≥0)
    (hU : ∀ k, LipschitzWith (L k) (U k)) (hUc : ∀ k, HasCompactSupport (U k))
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X] U k)
    (hA : ∀ k, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x| ≤ A k)
    (hd0 : ∀ k, d k =ᵐ[(hausdorff n X).restrict (ball (p k) (8*r k))] fun _ => 0) :
    let m := hausdorff n X
    let q := hX.quadratic
    ∃ (s : ℕ → ℝ) (hs : ∀ k, 0 < s k),
      (∀ k, s k ≤ 1) ∧ Tendsto s atTop (𝓝 0) ∧
      (let w k := heatSobolev m q (s k) (hs k) (SobolevSpace.toLp m q (u k))
       let D k := heatSobolevMap m q (s k/2) (half_pos (hs k))
         (-heatGeneratorAt m q (s k-s k/2) (SobolevSpace.toLp m q (u k)))
       Tendsto (fun k => ‖w k-u k‖/r k) atTop (𝓝 0) ∧
       Tendsto (fun k => ‖w k-u k‖/(r k*Real.sqrt (m.real (ball (p k) (8*r k))))) atTop (𝓝 0) ∧
       ∃ (G : ℕ → SobolevSpace m q) (σ : ℕ → Measure X),
         (∀ k, IsFiniteMeasure (σ k)) ∧
         (∀ k, SobolevSpace.toLp m q (G k) =ᵐ[m] localGamma m q (w k) (w k)) ∧
         (∀ k (ψ : SobolevSpace m q) (v : X → ℝ), Continuous v → HasCompactSupport v →
           tsupport v ⊆ ball (p k) (6*r k) → SobolevSpace.toLp m q ψ =ᵐ[m] v →
           (∫ x, v x ∂σ k)=-(1/2:ℝ)*energyForm m q (G k) ψ-
             weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)-
             K*weightedGamma m q v (w k) (w k)) ∧
         ∀ k, (σ k).real (closedBall (p k) (r k)) ≤
           (C/(2*r k)^2)/2*(∫ x in closedBall (p k) (4*r k), |localGamma m q (u k) (u k) x-1| ∂m)+
           (-K)*((∫ x in closedBall (p k) (4*r k), |localGamma m q (u k) (u k) x-1| ∂m)+
             m.real (closedBall (p k) (4*r k)))+
           m.real (ball (p k) (8*r k))/((r k)^2*((k:ℝ)+1))) := by
  intro m q
  let τ (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hτ (j : ℕ) : 0 < τ j := by dsimp only [τ]; positivity
  have hτ1 (j : ℕ) : τ j ≤ 1 := by
    dsimp only [τ]
    apply (div_le_one (by positivity : 0 < (j:ℝ)+1)).mpr
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hτ0 : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w k j := heatSobolev m q (τ j) (hτ j) (SobolevSpace.toLp m q (u k))
  choose G σ hσ hG hrep hmass using fun k =>
    hX.heat_harmonic_mass_control hn (p k) hK (u k) (d k) (hd k) (U k) (L k) (A k)
      (hU k) (hUc k) (hu k) (hA k) (hr k) hC (χ k)
      (show 4*r k < 8*r k by linarith [hr k]) (hd0 k) 1 τ hτ hτ1 hτ0
  let m₀ k := m.real (ball (p k) (8*r k))
  have hm (k : ℕ) : 0 < m₀ k :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (by linarith [hr k])).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  let β (k : ℕ) := min 1 (Real.sqrt (m₀ k))
  have hβ (k : ℕ) : 0 < β k := lt_min zero_lt_one (Real.sqrt_pos.mpr (hm k))
  have hval (k : ℕ) : Tendsto (fun j => ‖w k j-u k‖/β k) atTop (𝓝 0) := by
    have hh := (((heat_regularization_value_source_converges m q (u k) (d k) (hd k) τ hτ hτ0).1.sub
      (tendsto_const_nhds (x := u k))).norm).div_const (β k)
    simpa only [sub_self,norm_zero,zero_div] using hh
  obtain ⟨j,hj,hvalue,hmj⟩ := heat_mass_diagonal_selection r m₀ _ _ _ hr hm hval hmass
  let s k := τ (j k)
  have hs (k : ℕ) : 0 < s k := hτ (j k)
  have hsτ (k : ℕ) : s k ≤ τ k :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (hj k) 1)
  have hvb (k : ℕ) : ‖w k (j k)-u k‖ ≤ (r k/((k:ℝ)+1))*β k :=
    (div_le_iff₀ (hβ k)).mp (hvalue k)
  have hv₁ (k : ℕ) : ‖w k (j k)-u k‖/r k ≤ τ k := by
    apply (div_le_iff₀ (hr k)).mpr
    have hbound := mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (Real.sqrt (m₀ k)))
      (div_nonneg (hr k).le (by positivity : (0:ℝ) ≤ (k:ℝ)+1))
    calc
      ‖w k (j k)-u k‖ ≤ (r k/((k:ℝ)+1))*β k := hvb k
      _ ≤ (r k/((k:ℝ)+1))*1 := hbound
      _ = τ k*r k := by dsimp only [τ]; ring
  have hv₂ (k : ℕ) : ‖w k (j k)-u k‖/(r k*Real.sqrt (m₀ k)) ≤ τ k := by
    apply (div_le_iff₀ (mul_pos (hr k) (Real.sqrt_pos.mpr (hm k)))).mpr
    have hbound := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (Real.sqrt (m₀ k)))
      (div_nonneg (hr k).le (by positivity : (0:ℝ) ≤ (k:ℝ)+1))
    have heq : (r k/((k:ℝ)+1))*Real.sqrt (m₀ k)=τ k*(r k*Real.sqrt (m₀ k)) := by
      dsimp only [τ]
      ring
    exact (hvb k).trans (hbound.trans_eq heq)
  refine ⟨s,hs,fun k => (hsτ k).trans (hτ1 k),
    squeeze_zero (fun k => (hs k).le) hsτ hτ0,?_,?_,
    (fun k => G k (j k)),(fun k => σ k (j k)),
    (fun k => hσ k (j k)),(fun k => hG k (j k)),
    (fun k => hrep k (j k)),?_⟩
  · exact squeeze_zero (fun k => div_nonneg (norm_nonneg _) (hr k).le) hv₁ hτ0
  · exact squeeze_zero (fun k => div_nonneg (norm_nonneg _)
      (mul_pos (hr k) (Real.sqrt_pos.mpr (hm k))).le) hv₂ hτ0
  · intro k
    simpa only [one_mul] using hmj k

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
