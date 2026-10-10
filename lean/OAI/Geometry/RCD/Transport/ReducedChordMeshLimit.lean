import OAI.Geometry.RCD.Transport.ReducedDistanceLimit
import OAI.Geometry.RCD.Transport.WeightedChordBins

namespace OAI

/-! # Fatou's lemma for both exact endpoint distortion weights -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem reduced_chord_mesh_limit (μ : Measure X) {K N : ℝ} (hK : K≤0) (hN : 1<N)
    (t : Time) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1)
    (L : X → ℝ) (hL : Measurable L) (hL0 : ∀ x, 0≤L x)
    (g₀ g₁ : X → ℝ≥0∞) (hg₀ : Measurable g₀) (hg₁ : Measurable g₁)
    {ε : ℕ → ℝ} (hε : ∀ m, 0<ε m) (hεt : Tendsto ε atTop (𝓝 0))
    {B : ℝ≥0∞} (hb : ∀ m,
      (∫⁻ x, sigma K N (1-(t:ℝ)) (upperLength (ε m) (L x))*g₀ x+
        sigma K N (t:ℝ) (upperLength (ε m) (L x))*g₁ x ∂μ)≤B) :
    (∫⁻ x, sigma K N (1-(t:ℝ)) (L x)*g₀ x+sigma K N (t:ℝ) (L x)*g₁ x ∂μ)≤B := by
  let F := fun m x => sigma K N (1-(t:ℝ)) (upperLength (ε m) (L x))*g₀ x+
    sigma K N (t:ℝ) (upperLength (ε m) (L x))*g₁ x
  have hw (s : ℝ) (m : ℕ) : Measurable (fun x => sigma K N s (upperLength (ε m) (L x))) :=
    (measurable_of_countable (fun i : ℕ => sigma K N s (((i:ℝ)+1)*ε m))).comp
      (hL.div_const (ε m)).nat_floor
  have hm (m) : Measurable (F m) := ((hw _ m).mul hg₀).add ((hw _ m).mul hg₁)
  have hh (s : ℝ) (hs0 : 0<s) (hs1 : s≤1) (g : X → ℝ≥0∞) (x : X) :
      Tendsto (fun m => sigma K N s (upperLength (ε m) (L x))*g x) atTop
        (𝓝 (sigma K N s (L x)*g x)) := by
    apply ENNReal.Tendsto.mul
      (sigma_nonpos_length_tendsto hK hN hs0 hs1 (hL0 x)
        (fun m => upperLength_pos (hε m)) (upperLength_tendsto hε hεt (hL0 x)))
      (Or.inl (sigma_nonpos_ne_zero hK hN hs0 (hL0 x))) tendsto_const_nhds
      (Or.inr (sigma_nonpos_ne_top hK hN (hL0 x)))
  have hl (x) : Tendsto (fun m => F m x) atTop
      (𝓝 (sigma K N (1-(t:ℝ)) (L x)*g₀ x+sigma K N (t:ℝ) (L x)*g₁ x)) :=
    (hh _ (by linarith) (by linarith) g₀ x).add (hh _ ht0 ht1.le g₁ x)
  calc
    _ = ∫⁻ x, liminf (fun m => F m x) atTop ∂μ := lintegral_congr (fun x => (hl x).liminf_eq.symm)
    _ ≤ liminf (fun m => ∫⁻ x, F m x ∂μ) atTop := lintegral_liminf_le hm
    _ ≤ liminf (fun _ : ℕ => B) atTop := Filter.liminf_le_liminf (Eventually.of_forall hb)
    _ = B := by simp

end RegularPointCoordinates

end

end OAI
