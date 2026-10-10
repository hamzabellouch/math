import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Algebra.MulAction

namespace OAI

/-!
# Fixed vectors from small group sandwiches

These metric arguments are the part of the Mautner phenomenon needed
for the actual root-pair calculation. They apply to the continuous
isometric action on L². No ergodicity or homogeneous-orbit premise is
introduced.
-/

noncomputable section
open Filter
open scoped Topology

namespace DukePrimeDegree

variable {G Y : Type*} [Group G] [TopologicalSpace G]
  [MetricSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [IsIsometricSMul G Y]

omit [TopologicalSpace G] [ContinuousSMul G Y] in
lemma dist_sandwich_of_fixed (x : Y) (a b c : G)
    (ha : a • x = x) (hb : b • x = x) :
    dist ((a * c * b) • x) x = dist (c • x) x := by
  rw [mul_smul, mul_smul, hb]
  calc
    dist (a • (c • x)) x = dist (a • (c • x)) (a • x) := by rw [ha]
    _ = dist (c • x) x := dist_smul a _ _

/-- Large left and right factors which fix the vector may squeeze a
small middle factor to a nontrivial group limit. That limit still fixes
the vector because both outer factors act isometrically. -/
theorem fixed_of_sandwich_tendsto
    (x : Y) (a b c : ℕ → G) (g : G)
    (ha : ∀ k, a k • x = x) (hb : ∀ k, b k • x = x)
    (hc : Tendsto c atTop (𝓝 1))
    (hlim : Tendsto (fun k => a k * c k * b k) atTop (𝓝 g)) :
    g • x = x := by
  have hsmall : Tendsto (fun k => dist (c k • x) x) atTop (𝓝 0) := by
    simpa only [one_smul, dist_self] using
      (hc.smul_const x).dist (tendsto_const_nhds (x := x))
  have hdist : Tendsto (fun k => dist ((a k * c k * b k) • x) x)
      atTop (𝓝 0) := by
    exact hsmall.congr' (Eventually.of_forall fun k =>
      (dist_sandwich_of_fixed x (a k) (b k) (c k) (ha k) (hb k)).symm)
  have hvalue := (hlim.smul_const x).dist (tendsto_const_nhds (x := x))
  exact dist_eq_zero.mp (tendsto_nhds_unique hvalue hdist)

/-- The usual contraction form of Mautner: a group element contracted
to identity by elements fixing the vector also fixes the vector. -/
theorem fixed_of_conjugate_tendsto
    (x : Y) (a : ℕ → G) (g : G)
    (ha : ∀ k, a k • x = x)
    (hlim : Tendsto (fun k => a k * g * (a k)⁻¹) atTop (𝓝 1)) :
    g • x = x := by
  have hai (k : ℕ) : (a k)⁻¹ • x = x := by
    apply (MulAction.injective (a k))
    simpa only [smul_smul, mul_inv_cancel, one_smul] using (ha k).symm
  have hzero : Tendsto (fun k => dist ((a k * g * (a k)⁻¹) • x) x)
      atTop (𝓝 0) := by
    simpa only [one_smul, dist_self] using
      (hlim.smul_const x).dist (tendsto_const_nhds (x := x))
  have hconst : Tendsto (fun _ : ℕ => dist (g • x) x) atTop (𝓝 0) := by
    exact hzero.congr' (Eventually.of_forall fun k =>
      dist_sandwich_of_fixed x (a k) ((a k)⁻¹) g (ha k) (hai k))
  exact dist_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hconst)

end DukePrimeDegree

end

end OAI
