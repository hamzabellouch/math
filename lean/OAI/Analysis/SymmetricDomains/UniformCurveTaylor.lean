import Mathlib
import OAI.Analysis.SymmetricDomains.CurveUniformConsistency

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

namespace Biholomorph
open Set Filter Topology Metric MeasureTheory
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem productCurve_uniform_consistency (hbd : Bornology.IsBounded U)
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t)
    (K : Set (Affine n)) (hK : IsCompact K) (hKU : K⊆U)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ y ∈ K,
      ‖(a t*b t).ambientAut y-y-t • (infinitesimalGenerator a y+infinitesimalGenerator b y)‖ ≤ ε*|t| := by
  apply curve_uniform_consistency hU (fun t => a t*b t) (by simp [ha0,hb0])
    (fun y => infinitesimalGenerator a y+infinitesimalGenerator b y) _ _ K hK hKU hε
  · intro x hx
    exact ((infinitesimalGenerator_analytic hU a ha hbd ha0 ham x hx).continuousAt.add
      (infinitesimalGenerator_analytic hU b hb hbd hb0 hbm x hx).continuousAt).continuousWithinAt
  · exact productCurve_joint_hasStrictFDerivAt hU a b ha hb hbd ha0 ham hb0 hbm
end Biholomorph

open Set Filter Topology Metric
open scoped NNReal

theorem finite_euler_error_bound (u : ℕ → ℝ) {N : ℕ} {c b : ℝ}
    (hc : 1≤c) (hb : 0≤b) (h0 : u 0≤0)
    (hs : ∀ j<N, u (j+1)≤c*u j+b) :
    ∀ j≤N, u j ≤ (j:ℝ)*b*c^j := by
  intro j hj
  induction j with
  | zero => simpa only [Nat.cast_zero,zero_mul] using h0
  | succ j ih =>
    have hiv := ih (Nat.le_trans (Nat.le_succ j) hj)
    have hp : 1≤c^(j+1) := one_le_pow₀ hc
    have hmul : c * u j ≤ c * ((j:ℝ)*b*c^j) := mul_le_mul_of_nonneg_left hiv (le_trans zero_le_one hc)
    have hbp : b ≤ b * c^(j+1) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hb
    calc
      u (j+1) ≤ c*u j+b := hs j (by omega)
      _ ≤ c*((j:ℝ)*b*c^j)+b := add_le_add hmul le_rfl
      _ ≤ c*((j:ℝ)*b*c^j)+b*c^(j+1) := add_le_add le_rfl hbp
      _ = ((j+1:ℕ):ℝ)*b*c^(j+1) := by rw [Nat.cast_add,Nat.cast_one,pow_succ]; ring

theorem uniform_curve_taylor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α v : ℝ → E) (K : Set ℝ) (hK : IsCompact K)
    (hv : ∀ s∈K, ContinuousAt v s) (hd : ∀ s∈K, HasStrictDerivAt α (v s) s)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ h : ℝ in 𝓝 0, ∀ s∈K, ‖α (s+h)-α s-h • v s‖≤ε*|h| := by
  apply hK.eventually_forall_of_forall_eventually
  intro s hs
  have hm : ContinuousAt (fun z : ℝ × ℝ => (z.2+z.1,z.2)) (0,s) := by fun_prop
  have he := hm.tendsto.eventually (by simpa only [add_zero] using (hd s hs).isLittleO.bound (half_pos hε))
  have hv' := ((hv s hs).comp (x := ((0:ℝ),s)) continuous_snd.continuousAt)
    (ball_mem_nhds (v s) (half_pos hε))
  filter_upwards [he,hv'] with z hz hzs
  have hz' : ‖α (z.2+z.1)-α z.2-z.1 • v s‖ ≤ ε/2*|z.1| := by
    simpa using hz
  have hzv : ‖v s-v z.2‖ ≤ ε/2 := by
    have ht : dist (v z.2) (v s) < ε/2 := hzs
    simpa only [dist_eq_norm,norm_sub_rev] using ht.le
  have heq : α (z.2+z.1)-α z.2-z.1 • v z.2 =
      (α (z.2+z.1)-α z.2-z.1 • v s)+z.1 • (v s-v z.2) := by
    rw [smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖α (z.2+z.1)-α z.2-z.1 • v s‖+‖z.1 • (v s-v z.2)‖ := norm_add_le _ _
    _ ≤ ε/2*|z.1|+|z.1| *(ε/2) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add hz' (mul_le_mul_of_nonneg_left hzv (abs_nonneg _))
    _ = ε*|z.1| := by ring

end Release061

end

end OAI
