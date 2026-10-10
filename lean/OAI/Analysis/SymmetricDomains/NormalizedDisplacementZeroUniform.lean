import Mathlib
import OAI.Analysis.SymmetricDomains.HolomorphicNearIdLower

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
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma iterateAverage_sub_id_bound_finite {f : E → E} {T : Set E} {ε : ℝ}
    (N : ℕ) (he : ∀ j≤N, ∀ x ∈ T, ‖f^[j] x-x‖ ≤ ε) {x : E} (hx : x ∈ T) :
    ‖iterateAverage f N x-x‖ ≤ ε := by
  have hn : (N+1 : ℝ) ≠ 0 := by positivity
  have hnC : (N+1 : ℂ) ≠ 0 := by exact_mod_cast hn
  have heq : iterateAverage f N x-x =
      (N+1 : ℂ)⁻¹ • ∑ j ∈ Finset.range (N+1), (f^[j] x-x) := by
    rw [Finset.sum_sub_distrib,smul_sub]
    simp only [Finset.sum_const,Finset.card_range,← Nat.cast_smul_eq_nsmul ℂ,
      Nat.cast_add,Nat.cast_one,smul_smul,inv_mul_cancel₀ hnC,one_smul,iterateAverage]
  rw [heq,norm_smul,norm_inv]
  rw [show (N : ℂ)+1 = ((N+1 : ℕ) : ℂ) by push_cast; rfl,Complex.norm_natCast]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    ((N : ℝ)+1)⁻¹ * ‖∑ j ∈ Finset.range (N+1), (f^[j] x-x)‖ ≤
        ((N : ℝ)+1)⁻¹ * ∑ j ∈ Finset.range (N+1), ‖f^[j] x-x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((N : ℝ)+1)⁻¹ * ∑ _j ∈ Finset.range (N+1), ε := by
      gcongr with j hj
      exact he j (by have := Finset.mem_range.mp hj; omega) x hx
    _ = ε := by simp [hn]

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem displacement_set_mem_nhds_one [LocallyCompactSpace U]
    (K : Set (Affine n)) (hK : IsCompact K) (hKU : K⊆U) {ε : ℝ} (hε : 0<ε) :
    {a : Biholomorph U U | ∀ x∈K, ‖a.ambientAut x-x‖<ε}∈𝓝 1 := by
  have hconv := ambientAut_tendstoLocallyUniformly
    (show Tendsto (id : Biholomorph U U → Biholomorph U U) (𝓝 1) (𝓝 1) from tendsto_id)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hconv.mono hKU)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with a ha
  intro x hx
  simpa only [id_eq,ambientAut_apply 1 ⟨x,hKU hx⟩,one_apply,dist_eq_norm,norm_sub_rev] using ha x hx

theorem normalized_displacement_zero_of_uniform_small_powers
    (hU : IsOpen U) [LocallyCompactSpace U]
    {ι : Type*} (l : Filter ι) (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0<h i) (N : ι → ℕ)
    (hNH : ∀ᶠ i in l, 1≤((N i+1:ℕ):ℝ)*h i)
    (hpow : ∀ W : Set (Biholomorph U U), W∈𝓝 1 →
      ∀ᶠ i in l, ∀ j≤N i+1, (q i)^j∈W) :
    TendstoLocallyUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x))
      (fun _ => 0) l U := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro p hpU
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hpU)
  refine ⟨ball p (r/8),mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p (by positivity)),?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let d : ℝ := min (r/16) (ε/4)
  have hd : 0<d := lt_min (by positivity) (by positivity)
  let W : Set (Biholomorph U U) := {a | ∀ x∈closedBall p r, ‖a.ambientAut x-x‖<d}
  have hW : W∈𝓝 1 := displacement_set_mem_nhds_one _ (isCompact_closedBall _ _) hrU hd
  filter_upwards [hNH,hpow W hW] with i hi hpi
  intro x hx
  have hxR : x∈closedBall p r := ball_subset_closedBall (ball_subset_ball (by linarith) hx)
  have hclose (j : ℕ) (hj : j≤N i+1) (z : Affine n) (hz : z∈closedBall p r) :
      ‖((q i).ambientAut^[j]) z-z‖<d := by
    have hv := hpi j hj z hz
    simpa only [ambientAut_iterate (p := ⟨z,hrU hz⟩),ambientAut_apply (p := ⟨z,hrU hz⟩)] using hv
  let F : Affine n → Affine n := iterateAverage (q i).ambientAut (N i)
  have hm : MapsTo (q i).ambientAut U U := fun z hz => by
    rw [ambientAut_apply (q i) ⟨z,hz⟩]
    exact ((q i).toHomeomorph ⟨z,hz⟩).property
  have hFd : DifferentiableOn ℂ F (ball p r) :=
    (iterateAverage_analytic ((q i).ambientAut_analytic hU) hm (N i)).differentiableOn.mono (ball_subset_closedBall.trans hrU)
  have hFb (z : Affine n) (hz : z∈ball p r) : ‖F z-z‖≤r/16 := by
    have he : ∀ j≤N i, ∀ y∈ball p r, ‖((q i).ambientAut^[j]) y-y‖≤d := by
      intro j hj y hy
      exact (hclose j (by omega) y (ball_subset_closedBall hy)).le
    exact (iterateAverage_sub_id_bound_finite (N i) he hz).trans (min_le_left _ _)
  have hqx : (q i).ambientAut x∈ball p (r/4) := by
    have hh := hclose 1 (by omega) x hxR
    simp only [Function.iterate_one] at hh
    have hb : d≤r/16 := min_le_left _ _
    exact (dist_triangle ((q i).ambientAut x) x p).trans_lt (by rw [dist_eq_norm]; linarith [mem_ball.mp hx])
  have hl := holomorphic_near_id_lower_dist hr hFd hFb x
    (ball_subset_ball (by linarith) hx) ((q i).ambientAut x) hqx
  have hmean : dist (F x) (F ((q i).ambientAut x)) =
      (((N i+1:ℕ):ℝ))⁻¹ * ‖((q i).ambientAut^[N i+1]) x-x‖ := by
    rw [dist_eq_norm,norm_sub_rev,iterateAverage_coboundary]
    rw [norm_smul,norm_inv]
    congr 1
    rw [show (N i:ℂ)+1=((N i+1:ℕ):ℂ) by push_cast; rfl,Complex.norm_natCast]
  rw [hmean,dist_eq_norm,norm_sub_rev] at hl
  have hhclose : ‖((q i).ambientAut^[N i+1]) x-x‖<ε/4 := (hclose _ le_rfl x hxR).trans_le (min_le_right _ _)
  have he : ((h i)⁻¹ * (((N i+1:ℕ):ℝ))⁻¹)≤1 := by
    rw [← mul_inv_rev]
    exact inv_le_one_of_one_le₀ hi
  rw [dist_eq_norm,zero_sub,norm_neg,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hp i)]
  calc
    _ ≤ (h i)⁻¹*(2*((((N i+1:ℕ):ℝ))⁻¹*‖((q i).ambientAut^[N i+1]) x-x‖)) :=
      mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr (hp i).le)
    _ = 2*((h i)⁻¹*(((N i+1:ℕ):ℝ))⁻¹)*‖((q i).ambientAut^[N i+1]) x-x‖ := by ring
    _ ≤ 2*‖((q i).ambientAut^[N i+1]) x-x‖ := by
      nlinarith [norm_nonneg (((q i).ambientAut^[N i+1]) x-x)]
    _ < ε := by linarith
end Biholomorph
end Release061

end

end OAI
