import Mathlib
import OAI.Analysis.SymmetricDomains.PowersTendstoOneVanishing

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

namespace Biholomorph
open Set Filter Topology Metric
variable {n : ℕ} {U : Set (Affine n)}

theorem powers_eventually_mem_nhds_of_vanishing_normalized_displacement
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0≤h i) (N : ι → ℕ) {T : ℝ} (hT : 0<T)
    (hNT : ∀ i, (N i:ℝ)*h i≤T) (p : U) {R : ℝ} (hR : 0<R)
    (hRU : closedBall p.val R⊆U)
    (hstep : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ y∈closedBall p.val R,
      ‖(q i).ambientAut y-y‖≤ε*h i)
    (W : Set (Biholomorph U U)) (hW : W∈𝓝 1) :
    ∀ᶠ i in l, ∀ j≤N i, (q i)^j∈W := by
  let J := {z : ι × ℕ // z.2≤N z.1}
  let π : J → ι := fun z => z.val.1
  let k : Filter J := comap π l
  have hπ : Function.Surjective π := fun i => ⟨⟨(i,0),Nat.zero_le _⟩,rfl⟩
  have : NeBot k := (inferInstance : NeBot l).comap_of_surj hπ
  have hcπ : Tendsto π k l := tendsto_comap
  have hN' (z : J) : (z.val.2:ℝ)*h (π z)≤T :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr z.property) (hp (π z))).trans (hNT (π z))
  have ht := powers_tendsto_one_of_vanishing_normalized_displacement hU hc hbd Γ hhol k
    (fun z => q (π z)) (fun z => h (π z)) (fun z => hp (π z)) (fun z => z.val.2) hT hN' p hR hRU (by
      intro ε hε
      exact hcπ.eventually (hstep ε hε))
  have he := ht.eventually hW
  obtain ⟨S,hS,hsub⟩ := mem_comap.mp he
  filter_upwards [hS] with i hi
  intro j hj
  exact hsub (show π ⟨(i,j),hj⟩∈S from hi)
end Biholomorph

open Set Filter Metric Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem holomorphic_near_id_lower_dist {g : E → E} {p : E} {R : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball p R))
    (hb : ∀ x ∈ ball p R, ‖g x-x‖ ≤ R/16) : ∀ x∈ball p (R/4), ∀ y∈ball p (R/4), dist x y≤2*dist (g x) (g y) := by
  intro x hx y hy
  let h : E → E := fun z => g z-z
  have hsub : ball x (R/2) ⊆ ball p R := by
    intro z hz
    rw [mem_ball] at *
    exact (dist_triangle z x p).trans_lt (by linarith)
  have hdiff : DifferentiableOn ℂ h (ball x (R/2)) :=
    (hg.sub differentiableOn_id).mono hsub
  have hm : MapsTo h (ball x (R/2)) (closedBall (h x) (R/8)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      have hz' := hb z (hsub hz)
      have hx' := hb x (ball_subset_ball (by linarith) hx)
      dsimp [h]
      linarith)
  have hyx : y ∈ ball x (R/2) := by
    rw [mem_ball] at *
    exact (dist_triangle y p x).trans_lt (by rw [dist_comm p x]; linarith)
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hm hyx
  have hc : (R/8)/(R/2)=(1/4 : ℝ) := by field_simp [ne_of_gt hR]; ring
  rw [hc] at hs
  have he : y-x=(g y-g x)-(h y-h x) := by dsimp [h]; abel
  have hdist : dist y x≤dist (g y) (g x)+dist (h y) (h x) := by
    rw [dist_eq_norm y x,he]
    simpa only [dist_eq_norm] using norm_sub_le (g y-g x) (h y-h x)
  rw [dist_comm y x] at hs
  rw [dist_comm y x,dist_comm (g y) (g x)] at hdist
  linarith [dist_nonneg (x := g x) (y := g y)]
end Release061

end

end OAI
