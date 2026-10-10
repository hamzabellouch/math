import OAI.Probability.ContinuumTransition.InitialUniform

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma initial_triple_of_limits {p τ γ r : ℝ} (hp : 0 < p) (hτ : 0 < τ)
    (hγ : 0 < γ) (hr : 0 < r) (hr' : r < 1/2)
    (hgeom : closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range (triangleVertex p)))
    {Q P : ℕ → Parameter → ℝ}
    (hQ : TendstoLocallyUniformlyOn Q (threeCore p) atTop pressureDomain)
    (hQc : ∀ n, ConvexOn ℝ pressureDomain (Q n))
    (hP : ∀ n, IsMeanField (Q n) (firstMass p) (P n))
    (hatt : ∀ n, ∀ y ∈ pressureDomain, ∃ d, quadraticCost (Q n) (firstMass p) y d = P n y)
    (hPt : TendstoLocallyUniformlyOn P (threeMeanField p (firstMass p)) atTop (ball initialPoint (1/2)))
    (hD : ∀ n, ∀ y ∈ ball initialPoint (1/2), ∀ w ∈ activeLifts (Q n) (firstMass p) (P n) y,
      w.2 ∈ Icc (0:ℝ) 1048576) (N : ℕ) :
    ∃ n ≥ N, ∃ x ∈ ball initialPoint r, HasVertexTriple (P n) x p (τ/2) := by
  let U := ⋃ i : Fin 3, ball (triangleVertex p i) (τ/2)
  have hAU : activeLifts (threeCore p) (firstMass p) (threeMeanField p (firstMass p)) initialPoint ⊆ U := by
    intro w hw
    obtain ⟨i,rfl⟩ := three_active_initial hp hw
    exact mem_iUnion.mpr ⟨i,mem_ball_self (by positivity)⟩
  have hball : ball initialPoint (1/2) ⊆ pressureDomain :=
    ball_subset_closedBall.trans (initial_ball_moderate.trans moderateBox_subset)
  obtain ⟨δ,hδ,hδ',M,hM⟩ := active_uniform_near hQ hQc
    ((threeCore_convex p).continuousOn isOpen_pressureDomain) hP (three_meanField (firstMass_pos hp).le)
    (show initialPoint ∈ pressureDomain by norm_num [initialPoint,pressureDomain])
    (show (0:ℝ) < 1/2 by norm_num) hball hD (isOpen_iUnion fun _ => isOpen_ball) hAU
  let s := min r (δ/2)
  have hs : 0 < s := lt_min hr (by positivity)
  have hsr : s ≤ r := min_le_left _ _
  have hsd : s < δ := (min_le_right _ _).trans_lt (by linarith)
  have hsW : closedBall initialPoint s ⊆ ball initialPoint (1/2) :=
    fun _ hx => hx.trans_lt (hsr.trans_lt hr')
  have huni := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_closedBall initialPoint s)).mp (hPt.mono hsW)
  have he : 0 < γ*s/4 := by positivity
  have happ := (Metric.tendstoUniformlyOn_iff.mp huni) (γ*s/4) he
  obtain ⟨n,hn,hN,hMn⟩ := (happ.and ((eventually_ge_atTop N).and (eventually_ge_atTop M))).exists
  have hc := meanField_convex (hQc n) (hP n)
  obtain ⟨x,hx,hgx⟩ := nearby_support_of_uniform hc hγ hs (hsW.trans hball)
    (hgeom.trans (three_support_contains_triangle hp))
    (fun y hy => by have hh := hn y hy; simpa only [Real.dist_eq,abs_sub_comm] using hh.le)
    (show 2*(γ*s/4) < γ*s by nlinarith only [mul_pos hγ hs])
  refine ⟨n,hN,x,hx.trans_le hsr,hgx,regroup_active (firstMass_pos hp) (hQc n) (hP n) (hatt n)
    (hball (hx.trans (hsr.trans_lt hr'))) ?_⟩
  intro w hw
  have hh := hM n hMn x (hx.trans hsd) hw
  obtain ⟨i,hi⟩ := mem_iUnion.mp hh
  exact mem_iUnion.mpr ⟨i,show dist w (triangleVertex p i) ≤ τ/2 from le_of_lt hi⟩

lemma physical_initial_triple {τ γ r T : ℝ} (hτ : 0 < τ) (hγ : 0 < γ)
    (hr : 0 < r) (hr' : r < 1/2) (hT : 1 < T) (hTa : 1024*firstMass packingDensity < T)
    (hgeom : closedBall (triangleCenter packingDensity) γ ⊆ convexHull ℝ (range (triangleVertex packingDensity))) :
    ∃ t ≥ T, ∃ x ∈ ball initialPoint r,
      HasVertexTriple (meanField (physicalPressure (coreProfile t) t) (firstMass packingDensity)) x packingDensity (τ/2) := by
  let a := firstMass packingDensity
  have ha : 0 < a := firstMass_pos packingDensity_pos
  let Q := fun n : ℕ => physicalPressure (coreProfile ((n:ℝ)+T)) ((n:ℝ)+T)
  have ht (n : ℕ) : 1 < (n:ℝ)+T := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hat (n : ℕ) : 1024*a < (n:ℝ)+T := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm (n : ℕ) : 17576*kernelHeight*(∑' _ : ℕ, (0:ℝ)) ≤ (n:ℝ)+T := by simp; linarith [ht n]
  have hQc (n : ℕ) : ConvexOn ℝ pressureDomain (Q n) := by
    simpa only [physicalProfile_zero] using physical_convex_bounded (ht n)
      (fun _ : ℕ => le_refl (0:ℝ)) (fun _ : ℕ => le_refl (1:ℝ)) summable_zero (hm n)
  have hPQ (n : ℕ) := physical_meanField_bounded (ht n) ha
    (fun _ : ℕ => le_refl (0:ℝ)) (fun _ : ℕ => le_refl (1:ℝ)) summable_zero (hm n) (hat n)
  simp only [physicalProfile_zero] at hPQ
  obtain ⟨n,_,x,hx,htr⟩ := initial_triple_of_limits packingDensity_pos hτ hγ hr hr' hgeom
    (locallyUniform_reindex core_pressure_locally_uniform (tendsto_atTop_add_const_right atTop T tendsto_natCast_atTop_atTop))
    hQc (fun n => (hPQ n).1) (fun n => (hPQ n).2) (core_transform_locally_uniform hT ha hTa)
    (fun n y hy w hw => by
      have hh := initial_ball_moderate (ball_subset_closedBall hy)
      exact physical_transform_active_bound (ht n) ha
        (fun _ : ℕ => le_refl (0:ℝ)) (fun _ : ℕ => le_refl (1:ℝ)) summable_zero (hm n) (hat n)
        hh.1 hh.2.1 hh.2.2 (by simpa only [physicalProfile_zero] using hw)) 0
  exact ⟨(n:ℝ)+T,by linarith [Nat.cast_nonneg (α := ℝ) n],x,hx,htr⟩

end ContinuumTemperature
end
end

end OAI
