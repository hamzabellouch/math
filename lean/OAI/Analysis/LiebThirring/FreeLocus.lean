import OAI.Analysis.LiebThirring.InitialOrbit

namespace OAI

universe u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127 u128 u129 u130 u131 u132 u133 u134 u135

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter
open Set Finset

end

section


/-! Analytic compactness and free-locus facts for the PL continuation proof. -/

open Set Finset
namespace SharpLiebThirring.PLParity

section Compactness
variable {E : Type u116} {V : Type u117} [TopologicalSpace E] [NormedAddCommGroup V]

/-- On a compact domain, sufficiently small values lie in any open neighborhood
of the zero set. This is not an existence assumption about zeros. -/
lemma small_norm_near_zeros {C U : Set E} (hC : IsCompact C) (hU : IsOpen U)
    (f : E → V) (hf : ContinuousOn f C) (hzero : ∀ x ∈ C, f x = 0 → x ∈ U) :
    ∃ ε > 0, ∀ x ∈ C, ‖f x‖ < ε → x ∈ U := by
  by_cases hn : (C \ U).Nonempty
  · obtain ⟨x, hx, hmin⟩ := (hC.diff hU).exists_isMinOn hn (hf.norm.mono sdiff_subset)
    have hp : 0 < ‖f x‖ := norm_pos_iff.mpr (fun h ↦ hx.2 (hzero x hx.1 h))
    refine ⟨‖f x‖, hp, ?_⟩
    intro y hy hfy
    by_contra hu
    exact (not_lt_of_ge (hmin ⟨hy, hu⟩)) hfy
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx _
    by_contra hu
    exact hn ⟨x, hx, hu⟩
end Compactness

section ConvexError
variable {ι : Type u118} {V : Type u119} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma norm_of_convex_zero (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (a : ι → V) (ha : ∑ i, w i • a i = 0) (z : V) (ε : ℝ)
    (he : ∀ i, ‖a i - z‖ ≤ ε) : ‖z‖ ≤ ε := by
  have hid : ∑ i, w i • (a i - z) = -z := by
    simp only [smul_sub, Finset.sum_sub_distrib, ha, ← Finset.sum_smul, hs, one_smul, zero_sub]
  calc
    ‖z‖ = ‖∑ i, w i • (a i - z)‖ := by rw [hid, norm_neg]
    _ ≤ ∑ i, ‖w i • (a i - z)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (he i) (hw i)
    _ = ε := by rw [← Finset.sum_mul, hs, one_mul]

lemma norm_of_approximate_convex_zero (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (a b : ι → V) (ha : ∑ i, w i • a i = 0)
    (z : V) (ε δ : ℝ) (he : ∀ i, dist (a i) (b i) ≤ ε)
    (hd : ∀ i, dist (b i) z ≤ δ) : ‖z‖ ≤ ε + δ := by
  apply norm_of_convex_zero w hw hs a ha z (ε + δ)
  intro i
  rw [← dist_eq_norm]
  exact (dist_triangle _ _ _).trans (add_le_add (he i) (hd i))
end ConvexError

section FreeLocus
variable {G : Type u120} {E : Type u121} [Group G] [MulAction G E]

def freeLocus : Set E := {x | ∀ g : G, g • x = x → g = 1}

lemma freeLocus_smul (g : G) {x : E} (hx : x ∈ freeLocus (G := G)) :
    g • x ∈ freeLocus (G := G) := by
  intro s hs
  have hfix : (g⁻¹ * s * g) • x = x := by
    rw [mul_smul, mul_smul, hs, inv_smul_smul]
  have he := hx _ hfix
  have hh := congrArg (fun a : G ↦ g * a * g⁻¹) he
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hh

def freeSubMulAction : SubMulAction G E where
  carrier := freeLocus (G := G)
  smul_mem' g _ hx := freeLocus_smul g hx

instance : IsCancelSMul G (freeSubMulAction (G := G) (E := E)) where
  right_cancel' g h x he := by
    have he' : g • x.val = h • x.val := congrArg Subtype.val he
    have hh : (h⁻¹ * g) • x.val = x.val := by
      rw [mul_smul, he', inv_smul_smul]
    exact (inv_mul_eq_one.mp (x.prop _ hh)).symm

variable [TopologicalSpace E] [T2Space E] [ContinuousConstSMul G E] [Finite G]

lemma isOpen_freeLocus : IsOpen (freeLocus (G := G) (E := E)) := by
  classical
  have hset : freeLocus (G := G) (E := E) = ⋂ g : {g : G // g ≠ 1}, {x | g.val • x ≠ x} := by
    ext x
    simp only [freeLocus, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h ⟨g, hg⟩ he
      exact hg (h g he)
    · intro h g hg
      by_contra hn
      exact h ⟨g, hn⟩ hg
  rw [hset]
  apply isOpen_iInter_of_finite
  intro g
  exact (isClosed_eq (continuous_const_smul g.val) continuous_id).isOpen_compl

end FreeLocus
section FreeTube
variable {G : Type u122} {E : Type u123} [Group G] [MulAction G E] [MetricSpace E]
  [ContinuousConstSMul G E] [Finite G]

lemma compact_free_tube {K : Set E}
    (hK : IsCompact K) (hfree : K ⊆ freeLocus (G := G)) :
    ∃ r > 0, Metric.cthickening r K ⊆ freeLocus (G := G) :=
  hK.exists_cthickening_subset_open isOpen_freeLocus hfree

end FreeTube
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

def Flag.combination {n : ℕ} (h : ℝ) (F : Flag n) (w : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  h • ∑ k, w k • F.point k

lemma Flag.combination_neighbor {n : ℕ} [NeZero n] (h : ℝ) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (hj : w j = 0) :
    (F.neighbor j).combination h w = F.combination h w := by
  unfold combination
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = j
  · simp only [hk, hj, zero_smul]
  · have he : (F.neighbor j).point k = F.point k := by
      ext i
      simp only [point, congrFun (F.neighbor_vertex j k hk) i]
    rw [he]

lemma Flag.dist_combination_scaled_center {n : ℕ} (h : ℝ) (hh : 0 ≤ h) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    dist (F.combination h w) (h • F.center) ≤ h / 2 := by
  rw [combination, dist_scale h hh]
  nlinarith [F.dist_combination_center w hw hs]

lemma Flag.dist_combination_gridPoint {n : ℕ} (h : ℝ) (hh : 0 ≤ h) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (k : Fin (n + 1)) :
    dist (F.combination h w) (gridPoint h (F.vertex k)) ≤ h := by
  rw [gridPoint_vertex, combination, dist_scale h hh]
  nlinarith [F.dist_combination_point w hw hs k]

lemma nearCylinder_combination_cthickening {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ)
    (hh : 0 ≤ h) (t : Fin n) (m : ℕ) {F : Flag n} (hF : F ∈ nearCylinder K h r t m)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    F.combination h w ∈ Metric.cthickening (r + h / 2) K := by
  obtain ⟨x, hx, hd⟩ := hF.1
  apply Metric.mem_cthickening_of_dist_le _ x _ K hx
  calc
    _ ≤ dist (F.combination h w) (h • F.center) + dist (h • F.center) x := dist_triangle _ _ _
    _ ≤ h / 2 + r := add_le_add (F.dist_combination_scaled_center h hh w hw hs) hd.le
    _ = r + h / 2 := add_comm _ _

lemma cellHit_weights {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
    {V : Type u124} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : vertices H D → V) (F : D) (j : Fin (n + 1)) (hj : cellHit H D a F.val j) :
    ∃ w : Fin (n + 1) → ℝ, (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧ w j = 0 ∧
      ∑ k, w k • a (flagVertex H D F k) = 0 := by
  obtain ⟨w,he,hj,hw⟩ := hj
  refine ⟨w,hw,?_,hj,?_⟩
  · exact congrArg Prod.fst he
  · simpa only [augmentedMap_apply, extendValues_at] using congrArg Prod.snd he

/-- A PL zero gives a small value of the continuous map at its geometric point. -/
lemma norm_at_mesh_zero {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
    {V : Type u125} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : vertices H D → V) (f : (Fin n → ℝ) → V) (h ε δ : ℝ) (hh : 0 ≤ h)
    (C : Set (Fin n → ℝ))
    (ha : ∀ z : vertices H D, dist (a z) (f (gridPoint h z.val)) ≤ ε)
    (hf : ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ h → dist (f x) (f y) ≤ δ)
    (F : D) (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hz : ∑ k, w k • a (flagVertex H D F k) = 0)
    (hC : F.val.combination h w ∈ C)
    (hp : ∀ k, gridPoint h (F.val.vertex k) ∈ C) :
    ‖f (F.val.combination h w)‖ ≤ ε + δ := by
  apply norm_of_approximate_convex_zero w hw hs (fun k ↦ a (flagVertex H D F k))
    (fun k ↦ f (gridPoint h (F.val.vertex k))) hz (f (F.val.combination h w)) ε δ
  · intro k
    exact ha (flagVertex H D F k)
  · intro k
    exact hf _ (hp k) _ hC (by
      rw [dist_comm]
      exact F.val.dist_combination_gridPoint h hh w hw hs k)

lemma neighbor_near_centers_of_combination {n : ℕ} [NeZero n]
    (K : Set (Fin n → ℝ)) (h r : ℝ) (hh : 0 ≤ h) (hhr : h < r)
    (F : Flag n) (j : Fin (n + 1))
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (hj : w j = 0)
    (hx : ∃ x ∈ K, dist (F.combination h w) x < r / 2) :
    ∃ x ∈ K, dist (h • (F.neighbor j).center) x < r := by
  obtain ⟨x,hx,hd⟩ := hx
  refine ⟨x,hx,?_⟩
  have hc := (F.neighbor j).dist_combination_scaled_center h hh w hw hs
  rw [F.combination_neighbor h w j hj, dist_comm] at hc
  have ht := dist_triangle (h • (F.neighbor j).center) (F.combination h w) x
  linarith

lemma Flag.combination_time_boundary {n : ℕ} [NeZero n] (F : Flag n) (h : ℝ)
    (t : Fin n) (ht : (F.order.symm t).val = n - 1)
    (w : Fin (n + 1) → ℝ) (hs : ∑ k, w k = 1) (hz : w (Fin.last n) = 0) :
    F.combination h w t = h * ((F.base t : ℝ) + if F.corner t then 1 else 0) := by
  change h * (∑ k, w k • F.point k) t = _
  rw [Finset.sum_apply]
  have he : (∑ k, w k * F.point k t) =
      ∑ k, w k * ((F.base t : ℝ) + if F.corner t then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = Fin.last n
    · simp only [hk,hz,zero_mul]
    · rw [F.point_time_boundary t ht k hk]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [he, ← Finset.sum_mul, hs, one_mul]

end SharpLiebThirring.CubeFlags
end

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma Flag.combination_eq_sum_gridPoint {n : ℕ} (h : ℝ) (F : Flag n)
    (w : Fin (n + 1) → ℝ) :
    F.combination h w = ∑ k, w k • gridPoint h (F.vertex k) := by
  simp only [combination, gridPoint_vertex, Finset.smul_sum, smul_comm h]

lemma Signs.smul_sum_real {n : ℕ} {ι : Type u126} [Fintype ι] (s : Signs n)
    (w : ι → ℝ) (x : ι → Fin n → ℝ) :
    s • (∑ i, w i • x i) = ∑ i, w i • (s • x i) := by
  change s.linearIsometry (∑ i, w i • x i) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ map_smul s.linearIsometry (w i) (x i))

lemma Flag.combination_smul {n : ℕ} (s : Signs n) (h : ℝ) (F : Flag n)
    (w : Fin (n + 1) → ℝ) : (s • F).combination h w = s • F.combination h w := by
  rw [Flag.combination_eq_sum_gridPoint, Flag.combination_eq_sum_gridPoint, s.smul_sum_real]
  apply Finset.sum_congr rfl
  intro k _
  rw [F.vertex_smul, gridPoint_smul]

lemma sum_affine_linear {ι : Type u127} {E : Type u128} {V : Type u129} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    (L : E →ₗ[ℝ] V) (w : ι → ℝ) (hs : ∑ i, w i = 1) (x : ι → E) (q : E) :
    (∑ i, w i • L (x i - q)) = L ((∑ i, w i • x i) - q) := by
  simp only [map_sub, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hs, one_smul]

lemma cellHit_of_weights {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
    {V : Type u130} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : vertices H D → V) (F : D) (j : Fin (n + 1))
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hj : w j = 0) (hz : ∑ k, w k • a (flagVertex H D F k) = 0) : cellHit H D a F.val j := by
  refine ⟨w,?_,hj,hw⟩
  apply Prod.ext
  · exact hs
  · simpa only [augmentedMap_apply, extendValues_at] using hz

lemma affine_sum_on_facet {ι : Type u131} {E : Type u132} {V : Type u133} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    (L : E →ₗ[ℝ] V) (w : ι → ℝ) (hs : ∑ i, w i = 1)
    (j : ι) (hj : w j = 0) (x : ι → E) (q : E) (a : ι → V)
    (ha : ∀ k, k ≠ j → a k = L (x k - q)) :
    ∑ k, w k • a k = L ((∑ k, w k • x k) - q) := by
  rw [← sum_affine_linear L w hs x q]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = j
  · simp only [hk, hj, zero_smul]
  · rw [ha k hk]

lemma mesh_affine_zero_point {d : ℕ} (H : Subgroup (Signs (d + 1)))
    {V : Type u134} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (F : Flag (d + 1)) (j : Fin (d + 2)) (h : ℝ) (s : H) (q : Fin d → ℝ)
    (w : Fin (d + 2) → ℝ) (hs : ∑ k, w k = 1) (hj : w j = 0)
    (a : Fin (d + 2) → V) (hz : ∑ k, w k • a k = 0)
    (ha : ∀ k, k ≠ j → a k = ρ s (L (spatial (s⁻¹ • gridPoint h (F.vertex k)) - q)))
    (ht : F.combination h w (Fin.last d) = 0) :
    F.combination h w = s • embedSpatial q := by
  have he := affine_sum_on_facet (L.trans (ρ s)).toLinearMap w hs j hj
    (fun k ↦ spatial (s⁻¹ • gridPoint h (F.vertex k))) q a ha
  rw [hz] at he
  have hq : (∑ k, w k • spatial (s⁻¹ • gridPoint h (F.vertex k))) = q := by
    apply sub_eq_zero.mp
    apply (L.trans (ρ s)).injective
    change (L.trans (ρ s)) _ = (L.trans (ρ s)) 0
    rw [map_zero]
    exact he.symm
  have hsum : spatial (s⁻¹ • F.combination h w) = q := by
    rw [F.combination_eq_sum_gridPoint]
    rw [Subgroup.smul_def, Signs.smul_sum_real, map_sum]
    simpa only [map_smul, Subgroup.smul_def] using hq
  have ht' : (s⁻¹ • F.combination h w) (Fin.last d) = 0 :=
    s⁻¹.val.smul_time_zero _ ht
  have hx : s⁻¹ • F.combination h w = embedSpatial q := by
    rw [← hsum]
    exact (embed_spatial_of_time_zero _ ht').symm
  simpa only [smul_inv_smul] using congrArg (fun x ↦ s • x) hx

lemma model_seed_hit {d : ℕ} (H : Subgroup (Signs (d + 1)))
    (D : SubMulAction H (Flag (d + 1)))
    {V : Type u135} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p q : Fin d → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : 2*h < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (F : D) (hF : F.val = bottomSeed h p) (a : vertices H D → V)
    (ha : ∀ k, k ≠ Fin.last (d + 1) →
      a (flagVertex H D F k) = affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h (F.val.vertex k)))
    (w : Fin (d + 2) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hj : w (Fin.last (d + 1)) = 0)
    (he : ∑ k, w k • gridPoint h (F.val.vertex k) = embedSpatial q) :
    cellHit H D a F.val (Fin.last (d + 1)) := by
  apply cellHit_of_weights H D a F _ w hw hs hj
  have hv (k : Fin (d + 2)) : ballLabel (G := H) (embedSpatial p) R (gridPoint h (F.val.vertex k)) = 1 := by
    apply ballLabel_eq (embedSpatial p) R hR hsep
    rw [one_smul, hF, gridPoint_vertex]
    exact (bottomSeed_dist_point h hh p k).trans_lt hhr
  have haf (k : Fin (d + 2)) (hk : k ≠ Fin.last (d + 1)) :
      a (flagVertex H D F k) = L (spatial (gridPoint h (F.val.vertex k)) - q) := by
    rw [ha k hk]
    simp only [affineOrbitModel, hv, inv_one, one_smul, map_one]
    rfl
  rw [affine_sum_on_facet L.toLinearMap w hs _ hj
    (fun k ↦ spatial (gridPoint h (F.val.vertex k))) q _ haf]
  have hsp := congrArg spatial he
  simp only [map_sum, map_smul, spatial_embed] at hsp
  rw [hsp, sub_self, map_zero]

lemma bottom_facet_unique {d : ℕ} (h : ℝ) (hh : h ≠ 0) (p q : Fin d → ℝ)
    (s : Signs (d + 1)) (hst : s.val (Fin.last d) = false)
    (G : Flag (d + 1)) (hGb : G.base (Fin.last d) = 0) (hGc : G.corner (Fin.last d) = false)
    (w z : Fin (d + 2) → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hwp : ∀ k, k ≠ Fin.last (d + 1) → 0 < w k) (hz : ∀ k, 0 ≤ z k)
    (hsw : ∑ k, w k = 1) (hsz : ∑ k, z k = 1)
    (he : (bottomSeed h p).combination h w = embedSpatial q)
    (hg : G.combination h z = s • embedSpatial q) : G = s • bottomSeed h p := by
  have hx : (s • bottomSeed h p).combination h w = G.combination h z := by
    rw [Flag.combination_smul, he, hg]
  have hx' := (smul_right_injective (Fin (d + 1) → ℝ) hh) hx
  apply Eq.symm
  apply Flag.eq_of_facet_combination _ _ (Fin.last d) _ _ _ w z hw hwp hz hsw hsz hx'
  · simp [Flag.smul_def, Flag.reflect, bottomSeed]
  · simp [Flag.smul_def, Flag.reflect, bottomSeed, hst, hGb]
  · simp [Flag.smul_def, Flag.reflect, bottomSeed, hst, hGc]

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
