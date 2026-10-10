import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryInverseShadow

namespace OAI

/-! # Uniform compact sandwiches for boundary images

A coarse pair and its compact boundary shadows give both inclusions used
in the boundary volume comparison. The sets are uniform in the pair and
in the ambient basepoint.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped Pointwise

/-- A compact set in the source boundary has one common compact image
shadow under a family with common coarse Lipschitz and shadow bounds. -/
theorem compact_boundary_image_upper
    {P G S T : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G]
    [One S] [TopologicalSpace S] [One T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : P → S → T) (f : P → G → G)
    {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (σ : S → G) (hσ : Continuous σ) (hsection : ∀ q, actS (σ q) 1 = q)
    (KT : Set G) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ v ∈ KT, B p (actS x 1) = actT (f p x) (actT v 1))
    (U : Set S) (hU : IsCompact U) :
    ∃ V : Set G, IsCompact V ∧ ∀ p x,
      B p '' (actS x '' U) ⊆ actT (f p x) '' ((fun g => actT g 1) '' V) := by
  obtain ⟨R, hR⟩ := (hU.image hσ).exists_bound_of_continuousOn
    ((continuous_const : Continuous (fun _ : G => (1 : G))).dist continuous_id).continuousOn
  let radius := L * R + error
  refine ⟨closedBall (1 : G) radius * KT, (isCompact_closedBall _ _).mul hKT, ?_⟩
  intro p x y hy
  rcases hy with ⟨s, ⟨q, hq, rfl⟩, rfl⟩
  let u := σ q
  have hu : dist 1 u ≤ R := by
    have hh := hR u ⟨q, hq, rfl⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, id_eq] using hh
  obtain ⟨v, hv, he⟩ := hB p (x * u)
  let δ := (f p x)⁻¹ * f p (x * u)
  have hδ : δ ∈ closedBall (1 : G) radius := by
    have hd : dist 1 δ = dist (f p x) (f p (x * u)) := by
      simpa only [δ, mul_one, mul_inv_cancel_left] using
        (dist_mul_left (f p x) (1 : G) δ).symm
    have hc := hf p x (x * u)
    have hs : dist x (x * u) = dist 1 u := by
      simpa only [mul_one] using dist_mul_left x (1 : G) u
    rw [mem_closedBall, dist_comm, hd]
    exact hc.trans (by rw [hs]; exact add_le_add (mul_le_mul_of_nonneg_left hu hL) le_rfl)
  refine ⟨actT (δ * v) 1, ⟨δ * v, Set.mul_mem_mul hδ hv, rfl⟩, ?_⟩
  have hsource : actS (x * u) 1 = actS x q := by
    simp only [map_mul, Equiv.Perm.mul_apply, u, hsection]
  have htarget : actT (f p x) (actT (δ * v) 1) = actT (f p (x * u)) (actT v 1) := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← mul_assoc]
    simp only [δ, mul_inv_cancel_left, map_mul, Equiv.Perm.mul_apply]
  exact htarget.trans (by simpa only [hsource] using he.symm)

/-- Both compact inclusions needed for volume comparison follow from
coarse inverses and the already constructed boundary shadows. -/
theorem boundary_image_compact_sandwich
    {P G S T : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G]
    [One S] [TopologicalSpace S] [One T] [TopologicalSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (hcontS : Continuous (fun g => actS g 1))
    (hcontT : Continuous (fun g => actT g 1))
    (B : P → S → T) (C : P → T → S) (f g : P → G → G)
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hBC : ∀ p, Function.RightInverse (C p) (B p))
    (σS : S → G) (hσS : Continuous σS) (hsectionS : ∀ q, actS (σS q) 1 = q)
    (σT : T → G) (hσT : Continuous σT) (hsectionT : ∀ q, actT (σT q) 1 = q)
    (KS KT : Set G) (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ v ∈ KT, B p (actS x 1) = actT (f p x) (actT v 1))
    (hC : ∀ p x, ∃ v ∈ KS, C p (actT x 1) = actS (g p x) (actS v 1))
    (U₀ : Set S) (hU₀ : IsCompact U₀) (Vminus : Set T) (hVminus : IsCompact Vminus) :
    ∃ (U : Set S) (Vplus : Set T), IsCompact U ∧ IsCompact Vplus ∧ U₀ ⊆ U ∧
      ∀ p x, actT (f p x) '' Vminus ⊆ B p '' (actS x '' U) ∧
        B p '' (actS x '' U) ⊆ actT (f p x) '' Vplus := by
  obtain ⟨V, hV, hVupper⟩ := compact_boundary_image_upper actT actS C g hLg hg
    σT hσT hsectionT KS hKS hC Vminus hVminus
  let U := ((fun z => actS z 1) '' (closedBall (1 : G) E * V)) ∪ U₀
  have hU : IsCompact U := ((isCompact_closedBall _ _).mul hV).image hcontS |>.union hU₀
  obtain ⟨W, hW, hWupper⟩ := compact_boundary_image_upper actS actT B f hLf hf
    σS hσS hsectionS KT hKT hB U hU
  refine ⟨U, (fun z => actT z 1) '' W, hU, hW.image hcontT, subset_union_right, ?_⟩
  intro p x
  refine ⟨?_, hWupper p x⟩
  intro y hy
  have hc := hVupper p (f p x) (Set.mem_image_of_mem (C p) hy)
  rcases hc with ⟨q, ⟨v, hv, rfl⟩, hq⟩
  let δ := x⁻¹ * g p (f p x)
  have hδ : δ ∈ closedBall (1 : G) E := by
    have hd : dist 1 δ = dist x (g p (f p x)) := by
      simpa only [δ, mul_one, mul_inv_cancel_left] using
        (dist_mul_left x (1 : G) δ).symm
    rw [mem_closedBall, dist_comm, hd, dist_comm]
    exact hinv p x
  have hmem : actS (δ * v) 1 ∈ U := Or.inl ⟨δ * v, Set.mul_mem_mul hδ hv, rfl⟩
  have he : actS x (actS (δ * v) 1) = C p y := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← mul_assoc]
    simpa only [δ, mul_inv_cancel_left, map_mul, Equiv.Perm.mul_apply] using hq
  exact ⟨C p y, ⟨actS (δ * v) 1, hmem, he⟩, hBC p y⟩

end PolycyclicRecognition

end

end OAI
