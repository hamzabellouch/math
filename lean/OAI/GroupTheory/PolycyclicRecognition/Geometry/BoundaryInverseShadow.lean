import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactLiftQuotient
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-! # Transporting two compact shadows through a coarse inverse -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric Filter
open scoped Pointwise Topology

/-- On the second factor, the quotient action is the Cartan action. -/
theorem factor_quotient_action_second
    {N D G Q : Type*} [Group N] [Group D] [Group G] [Group Q]
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * α d q) (d : D) (q : Q) :
    act (κ d) q = α d q := by
  simpa only [map_one, one_mul] using hact 1 d q

/-- A continuous section turns a compact quotient shadow into compact
ambient representatives of that same shadow. -/
theorem compact_lift_boundary_shadow
    {G S T : Type*} [Group G] [TopologicalSpace G]
    [One S] [One T] [TopologicalSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : S → T) (f : G → G)
    (σ : T → G) (hσ : Continuous σ) (hsection : ∀ q, actT (σ q) 1 = q)
    (K : Set T) (hK : IsCompact K)
    (hshadow : ∀ x, ∃ q ∈ K, B (actS x 1) = actT (f x) q) :
    ∃ C : Set G, IsCompact C ∧ ∀ x, ∃ u ∈ C,
      B (actS x 1) = actT (f x) (actT u 1) := by
  refine ⟨σ '' K, hK.image hσ, ?_⟩
  intro x
  obtain ⟨q, hq, he⟩ := hshadow x
  exact ⟨σ q, ⟨q, hq, rfl⟩, by simpa only [hsection] using he⟩

/-- Compose the forward and inverse boundary shadows. Compact group
representatives of the shadows and the coarse-inverse estimate put their
composition in one fixed compact source shadow. -/
theorem inverse_boundary_compact_shadow
    {G S T : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G] [One S] [One T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : S → T) (C : T → S) (f g : G → G)
    {L error E : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, dist (g x) (g y) ≤ L * dist x y + error)
    (hinv : ∀ x, dist (g (f x)) x ≤ E)
    (KT KS : Set G) (hKT : IsCompact KT) (hKS : IsCompact KS)
    (hB : ∀ x, ∃ u ∈ KT, B (actS x 1) = actT (f x) (actT u 1))
    (hC : ∀ y, ∃ v ∈ KS, C (actT y 1) = actS (g y) (actS v 1)) :
    ∃ K : Set G, IsCompact K ∧ ∀ x, ∃ k ∈ K,
      C (B (actS x 1)) = actS x (actS k 1) := by
  obtain ⟨R, hR⟩ := hKT.exists_bound_of_continuousOn
    ((continuous_const : Continuous (fun _ : G => (1 : G))).dist continuous_id).continuousOn
  have hR' (u : G) (hu : u ∈ KT) : dist 1 u ≤ R := by
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hR u hu
  let D := E + L * R + error
  refine ⟨closedBall (1 : G) D * KS, (isCompact_closedBall _ _).mul hKS, ?_⟩
  intro x
  obtain ⟨u, hu, hBu⟩ := hB x
  obtain ⟨v, hv, hCv⟩ := hC (f x * u)
  let δ := x⁻¹ * g (f x * u)
  have hδ : δ ∈ closedBall (1 : G) D := by
    have hdist : dist 1 δ = dist x (g (f x * u)) := by
      simpa only [δ, mul_one, mul_inv_cancel_left] using
        (dist_mul_left x (1 : G) (x⁻¹ * g (f x * u))).symm
    have hu' : dist (f x) (f x * u) = dist 1 u := by
      simpa only [mul_one] using dist_mul_left (f x) (1 : G) u
    have hcoarse := hg (f x) (f x * u)
    rw [hu'] at hcoarse
    have hmul := mul_le_mul_of_nonneg_left (hR' u hu) hL
    have hi := hinv x
    have ht := dist_triangle x (g (f x)) (g (f x * u))
    rw [dist_comm x (g (f x))] at ht
    rw [mem_closedBall, dist_comm, hdist]
    change dist x (g (f x * u)) ≤ E + L * R + error
    linarith
  refine ⟨δ * v, Set.mul_mem_mul hδ hv, ?_⟩
  have hpoint : actT (f x) (actT u 1) = actT (f x * u) 1 := by
    rw [map_mul, Equiv.Perm.mul_apply]
  have hgroup : x * (δ * v) = g (f x * u) * v := by
    simp only [δ, ← mul_assoc, mul_inv_cancel, one_mul]
  calc
    C (B (actS x 1)) = C (actT (f x * u) 1) := congrArg C (hBu.trans hpoint)
    _ = actS (g (f x * u)) (actS v 1) := hCv
    _ = actS (g (f x * u) * v) 1 := by rw [map_mul, Equiv.Perm.mul_apply]
    _ = actS (x * (δ * v)) 1 := by rw [hgroup]
    _ = actS x (actS (δ * v) 1) := by rw [map_mul, Equiv.Perm.mul_apply]

/-- A composition constrained by one compact source shadow is the
identity when the negative ray fixes the basepoint and contracts compact
shadows. The compact-shadow premise is supplied by the coarse-inverse
transport theorem above. -/
theorem boundary_left_inverse_of_compact_shadow
    {G S T : Type*} [Group G] [TopologicalSpace G]
    [One S] [TopologicalSpace S] [T2Space S]
    (act : G →* Equiv.Perm S) (hact : ∀ g, Continuous (act g))
    (B : S → T) (C : T → S) (ray : ℕ → G)
    (hfix : ∀ n, act (ray n) 1 = 1)
    (hcontract : ∀ K : Set G, IsCompact K → ∀ k : ℕ → G,
      (∀ n, k n ∈ K) → Tendsto (fun n => act (ray n) (act (k n) 1)) atTop (𝓝 1))
    (hshadow : ∃ K : Set G, IsCompact K ∧ ∀ x, ∃ k ∈ K,
      C (B (act x 1)) = act x (act k 1)) :
    ∀ x, C (B (act x 1)) = act x 1 := by
  classical
  obtain ⟨K, hK, hshadow⟩ := hshadow
  intro x
  have hs (n : ℕ) : ∃ k ∈ K,
      C (B (act x 1)) = act x (act (ray n) (act k 1)) := by
    obtain ⟨k, hk, he⟩ := hshadow (x * ray n)
    refine ⟨k, hk, ?_⟩
    simpa only [map_mul, Equiv.Perm.mul_apply, hfix] using he
  choose k hk he using hs
  have ht := ((hact x).tendsto 1).comp (hcontract K hK k hk)
  have hconst : Tendsto (fun _ : ℕ => C (B (act x 1))) atTop (𝓝 (act x 1)) := by
    simpa only [Function.comp_def, ← he] using ht
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end PolycyclicRecognition

end

end OAI
