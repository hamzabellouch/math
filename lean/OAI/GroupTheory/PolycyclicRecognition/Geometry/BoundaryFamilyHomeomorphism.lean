import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryInverseShadow
import Mathlib.Topology.Homeomorph.Defs

namespace OAI

/-! # Boundary homeomorphisms from coarse inverse compact shadows -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology

/-- Contracting rays turn the two compact shadows of a coarse inverse pair
into inverse boundary maps. This applies to all members of a family with
the same compact shadow sets. -/
theorem boundary_family_homeomorphisms_of_compact_shadows
    {P G S T : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G]
    [One S] [TopologicalSpace S] [T2Space S]
    [One T] [TopologicalSpace T] [T2Space T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (hcontS : ∀ g, Continuous (actS g)) (hcontT : ∀ g, Continuous (actT g))
    (σS : S → G) (hσS : Continuous σS) (hsectionS : ∀ q, actS (σS q) 1 = q)
    (σT : T → G) (hσT : Continuous σT) (hsectionT : ∀ q, actT (σT q) 1 = q)
    (rayS rayT : ℕ → G)
    (hfixS : ∀ n, actS (rayS n) 1 = 1) (hfixT : ∀ n, actT (rayT n) 1 = 1)
    (hcontractS : ∀ K : Set G, IsCompact K → ∀ k : ℕ → G,
      (∀ n, k n ∈ K) → Tendsto (fun n => actS (rayS n) (actS (k n) 1)) atTop (𝓝 1))
    (hcontractT : ∀ K : Set G, IsCompact K → ∀ k : ℕ → G,
      (∀ n, k n ∈ K) → Tendsto (fun n => actT (rayT n) (actT (k n) 1)) atTop (𝓝 1))
    (B : P → S → T) (C : P → T → S)
    (hBcont : ∀ p, Continuous (B p)) (hCcont : ∀ p, Continuous (C p))
    (f g : P → G → G) {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ E)
    (KS : Set S) (KT : Set T) (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ q ∈ KT, B p (actS x 1) = actT (f p x) q)
    (hC : ∀ p x, ∃ q ∈ KS, C p (actT x 1) = actS (g p x) q) :
    ∃ D : P → S ≃ₜ T, (∀ p q, D p q = B p q) ∧
      (∀ p q, (D p).symm q = C p q) := by
  classical
  have hleft (p : P) : Function.LeftInverse (C p) (B p) := by
    obtain ⟨KT', hKT', hB'⟩ := compact_lift_boundary_shadow actS actT (B p) (f p)
      σT hσT hsectionT KT hKT (hB p)
    obtain ⟨KS', hKS', hC'⟩ := compact_lift_boundary_shadow actT actS (C p) (g p)
      σS hσS hsectionS KS hKS (hC p)
    have hshadow := inverse_boundary_compact_shadow actS actT (B p) (C p)
      (f p) (g p) hLg (hg p) (hgf p) KT' KS' hKT' hKS' hB' hC'
    have h := boundary_left_inverse_of_compact_shadow actS hcontS (B p) (C p)
      rayS hfixS hcontractS hshadow
    intro q
    simpa only [hsectionS] using h (σS q)
  have hright (p : P) : Function.RightInverse (C p) (B p) := by
    obtain ⟨KS', hKS', hC'⟩ := compact_lift_boundary_shadow actT actS (C p) (g p)
      σS hσS hsectionS KS hKS (hC p)
    obtain ⟨KT', hKT', hB'⟩ := compact_lift_boundary_shadow actS actT (B p) (f p)
      σT hσT hsectionT KT hKT (hB p)
    have hshadow := inverse_boundary_compact_shadow actT actS (C p) (B p)
      (g p) (f p) hLf (hf p) (hfg p) KS' KT' hKS' hKT' hC' hB'
    have h := boundary_left_inverse_of_compact_shadow actT hcontT (C p) (B p)
      rayT hfixT hcontractT hshadow
    intro q
    simpa only [hsectionT] using h (σT q)
  exact ⟨fun p => {
    toFun := B p, invFun := C p, left_inv := hleft p, right_inv := hright p
    continuous_toFun := hBcont p, continuous_invFun := hCcont p },
    fun _ _ => rfl, fun _ _ => rfl⟩

end PolycyclicRecognition

end

end OAI
