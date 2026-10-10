import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryFromLogProducts

namespace OAI

/-! # Descending centered ray limits to boundary maps with compact shadows -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology

/-- Continuous fixed-element actions transport normalized ray limits.
Asymptotic equality on the actual source fibers then gives a well-defined
boundary map and the same common compact shadow. -/
theorem boundary_shadow_of_centered_limits
    {G S Q : Type*} [Group G] [Group Q] [TopologicalSpace Q]
    [T2Space Q] [IsTopologicalGroup Q]
    (act : G →* Equiv.Perm Q) (hact : ∀ g, Continuous (act g))
    (q : G → S) (hq : Function.Surjective q) (F : G → G) (ray : ℕ → G)
    (K : Set Q) (k : G → Q) (hkK : ∀ x, k x ∈ K)
    (hk : ∀ x, Tendsto (fun n => act ((F x)⁻¹ * F (x * ray n)) 1)
      atTop (𝓝 (k x)))
    (hfiber : ∀ x y, q x = q y →
      Tendsto (fun n => (act (F (x * ray n)) 1)⁻¹ * act (F (y * ray n)) 1)
        atTop (𝓝 (1 : Q))) :
    ∃ B : S → Q, ∀ x,
      Tendsto (fun n => act (F (x * ray n)) 1) atTop (𝓝 (B (q x))) ∧
      ∃ z ∈ K, B (q x) = act (F x) z := by
  classical
  let b : G → Q := fun x => act (F x) (k x)
  have hb (x : G) : Tendsto (fun n => act (F (x * ray n)) 1) atTop (𝓝 (b x)) := by
    have ht := ((hact (F x)).tendsto (k x)).comp (hk x)
    have he (n : ℕ) : act (F x) (act ((F x)⁻¹ * F (x * ray n)) 1) =
        act (F (x * ray n)) 1 := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel_left]
    simpa only [Function.comp_def, he] using ht
  have heq (x y : G) (hxy : q x = q y) : b x = b y := by
    have he := tendsto_nhds_unique ((hb x).inv.mul (hb y)) (hfiber x y hxy)
    exact inv_mul_eq_one.mp he
  choose s hs using hq
  let B : S → Q := fun z => b (s z)
  have hdesc (x : G) : B (q x) = b x := heq _ _ (hs _)
  refine ⟨B, ?_⟩
  intro x
  refine ⟨?_, k x, hkK x, hdesc x⟩
  simpa only [hdesc] using hb x

end PolycyclicRecognition

end

end OAI
