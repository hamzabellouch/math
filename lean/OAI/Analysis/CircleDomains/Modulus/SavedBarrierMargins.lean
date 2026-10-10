import OAI.Analysis.CircleDomains.Topology.PlanarPairCalculus

namespace OAI

/-! Strict plateau and zero margins for the saved source barriers.
Uniformly small coordinate changes preserve the exact barrier values. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem saved_barrier_values_stable {X : Type*}
    (A A' : X → EuclideanPlane) (c : EuclideanPlane) (Φ : EuclideanPlane → ℝ)
    (I O : Set X) {r R η : ℝ} (_hη : 0 < η)
    (hplateau : ∀ y, ‖y‖ ≤ r → Φ y = 1)
    (hzero : ∀ y, R ≤ ‖y‖ → Φ y = 0)
    (hI : ∀ x ∈ I, ‖A x-c‖ ≤ r-η)
    (hO : ∀ x ∈ O, R+η ≤ ‖A x-c‖)
    (hchange : ∀ x ∈ I ∪ O, ‖A' x-A x‖ < η) :
    (∀ x ∈ I, Φ (A' x-c) = 1) ∧ (∀ x ∈ O, Φ (A' x-c) = 0) := by
  constructor
  · intro x hx
    apply hplateau
    have ht : ‖A' x-c‖ ≤ ‖A' x-A x‖+‖A x-c‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (A' x-A x) (A x-c)
    linarith [hI x hx,hchange x (Or.inl hx)]
  · intro x hx
    apply hzero
    have ht : ‖A x-c‖ ≤ ‖A' x-A x‖+‖A' x-c‖ := by
      have hh := norm_add_le (A x-A' x) (A' x-c)
      simpa only [sub_add_sub_cancel, norm_sub_rev (A x) (A' x)] using hh
    linarith [hO x hx,hchange x (Or.inr hx)]

 theorem saved_barrier_one_on_neighborhood
    (A : ℂ → EuclideanPlane) (hA : Continuous A) (c : EuclideanPlane)
    (Φ : EuclideanPlane → ℝ) (K : Set ℂ) {r : ℝ} (hr : 0 < r)
    (hplateau : ∀ y, ‖y‖ ≤ r → Φ y = 1)
    (hK : ∀ x ∈ K, ‖A x-c‖ ≤ r/2) :
    ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧
      ∀ A' : ℂ → EuclideanPlane, (∀ x ∈ V, ‖A' x-A x‖ < r/4) →
        ∀ x ∈ V, Φ (A' x-c) = 1 := by
  let V := {x : ℂ | ‖A x-c‖ < 3*r/4}
  refine ⟨V,isOpen_lt ((hA.sub continuous_const).norm) continuous_const,?_,?_⟩
  · intro x hx
    have := hK x hx
    change ‖A x-c‖ < 3*r/4
    linarith
  · intro A' hchange x hx
    apply hplateau
    have ht : ‖A' x-c‖ ≤ ‖A' x-A x‖+‖A x-c‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (A' x-A x) (A x-c)
    change ‖A x-c‖ < 3*r/4 at hx
    linarith [hchange x hx]

end CircleDomainRigidity

end

end OAI
