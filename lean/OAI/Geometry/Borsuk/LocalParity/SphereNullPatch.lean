import Mathlib
import OAI.Geometry.Borsuk.Projectors.FinitePatch
import OAI.Geometry.Borsuk.Projectors.FiniteClosedCutoffs
import OAI.Geometry.Borsuk.SphereGeometry.NormSphere

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
section SphereNullPatch
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
local notation "Y" => EuclideanSpace ℝ (Fin n)
lemma sphere_null_patch_models (hn : 1 < n)
    (F : normSphere n → Y) (hF : Continuous F) (hFz : ∀ A, F A ≠ 0)
    (C : ℝ × normSphere n → Y) (hC : ContinuousOn C (Icc (0:ℝ) 1 ×ˢ univ))
    (hCz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, C (t,u) ≠ 0)
    (hC1 : ∀ u, C (1,u) = F u)
    (G : κ → normSphere n → Y) (hG : ∀ a, Continuous (G a))
    (hGz : ∀ a A, G a A ≠ 0)
    (hGo : ∀ a (A B : normSphere n), B.val = -A.val → G a B = -G a A)
    (K S : κ → Set (normSphere n)) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
    (hKS : ∀ a, K a ⊆ S a) (hKd : Pairwise (fun a b => Disjoint (K a) (K b)))
    {y : Y} (hy : y ≠ 0)
    (hmiss : ∀ u, ¬ ∃ d : ℝ, 0 < d ∧ C (0,u) = d • y)
    (hcover : ∀ A, (∃ d : ℝ, 0 < d ∧ F A = d • y) → ∃ a, A ∈ K a)
    (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ K a)
    (hseg : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1, (1-t) • F A + t • G a A ≠ 0)
    (hhit : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1,
      (∃ d : ℝ, 0 < d ∧ (1-t) • F A + t • G a A = d • y) → A ∈ K a) :
    (Fintype.card κ : F₂) = 0 := by
  classical
  obtain ⟨U,q,hU,hKU,hqb,hq1,hqS,hqd⟩ := finite_closed_cutoffs K S hK hS hKS hKd
  let H : ℝ × normSphere n → Y := fun p => finitePatch F G (fun a => q a) p.1 p.2
  have hH : Continuous H := finitePatch_continuous hF hG (fun a => (q a).continuous)
  have hHz (t) (ht : t ∈ Icc (0:ℝ) 1) (A) : H (t,A) ≠ 0 :=
    finitePatch_ne_zero F G (fun a => q a) t A hqd ht (fun a => hqb a A) (hFz A)
      (fun a ha => hseg a A (hqS a A ha))
  refine sphere_null_local_models hn H C hH.continuousOn hHz hC hCz
    (fun u => by simpa only [H,finitePatch_zero] using hC1 u)
    G hG hGz hGo U hU ?_ hy hmiss ?_ ?_ ?_
  · intro a A hA
    apply finitePatch_one_of_disjoint F G (fun a => q a) A a (hq1 a A hA)
    intro b hba
    by_contra hb
    exact Set.disjoint_left.mp (hqd hba) hb (by
      change q a A ≠ 0
      rw [hq1 a A hA]; exact one_ne_zero)
  · intro A hA
    rcases finitePatch_cases F G (fun a => q a) 1 A hqd with he | ⟨a,ha,he⟩
    · have hr : ∃ d : ℝ, 0 < d ∧ F A = d • y := by
        simpa only [H,he] using hA
      obtain ⟨a,ha⟩ := hcover A hr
      exact ⟨a,hKU a ha⟩
    · refine ⟨a,hKU a (hhit a A (hqS a A ha) (q a A) (hqb a A) ?_)⟩
      simpa only [H,he,one_mul] using hA
  · intro a A hA
    exact hKU a (hroot a A hA)
  · intro a b hab
    exact (hqd hab).mono
      (fun A hA => by change q a A ≠ 0; rw [hq1 a A hA]; exact one_ne_zero)
      (fun A hA => by change q b A ≠ 0; rw [hq1 b A hA]; exact one_ne_zero)
end SphereNullPatch
end BorsukNine

end OAI
