import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientGroupAction
import Mathlib.GroupTheory.SemidirectProduct

namespace OAI

/-! # The quotient action descends through overlapping group factors

The factors need not form a direct or injective semidirect decomposition.
The only overlap condition is that the nilpotent quotient kills it.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N D Q G : Type*} [Group N] [Group D] [Group Q] [Group G]

/-- Translations and quotient automorphisms form the affine action of the
actual semidirect product. -/
def factorQuotientAction (π : N →* Q) (s : Q → N)
    (hs : Function.RightInverse s π) (a : D →* MulAut N)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker) : (N ⋊[a] D) →* Equiv.Perm Q where
  toFun p := ((descendQuotientAction π s hs a ha p.right).toEquiv).trans
    (Equiv.mulLeft (π p.left))
  map_one' := by
    ext q
    change π 1 * descendQuotientAction π s hs a ha 1 q = q
    simp only [map_one, MulAut.one_apply, one_mul]
  map_mul' p r := by
    ext q
    change π (p.left * a p.right r.left) *
        descendQuotientAction π s hs a ha (p.right * r.right) q =
      π p.left * descendQuotientAction π s hs a ha p.right
        (π r.left * descendQuotientAction π s hs a ha r.right q)
    simp only [map_mul, MulAut.mul_apply, descendQuotientAction_project, mul_assoc]

@[simp] theorem factorQuotientAction_apply (π : N →* Q) (s : Q → N)
    (hs : Function.RightInverse s π) (a : D →* MulAut N)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker) (p : N ⋊[a] D) (q : Q) :
    factorQuotientAction π s hs a ha p q =
      π p.left * descendQuotientAction π s hs a ha p.right q := rfl

/-- Killing the overlap makes the affine action well-defined on the ambient
group, even when multiplication of the two factors is not injective. -/
theorem exists_descended_factor_quotient_action
    (ι : N →* G) (κ : D →* G) (hι : Function.Injective ι)
    (a : D →* MulAut N)
    (hconj : ∀ d n, ι (a d n) = κ d * ι n * (κ d)⁻¹)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (π : N →* Q) (s : Q → N) (hs : Function.RightInverse s π)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker)
    (hoverlap : ∀ n d, ι n = κ d → π n = 1) :
    ∃ act : G →* Equiv.Perm Q,
      (∀ n d q, act (ι n * κ d) q = π n * descendQuotientAction π s hs a ha d q) ∧
      (∀ g, act g 1 = 1 ↔ ∃ n d, n ∈ π.ker ∧ ι n * κ d = g) ∧
      ∀ g h, act (g * h) 1 = act g (act h 1) := by
  have hcompat (d) : ι.comp (a d).toMonoidHom = (MulAut.conj (κ d)).toMonoidHom.comp ι := by
    ext n
    exact hconj d n
  let σ : (N ⋊[a] D) →* G := SemidirectProduct.lift ι κ hcompat
  have hσ : Function.Surjective σ := by
    intro g
    obtain ⟨⟨n, d⟩, h⟩ := hsurj g
    exact ⟨⟨n, d⟩, h⟩
  let ρ := factorQuotientAction π s hs a ha
  have hker : σ.ker ≤ ρ.ker := by
    intro p hp
    have hp' : ι p.left * κ p.right = 1 := hp
    have hn : ι p.left = κ (p.right⁻¹) := by
      simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul, map_inv] using
        congrArg (fun x => x * (κ p.right)⁻¹) hp'
    have hπn : π p.left = 1 := hoverlap _ _ hn
    have hk : κ p.right = ι (p.left⁻¹) := by
      simpa only [map_inv, inv_mul_cancel_left, mul_one] using
        congrArg (fun x => (ι p.left)⁻¹ * x) hp'
    have had (x : N) : a p.right x = p.left⁻¹ * x * p.left := by
      apply hι
      rw [hconj, hk]
      simp only [map_mul, map_inv, inv_inv]
    apply Equiv.ext
    intro q
    obtain ⟨x, rfl⟩ := hs.surjective q
    change π p.left * descendQuotientAction π s hs a ha p.right (π x) = π x
    rw [descendQuotientAction_project, had]
    simp only [map_mul, map_inv, hπn, inv_one, one_mul, mul_one]
  let act := σ.liftOfSurjective hσ ⟨ρ, hker⟩
  have hact (p : N ⋊[a] D) : act (σ p) = ρ p :=
    σ.liftOfRightInverse_comp_apply _ _ _ p
  have hformula (n : N) (d : D) (q : Q) :
      act (ι n * κ d) q = π n * descendQuotientAction π s hs a ha d q := by
    exact congrArg (fun f : Equiv.Perm Q => f q) (hact ⟨n, d⟩)
  refine ⟨act, hformula, ?_, ?_⟩
  · intro g
    constructor
    · intro hg
      obtain ⟨⟨n, d⟩, he⟩ := hsurj g
      refine ⟨n, d, ?_, he⟩
      rw [← he, hformula, map_one, mul_one] at hg
      exact hg
    · rintro ⟨n, d, hn, rfl⟩
      rw [hformula, map_one, mul_one]
      exact hn
  · intro g h
    exact congrArg (fun f : Equiv.Perm Q => f 1) (act.map_mul g h)

end PolycyclicRecognition

end

end OAI
