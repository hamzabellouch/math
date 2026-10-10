import OAI.Analysis.BoundedHochschild.CentralProjectionSuprema
import OAI.Analysis.BoundedHochschild.TypeIIStructure

namespace OAI

/-!
# Central type I support without a trace

The maximal central projection annihilating an abelian projection exists by
weak-star compactness. Its complement is a nonzero central type I support.
The construction applies to every von Neumann algebra and requires no
faithful tracial state.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A chain of central projections annihilating one element has a central
projection upper bound that still annihilates it. -/
lemma central_annihilator_chain (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : M) (c : Set M) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ q ∈ c, CentralProjection q ∧ q * p = 0) :
    ∃ s : M, CentralProjection s ∧ s * p = 0 ∧ ∀ q ∈ c, q ≤ s := by
  obtain ⟨s, hsp, hsc, hub, _hleast, hann⟩ :=
    exists_central_projection_chain_supremum e c hne hc
      (fun q hq => (hs q hq).1.1) (fun q hq a => ((hs q hq).1.2 a).eq)
  exact ⟨s, ⟨hsp, fun a => hsc a⟩, hann p (fun q hq => (hs q hq).2), hub⟩

/-- Every nonzero abelian projection has a nonzero central type I support. -/
theorem exists_typeI_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) :
    ∃ z : M, TypeICentralSummand z ∧ p ≤ z ∧ z ≠ 0 := by
  classical
  let S : Set M := {s | CentralProjection s ∧ s * p = 0}
  have hz : (0 : M) ∈ S :=
    ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, zero_mul _⟩
  obtain ⟨s, _hs0, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨t, ht, htp, hupper⟩ :=
      central_annihilator_chain e p c hchain ⟨y, hy⟩ (fun q hq => hc hq)
    exact ⟨t, ⟨ht, htp⟩, hupper⟩) 0 hz
  have hs : CentralProjection s := hmax.1.1
  have hsp : s * p = 0 := hmax.1.2
  have hzc : CentralProjection (1 - s) :=
    ⟨hs.1.one_sub, fun a => (Commute.one_left a).sub_left (hs.2 a)⟩
  have hpz : p ≤ 1 - s := (hp.1.le_iff_mul_eq_right hs.1.one_sub).mpr
    (by rw [sub_mul, one_mul, hsp, sub_zero])
  refine ⟨1 - s, ⟨hzc, ?_⟩, hpz, ?_⟩
  · intro c hc hcz hc0
    have hcp : IsStarProjection (c * p) := hc.1.mul hp.1 (hc.2 p)
    have hcpp : c * p ≤ p := (hcp.le_iff_mul_eq_left hp.1).mpr
      (by rw [mul_assoc, hp.1.isIdempotentElem.eq])
    have hcpc : c * p ≤ c := (hcp.le_iff_mul_eq_right hc.1).mpr
      (by rw [← mul_assoc, hc.1.isIdempotentElem.eq])
    refine ⟨c * p, HochschildTypeII.abelian_of_le hp hcp hcpp, hcpc, ?_⟩
    intro hzero
    have hsc := HochschildTypeII.projection_orthogonal_of_le_complement hs.1 hc.1 hcz
    have hnew : s + c ∈ S := ⟨⟨hs.1.add hc.1 hsc,
      fun a => (hs.2 a).add_left (hc.2 a)⟩,
      by rw [add_mul, hsp, hzero, zero_add]⟩
    have hle : s ≤ s + c := le_add_of_nonneg_right hc.1.nonneg
    have he := le_antisymm (hmax.2 hnew hle) hle
    exact hc0 (add_eq_left.mp he)
  · intro he
    exact hp0 (le_antisymm (he ▸ hpz) hp.1.nonneg)

end KadisonRingrose
end BoundedHochschild

end

end OAI
