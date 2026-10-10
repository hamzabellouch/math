import OAI.Analysis.BoundedHochschild.TypeICentralSupport
import OAI.Analysis.BoundedHochschild.TraceFreeSeparation
import OAI.Analysis.BoundedHochschild.PartialIsoCornerEquivalence
import OAI.Analysis.BoundedHochschild.TraceFreeHalving

namespace OAI

/-!
# Type II structure without an assumed trace

A nonzero abelian projection has a central type I support, with the type I
condition tested on all subprojections. Thus absence of a type I central
part is equivalent to absence of abelian corners, before constructing a
trace. The projection-halving theorem can consequently use exactly the
type II hypothesis of the main application.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A nonzero abelian projection generates a nonzero central type I part. -/
theorem exists_typeICorner_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (hpa : PopaTypeII.AbelianProjection hp)
    (hp0 : p ≠ 0) :
    ∃ (z : M) (hz : IsStarProjection z), (∀ a : M, z * a = a * z) ∧
      p ≤ z ∧ z ≠ 0 ∧ PopaTypeII.TypeICorner hz := by
  classical
  let S : Set M := {s | CentralProjection s ∧ s * p = 0}
  have hzero : (0 : M) ∈ S :=
    ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, zero_mul _⟩
  obtain ⟨s, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨t, ht, htp, hu⟩ := central_annihilator_chain e p c hchain ⟨y, hy⟩
      (fun q hq => hc hq)
    exact ⟨t, ⟨ht, htp⟩, hu⟩) 0 hzero
  have hs : CentralProjection s := hmax.1.1
  have hsp : s * p = 0 := hmax.1.2
  have hz : IsStarProjection (1 - s) := hs.1.one_sub
  have hzc : ∀ a : M, (1 - s) * a = a * (1 - s) := by
    intro a
    exact ((Commute.one_left a).sub_left (hs.2 a)).eq
  have hpz : p ≤ 1 - s := (hp.le_iff_mul_eq_right hz).mpr
    (by rw [sub_mul, one_mul, hsp, sub_zero])
  refine ⟨1 - s, hz, hzc, hpz, ?_, ?_⟩
  · intro h
    exact hp0 (le_antisymm (h ▸ hpz) hp.nonneg)
  · intro q hq hqz hq0
    have hex : ∃ a : M, q * a * p ≠ 0 := by
      by_contra hn
      push Not at hn
      obtain ⟨r, hr, hqr, hrp⟩ := exists_trace_free_central_separator e hq hp hn
      let t := (1 - s) * r
      have ht : CentralProjection t :=
        ⟨hz.mul hr.1 (hzc r), fun a => (show Commute (1 - s) a from hzc a).mul_left (hr.2 a)⟩
      have hst : s * t = 0 := by
        dsimp [t]
        rw [← mul_assoc, hs.1.mul_one_sub_self, zero_mul]
      have htp : t * p = 0 := by
        dsimp [t]
        rw [mul_assoc, hrp, mul_zero]
      have hnew : s + t ∈ S :=
        ⟨⟨hs.1.add ht.1 hst, fun a => (hs.2 a).add_left (ht.2 a)⟩,
          by rw [add_mul, hsp, htp, zero_add]⟩
      have hle : s ≤ s + t := le_add_of_nonneg_right ht.1.nonneg
      have ht0 : t = 0 := add_eq_left.mp (le_antisymm (hmax.2 hnew hle) hle)
      have htq : t * q = q := by
        dsimp [t]
        rw [mul_assoc, (hq.le_iff_mul_eq_right hr.1).mp hqr,
          (hq.le_iff_mul_eq_right hz).mp hqz]
      exact hq0 (by simpa only [ht0, zero_mul] using htq.symm)
    obtain ⟨a, ha⟩ := hex
    obtain ⟨v, hv0, hvi, hvf⟩ := partialIso_of_nonzero_corner e hq hp (q * a * p) ha
      (by rw [← mul_assoc, ← mul_assoc, hq.isIdempotentElem.eq])
      (by rw [mul_assoc, hp.isIdempotentElem.eq])
    have hfinal0 : v.final ≠ 0 := by
      intro h
      apply hv0
      simpa only [h, zero_mul] using v.final_mul.symm
    exact ⟨v.final, v.final_proj, hvf, hfinal0,
      abelianProjection_partialIso v (abelian_projection_mono hp v.initial_proj hvi hpa)⟩

/-- The two type II hypotheses agree for every von Neumann algebra, without
a faithful normal trace hypothesis. -/
theorem noTypeICentralPart_iff_noAbelianCorners (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    PopaTypeII.NoTypeICentralPart M ↔ PopaTypeII.NoAbelianCorners M := by
  constructor
  · intro hM p hp hp0
    by_contra hn
    push Not at hn
    have hab : PopaTypeII.AbelianProjection hp := fun a b => hn a b
    obtain ⟨z, hz, hzc, _, hz0, hI⟩ := exists_typeICorner_support e hp hab hp0
    exact hM z hz (fun a => hzc a) hz0 hI
  · intro hM z hz _ hz0 hI
    obtain ⟨p, hp, _, hp0, hab⟩ := hI z hz le_rfl hz0
    obtain ⟨a, b, h⟩ := hM p hp hp0
    exact h (hab a b)

/-- Exact type II projection halving, before the finite trace is constructed. -/
theorem typeII_projection_halving (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hII : PopaTypeII.NoTypeICentralPart M) {p : M} (hp : IsStarProjection p) :
    ∃ v : PartialIso M, v.initial * v.final = 0 ∧ v.initial + v.final = p :=
  exists_trace_free_halving e ((noTypeICentralPart_iff_noAbelianCorners e).mp hII) hp

end KadisonRingrose
end BoundedHochschild

end

end OAI
