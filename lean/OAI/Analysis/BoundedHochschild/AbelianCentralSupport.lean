import OAI.Analysis.BoundedHochschild.TraceFreeComparison
import OAI.Analysis.BoundedHochschild.AbelianComparison
import OAI.Analysis.BoundedHochschild.TypeIICharacterization

namespace OAI

/-! Central support and comparison of abelian projections for type I reduction. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The central support of a projection, expressed by its central annihilators. -/
def IsCentralSupport (p z : M) : Prop :=
  CentralProjection z ∧ p ≤ z ∧
    ∀ c : M, CentralProjection c → c * p = 0 → c * z = 0

theorem exists_central_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) : ∃ z : M, IsCentralSupport p z := by
  classical
  let S : Set M := {s | CentralProjection s ∧ s * p = 0}
  have hzero : (0 : M) ∈ S :=
    ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, zero_mul _⟩
  obtain ⟨s, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain a ha => by
    obtain ⟨t, ht, htp, hu⟩ := central_annihilator_chain e p C hchain ⟨a, ha⟩
      (fun q hq => hC hq)
    exact ⟨t, ⟨ht, htp⟩, hu⟩) 0 hzero
  have hs := hm.1.1
  have hsp := hm.1.2
  let z := 1 - s
  have hz : CentralProjection z :=
    ⟨hs.1.one_sub, fun a => (Commute.one_left a).sub_left (hs.2 a)⟩
  refine ⟨z, hz, (hp.le_iff_mul_eq_right hz.1).mpr ?_, ?_⟩
  · change (1 - s) * p = p
    rw [sub_mul, one_mul, hsp, sub_zero]
  · intro c hc hcp
    let t := z * c
    have ht : CentralProjection t :=
      ⟨hz.1.mul hc.1 (hz.2 c), fun a => (hz.2 a).mul_left (hc.2 a)⟩
    have hst : s * t = 0 := by
      change s * ((1 - s) * c) = 0
      rw [← mul_assoc, hs.1.mul_one_sub_self, zero_mul]
    have htp : t * p = 0 := by
      change z * c * p = 0
      rw [mul_assoc, hcp, mul_zero]
    have hnew : s + t ∈ S :=
      ⟨⟨hs.1.add ht.1 hst, fun a => (hs.2 a).add_left (ht.2 a)⟩,
        by rw [add_mul, hsp, htp, zero_add]⟩
    have hle : s ≤ s + t := le_add_of_nonneg_right ht.1.nonneg
    have ht0 : t = 0 := add_eq_left.mp (le_antisymm (hm.2 hnew hle) hle)
    exact (hc.2 z).eq.trans ht0

theorem central_support_full (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p z r : M} (hp : IsStarProjection p) (hz : IsCentralSupport p z)
    (hr : IsStarProjection r) (hrz : r ≤ z) (hr0 : r ≠ 0) :
    ∃ a : M, p * a * r ≠ 0 := by
  by_contra hn
  push Not at hn
  have hrp (a : M) : r * a * p = 0 := by
    simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq,
      hr.isSelfAdjoint.star_eq, star_zero, mul_assoc] using congrArg star (hn (star a))
  obtain ⟨c, hc, hrc, hcp⟩ := exists_trace_free_central_separator e hr hp hrp
  have hcz := hz.2.2 c hc hcp
  have he : c * z * r = r := by
    rw [mul_assoc, (hr.le_iff_mul_eq_right hz.1.1).mp hrz,
      (hr.le_iff_mul_eq_right hc.1).mp hrc]
  rw [hcz, zero_mul] at he
  exact hr0 he.symm

theorem trace_free_abelian_subequivalent (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : AbelianProjection p) (hq : IsStarProjection q)
    (hfull : ∀ r : M, IsStarProjection r → r ≤ p → r ≠ 0 → ∃ a : M, q * a * r ≠ 0) :
    ∃ v : PartialIso M, v.initial = p ∧ v.final ≤ q := by
  classical
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hz : (0 : PartialIso M) ∈ S :=
    ⟨by simpa using hp.1.nonneg, by simpa using hq.nonneg⟩
  obtain ⟨v, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain a ha => by
    obtain ⟨w, hwp, hwq, hu⟩ := partialIso_chain_upper e hp.1 hq C hchain ⟨a, ha⟩
      (fun t ht => hC ht)
    exact ⟨w, ⟨hwp, hwq⟩, hu⟩) 0 hz
  have hvp := hm.1.1
  have hvq := hm.1.2
  have hr := (v.initial_proj.le_iff_sub hp.1).mp hvp
  have hs := (v.final_proj.le_iff_sub hq).mp hvq
  have hir : v.initial * (p - v.initial) = 0 := by
    rw [mul_sub, (v.initial_proj.le_iff_mul_eq_left hp.1).mp hvp,
      v.initial_proj.isIdempotentElem.eq, sub_self]
  have hvr (a : M) : v.final * a * (p - v.initial) = 0 := by
    have h := HochschildTypeII.abelian_orthogonal_mul hp v.initial_proj hr hvp
      (sub_le_self _ v.initial_proj.nonneg) hir (star (v : M) * a)
    calc
      _ = (v : M) * (v.initial * (star (v : M) * a) * (p - v.initial)) := by
        simp only [← mul_assoc, v.mul_initial, PartialIso.final]
      _ = 0 := by rw [h, mul_zero]
  refine ⟨v, ?_, hvq⟩
  by_contra hi
  obtain ⟨a, ha⟩ := hfull (p - v.initial) hr (sub_le_self _ v.initial_proj.nonneg)
    (sub_ne_zero.mpr (Ne.symm hi))
  have hba : (q - v.final) * a * (p - v.initial) ≠ 0 := by
    simpa only [sub_mul, hvr a, sub_zero] using ha
  obtain ⟨w, hw0, hwi, hwf⟩ := partialIso_of_nonzero_corner e hs hr
    ((q - v.final) * a * (p - v.initial)) hba
    (by rw [← mul_assoc, ← mul_assoc, hs.isIdempotentElem.eq])
    (by rw [mul_assoc, hr.isIdempotentElem.eq])
  have hio := HochschildCentralComparison.orthogonal_of_le_sub hp.1 v.initial_proj
    w.initial_proj hvp hwi
  have hfo := HochschildCentralComparison.orthogonal_of_le_sub hq v.final_proj
    w.final_proj hvq hwf
  have hnew : v.orthogonalSum w hio hfo ∈ S := by
    constructor
    · rw [PartialIso.orthogonalSum_initial]
      calc
        v.initial + w.initial ≤ v.initial + (p - v.initial) := add_le_add_right hwi _
        _ = p := by abel
    · rw [PartialIso.orthogonalSum_final]
      calc
        v.final + w.final ≤ v.final + (q - v.final) := add_le_add_right hwf _
        _ = q := by abel
  have hle := v.le_orthogonalSum w hio hfo
  have he := congrArg (fun t : PartialIso M => (t : M))
    (le_antisymm (hm.2 hnew hle) hle)
  exact hw0 (add_eq_left.mp he)

end KadisonRingrose
end BoundedHochschild

end

end OAI
