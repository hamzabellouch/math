import OAI.Analysis.BoundedHochschild.PartialIsometryChains
import OAI.Analysis.TracialCohomology.TypeII

namespace OAI

/-!
# Halving projections without a trace

Orthogonality of initial and final projections is preserved by increasing
chains of partial isometries. A maximal such partial isometry exhausts any
projection in an algebra with no nonzero abelian corners.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The initial/final orthogonality condition is closed under chain suprema. -/
lemma orthogonal_partialIso_chain_upper (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ v ∈ c, v.initial ≤ p ∧ v.final ≤ p ∧ v.initial * v.final = 0) :
    ∃ w : PartialIso M, w.initial ≤ p ∧ w.final ≤ p ∧
      w.initial * w.final = 0 ∧ ∀ v ∈ c, v ≤ w := by
  obtain ⟨w, hu, _, hi, hf⟩ := exists_partialIso_chain_supremum e c hc hne
  have hcross (v : PartialIso M) (hv : v ∈ c) (z : PartialIso M) (hz : z ∈ c) :
      v.initial * z.final = 0 := by
    rcases hc.total hv hz with h | h
    · calc
        v.initial * z.final = (v.initial * z.initial) * z.final := by
          rw [(v.initial_proj.le_iff_mul_eq_left z.initial_proj).mp h.1]
        _ = 0 := by rw [mul_assoc, (hs z hz).2.2, mul_zero]
    · calc
        v.initial * z.final = v.initial * (v.final * z.final) := by
          rw [(z.final_proj.le_iff_mul_eq_right v.final_proj).mp
            (PartialIso.final_mono h)]
        _ = 0 := by rw [← mul_assoc, (hs v hv).2.2, zero_mul]
  have hwi (v : PartialIso M) (hv : v ∈ c) : w.initial * v.final = 0 := by
    have hb : w.initial ≤ 1 - v.final := hi _ v.final_proj.one_sub (fun z hz =>
      (z.initial_proj.le_iff_mul_eq_left v.final_proj.one_sub).mpr (by
        rw [mul_sub, mul_one, hcross z hz v hv, sub_zero]))
    have he := (w.initial_proj.le_iff_mul_eq_left v.final_proj.one_sub).mp hb
    rw [mul_sub, mul_one] at he
    exact sub_eq_self.mp he
  have hfinal : w.final ≤ 1 - w.initial := hf _ w.initial_proj.one_sub (fun v hv => by
    apply (v.final_proj.le_iff_mul_eq_left w.initial_proj.one_sub).mpr
    have ho : v.final * w.initial = 0 := by
      simpa only [star_mul, w.initial_proj.isSelfAdjoint.star_eq,
        v.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star (hwi v hv)
    rw [mul_sub, mul_one, ho, sub_zero])
  refine ⟨w, hi p hp (fun v hv => (hs v hv).1),
    hf p hp (fun v hv => (hs v hv).2.1), ?_, hu⟩
  have he := (w.final_proj.le_iff_mul_eq_right w.initial_proj.one_sub).mp hfinal
  rw [sub_mul, one_mul] at he
  exact sub_eq_self.mp he

/-- Every projection in a von Neumann algebra without abelian corners is the
sum of the orthogonal initial and final projections of a partial isometry. -/
theorem exists_trace_free_halving (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hII : PopaTypeII.NoAbelianCorners M) {p : M} (hp : IsStarProjection p) :
    ∃ v : PartialIso M, v.initial * v.final = 0 ∧ v.initial + v.final = p := by
  classical
  let S : Set (PartialIso M) :=
    {v | v.initial ≤ p ∧ v.final ≤ p ∧ v.initial * v.final = 0}
  have hz : (0 : PartialIso M) ∈ S :=
    ⟨by simpa using hp.nonneg, by simpa using hp.nonneg, by simp⟩
  obtain ⟨v, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨w, hwi, hwf, hwo, hu⟩ := orthogonal_partialIso_chain_upper e hp c hchain
      ⟨y, hy⟩ (fun z hz => hc hz)
    exact ⟨w, ⟨hwi, hwf, hwo⟩, hu⟩) 0 hz
  have hvi : v.initial ≤ p := hmax.1.1
  have hvf : v.final ≤ p := hmax.1.2.1
  have hvo : v.initial * v.final = 0 := hmax.1.2.2
  have hsum : IsStarProjection (v.initial + v.final) :=
    v.initial_proj.add v.final_proj hvo
  have hsump : v.initial + v.final ≤ p := by
    apply (hsum.le_iff_mul_eq_right hp).mpr
    rw [mul_add, (v.initial_proj.le_iff_mul_eq_right hp).mp hvi,
      (v.final_proj.le_iff_mul_eq_right hp).mp hvf]
  let r : M := p - (v.initial + v.final)
  have hr : IsStarProjection r := (hsum.le_iff_sub hp).mp hsump
  have hrI : r ≤ p - v.initial :=
    sub_le_sub_left (le_add_of_nonneg_right v.final_proj.nonneg) p
  have hrF : r ≤ p - v.final :=
    sub_le_sub_left (le_add_of_nonneg_left v.initial_proj.nonneg) p
  have hr0 : r = 0 := by
    by_contra hr0
    obtain ⟨u, huo, hu0⟩ := PopaTypeII.orthogonal_pair e hII hr hr0
    let U : PartialIso M := ⟨(u : M), by
      simpa only [← mul_assoc] using u.absorb⟩
    have hUi : U.initial ≤ r := u.init_le
    have hUf : U.final ≤ r := u.final_le
    have hUo : U.initial * U.final = 0 := huo
    have hi : v.initial * U.initial = 0 :=
      PopaCorners.CornerIso.projection_mul_zero_of_le_sub hp v.initial_proj U.initial_proj
        hvi (hUi.trans hrI)
    have hf : v.final * U.final = 0 :=
      PopaCorners.CornerIso.projection_mul_zero_of_le_sub hp v.final_proj U.final_proj
        hvf (hUf.trans hrF)
    have hiF : v.initial * U.final = 0 :=
      PopaCorners.CornerIso.projection_mul_zero_of_le_sub hp v.initial_proj U.final_proj
        hvi (hUf.trans hrI)
    have hfI : U.initial * v.final = 0 := by
      have h := PopaCorners.CornerIso.projection_mul_zero_of_le_sub hp v.final_proj U.initial_proj
        hvf (hUi.trans hrF)
      simpa only [star_mul, v.final_proj.isSelfAdjoint.star_eq,
        U.initial_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star h
    have hW : v.orthogonalSum U hi hf ∈ S := by
      constructor
      · rw [PartialIso.orthogonalSum_initial]
        calc
          v.initial + U.initial ≤ v.initial + (p - v.initial) :=
            add_le_add_right (hUi.trans hrI) _
          _ = p := by abel
      constructor
      · rw [PartialIso.orthogonalSum_final]
        calc
          v.final + U.final ≤ v.final + (p - v.final) :=
            add_le_add_right (hUf.trans hrF) _
          _ = p := by abel
      · rw [PartialIso.orthogonalSum_initial, PartialIso.orthogonalSum_final,
          add_mul, mul_add, mul_add, hvo, hiF, hfI, hUo, zero_add, add_zero]
    have hle := v.le_orthogonalSum U hi hf
    have heq := le_antisymm (hmax.2 hW hle) hle
    have he : (v : M) + (u : M) = v :=
      congrArg (fun z : PartialIso M => (z : M)) heq
    exact hu0 (add_eq_left.mp he)
  exact ⟨v, hvo, (sub_eq_zero.mp hr0).symm⟩

/-- Corner-isometry form of trace-free halving, matching the tracial API. -/
theorem trace_free_halve_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hII : PopaTypeII.NoAbelianCorners M) {p : M} (hp : IsStarProjection p) :
    ∃ v : PopaCorners.CornerIso p p, v.initial * v.final = 0 ∧
      v.initial + v.final = p := by
  obtain ⟨v, hvo, hsum⟩ := exists_trace_free_halving e hII hp
  have hi : v.initial ≤ p := hsum ▸ le_add_of_nonneg_right v.final_proj.nonneg
  have hf : v.final ≤ p := hsum ▸ le_add_of_nonneg_left v.initial_proj.nonneg
  exact ⟨⟨(v : M), v.initial_proj, v.mul_initial, hi, hf⟩, hvo, hsum⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
