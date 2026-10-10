import OAI.Analysis.BoundedHochschild.CentralSupportRows

namespace OAI

/-! Complete the row covering a central support by the complementary central
projection. The resulting row has square sum one in the given predual. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def centralSupportRow (z : M) (S : Set (PartialIso M)) : Option S → M
  | none => 1 - z
  | some v => star (v.val : M)

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralSupportRow_square (z : M) (hz : IsStarProjection z)
    (S : Set (PartialIso M)) (i : Option S) :
    centralSupportRow z S i * star (centralSupportRow z S i) =
      Option.elim i (1 - z) (fun v => v.val.initial) := by
  cases i with
  | none =>
      change (1 - z) * star (1 - z) = 1 - z
      rw [hz.one_sub.isSelfAdjoint.star_eq, hz.one_sub.isIdempotentElem.eq]
  | some v => simp only [centralSupportRow, star_star, PartialIso.initial, Option.elim_some]

theorem centralSupportRow_normalized (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {z : M} (hz : IsStarProjection z) (S : Set (PartialIso M))
    (hvz : ∀ v ∈ S, v.initial ≤ z)
    (horth : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → v.initial * w.initial = 0)
    (ht : PredualTendsto e (fun s : Finset S => ∑ v ∈ s, v.val.initial) atTop z) :
    (∀ s : Finset (Option S),
      ∑ i ∈ s, centralSupportRow z S i * star (centralSupportRow z S i) ≤ 1) ∧
    PredualTendsto e (fun s : Finset (Option S) =>
      ∑ i ∈ s, centralSupportRow z S i * star (centralSupportRow z S i)) atTop 1 := by
  classical
  let q : Option S → M := fun i => Option.elim i (1 - z) (fun v => v.val.initial)
  have hq (i : Option S) : IsStarProjection (q i) := by
    cases i with
    | none => exact hz.one_sub
    | some v => exact v.val.initial_proj
  have ho (i j : Option S) (hij : i ≠ j) : q i * q j = 0 := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some v =>
        change (1 - z) * v.val.initial = 0
        rw [sub_mul, one_mul, (v.val.initial_proj.le_iff_mul_eq_right hz).mp
          (hvz v v.property), sub_self]
    | some v =>
      cases j with
      | none =>
        change v.val.initial * (1 - z) = 0
        rw [mul_sub, mul_one, (v.val.initial_proj.le_iff_mul_eq_left hz).mp
          (hvz v v.property), sub_self]
      | some w =>
          exact horth v v.property w w.property
            (fun h => hij (congrArg some (Subtype.ext h)))
  obtain ⟨Q, hQ, hiQ, _, htQ⟩ := exists_orthogonal_projection_sum e q hq ho
  have hzQ : z ≤ Q := by
    apply (hz.le_iff_mul_eq_left hQ).mpr
    have hh := orthogonal_projection_sum_annihilator e (fun v : S => v.val.initial)
      (1 - Q) z ht (fun v => by
        rw [mul_sub, mul_one, (v.val.initial_proj.le_iff_mul_eq_left hQ).mp
          (hiQ (some v)), sub_self])
    rw [mul_sub, mul_one, sub_eq_zero] at hh
    exact hh.symm
  have hQ1 : Q = 1 := by
    have hzfix := (hz.le_iff_mul_eq_right hQ).mp hzQ
    have hcfix := (hz.one_sub.le_iff_mul_eq_right hQ).mp (hiQ none)
    have he : Q * (z + (1 - z)) = z + (1 - z) := by rw [mul_add, hzfix, hcfix]
    simpa only [add_sub_cancel, mul_one] using he
  have he (i : Option S) := centralSupportRow_square z hz S i
  constructor
  · intro s
    simpa only [he] using (orthogonal_projection_finset_sum q hq ho s).le_one
  · simpa only [he, hQ1] using htQ

end BoundedHochschild.KadisonRingrose

end

end OAI
