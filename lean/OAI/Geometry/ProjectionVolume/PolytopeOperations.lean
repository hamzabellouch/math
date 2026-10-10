import OAI.Geometry.ProjectionVolume.PolytopeDefinitions

namespace OAI

universe uι uκ

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section
namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

def reindex (P : HPolytope d ι) (e : κ ≃ ι) : HPolytope d κ where
  normal i := P.normal (e i)
  offset i := P.offset (e i)
  normal_unit i := P.normal_unit (e i)
  compact := by
    convert P.compact using 1
    ext x
    constructor
    · intro h i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact h j
    · intro h j
      exact h (e j)
  strict_feasible := by
    obtain ⟨x, hx⟩ := P.strict_feasible
    exact ⟨x, fun i => hx (e i)⟩
  distinct := fun i j h => e.injective (P.distinct h)

theorem reindex_body (P : HPolytope d ι) (e : κ ≃ ι) :
    (P.reindex e).body = P.body := by
  ext x
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact h j
  · intro h j
    exact h (e j)

def translate (P : HPolytope d ι) (v : Euclidean d) : HPolytope d ι where
  normal := P.normal
  offset i := P.offset i + ⟪P.normal i, v⟫
  normal_unit := P.normal_unit
  compact := by
    have heq : {x : Euclidean d | ∀ i, ⟪P.normal i, x⟫ ≤ P.offset i + ⟪P.normal i, v⟫} =
        (fun x => v + x) '' P.body := by
      ext x
      constructor
      · intro hx
        refine ⟨x - v, ?_, by abel_nf⟩
        intro i
        have := hx i
        simpa only [inner_sub_right, sub_le_iff_le_add] using this
      · rintro ⟨x, hx, rfl⟩ i
        simpa only [inner_add_right, add_comm] using add_le_add_right (hx i) ⟪P.normal i, v⟫
    rw [heq]
    exact P.compact.image (continuous_const.add continuous_id)
  strict_feasible := by
    obtain ⟨x, hx⟩ := P.strict_feasible
    refine ⟨v + x, fun i => ?_⟩
    simpa only [inner_add_right, add_comm] using add_lt_add_right (hx i) ⟪P.normal i, v⟫
  distinct := by
    intro i j h
    apply P.distinct
    have hn := congrArg Prod.fst h
    have ho := congrArg Prod.snd h
    dsimp at hn ho
    exact Prod.ext hn (by simpa only [hn, add_left_inj] using ho)

theorem translate_body (P : HPolytope d ι) (v : Euclidean d) :
    (P.translate v).body = v +ᵥ P.body := by
  ext x
  constructor
  · intro hx
    refine ⟨x - v, ?_, by dsimp; abel_nf⟩
    intro i
    have h := hx i
    change ⟪P.normal i, x⟫ ≤ P.offset i + ⟪P.normal i, v⟫ at h
    simpa only [inner_sub_right, sub_le_iff_le_add] using h
  · rintro ⟨x, hx, rfl⟩ i
    change ⟪P.normal i, v + x⟫ ≤ P.offset i + ⟪P.normal i, v⟫
    simpa only [inner_add_right, add_comm] using add_le_add_right (hx i) ⟪P.normal i, v⟫

end Paper092.HPolytope

end

end OAI
