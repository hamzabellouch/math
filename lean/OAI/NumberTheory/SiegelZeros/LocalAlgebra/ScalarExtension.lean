import OAI.NumberTheory.SiegelZeros.Determinants.DeterminantBridge

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W30

open Matrix Module

variable {K L : Type*} [Field K] [Field L]
variable {n : Type*} [Fintype n] [DecidableEq n]

def coordinateMap (f : K →+* L) : (n → K) →ₛₗ[f] (n → L) where
  toFun v := fun j => f (v j)
  map_add' x y := by ext j; exact f.map_add _ _
  map_smul' a x := by ext j; exact f.map_mul _ _

theorem independent_coordinateMap {ι : Type*} (f : K →+* L)
    (v : ι → n → K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i j => f (v i j)) := by
  classical
  let b := Basis.extend hv.linearIndepOn_id
  let basisIndexFintype := FiniteDimensional.fintypeBasisIndex b
  have hc := (Module.finrank_eq_card_basis b).symm.trans
    (Module.finrank_pi K (ι := n))
  let e := Fintype.equivOfCardEq hc
  let b' : Basis n K (n → K) := b.reindex e
  let a : ι → (hv.linearIndepOn_id.extend (Set.subset_univ _)) :=
    fun i => ⟨v i, Basis.subset_extend hv.linearIndepOn_id ⟨i, rfl⟩⟩
  have ha : Function.Injective a := by
    intro i j hij
    apply hv.injective
    exact congrArg Subtype.val hij
  have hfull : LinearIndependent L (fun i j => f (b' i j)) :=
    (independent_rows_map_iff f (fun i j => b' i j)).mpr b'.linearIndependent
  have hsub := hfull.comp (fun i => e (a i)) (e.injective.comp ha)
  simpa [b', b, a, Module.Basis.reindex_apply, Module.Basis.extend_apply_self,
    Function.comp_def] using hsub

theorem finrank_span_coordinateMap (f : K →+* L) {ι : Type*}
    (v : ι → n → K) :
    Module.finrank L (Submodule.span L (Set.range (fun i j => f (v i j)))) =
      Module.finrank K (Submodule.span K (Set.range v)) := by
  classical
  let S := Submodule.span K (Set.range v)
  let b := Basis.ofVectorSpace K S
  let basisIndexFintype := FiniteDimensional.fintypeBasisIndex b
  let w := fun i => ((b i : S) : n → K)
  have hw : LinearIndependent K w :=
    b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hwspan : Submodule.span K (Set.range w) = S := by
    have h := congrArg (Submodule.map S.subtype) b.span_eq
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.map_top, Submodule.range_subtype, Submodule.subtype_apply, w] using h
  have hfw := independent_coordinateMap f w hw
  have heq : Submodule.span L (Set.range (fun i j => f (w i j))) =
      Submodule.span L (Set.range (fun i j => f (v i j))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.mapsTo_span (f := coordinateMap f)
        (s := Set.range v) (t := Set.range (fun i j => f (v i j)))
      · rintro _ ⟨j, rfl⟩
        exact ⟨j, rfl⟩
      · exact (b i).property
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.mapsTo_span (f := coordinateMap f)
        (s := Set.range w) (t := Set.range (fun i j => f (w i j)))
      · rintro _ ⟨j, rfl⟩
        exact ⟨j, rfl⟩
      · rw [hwspan]
        exact Submodule.subset_span ⟨i, rfl⟩
  rw [← heq]
  exact (_root_.finrank_span_eq_card hfw).trans (Module.finrank_eq_card_basis b).symm

theorem matrix_rank_map (f : K →+* L) {m : Type*} [Fintype m]
    (A : Matrix m n K) : (A.map f).rank = A.rank := by
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  exact finrank_span_coordinateMap f A.row

end SiegelZerosAwei.W30

end

end SiegelZeros

end OAI
