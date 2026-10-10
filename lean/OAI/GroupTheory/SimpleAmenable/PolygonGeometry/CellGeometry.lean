import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowCellPartition

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CellGeometry

theorem coordinateInterval_union {a : ℕ} (j : Fin 2) (u v w : CutRing)
    (huv : ordinary u ≤ ordinary v) (hvw : ordinary v ≤ ordinary w)
    (hlen : ordinary w-ordinary u < 1) :
    coordinateInterval a j u w = coordinateInterval a j u v ⊔ coordinateInterval a j v w := by
  apply Subtype.ext
  ext p
  change p ∈ coordinateBetween a j u w ↔ p ∈ coordinateBetween a j u v ∨ p ∈ coordinateBetween a j v w
  rw [mem_coordinateBetween_iff j u w (huv.trans hvw) hlen,
    mem_coordinateBetween_iff j u v huv (by linarith),
    mem_coordinateBetween_iff j v w hvw (by linarith)]
  constructor
  · rintro ⟨k,hk,hk'⟩
    by_cases hh : coordinate j p+(k:ℝ) < ordinary v
    · exact Or.inl ⟨k,hk,hh⟩
    · exact Or.inr ⟨k,le_of_not_gt hh,hk'⟩
  · rintro (⟨k,hk,hk'⟩|⟨k,hk,hk'⟩)
    · exact ⟨k,hk,hk'.trans_le hvw⟩
    · exact ⟨k,huv.trans hk,hk'⟩

theorem coordinateInterval_nonempty {a : ℕ} (j : Fin 2) (u v : CutRing)
    (huv : ordinary u < ordinary v) (hlen : ordinary v-ordinary u < 1) :
    (coordinateInterval a j u v).val.Nonempty := by
  have hd : 0 < ordinary v-ordinary u := sub_pos.mpr huv
  have hp : ∃ p : GenericSquare a, coordinate j p < ordinary v-ordinary u := by
    fin_cases j
    · obtain ⟨p,hp,_⟩ := generic_rectangle a 0 (ordinary v-ordinary u) 0 1
        (by norm_num) hlen.le hd (by norm_num) (by norm_num) (by norm_num)
      exact ⟨p,hp.2⟩
    · obtain ⟨p,_,hp⟩ := generic_rectangle a 0 1 0 (ordinary v-ordinary u)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlen.le hd
      exact ⟨p,hp.2⟩
  obtain ⟨p,hp⟩ := hp
  refine ⟨translate a (coordinateShift j u) p,?_⟩
  change translate a (-coordinateShift j u) (translate a (coordinateShift j u) p) ∈ coordinateArc a j (v-u)
  rw [← translate_add,neg_add_cancel,translate_zero]
  change coordinate j p < Int.fract (ordinary (v-u))
  rw [map_sub,Int.fract_eq_self.mpr ⟨hd.le,hlen⟩]
  exact hp

theorem windowCell_nonempty {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ) (i : Fin n) :
    (windowCell a j n q i).val.Nonempty := by
  apply coordinateInterval_nonempty
  · exact windowCut_strictMono n q (Fin.castSucc_lt_succ (i := i))
  · have hn' : (200:ℝ) < n := by exact_mod_cast (by omega : 200 < n)
    exact (windowCut_mesh n q i).trans_lt ((div_lt_one (by linarith)).mpr hn')

theorem windowCell_axis_resolved {a : ℕ} {r : CutRing} (j : Fin 2) (n : ℕ) (hn : 0 < n) (q : ℤ) (i : Fin n) :
    ResolvedBy (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j n q) z).val) (windowCell a j n q i).val :=
  axisInterval_resolved j n q _ _ (windowCut_label n q hn i.castSucc) (windowCut_label n q hn i.succ)

end CellGeometry

end SimpleAmenable
end
end

end OAI
