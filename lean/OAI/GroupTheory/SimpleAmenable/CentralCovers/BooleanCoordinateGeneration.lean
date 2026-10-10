import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrackTranslationChart

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BooleanCoordinateGeneration

noncomputable def coordinate {a : ℕ} (j : Fin 2) (p : GenericSquare a) : ℝ :=
  ![p.val.1,p.val.2] j

noncomputable def coordinateShift (j : Fin 2) (z : CutRing) : CutRing × CutRing :=
  if j = 0 then (z,0) else (0,z)

theorem coordinate_bounds {a : ℕ} (j : Fin 2) (p : GenericSquare a) :
    0 ≤ coordinate j p ∧ coordinate j p < 1 := by
  fin_cases j
  · exact p.property.1
  · exact p.property.2.1

theorem coordinate_translate {a : ℕ} (j : Fin 2) (z : CutRing) (p : GenericSquare a) :
    coordinate j (translate a (coordinateShift j z) p) =
      Int.fract (coordinate j p + ordinary z) := by
  fin_cases j <;> simp [coordinate,coordinateShift,translate_val]

noncomputable def coordinateArc (a : ℕ) (j : Fin 2) (z : CutRing) : Set (GenericSquare a) :=
  {p | coordinate j p < Int.fract (ordinary z)}

private theorem fract_sub_unit {x u : ℝ} (hx : 0 ≤ x ∧ x < 1)
    (hu : 0 ≤ u ∧ u < 1) :
    Int.fract (x-u) = if x < u then x-u+1 else x-u := by
  split_ifs with h
  · have hf : ⌊x-u⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith,by norm_num; linarith⟩
    simp only [Int.fract,hf,Int.cast_neg,Int.cast_one]
    ring
  · exact Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩

private theorem fract_sum_unit {u v : ℝ} (hu : 0 ≤ u ∧ u < 1)
    (hv : 0 ≤ v ∧ v < 1) :
    Int.fract (u+v) = if u+v < 1 then u+v else u+v-1 := by
  split_ifs with h
  · exact Int.fract_eq_self.mpr ⟨by linarith,h⟩
  · have hf : ⌊u+v⌋ = (1 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith,by norm_num; linarith⟩
    simp [Int.fract,hf]

private theorem arc_add_test (x u v : ℝ) (hx : 0 ≤ x ∧ x < 1)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) :
    (x < Int.fract (u+v)) ↔
      if u+v < 1 then Xor (x < u) (Int.fract (x-u) < v)
      else ¬ Xor (x < u) (Int.fract (x-u) < v) := by
  rw [fract_sum_unit hu hv,fract_sub_unit hx hu]
  by_cases hs : u+v < 1 <;> by_cases hxu : x < u <;>
    simp only [hs,hxu,ite_true,ite_false,Xor,true_and,false_and,false_or,
      not_true_eq_false,not_false_eq_true,and_true,and_false,or_false,not_lt] <;>
    constructor <;> intro h <;> linarith

private theorem fract_add_fracts (x y : ℝ) :
    Int.fract (Int.fract x + Int.fract y) = Int.fract (x+y) := by
  rw [fract_fract_add]
  change Int.fract (x+(y-(⌊y⌋ : ℝ))) = _
  rw [← add_sub_assoc,Int.fract_sub_intCast]

private theorem fract_sub_fract (x y : ℝ) :
    Int.fract (x-Int.fract y) = Int.fract (x-y) := by
  change Int.fract (x-(y-(⌊y⌋ : ℝ))) = _
  rw [sub_sub_eq_add_sub,add_sub_right_comm,Int.fract_add_intCast]

theorem coordinateArc_add {a : ℕ} (j : Fin 2) (u v : CutRing) :
    coordinateArc a j (u+v) =
      if Int.fract (ordinary u)+Int.fract (ordinary v) < 1 then
        symmDiff (coordinateArc a j u)
          (translate a (coordinateShift j (-u)) ⁻¹' coordinateArc a j v)
      else (symmDiff (coordinateArc a j u)
          (translate a (coordinateShift j (-u)) ⁻¹' coordinateArc a j v))ᶜ := by
  ext p
  have hc := arc_add_test (coordinate j p) (Int.fract (ordinary u)) (Int.fract (ordinary v))
    (coordinate_bounds j p) ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
      ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  rw [fract_add_fracts,fract_sub_fract] at hc
  split_ifs with h
  · simpa only [coordinateArc,Set.mem_ofPred_eq,Set.mem_symmDiff,Set.mem_preimage,
      coordinate_translate,map_neg,map_add,sub_eq_add_neg,Xor,h,ite_true] using hc
  · simpa only [coordinateArc,Set.mem_ofPred_eq,Set.mem_compl_iff,Set.mem_symmDiff,
      Set.mem_preimage,coordinate_translate,map_neg,map_add,sub_eq_add_neg,Xor,h,ite_false] using hc

private theorem arc_neg_test (x u : ℝ) (hx : 0 ≤ x ∧ x < 1)
    (hu : 0 < u ∧ u < 1) :
    (x < 1-u) ↔ ¬ Int.fract (x+u) < u := by
  rw [fract_sum_unit hx ⟨hu.1.le,hu.2⟩]
  split_ifs <;> push Not <;> constructor <;> intro h <;> linarith

theorem coordinateArc_neg {a : ℕ} (j : Fin 2) (u : CutRing)
    (hu : Int.fract (ordinary u) ≠ 0) :
    coordinateArc a j (-u) =
      (translate a (coordinateShift j u) ⁻¹' coordinateArc a j u)ᶜ := by
  ext p
  simp only [coordinateArc,Set.mem_ofPred_eq,Set.mem_compl_iff,Set.mem_preimage,
    coordinate_translate,map_neg,Int.fract_neg hu]
  rw [← fract_fract_add (coordinate j p) (ordinary u)]
  rw [Int.fract_eq_self.mpr (coordinate_bounds j p)]
  have he : Int.fract (coordinate j p + ordinary u) =
      Int.fract (coordinate j p + Int.fract (ordinary u)) := by
    rw [← fract_add_fracts,Int.fract_eq_self.mpr (coordinate_bounds j p)]
  rw [he]
  exact arc_neg_test _ _ (coordinate_bounds j p)
    ⟨lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hu),Int.fract_lt_one _⟩

theorem coordinateArc_zero_of_fract {a : ℕ} (j : Fin 2) (u : CutRing)
    (hu : Int.fract (ordinary u) = 0) : coordinateArc a j u = ∅ := by
  ext p
  simp only [coordinateArc,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_lt,hu]
  exact (coordinate_bounds j p).1

theorem coordinate_cuts_generated {a : ℕ} (B : BooleanSubalgebra (Set (GenericSquare a)))
    (j : Fin 2) (htrans : ∀ u U, U ∈ B → translate a u ⁻¹' U ∈ B)
    (hprimitive : (coordinatePrimitive a j).val ∈ B) (z : CutRing) :
    halfPlane a (Fin.castLE (by omega) j) z ∈ B := by
  classical
  have hsymm {U V : Set (GenericSquare a)} (hU : U ∈ B) (hV : V ∈ B) :
      symmDiff U V ∈ B := by
    rw [Set.symmDiff_def]
    exact BooleanSubalgebra.sup_mem (BooleanSubalgebra.sdiff_mem hU hV)
      (BooleanSubalgebra.sdiff_mem hV hU)
  let H : AddSubgroup CutRing := {
    carrier := {u | coordinateArc a j u ∈ B}
    zero_mem' := by
      change coordinateArc a j 0 ∈ B
      rw [coordinateArc_zero_of_fract j 0 (by simp)]
      exact BooleanSubalgebra.bot_mem
    add_mem' := by
      intro u v hu hv
      change coordinateArc a j (u+v) ∈ B
      rw [coordinateArc_add]
      split_ifs
      · exact hsymm hu (htrans _ _ hv)
      · exact BooleanSubalgebra.compl_mem (hsymm hu (htrans _ _ hv))
    neg_mem' := by
      intro u hu
      change coordinateArc a j (-u) ∈ B
      by_cases hzero : Int.fract (ordinary u) = 0
      · have hh : Int.fract (ordinary (-u)) = 0 := by
          rw [map_neg,Int.fract_neg_eq_zero.mpr hzero]
        rw [coordinateArc_zero_of_fract j (-u) hh]
        exact BooleanSubalgebra.bot_mem
      · rw [coordinateArc_neg j u hzero]
        exact BooleanSubalgebra.compl_mem (htrans _ _ hu) }
  have hτ : cutTau ∈ H := by
    have hfloor : ⌊Real.goldenRatio⌋ = (1 : ℤ) :=
      Int.floor_eq_iff.mpr ⟨by norm_num; exact Real.one_lt_goldenRatio.le,by norm_num; exact Real.goldenRatio_lt_two⟩
    have he : coordinateArc a j cutTau = (coordinatePrimitive a j).val := by
      ext p
      have hp := (coordinate_bounds j p).1
      fin_cases j <;>
        simp [coordinateArc,coordinate,coordinatePrimitive,halfPlane,cutForm,
          Int.fract,hfloor,ordinary_cutTau] <;> intro _ <;> exact hp
    change coordinateArc a j cutTau ∈ B
    rw [he]
    exact hprimitive
  have hint (n : ℤ) : (n : CutRing) ∈ H := by
    change coordinateArc a j (n : CutRing) ∈ B
    rw [coordinateArc_zero_of_fract j _ (by simp)]
    exact BooleanSubalgebra.bot_mem
  have hall (u : CutRing) : coordinateArc a j u ∈ B := by
    have he : u = (u.re : CutRing) + u.im • cutTau := by
      apply QuadraticAlgebra.ext <;> simp [cutTau]
    change u ∈ H
    rw [he]
    exact H.add_mem (hint _) (H.zsmul_mem hτ _)
  have hcoord : ∀ p : GenericSquare a,
      cutForm a (Fin.castLE (by omega) j) p.val = coordinate j p := by
    intro p
    fin_cases j <;> rfl
  by_cases hz0 : ordinary z ≤ 0
  · have he : halfPlane a (Fin.castLE (by omega) j) z = ∅ := by
      ext p
      simp only [halfPlane,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_lt,hcoord]
      exact hz0.trans (coordinate_bounds j p).1
    rw [he]
    exact BooleanSubalgebra.bot_mem
  by_cases hz1 : 1 ≤ ordinary z
  · have he : halfPlane a (Fin.castLE (by omega) j) z = Set.univ := by
      ext p
      simp only [halfPlane,Set.mem_ofPred_eq,Set.mem_univ,iff_true,hcoord]
      exact (coordinate_bounds j p).2.trans_le hz1
    rw [he]
    exact BooleanSubalgebra.top_mem
  have he : halfPlane a (Fin.castLE (by omega) j) z = coordinateArc a j z := by
    ext p
    simp only [halfPlane,coordinateArc,Set.mem_ofPred_eq,hcoord,
      Int.fract_eq_self.mpr (show 0 ≤ ordinary z ∧ ordinary z < 1 by constructor <;> linarith)]
  rw [he]
  exact hall z

end BooleanCoordinateGeneration

end SimpleAmenable
end
end

end OAI
