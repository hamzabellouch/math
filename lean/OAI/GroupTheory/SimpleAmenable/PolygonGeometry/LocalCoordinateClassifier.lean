import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowRectangles

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LocalCoordinateClassifier

theorem circular_interval_on_short_cell (t l u v : ℝ) (_ht : 0<t ∧ t<1)
    (_hlu : l≤u) (hmesh₁ : u-l<t) (hmesh₂ : u-l<1-t) :
    (∀ x, l≤x → x<u → Int.fract (x-v)<t) ∨
    (∀ x, l≤x → x<u → ¬ Int.fract (x-v)<t) ∨
    (∃ k : ℤ, l≤v+(k:ℝ)+t ∧ v+(k:ℝ)+t≤u ∧
      ∀ x, l≤x → x<u → (Int.fract (x-v)<t ↔ x<v+(k:ℝ)+t)) ∨
    (∃ k : ℤ, l≤v+(k:ℝ) ∧ v+(k:ℝ)≤u ∧
      ∀ x, l≤x → x<u → (Int.fract (x-v)<t ↔ v+(k:ℝ)≤x)) := by
  let k : ℤ := ⌊l-v⌋
  have hk : (k:ℝ)≤l-v ∧ l-v<(k:ℝ)+1 := ⟨Int.floor_le _,Int.lt_floor_add_one _⟩
  have hf (x : ℝ) (hl : v+(k:ℝ)≤x) (hu : x<v+(k:ℝ)+1) :
      Int.fract (x-v)=x-v-(k:ℝ) := by
    rw [Int.fract,Int.floor_eq_iff.mpr (show (k:ℝ)≤x-v ∧ x-v<(k:ℝ)+1 from
      ⟨by linarith,by linarith⟩)]
  by_cases hu : u≤v+(k:ℝ)+t
  · left
    intro x hxl hxu
    rw [hf x (by linarith [hk.1]) (by linarith [_ht.2])]
    linarith
  · by_cases hl : v+(k:ℝ)+t≤l
    · by_cases hu' : u≤v+(k:ℝ)+1
      · right; left
        intro x hxl hxu
        rw [hf x (by linarith [hk.1]) (by linarith)]
        linarith
      · right; right; right
        refine ⟨k+1,by push_cast; linarith [hk.2],by push_cast; linarith,?_⟩
        intro x hxl hxu
        by_cases hx : x<v+(k:ℝ)+1
        · rw [hf x (by linarith [hk.1]) hx]
          push_cast
          constructor <;> intro hh <;> linarith
        · have hx' : Int.fract (x-v)=x-v-((k:ℝ)+1) := by
            have he : ⌊x-v⌋=k+1 := Int.floor_eq_iff.mpr (by push_cast; constructor <;> linarith [hk.2,_ht.2])
            rw [Int.fract,he]
            push_cast
            rfl
          rw [hx']
          push_cast
          constructor <;> intro hh <;> linarith [hk.2]
    · right; right; left
      refine ⟨k,by linarith,by linarith,?_⟩
      intro x hxl hxu
      rw [hf x (by linarith [hk.1]) (by linarith)]
      constructor <;> intro hh <;> linarith

end LocalCoordinateClassifier

section ActualCoordinateClassifier

theorem translated_coordinate_fract {a : ℕ} (j : Fin 2) (u : CutRing × CutRing)
    (p : GenericSquare a) (z : ℝ × ℝ) (hz : p.val=(Int.fract z.1,Int.fract z.2)) :
    p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
      Int.fract (realCoordinate z j-ordinary (pointCoordinate u j))<Real.goldenRatio-1 := by
  have ht := translate_planar_lift p z hz (-u)
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg] at ht
  have hc : coordinate j (translate a (-u) p)=
      Int.fract (realCoordinate z j-ordinary (pointCoordinate u j)) := by
    fin_cases j
    · exact congrArg Prod.fst ht
    · exact congrArg Prod.snd ht
  change (cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary (cutTau-1) ∧
    ¬cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary 0) ↔ _
  have hform : cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val=
      coordinate j (translate a (-u) p) := by fin_cases j <;> rfl
  simp only [hform,map_sub,ordinary_cutTau,map_one,map_zero,not_lt,
    hc,Int.fract_nonneg,and_true]

theorem windowRectangle_coordinate_classify {a : ℕ} (n : ℕ) (hn : 201≤n)
    (hmesh₁ : 200/(n:ℝ)<Real.goldenRatio-1) (hmesh₂ : 200/(n:ℝ)<2-Real.goldenRatio)
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n) (j : Fin 2) (u : CutRing × CutRing) :
    (∀ p ∈ (windowRectangle a n q cell).val,
      p ∈ (spatialTranslate u (coordinatePrimitive a j)).val) ∨
    (∀ p ∈ (windowRectangle a n q cell).val,
      p ∉ (spatialTranslate u (coordinatePrimitive a j)).val) ∨
    (∃ b : CutRing, ordinary (windowCut n (q j) (cell j).castSucc)≤ordinary b ∧
      ordinary b≤ordinary (windowCut n (q j) (cell j).succ) ∧
      ∀ p ∈ (windowRectangle a n q cell).val,
        (p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
          realCoordinate (windowPlanarLift q p) j<ordinary b)) ∨
    (∃ b : CutRing, ordinary (windowCut n (q j) (cell j).castSucc)≤ordinary b ∧
      ordinary b≤ordinary (windowCut n (q j) (cell j).succ) ∧
      ∀ p ∈ (windowRectangle a n q cell).val,
        (p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
          ordinary b≤realCoordinate (windowPlanarLift q p) j)) := by
  have hh := circular_interval_on_short_cell (Real.goldenRatio-1)
    (ordinary (windowCut n (q j) (cell j).castSucc))
    (ordinary (windowCut n (q j) (cell j).succ)) (ordinary (pointCoordinate u j))
    ⟨by linarith [Real.one_lt_goldenRatio],by linarith [Real.goldenRatio_lt_two]⟩
    (windowCut_strictMono n (q j) (Fin.castSucc_lt_succ (i := cell j))).le
    ((windowCut_mesh n (q j) (cell j)).trans_lt hmesh₁)
    (by have h := (windowCut_mesh n (q j) (cell j)).trans_lt hmesh₂; linarith)
  rcases hh with h | h | ⟨k,hk,hk',h⟩ | ⟨k,hk,hk',h⟩
  · left
    intro p hp
    rw [translated_coordinate_fract j u p _ (windowPlanarLift_spec q p)]
    have hb := (windowRectangle_mem n hn q cell p).mp hp j
    exact h _ hb.1 hb.2
  · right; left
    intro p hp
    rw [translated_coordinate_fract j u p _ (windowPlanarLift_spec q p)]
    have hb := (windowRectangle_mem n hn q cell p).mp hp j
    exact h _ hb.1 hb.2
  · right; right; left
    refine ⟨pointCoordinate u j+(k:CutRing)+(cutTau-1),?_,?_,?_⟩
    · simpa only [map_add,map_sub,map_intCast,ordinary_cutTau,map_one] using hk
    · simpa only [map_add,map_sub,map_intCast,ordinary_cutTau,map_one] using hk'
    · intro p hp
      rw [translated_coordinate_fract j u p _ (windowPlanarLift_spec q p)]
      have hb := (windowRectangle_mem n hn q cell p).mp hp j
      simpa only [map_add,map_sub,map_intCast,ordinary_cutTau,map_one] using h _ hb.1 hb.2
  · right; right; right
    refine ⟨pointCoordinate u j+(k:CutRing),?_,?_,?_⟩
    · simpa only [map_add,map_intCast] using hk
    · simpa only [map_add,map_intCast] using hk'
    · intro p hp
      rw [translated_coordinate_fract j u p _ (windowPlanarLift_spec q p)]
      have hb := (windowRectangle_mem n hn q cell p).mp hp j
      simpa only [map_add,map_intCast] using h _ hb.1 hb.2

end ActualCoordinateClassifier

section WindowEndpointConstancy

theorem window_cell_interval_constant (n : ℕ) (q : ℤ) (cell : Fin n)
    (b e : CutRing) (hbe : 0<ordinary e-ordinary b ∧ ordinary e-ordinary b<1)
    (hb : q≤endpointLabel b ∧ endpointLabel b<q+n)
    (he : q≤endpointLabel e ∧ endpointLabel e<q+n)
    (hmesh₁ : 200/(n:ℝ)<ordinary e-ordinary b)
    (hmesh₂ : 200/(n:ℝ)<1-(ordinary e-ordinary b)) :
    ∀ x y : ℝ,
      ordinary (windowCut n q cell.castSucc)≤x → x<ordinary (windowCut n q cell.succ) →
      ordinary (windowCut n q cell.castSucc)≤y → y<ordinary (windowCut n q cell.succ) →
      (Int.fract (x-ordinary b)<ordinary e-ordinary b ↔
        Int.fract (y-ordinary b)<ordinary e-ordinary b) := by
  let l := ordinary (windowCut n q cell.castSucc)
  let u := ordinary (windowCut n q cell.succ)
  have hclass := circular_interval_on_short_cell (ordinary e-ordinary b) l u (ordinary b)
    hbe (windowCut_strictMono n q (Fin.castSucc_lt_succ (i := cell))).le
    ((windowCut_mesh n q cell).trans_lt hmesh₁) ((windowCut_mesh n q cell).trans_lt hmesh₂)
  have hn (z : CutRing) (hz : q≤endpointLabel z ∧ endpointLabel z<q+n) (k : ℤ) :
      ¬(l<ordinary z+(k:ℝ) ∧ ordinary z+(k:ℝ)<u) := by
    have hl : endpointLabel (z+(k:CutRing))=endpointLabel z := by simp [endpointLabel_add]
    simpa only [map_add,map_intCast] using windowCut_no_between n q cell (z+(k:CutRing)) (by rwa [hl])
  intro x y hxl hxu hyl hyu
  rcases hclass with h | h | ⟨k,hkl,hku,h⟩ | ⟨k,hkl,hku,h⟩
  · exact iff_of_true (h _ hxl hxu) (h _ hyl hyu)
  · exact iff_of_false (h _ hxl hxu) (h _ hyl hyu)
  · rw [h x hxl hxu,h y hyl hyu]
    have hkn := hn e he k
    by_cases hh : ordinary e+(k:ℝ)≤l
    · constructor <;> intro hx <;> linarith
    · have hu : u≤ordinary e+(k:ℝ) := by
        by_contra hu
        exact hkn ⟨by linarith,by linarith⟩
      exact iff_of_true (by linarith) (by linarith)
  · rw [h x hxl hxu,h y hyl hyu]
    have hkn := hn b hb k
    by_cases hh : ordinary b+(k:ℝ)≤l
    · exact iff_of_true (by linarith) (by linarith)
    · have hu : u≤ordinary b+(k:ℝ) := by
        by_contra hu
        exact hkn ⟨by linarith,by linarith⟩
      constructor <;> intro hx <;> linarith

theorem coordinateInterval_planar {a : ℕ} (j : Fin 2) (b e : CutRing)
    (hbe : 0≤ordinary e-ordinary b ∧ ordinary e-ordinary b<1)
    (p : GenericSquare a) (z : ℝ × ℝ) (hz : p.val=(Int.fract z.1,Int.fract z.2)) :
    p ∈ (coordinateInterval a j b e).val ↔
      Int.fract (realCoordinate z j-ordinary b)<ordinary e-ordinary b := by
  change coordinate j (translate a (-coordinateShift j b) p)<Int.fract (ordinary (e-b)) ↔ _
  rw [← coordinateShift_neg,coordinate_translate,map_neg,map_sub,Int.fract_eq_self.mpr hbe]
  have hc : coordinate j p=Int.fract (realCoordinate z j) := by
    fin_cases j
    · exact congrArg Prod.fst hz
    · exact congrArg Prod.snd hz
  simp only [hc,sub_eq_add_neg,fract_fract_add_eq]

theorem windowRectangle_interval_constant {a : ℕ} (n : ℕ) (hn : 201≤n)
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n) (j : Fin 2) (b e : CutRing)
    (hbe : 0<ordinary e-ordinary b ∧ ordinary e-ordinary b<1)
    (hb : q j≤endpointLabel b ∧ endpointLabel b<q j+n)
    (he : q j≤endpointLabel e ∧ endpointLabel e<q j+n)
    (hmesh₁ : 200/(n:ℝ)<ordinary e-ordinary b)
    (hmesh₂ : 200/(n:ℝ)<1-(ordinary e-ordinary b))
    (p t : GenericSquare a) (hp : p ∈ (windowRectangle a n q cell).val)
    (ht : t ∈ (windowRectangle a n q cell).val) :
    p ∈ (coordinateInterval a j b e).val ↔ t ∈ (coordinateInterval a j b e).val := by
  rw [coordinateInterval_planar j b e ⟨hbe.1.le,hbe.2⟩ p _ (windowPlanarLift_spec q p),
    coordinateInterval_planar j b e ⟨hbe.1.le,hbe.2⟩ t _ (windowPlanarLift_spec q t)]
  have hp' := (windowRectangle_mem n hn q cell p).mp hp j
  have ht' := (windowRectangle_mem n hn q cell t).mp ht j
  exact window_cell_interval_constant n (q j) (cell j) b e hbe hb he hmesh₁ hmesh₂ _ _
    hp'.1 hp'.2 ht'.1 ht'.2

end WindowEndpointConstancy

end SimpleAmenable
end
end

end OAI
