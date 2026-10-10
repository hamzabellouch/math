import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ArithmeticTangentBasis
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TangentChartTemplates

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IntervalTangentConnectivity

def TangentIntervalStep (u : CutRing) (L H : ℝ) (x y : CutRing) : Prop :=
  L ≤ ordinary x ∧ ordinary x ≤ H ∧ L ≤ ordinary y ∧ ordinary y ≤ H ∧
    (y-x=u ∨ y-x= -u ∨ y-x=cutTau*u ∨ y-x= -(cutTau*u))

def TangentIntervalReach (u : CutRing) (L H : ℝ) (x y : CutRing) : Prop :=
  Relation.ReflTransGen (TangentIntervalStep u L H) x y

theorem tangentIntervalStep_symm {u x y : CutRing} {L H : ℝ}
    (h : TangentIntervalStep u L H x y) : TangentIntervalStep u L H y x := by
  rcases h with ⟨h1,h2,h3,h4,h⟩
  refine ⟨h3,h4,h1,h2,?_⟩
  have he : x-y= -(y-x) := by abel
  rw [he]
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl (congrArg Neg.neg h))
  · left; simpa using congrArg Neg.neg h
  · exact Or.inr (Or.inr (Or.inr (congrArg Neg.neg h)))
  · right; right; left; simpa using congrArg Neg.neg h

theorem tangentIntervalReach_symm {u x y : CutRing} {L H : ℝ}
    (h : TangentIntervalReach u L H x y) : TangentIntervalReach u L H y x := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.head (tangentIntervalStep_symm hstep)

theorem tangentIntervalStep_index {u x y : CutRing} {L H : ℝ}
    (h : TangentIntervalStep u L H x y) :
    ∃ e : Fin 5, y=x+signedShortSteps u e := by
  rcases h.2.2.2.2 with h | h | h | h
  · exact ⟨1,by change y=x+u; linear_combination h⟩
  · exact ⟨2,by change y=x+ -u; linear_combination h⟩
  · exact ⟨3,by change y=x+cutTau*u; linear_combination h⟩
  · exact ⟨4,by change y=x+ -(cutTau*u); linear_combination h⟩

theorem tangentInterval_natural (u v x : CutRing) (L H : ℝ) (n : ℕ)
    (hv : v=u ∨ v= -u)
    (hx : L ≤ ordinary x ∧ ordinary x ≤ H)
    (hy : L ≤ ordinary (x+(n:CutRing)*v) ∧ ordinary (x+(n:CutRing)*v) ≤ H) :
    TangentIntervalReach u L H x (x+(n:CutRing)*v) := by
  have hi (i : ℕ) (hin : i ≤ n) :
      L ≤ ordinary (x+(i:CutRing)*v) ∧ ordinary (x+(i:CutRing)*v) ≤ H := by
    have hi' : (i:ℝ) ≤ n := by exact_mod_cast hin
    simp only [map_add,map_mul,map_natCast] at hy ⊢
    by_cases hv0 : 0 ≤ ordinary v
    · have hm := mul_le_mul_of_nonneg_right hi' hv0
      have hp : 0 ≤ (i:ℝ)*ordinary v := mul_nonneg (Nat.cast_nonneg _) hv0
      constructor <;> linarith
    · have hm := mul_le_mul_of_nonpos_right hi' (le_of_not_ge hv0)
      have hp : (i:ℝ)*ordinary v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
        (Nat.cast_nonneg _) (le_of_not_ge hv0)
      constructor <;> linarith
  have hpath i (hin : i ≤ n) : TangentIntervalReach u L H x (x+(i:CutRing)*v) := by
    induction i with
    | zero => simpa [TangentIntervalReach] using (Relation.ReflTransGen.refl (a := x) (r := TangentIntervalStep u L H))
    | succ i ih =>
      apply (ih (by omega)).tail
      refine ⟨(hi i (by omega)).1,(hi i (by omega)).2,(hi (i+1) hin).1,(hi (i+1) hin).2,?_⟩
      have he : x+((i+1:ℕ):CutRing)*v-(x+(i:CutRing)*v)=v := by push_cast; ring
      rw [he]
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)
  exact hpath n le_rfl

theorem tangentInterval_integer (u v x : CutRing) (L H : ℝ) (n : ℤ)
    (hv : v=u ∨ v= -u)
    (hx : L ≤ ordinary x ∧ ordinary x ≤ H)
    (hy : L ≤ ordinary (x+(n:CutRing)*v) ∧ ordinary (x+(n:CutRing)*v) ≤ H) :
    TangentIntervalReach u L H x (x+(n:CutRing)*v) := by
  by_cases hn : 0 ≤ n
  · have he : (n.toNat:CutRing)=(n:CutRing) := by exact_mod_cast Int.toNat_of_nonneg hn
    simpa only [he] using tangentInterval_natural u v x L H n.toNat hv hx (by simpa only [he] using hy)
  · have hev : -v=u ∨ -v= -u := by
      rcases hv with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (neg_neg u)
    have he : ((-n).toNat:CutRing)= -(n:CutRing) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ -n)
    simpa only [he,neg_mul_neg] using tangentInterval_natural u (-v) x L H (-n).toNat hev hx
      (by simpa only [he,neg_mul_neg] using hy)

theorem tangentInterval_list (u x : CutRing) (L H : ℝ) (w : List CutRing)
    (hw : ∀ e ∈ w, e=u ∨ e= -u ∨ e=cutTau*u ∨ e= -(cutTau*u))
    (hb : ∀ n, L ≤ ordinary (x+(w.take n).sum) ∧ ordinary (x+(w.take n).sum) ≤ H) :
    TangentIntervalReach u L H x (x+w.sum) := by
  have hp n (hn : n ≤ w.length) : TangentIntervalReach u L H x (x+(w.take n).sum) := by
    induction n with
    | zero => simpa [TangentIntervalReach] using (Relation.ReflTransGen.refl (a := x) (r := TangentIntervalStep u L H))
    | succ n ih =>
      have hn' : n < w.length := by omega
      apply (ih (by omega)).tail
      refine ⟨(hb n).1,(hb n).2,(hb (n+1)).1,(hb (n+1)).2,?_⟩
      have he : x+(w.take (n+1)).sum-(x+(w.take n).sum)=w[n] := by
        rw [List.take_add_one,List.getElem?_eq_getElem hn',Option.toList_some,List.sum_append,List.sum_singleton]
        abel
      rw [he]
      exact hw _ (List.getElem_mem hn')
  simpa using hp w.length le_rfl

theorem tangentInterval_recenter (u v : CutRing) (huv : u*v=1)
    (L H c : ℝ) (x : CutRing) (hx : L ≤ ordinary x ∧ ordinary x ≤ H)
    (hL : L ≤ c-|ordinary u|) (hH : c ≤ H) :
    ∃ y : CutRing, c-|ordinary u| < ordinary y ∧ ordinary y ≤ c ∧
      TangentIntervalReach u L H x y := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at huv
  have huo : ordinary u ≠ 0 := by simpa using ordinary_injective.ne hu0
  let u' : CutRing := if 0 ≤ ordinary u then u else -u
  have hu' : u'=u ∨ u'= -u := by dsimp [u']; split <;> simp
  have hpos : ordinary u'=|ordinary u| := by
    dsimp [u']; split_ifs with h
    · exact (abs_of_nonneg h).symm
    · rw [map_neg,abs_of_neg (lt_of_not_ge h)]
  have hα : 0 < ordinary u' := by rw [hpos]; exact abs_pos.mpr huo
  let n : ℤ := ⌊(c-ordinary x)/ordinary u'⌋
  let y : CutRing := x+(n:CutRing)*u'
  have hny : c-ordinary u' < ordinary y ∧ ordinary y ≤ c := by
    have hl := Int.floor_le ((c-ordinary x)/ordinary u')
    have hh := Int.lt_floor_add_one ((c-ordinary x)/ordinary u')
    have hl' := (le_div_iff₀ hα).mp hl
    have hh' := (div_lt_iff₀ hα).mp hh
    dsimp only [y]
    simp only [map_add,map_mul,map_intCast]
    dsimp only [n] at *
    constructor <;> linarith
  refine ⟨y,by simpa only [hpos] using hny.1,hny.2,?_⟩
  exact tangentInterval_integer u u' x L H n hu' hx
    ⟨hL.trans (by rw [← hpos]; exact hny.1.le),hny.2.trans hH⟩

theorem tangentInterval_connected (u v : CutRing) (huv : u*v=1)
    (L H : ℝ) (hwidth : 4*(|ordinary u|+|ordinary (cutTau*u)|) ≤ H-L)
    (x y : CutRing)
    (hx : L ≤ ordinary x ∧ ordinary x ≤ H)
    (hy : L ≤ ordinary y ∧ ordinary y ≤ H) : TangentIntervalReach u L H x y := by
  let c : ℝ := (L+H)/2
  let b : ℝ := |ordinary u|+|ordinary (cutTau*u)|
  have hb : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hub : |ordinary u| ≤ b := le_add_of_nonneg_right (abs_nonneg _)
  have hlo : L ≤ c-|ordinary u| := by dsimp [c]; dsimp [b] at hub; linarith
  have hup : c ≤ H := by dsimp [c]; dsimp [b] at hb; linarith
  obtain ⟨x',hxL,hxH,hxx'⟩ := tangentInterval_recenter u v huv L H c x hx hlo hup
  obtain ⟨y',hyL,hyH,hyy'⟩ := tangentInterval_recenter u v huv L H c y hy hlo hup
  obtain ⟨w,hws,hwm,_,hwb,_⟩ := tangent_chain u v huv (y'-x')
  have hm : TangentIntervalReach u L H x' y' := by
    have he : x'+w.sum=y' := by rw [hws]; abel
    rw [← he]
    apply tangentInterval_list u x' L H w hwm
    intro n
    have hn := hwb n
    simp only [map_add,map_sub] at hn ⊢
    change min 0 (ordinary y'-ordinary x')-b ≤ ordinary (w.take n).sum ∧
      ordinary (w.take n).sum ≤ max 0 (ordinary y'-ordinary x')+b at hn
    have hw' : 4*b ≤ H-L := hwidth
    have hcL : L ≤ c-2*b := by dsimp [c]; linarith
    have hcH : c+2*b ≤ H := by dsimp [c]; linarith
    by_cases hh : ordinary x' ≤ ordinary y'
    · rw [min_eq_left (by linarith),max_eq_right (by linarith)] at hn
      constructor <;> linarith
    · rw [min_eq_right (by linarith),max_eq_left (by linarith)] at hn
      constructor <;> linarith
  exact hxx'.trans (hm.trans (tangentIntervalReach_symm hyy'))

end IntervalTangentConnectivity

end SimpleAmenable
end
end

end OAI
