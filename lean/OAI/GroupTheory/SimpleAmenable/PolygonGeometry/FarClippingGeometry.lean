import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FinePatchAtlas

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FarClippingGeometry

theorem windowRectangle_clipping_chart_at_lift {a : ℕ} (r : CutRing)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (hb : ∀ d, q d≤endpointLabel (-r) ∧ endpointLabel (-r)<q d+n)
    (he : ∀ d, q d≤endpointLabel r ∧ endpointLabel r<q d+n)
    (p : GenericSquare a) (hp : p ∈ (windowRectangle a n q cell).val)
    (z : ℝ × ℝ) (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hclip : ∀ d, -ordinary r≤realCoordinate z d ∧ realCoordinate z d<ordinary r) :
    ∃ k : Fin 2 → ℤ,
      (∀ d, -ordinary r≤ordinary (windowCut n (q d) (cell d).castSucc)+(k d:ℝ) ∧
        ordinary (windowCut n (q d) (cell d).succ)+(k d:ℝ)≤ordinary r) ∧
      windowPlanarLift q p+((k 0:ℝ),(k 1:ℝ))=z := by
  have hs := windowPlanarLift_spec q p
  have hd (d : Fin 2) : ∃ k : ℤ, realCoordinate z d-realCoordinate (windowPlanarLift q p) d=(k:ℝ) := by
    apply Int.fract_eq_fract.mp
    fin_cases d
    · exact (congrArg Prod.fst hz).symm.trans (congrArg Prod.fst hs)
    · exact (congrArg Prod.snd hz).symm.trans (congrArg Prod.snd hs)
  choose k hk using hd
  refine ⟨k,?_,?_⟩
  · intro d
    have h := window_cell_enclosure n (q d) (cell d) (-r) r (hb d) (he d)
      (realCoordinate (windowPlanarLift q p) d) (k d)
      ((windowRectangle_mem n hn q cell p).mp hp d)
      (by simp only [map_neg]; constructor <;> linarith [(hk d),(hclip d).1,(hclip d).2])
    simpa only [map_neg] using h
  · apply Prod.ext
    · change (windowPlanarLift q p).1+(k 0:ℝ)=z.1
      have h := hk 0
      change z.1-(windowPlanarLift q p).1=(k 0:ℝ) at h
      linarith
    · change (windowPlanarLift q p).2+(k 1:ℝ)=z.2
      have h := hk 1
      change z.2-(windowPlanarLift q p).2=(k 1:ℝ) at h
      linarith

theorem far_cut_neighborhood (a : ℕ) (j : Fin 4) (z : ℝ × ℝ) (c R E : ℝ)
    (hR : 0<R) (hE : E<R/4) (hfar : R≤|cutForm a j z-c|) :
    ∃ δ : ℝ, 0<δ ∧ ∀ p : ℝ × ℝ, dist p z<δ →
      E < |cutForm a j p-c| ∧ (0≤cutForm a j p-c ↔ c<cutForm a j z) := by
  let K := 1+|ordinary (cutTau^a)|
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨R/(4*K),by positivity,?_⟩
  intro p hp
  have hdist : K*dist p z<R/4 := by
    have hh := (lt_div_iff₀ (by positivity : 0<4*K)).mp hp
    nlinarith
  have hd : |cutForm a j p-cutForm a j z|<R/4 :=
    (cutForm_dist_bound a j p z).trans_lt hdist
  rcases le_total c (cutForm a j z) with hz | hz
  · rw [abs_of_nonneg (sub_nonneg.mpr hz)] at hfar
    have hs : 0<cutForm a j p-c := by linarith [(abs_lt.mp hd).1]
    refine ⟨?_,iff_of_true hs.le (by linarith)⟩
    rw [abs_of_pos hs]
    linarith [(abs_lt.mp hd).1]
  · rw [abs_of_nonpos (sub_nonpos.mpr hz)] at hfar
    have hs : cutForm a j p-c<0 := by linarith [(abs_lt.mp hd).2]
    refine ⟨?_,iff_of_false (not_le_of_gt hs) (not_lt_of_ge hz)⟩
    rw [abs_of_neg hs]
    linarith [(abs_lt.mp hd).2]

end FarClippingGeometry

section WindowBoxDichotomy

theorem windowRectangle_le_clipping_box {a : ℕ} (r : CutRing)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (k : Fin 2 → ℤ)
    (hk : ∀ d, -ordinary r≤ordinary (windowCut n (q d) (cell d).castSucc)+(k d:ℝ) ∧
      ordinary (windowCut n (q d) (cell d).succ)+(k d:ℝ)≤ordinary r) :
    windowRectangle a n q cell ≤ coordinateRectangle a (fun _ => -r) (fun _ => r) := by
  intro p hp
  have hb (d : Fin 2) : p ∈ coordinateBetween a d (-r) r := by
    apply (mem_coordinateBetween_iff d (-r) r (by rw [map_neg]; linarith [hr.1])
      (by rw [map_neg]; linarith [hr.2]) p).mpr
    refine ⟨k d-⌊coordinate d p-ordinary ((q d:CutRing)*cutTau)⌋,?_⟩
    have hh := (windowRectangle_mem n hn q cell p).mp hp d
    simp only [windowPlanarLift_coordinate,liftedCoordinate] at hh
    simp only [map_neg,Int.cast_sub]
    constructor <;> linarith [(hk d).1,(hk d).2,hh.1,hh.2]
  exact ⟨hb 0,hb 1⟩

theorem windowRectangle_clipping_dichotomy {a : ℕ} (r : CutRing)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (hb : ∀ d, q d≤endpointLabel (-r) ∧ endpointLabel (-r)<q d+n)
    (he : ∀ d, q d≤endpointLabel r ∧ endpointLabel r<q d+n) :
    Disjoint (windowRectangle a n q cell) (coordinateRectangle a (fun _ => -r) (fun _ => r)) ∨
    windowRectangle a n q cell ≤ coordinateRectangle a (fun _ => -r) (fun _ => r) := by
  classical
  by_cases h : ∃ p : GenericSquare a, p ∈ (windowRectangle a n q cell).val ∧
      p ∈ (coordinateRectangle a (fun _ => -r) (fun _ => r)).val
  · obtain ⟨p,hp,hbox⟩ := h
    obtain ⟨k,hk⟩ := windowRectangle_clipping_chart r hr n hn q cell hb he p hp hbox
    exact Or.inr (windowRectangle_le_clipping_box r hr n hn q cell k hk)
  · left
    rw [disjoint_iff_inf_le]
    exact fun p hp => h ⟨p,hp.1,hp.2⟩

theorem windowRectangle_exterior_of_point {a : ℕ} (r : CutRing)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (hb : ∀ d, q d≤endpointLabel (-r) ∧ endpointLabel (-r)<q d+n)
    (he : ∀ d, q d≤endpointLabel r ∧ endpointLabel r<q d+n)
    (p : GenericSquare a) (hp : p ∈ (windowRectangle a n q cell).val)
    (hout : p ∉ (coordinateRectangle a (fun _ => -r) (fun _ => r)).val) :
    Disjoint (windowRectangle a n q cell) (coordinateRectangle a (fun _ => -r) (fun _ => r)) := by
  rcases windowRectangle_clipping_dichotomy r hr n hn q cell hb he with h | h
  · exact h
  · exact False.elim (hout (h hp))

end WindowBoxDichotomy

end SimpleAmenable
end
end

end OAI
