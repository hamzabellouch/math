import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentAnchors
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LocalChartDecisions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WindowRectangles

noncomputable def windowRectangle (a n : ℕ) (q : Fin 2 → ℤ) (i : Fin 2 → Fin n) :
    polygonAlgebra a :=
  coordinateRectangle a (fun j => windowCut n (q j) (i j).castSucc)
    (fun j => windowCut n (q j) (i j).succ)

noncomputable def windowPlanarLift {a : ℕ} (q : Fin 2 → ℤ) (p : GenericSquare a) : ℝ × ℝ :=
  (liftedCoordinate 0 ((q 0:CutRing)*cutTau) p,
   liftedCoordinate 1 ((q 1:CutRing)*cutTau) p)

theorem windowPlanarLift_coordinate {a : ℕ} (q : Fin 2 → ℤ) (p : GenericSquare a)
    (j : Fin 2) : realCoordinate (windowPlanarLift q p) j =
      liftedCoordinate j ((q j:CutRing)*cutTau) p := by fin_cases j <;> rfl

theorem windowPlanarLift_spec {a : ℕ} (q : Fin 2 → ℤ) (p : GenericSquare a) :
    p.val=(Int.fract (windowPlanarLift q p).1,Int.fract (windowPlanarLift q p).2) := by
  simp only [windowPlanarLift,liftedCoordinate,Int.fract_sub_intCast]
  apply Prod.ext
  · exact (Int.fract_eq_self.mpr p.property.1).symm
  · exact (Int.fract_eq_self.mpr p.property.2.1).symm

theorem windowRectangle_mem {a : ℕ} (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ)
    (i : Fin 2 → Fin n) (p : GenericSquare a) :
    p ∈ (windowRectangle a n q i).val ↔ ∀ j : Fin 2,
      ordinary (windowCut n (q j) (i j).castSucc) ≤ realCoordinate (windowPlanarLift q p) j ∧
      realCoordinate (windowPlanarLift q p) j < ordinary (windowCut n (q j) (i j).succ) := by
  change (p ∈ (windowCell a 0 n (q 0) (i 0)).val ∧
    p ∈ (windowCell a 1 n (q 1) (i 1)).val) ↔ _
  simp only [windowCell_mem _ n hn,windowPlanarLift_coordinate]
  rw [Fin.forall_fin_two]

theorem windowRectangle_cover {a : ℕ} (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ)
    (p : GenericSquare a) : ∃ i : Fin 2 → Fin n, p ∈ (windowRectangle a n q i).val := by
  have hh (j : Fin 2) := windowCell_cover (a := a) j n hn (q j) p
  choose i hi using hh
  refine ⟨i,hi 0,hi 1⟩

theorem windowRectangle_pairwise_disjoint {a : ℕ} (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ) :
    Pairwise fun i k : Fin 2 → Fin n => Disjoint (windowRectangle a n q i).val (windowRectangle a n q k).val := by
  intro i k hik
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hik
  apply Set.disjoint_left.mpr
  intro p hp hk
  have hi' := (windowRectangle_mem n hn q i p).mp hp j
  have hk' := (windowRectangle_mem n hn q k p).mp hk j
  simp only [windowPlanarLift_coordinate] at hi' hk'
  exact Set.disjoint_left.mp (windowCell_pairwise_disjoint (a := a) j n hn (q j) hj)
    ((windowCell_mem j n hn (q j) (i j) p).mpr hi')
    ((windowCell_mem j n hn (q j) (k j) p).mpr hk')

theorem windowRectangle_resolved {a : ℕ} {r : CutRing} (n : ℕ) (hn : 0<n)
    (q : Fin 2 → ℤ) (i : Fin 2 → Fin n) :
    ResolvedBy (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) z).val) (windowRectangle a n q i).val := by
  intro x y he
  have hx := coordinateLabelWindow_resolved (a := a) (r := r) n q 0 _ _
      (windowCut_label n (q 0) hn (i 0).castSucc) (windowCut_label n (q 0) hn (i 0).succ) x y he
  have hy := coordinateLabelWindow_resolved (a := a) (r := r) n q 1 _ _
      (windowCut_label n (q 1) hn (i 1).castSucc) (windowCut_label n (q 1) hn (i 1).succ) x y he
  exact and_congr hx hy

theorem windowRectangle_diameter {a : ℕ} (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ)
    (i : Fin 2 → Fin n) (p t : GenericSquare a)
    (hp : p ∈ (windowRectangle a n q i).val) (ht : t ∈ (windowRectangle a n q i).val) :
    dist (windowPlanarLift q p) (windowPlanarLift q t) ≤ 200/(n:ℝ) := by
  have hd (j : Fin 2) : |realCoordinate (windowPlanarLift q p) j-
      realCoordinate (windowPlanarLift q t) j| ≤ 200/(n:ℝ) := by
    have hp' := (windowRectangle_mem n hn q i p).mp hp j
    have ht' := (windowRectangle_mem n hn q i t).mp ht j
    have hm := windowCut_mesh n (q j) (i j)
    apply abs_le.mpr
    constructor <;> linarith
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff]
  exact ⟨hd 0,hd 1⟩

end WindowRectangles

section CellLineIntersections

theorem linear_form_dist_bound (A B : ℝ) (x y : ℝ × ℝ) :
    |(A*x.1+B*x.2)-(A*y.1+B*y.2)| ≤ (|A|+|B|)*dist x y := by
  have hx : |x.1-y.1| ≤ dist x y := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have hy : |x.2-y.2| ≤ dist x y := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  calc
    _ = |A*(x.1-y.1)+B*(x.2-y.2)| := by congr 1; ring
    _ ≤ |A*(x.1-y.1)|+|B*(x.2-y.2)| := abs_add_le _ _
    _ ≤ |A| *dist x y+|B| *dist x y := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
    _ = _ := by ring

theorem crossing_level_bound (A B c δ : ℝ) (p x y : ℝ × ℝ)
    (hx : A*x.1+B*x.2≤c) (hy : c≤A*y.1+B*y.2)
    (hpx : dist p x≤δ) (hpy : dist p y≤δ) :
    |c-(A*p.1+B*p.2)| ≤ (|A|+|B|)*δ := by
  have h₁ := (linear_form_dist_bound A B x p).trans
    (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hpx) (by positivity))
  have h₂ := (linear_form_dist_bound A B y p).trans
    (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hpy) (by positivity))
  have h₁' := (abs_le.mp h₁).1
  have h₂' := (abs_le.mp h₂).2
  apply abs_le.mpr
  constructor <;> linarith

theorem line_point_in_box (A B c : ℝ) (L V : Fin 2 → ℝ) (x y : ℝ × ℝ)
    (hx : ∀ j, L j≤realCoordinate x j ∧ realCoordinate x j≤V j)
    (hy : ∀ j, L j≤realCoordinate y j ∧ realCoordinate y j≤V j)
    (hcx : A*x.1+B*x.2≤c) (hcy : c≤A*y.1+B*y.2) :
    ∃ z : ℝ × ℝ, A*z.1+B*z.2=c ∧
      ∀ j, L j≤realCoordinate z j ∧ realCoordinate z j≤V j := by
  let f : ℝ → ℝ := fun t => A*((1-t)*x.1+t*y.1)+B*((1-t)*x.2+t*y.2)
  have hf : Continuous f := by unfold f; fun_prop
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hf.continuousOn
    (show c ∈ Set.Icc (f 0) (f 1) from by simpa [f] using And.intro hcx hcy)
  refine ⟨((1-t)*x.1+t*y.1,(1-t)*x.2+t*y.2),he,?_⟩
  intro j
  have hx' := hx j
  have hy' := hy j
  have hform : realCoordinate ((1-t)*x.1+t*y.1,(1-t)*x.2+t*y.2) j=
      (1-t)*realCoordinate x j+t*realCoordinate y j := by fin_cases j <;> rfl
  rw [hform]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hx'.1),
    mul_nonneg ht.1 (sub_nonneg.mpr hy'.1),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hx'.2),
    mul_nonneg ht.1 (sub_nonneg.mpr hy'.2)]

theorem windowRectangle_intersection_near {a : ℕ} (ha : 0<a)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing)
    (p x y u v : GenericSquare a)
    (hp : p ∈ (windowRectangle a n q cell).val)
    (hx : x ∈ (windowRectangle a n q cell).val)
    (hy : y ∈ (windowRectangle a n q cell).val)
    (hu : u ∈ (windowRectangle a n q cell).val)
    (hv : v ∈ (windowRectangle a n q cell).val)
    (hcx : cutForm a i (windowPlanarLift q x)≤ordinary c)
    (hcy : ordinary c≤cutForm a i (windowPlanarLift q y))
    (hdu : cutForm a j (windowPlanarLift q u)≤ordinary d)
    (hdv : ordinary d≤cutForm a j (windowPlanarLift q v)) :
    ∃ z : ℝ × ℝ, cutForm a i z=ordinary c ∧ cutForm a j z=ordinary d ∧
      dist z (windowPlanarLift q p) ≤
        ((|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|+
          |ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)/
          |ordinary (lineDet a i j)|)*
        (max (|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|)
          (|ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)*(200/(n:ℝ))) := by
  obtain ⟨z,hz,hz'⟩ := allowable_lines_intersect ha i j hij c d
  refine ⟨z,hz,hz',?_⟩
  have h₁ := crossing_level_bound (ordinary (lineNormal a i).1) (ordinary (lineNormal a i).2)
    (ordinary c) (200/(n:ℝ)) (windowPlanarLift q p) (windowPlanarLift q x) (windowPlanarLift q y)
    (by simpa only [cutForm_normal] using hcx) (by simpa only [cutForm_normal] using hcy)
    (windowRectangle_diameter n hn q cell p x hp hx) (windowRectangle_diameter n hn q cell p y hp hy)
  have h₂ := crossing_level_bound (ordinary (lineNormal a j).1) (ordinary (lineNormal a j).2)
    (ordinary d) (200/(n:ℝ)) (windowPlanarLift q p) (windowPlanarLift q u) (windowPlanarLift q v)
    (by simpa only [cutForm_normal] using hdu) (by simpa only [cutForm_normal] using hdv)
    (windowRectangle_diameter n hn q cell p u hp hu) (windowRectangle_diameter n hn q cell p v hp hv)
  have hδ : 0≤200/(n:ℝ) := by positivity
  have hm₁ := mul_le_mul_of_nonneg_right (le_max_left
    (|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|)
    (|ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)) hδ
  have hm₂ := mul_le_mul_of_nonneg_right (le_max_right
    (|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|)
    (|ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)) hδ
  have hh := real_two_lines_distance_bound _ _ _ _ (ordinary c) (ordinary d)
    (real_lineDet_ne_zero ha i j hij) z (windowPlanarLift q p) (by simpa only [cutForm_normal] using hz)
    (by simpa only [cutForm_normal] using hz') _ (by positivity) (h₁.trans hm₁) (h₂.trans hm₂)
  simpa only [lineDet,map_sub,map_mul] using hh

end CellLineIntersections

end SimpleAmenable
end
end

end OAI
