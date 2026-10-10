import Mathlib

namespace OAI

/-!
Closed radix rectangles for Section 4 of *Finite Instructions and Solenoidal
Shear Flows*. These statements concern whole intervals and rectangles, not
merely the subset consisting of encoded tapes.
-/

namespace ForcedComputation.Radix

noncomputable section

open Set

def push (B d x : ℝ) : ℝ := (d + x) / B

def pop (B d x : ℝ) : ℝ := B * x - d

def cylinder (B d : ℝ) : Set ℝ := Icc (d / B) ((d + 1) / B)

theorem pop_push {B : ℝ} (hB : B ≠ 0) (d x : ℝ) :
    pop B d (push B d x) = x := by
  dsimp [pop, push]
  field_simp
  ring

theorem push_pop {B : ℝ} (hB : B ≠ 0) (d x : ℝ) :
    push B d (pop B d x) = x := by
  dsimp [pop, push]
  field_simp
  ring

theorem push_mem_cylinder {B : ℝ} (hB : 0 < B) (d : ℝ) {x : ℝ} :
    push B d x ∈ cylinder B d ↔ x ∈ Icc (0 : ℝ) 1 := by
  simp only [push, cylinder, mem_Icc]
  constructor
  · rintro ⟨hl, hu⟩
    constructor <;> nlinarith [(div_le_div_iff_of_pos_right hB).mp hl,
      (div_le_div_iff_of_pos_right hB).mp hu]
  · rintro ⟨hl, hu⟩
    constructor <;> apply (div_le_div_iff_of_pos_right hB).mpr <;> linarith

theorem pop_mem_unit {B : ℝ} (hB : 0 < B) (d : ℝ) {x : ℝ} :
    pop B d x ∈ Icc (0 : ℝ) 1 ↔ x ∈ cylinder B d := by
  rw [← push_mem_cylinder hB d, push_pop hB.ne']

theorem push_image_unit {B : ℝ} (hB : 0 < B) (d : ℝ) :
    push B d '' Icc (0 : ℝ) 1 = cylinder B d := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (push_mem_cylinder hB d).mpr hy
  · intro hx
    exact ⟨pop B d x, (pop_mem_unit hB d).mpr hx, push_pop hB.ne' d x⟩

theorem pop_image_cylinder {B : ℝ} (hB : 0 < B) (d : ℝ) :
    pop B d '' cylinder B d = Icc (0 : ℝ) 1 := by
  rw [← push_image_unit hB d, ← image_comp]
  simp only [Function.comp_def, pop_push hB.ne', image_id']

theorem cylinder_gap {B : ℝ} (hB : 0 < B) {d e : ℝ} (hde : d + 2 ≤ e)
    {x y : ℝ} (hx : x ∈ cylinder B d) (hy : y ∈ cylinder B e) :
    1 / B ≤ y - x := by
  have hxy : (d + 1) / B ≤ e / B - 1 / B := by
    rw [← sub_div]
    apply (div_le_div_iff_of_pos_right hB).mpr
    linarith
  exact (le_sub_iff_add_le).mpr (by linarith [hx.2, hy.1])

theorem nested_cylinder_gap {B : ℝ} (hB : 0 < B) (a : ℝ)
    {d e : ℝ} (hde : d + 2 ≤ e) {x y : ℝ}
    (hx : x ∈ push B a '' cylinder B d)
    (hy : y ∈ push B a '' cylinder B e) : 1 / B ^ 2 ≤ y - x := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  have hgap := cylinder_gap hB hde hu hv
  have h := (div_le_div_iff_of_pos_right hB).mpr hgap
  dsimp [push]
  calc
    1 / B ^ 2 = (1 / B) / B := by ring
    _ ≤ (v - u) / B := h
    _ = (a + v) / B - (a + u) / B := by ring

def rectangle (B l a : ℝ) : Set (ℝ × ℝ) := cylinder B l ×ˢ cylinder B a

def rightMove (B a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (push B b p.1, pop B a p.2)

def stayMove (B a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, push B b (pop B a p.2))

def leftMove (B l a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (pop B l p.1, push B l (push B b (pop B a p.2)))

theorem rightMove_image {B : ℝ} (hB : 0 < B) (l a b : ℝ) :
    rightMove B a b '' rectangle B l a =
      (push B b '' cylinder B l) ×ˢ Icc (0 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q.1, hq.1, rfl⟩, (pop_mem_unit hB a).mpr hq.2⟩
  · rintro ⟨⟨x, hx, he⟩, hy⟩
    refine ⟨(x, push B a p.2), ⟨hx, (push_mem_cylinder hB a).mpr hy⟩, ?_⟩
    exact Prod.ext he (pop_push hB.ne' a p.2)

theorem stayMove_image {B : ℝ} (hB : 0 < B) (l a b : ℝ) :
    stayMove B a b '' rectangle B l a = cylinder B l ×ˢ cylinder B b := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1, (push_mem_cylinder hB b).mpr ((pop_mem_unit hB a).mpr hq.2)⟩
  · intro hp
    refine ⟨(p.1, push B a (pop B b p.2)),
      ⟨hp.1, (push_mem_cylinder hB a).mpr ((pop_mem_unit hB b).mpr hp.2)⟩, ?_⟩
    apply Prod.ext
    · rfl
    · dsimp [stayMove]
      rw [pop_push hB.ne', push_pop hB.ne']

theorem leftMove_image {B : ℝ} (hB : 0 < B) (l a b : ℝ) :
    leftMove B l a b '' rectangle B l a =
      Icc (0 : ℝ) 1 ×ˢ (push B l '' cylinder B b) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨(pop_mem_unit hB l).mpr hq.1,
      ⟨push B b (pop B a q.2),
        (push_mem_cylinder hB b).mpr ((pop_mem_unit hB a).mpr hq.2), rfl⟩⟩
  · rintro ⟨hx, ⟨y, hy, he⟩⟩
    refine ⟨(push B l p.1, push B a (pop B b y)),
      ⟨(push_mem_cylinder hB l).mpr hx,
        (push_mem_cylinder hB a).mpr ((pop_mem_unit hB b).mpr hy)⟩, ?_⟩
    apply Prod.ext (pop_push hB.ne' l p.1)
    dsimp [leftMove]
    rw [pop_push hB.ne', push_pop hB.ne']
    exact he

end

end ForcedComputation.Radix

end OAI
