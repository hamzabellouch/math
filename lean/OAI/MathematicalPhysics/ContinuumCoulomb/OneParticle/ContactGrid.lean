import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactLattice

namespace OAI

/-! Rigid placements of the fixed contact strip on the square lattice.
Reversing an original edge reflects its axial coordinate; this keeps its
internal points in the same canonical strip. -/

noncomputable section
namespace ContinuumCoulomb

/-- The original square-lattice vertices are spaced seventeen units apart. -/
def contactGridPoint (a : ℤ × ℤ) : ContactPoint :=
  contactPoint (17 * a.1) (17 * a.2)

def contactReflect (p : ContactPoint) : ContactPoint := contactPoint (17 - p 0) (p 1)

def contactHorizontal (a : ℤ × ℤ) (p : ContactPoint) : ContactPoint :=
  contactPoint (17 * a.1 + p 0) (17 * a.2 + p 1)

def contactVertical (a : ℤ × ℤ) (p : ContactPoint) : ContactPoint :=
  contactPoint (17 * a.1 - p 1) (17 * a.2 + p 0)

private theorem contact_dist_eq_of_sq_eq {p q x y : ContactPoint}
    (h : dist p q ^ 2 = dist x y ^ 2) : dist p q = dist x y := by
  nlinarith [dist_nonneg (x := p) (y := q), dist_nonneg (x := x) (y := y)]

theorem contactReflect_dist (p q : ContactPoint) :
    dist (contactReflect p) (contactReflect q) = dist p q := by
  apply contact_dist_eq_of_sq_eq
  rw [contactReflect, contactReflect, contactPoint_dist_sq, ← contactPoint_eta p,
    ← contactPoint_eta q, contactPoint_dist_sq]
  simp only [contactPoint_zero, contactPoint_one]
  ring

theorem contactHorizontal_dist (a : ℤ × ℤ) (p q : ContactPoint) :
    dist (contactHorizontal a p) (contactHorizontal a q) = dist p q := by
  apply contact_dist_eq_of_sq_eq
  rw [contactHorizontal, contactHorizontal, contactPoint_dist_sq, ← contactPoint_eta p,
    ← contactPoint_eta q, contactPoint_dist_sq]
  simp only [contactPoint_zero, contactPoint_one]
  ring

theorem contactVertical_dist (a : ℤ × ℤ) (p q : ContactPoint) :
    dist (contactVertical a p) (contactVertical a q) = dist p q := by
  apply contact_dist_eq_of_sq_eq
  rw [contactVertical, contactVertical, contactPoint_dist_sq, ← contactPoint_eta p,
    ← contactPoint_eta q, contactPoint_dist_sq]
  simp only [contactPoint_zero, contactPoint_one]
  ring

def ContactStripSite.reflect (p : ContactStripSite) : ContactStripSite where
  axial := 17 - p.axial
  transverse := p.transverse
  axial_lower := by linarith [p.axial_upper]
  axial_upper := by linarith [p.axial_lower]
  transverse_lower := p.transverse_lower
  transverse_upper := p.transverse_upper
  off_axis_lower := by intro h; linarith [p.off_axis_upper h]
  off_axis_upper := by intro h; linarith [p.off_axis_lower h]

@[simp] theorem contactReflect_strip (p : ContactStripSite) :
    contactReflect (contactPoint p.axial p.transverse) =
      contactPoint p.reflect.axial p.reflect.transverse := rfl

/-- The canonical key of a lattice edge consists of its direction and its
lower/left endpoint. The final Boolean records the input orientation. -/
structure ContactGridEdge where
  vertical : Bool
  anchor : ℤ × ℤ
  reversed : Bool
  deriving DecidableEq

def ContactGridEdge.key (e : ContactGridEdge) : Bool × (ℤ × ℤ) := (e.vertical, e.anchor)

def ContactGridEdge.upper (e : ContactGridEdge) : ℤ × ℤ :=
  if e.vertical then (e.anchor.1, e.anchor.2 + 1) else (e.anchor.1 + 1, e.anchor.2)

def ContactGridEdge.left (e : ContactGridEdge) : ℤ × ℤ :=
  if e.reversed then e.upper else e.anchor

def ContactGridEdge.right (e : ContactGridEdge) : ℤ × ℤ :=
  if e.reversed then e.anchor else e.upper

def ContactGridEdge.place (e : ContactGridEdge) (p : ContactPoint) : ContactPoint :=
  let p' := if e.reversed then contactReflect p else p
  if e.vertical then contactVertical e.anchor p' else contactHorizontal e.anchor p'

theorem ContactGridEdge.place_dist (e : ContactGridEdge) (p q : ContactPoint) :
    dist (e.place p) (e.place q) = dist p q := by
  cases e with
  | mk vertical anchor reversed =>
    cases vertical <;> cases reversed <;>
      simp [ContactGridEdge.place, contactHorizontal_dist, contactVertical_dist, contactReflect_dist]

@[simp] theorem ContactGridEdge.place_zero (e : ContactGridEdge) :
    e.place (contactPoint 0 0) = contactGridPoint e.left := by
  rcases e with ⟨vertical, ⟨a, b⟩, reversed⟩
  cases vertical <;> cases reversed <;> ext i <;> fin_cases i <;>
    simp [ContactGridEdge.place, ContactGridEdge.left, ContactGridEdge.upper,
      contactReflect, contactHorizontal, contactVertical, contactGridPoint, contactPoint] <;> ring

@[simp] theorem ContactGridEdge.place_end (e : ContactGridEdge) :
    e.place (contactPoint 17 0) = contactGridPoint e.right := by
  rcases e with ⟨vertical, ⟨a, b⟩, reversed⟩
  cases vertical <;> cases reversed <;> ext i <;> fin_cases i <;>
    simp [ContactGridEdge.place, ContactGridEdge.right, ContactGridEdge.upper,
      contactReflect, contactHorizontal, contactVertical, contactGridPoint, contactPoint] <;> ring

/-- The orientation flag does not alter the strip containing an internal site. -/
theorem ContactGridEdge.place_strip (e : ContactGridEdge) (p : ContactStripSite) :
    ∃ q : ContactStripSite, e.place (contactPoint p.axial p.transverse) =
      if e.vertical then verticalContact e.anchor.1 e.anchor.2 q
      else horizontalContact e.anchor.1 e.anchor.2 q := by
  refine ⟨if e.reversed then p.reflect else p, ?_⟩
  cases h : e.reversed <;> cases v : e.vertical <;>
    simp [ContactGridEdge.place, h, v, contactReflect, contactHorizontal, contactVertical,
      horizontalContact, verticalContact, ContactStripSite.reflect]

/-- Vertical parallel strips have the same separation as horizontal ones. -/
theorem verticalContact_separation (a b c d : ℤ)
    (hne : (a, b) ≠ (c, d)) (p q : ContactStripSite) :
    7 / 5 < dist (verticalContact a b p) (verticalContact c d q) := by
  have hk : (b, -a) ≠ (d, -c) := by
    intro h
    apply hne
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (by omega) h₁
  have hs := horizontalContact_separation b (-a) d (-c) hk p q
  have hd : dist (verticalContact a b p) (verticalContact c d q) =
      dist (horizontalContact b (-a) p) (horizontalContact d (-c) q) := by
    apply contact_dist_eq_of_sq_eq
    simp only [verticalContact, horizontalContact, contactPoint_dist_sq, Int.cast_neg]
    ring
  rw [hd]
  exact hs

theorem ContactGridEdge.distinct_strip_separation (e f : ContactGridEdge)
    (hne : e.key ≠ f.key) (p q : ContactStripSite) :
    7 / 5 < dist (e.place (contactPoint p.axial p.transverse))
      (f.place (contactPoint q.axial q.transverse)) := by
  obtain ⟨p', hp⟩ := e.place_strip p
  obtain ⟨q', hq⟩ := f.place_strip q
  rw [hp, hq]
  cases he : e.vertical <;> cases hf : f.vertical <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · apply horizontalContact_separation _ _ _ _ _ p' q'
    intro h
    exact hne (by simp [ContactGridEdge.key, he, hf, Prod.ext_iff] at h ⊢; exact h)
  · exact perpendicularContact_separation _ _ _ _ p' q'
  · rw [dist_comm]
    exact perpendicularContact_separation _ _ _ _ q' p'
  · apply verticalContact_separation _ _ _ _ _ p' q'
    intro h
    exact hne (by simp [ContactGridEdge.key, he, hf, Prod.ext_iff] at h ⊢; exact h)

/-- Perturbed internal nodes of distinct original edges remain noncontacts. -/
theorem ContactGridEdge.distinct_perturbed_separation (e f : ContactGridEdge)
    (hne : e.key ≠ f.key) (p q : ContactStripSite) (x y : ContactPoint)
    (hx : dist (e.place (contactPoint p.axial p.transverse)) x ≤ 1 / 20)
    (hy : dist (f.place (contactPoint q.axial q.transverse)) y ≤ 1 / 20) :
    6 / 5 < dist x y :=
  contact_separation_stable _ _ _ _ (e.distinct_strip_separation f hne p q).le hx hy

private theorem int_abs_difference_one {a b : ℤ} (h : a ≠ b) :
    (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases lt_or_gt_of_ne h with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    exact (neg_le_abs _).trans' (by linarith)
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    exact (le_abs_self _).trans' (by linarith)

theorem contactGridPoint_separation {a b : ℤ × ℤ} (hne : a ≠ b) :
    17 ≤ dist (contactGridPoint a) (contactGridPoint b) := by
  by_cases h₀ : a.1 = b.1
  · have h₁ : a.2 ≠ b.2 := fun h => hne (Prod.ext h₀ h)
    have ha := int_abs_difference_one h₁
    have hd := contactPoint_coordinate_le_dist (contactGridPoint a) (contactGridPoint b) 1
    change |17 * (a.2 : ℝ) - 17 * b.2| ≤ _ at hd
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 17)] at hd
    linarith
  · have ha := int_abs_difference_one h₀
    have hd := contactPoint_coordinate_le_dist (contactGridPoint a) (contactGridPoint b) 0
    change |17 * (a.1 : ℝ) - 17 * b.1| ≤ _ at hd
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 17)] at hd
    linarith

/-- A lattice vertex outside the two endpoints is far from the entire
horizontal internal strip, before any adjustment. -/
theorem horizontalContact_external_vertex (a c : ℤ × ℤ) (p : ContactStripSite)
    (h₀ : c ≠ a) (h₁ : c ≠ (a.1 + 1, a.2)) :
    7 / 5 < dist (horizontalContact a.1 a.2 p) (contactGridPoint c) := by
  by_cases hb : c.2 = a.2
  · have hc₀ : c.1 ≠ a.1 := fun h => h₀ (Prod.ext h hb)
    have hc₁ : c.1 ≠ a.1 + 1 := fun h => h₁ (Prod.ext h hb)
    have hd := contactPoint_coordinate_le_dist
      (horizontalContact a.1 a.2 p) (contactGridPoint c) 0
    change |17 * (a.1 : ℝ) + p.axial - 17 * c.1| ≤ _ at hd
    have hc : c.1 ≤ a.1 - 1 ∨ a.1 + 2 ≤ c.1 := by omega
    rcases hc with hc | hc
    · have hc' : (c.1 : ℝ) ≤ a.1 - 1 := by exact_mod_cast hc
      have hp := p.axial_lower
      have hx := le_abs_self (17 * (a.1 : ℝ) + p.axial - 17 * c.1)
      linarith
    · have hc' : (a.1 : ℝ) + 2 ≤ c.1 := by exact_mod_cast hc
      have hp := p.axial_upper
      have hx := neg_le_abs (17 * (a.1 : ℝ) + p.axial - 17 * c.1)
      linarith
  · have hd := contactPoint_coordinate_le_dist
      (horizontalContact a.1 a.2 p) (contactGridPoint c) 1
    change |17 * (a.2 : ℝ) + p.transverse - 17 * c.2| ≤ _ at hd
    have hsep := contact_parallel_line_separation a.2 c.2 (Ne.symm hb)
      p.transverse_lower p.transverse_upper (show (0 : ℝ) ≤ 0 by norm_num)
      (show (0 : ℝ) ≤ 4 / 3 by norm_num)
    simp only [add_zero] at hsep
    linarith

theorem verticalContact_external_vertex (a c : ℤ × ℤ) (p : ContactStripSite)
    (h₀ : c ≠ a) (h₁ : c ≠ (a.1, a.2 + 1)) :
    7 / 5 < dist (verticalContact a.1 a.2 p) (contactGridPoint c) := by
  have hc₀ : (c.2, -c.1) ≠ (a.2, -a.1) := by
    intro h
    apply h₀
    exact Prod.ext (by have := congrArg Prod.snd h; dsimp at this; omega)
      (congrArg Prod.fst h)
  have hc₁ : (c.2, -c.1) ≠ (a.2 + 1, -a.1) := by
    intro h
    apply h₁
    exact Prod.ext (by have := congrArg Prod.snd h; dsimp at this; omega)
      (congrArg Prod.fst h)
  have hs := horizontalContact_external_vertex (a.2, -a.1) (c.2, -c.1) p hc₀ hc₁
  have hd : dist (verticalContact a.1 a.2 p) (contactGridPoint c) =
      dist (horizontalContact a.2 (-a.1) p) (contactGridPoint (c.2, -c.1)) := by
    apply contact_dist_eq_of_sq_eq
    simp only [verticalContact, horizontalContact, contactGridPoint, contactPoint_dist_sq,
      Int.cast_neg]
    ring
  rw [hd]
  exact hs

theorem ContactGridEdge.external_vertex_separation (e : ContactGridEdge)
    (c : ℤ × ℤ) (hc₀ : c ≠ e.left) (hc₁ : c ≠ e.right) (p : ContactStripSite) :
    7 / 5 < dist (e.place (contactPoint p.axial p.transverse)) (contactGridPoint c) := by
  have ha : c ≠ e.anchor := by
    cases h : e.reversed
    · simpa [ContactGridEdge.left, h] using hc₀
    · simpa [ContactGridEdge.right, h] using hc₁
  have hu : c ≠ e.upper := by
    cases h : e.reversed
    · simpa [ContactGridEdge.right, h] using hc₁
    · simpa [ContactGridEdge.left, h] using hc₀
  obtain ⟨q, hq⟩ := e.place_strip p
  rw [hq]
  cases h : e.vertical
  · simp only [Bool.false_eq_true, ite_false]
    exact horizontalContact_external_vertex e.anchor c q ha
      (by simpa [ContactGridEdge.upper, h] using hu)
  · simp only [ite_true]
    exact verticalContact_external_vertex e.anchor c q ha
      (by simpa [ContactGridEdge.upper, h] using hu)

end ContinuumCoulomb

end

end OAI
