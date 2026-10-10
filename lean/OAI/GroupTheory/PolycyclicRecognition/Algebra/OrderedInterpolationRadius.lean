import OAI.GroupTheory.PolycyclicRecognition.Algebra.OrderedInterpolation

namespace OAI

/-! # Uniform radius of interpolation on a bounded number of vertices -/

namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

theorem listMass_tail_fraction_mem (a : I → ℝ) (i : I) (l : List I)
    (ha : ∀ j ∈ i :: l, 0 ≤ a j) :
    listMass a l / listMass a (i :: l) ∈ Set.Icc (0 : ℝ) 1 := by
  have ht := listMass_nonneg a l (fun j hj => ha j (by simp [hj]))
  have htot := listMass_nonneg a (i :: l) ha
  refine ⟨div_nonneg ht htot, ?_⟩
  by_cases hz : listMass a (i :: l) = 0
  · simp [hz]
  · apply (div_le_one (lt_of_le_of_ne htot (Ne.symm hz))).mpr
    change listMass a l ≤ a i + listMass a l
    exact le_add_of_nonneg_left (ha i (by simp))

def InterpolationRadius (c : ControlledContraction G) (D : ℝ) (n : ℕ) (R : ℝ) : Prop :=
  ∀ (l : List I) (p₀ : G) (v : I → G) (a : I → ℝ),
    l ≠ [] → l.length ≤ n → (∀ i ∈ l, 0 ≤ a i) →
    (∀ i ∈ l, ∀ j ∈ l, dist (v i) (v j) ≤ D) →
    ∀ p : G, (∀ i ∈ l, dist (v i) p ≤ D) → dist (orderedCenter c p₀ v a l) p ≤ R

/-- With at most `n` input vertices of bounded diameter, interpolation
stays within a radius depending only on `n`, the diameter, and the contraction. -/
theorem exists_interpolation_radius (c : ControlledContraction G) {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ InterpolationRadius (I := I) c D n R := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro l p₀ v a hne hlen ha hdiam p hp
    have : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    exact (hne this).elim
  | succ n ih =>
    obtain ⟨R, hR, hrad⟩ := ih
    obtain ⟨C, hC, hcontrol⟩ := c.bounds R hR
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    refine ⟨C + D, add_nonneg hC0 hD, ?_⟩
    intro l p₀ v a hne hlen ha hdiam p hp
    cases l with
    | nil => exact (hne rfl).elim
    | cons i l =>
      cases l with
      | nil =>
        rw [orderedCenter_singleton]
        exact (hp i (by simp)).trans (le_add_of_nonneg_left hC0)
      | cons j tail =>
        have htlen : (j :: tail).length ≤ n := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen
        have hat : ∀ k ∈ j :: tail, 0 ≤ a k := fun k hk => ha k (List.mem_cons_of_mem i hk)
        have hdiamt : ∀ k ∈ j :: tail, ∀ m ∈ j :: tail, dist (v k) (v m) ≤ D :=
          fun k hk m hm => hdiam k (List.mem_cons_of_mem i hk) m (List.mem_cons_of_mem i hm)
        have hi : ∀ k ∈ j :: tail, dist (v k) (v i) ≤ D :=
          fun k hk => hdiam k (List.mem_cons_of_mem i hk) i (by simp)
        have hr := hrad (j :: tail) p₀ v a (by simp) htlen hat hdiamt (v i) hi
        have hs := listMass_tail_fraction_mem a i (j :: tail) ha
        have hb := c.dist_center_le hcontrol hr hs
        change dist (c.contract (v i) (listMass a (j :: tail) / listMass a (i :: j :: tail))
          (orderedCenter c p₀ v a (j :: tail))) p ≤ C + D
        exact (dist_triangle _ (v i) p).trans (add_le_add
          (hb.trans (mul_le_of_le_one_right hC0 hs.2)) (hp i (by simp)))

end PolycyclicRecognition

end OAI
