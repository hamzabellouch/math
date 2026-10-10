import OAI.GroupTheory.PolycyclicRecognition.Algebra.OrderedInterpolationRadius

namespace OAI

/-! # Stability of ordered interpolation under changes of mass -/

namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

def InterpolationWeightControl (c : ControlledContraction G) (D : ℝ) (n : ℕ) (K : ℝ) : Prop :=
  ∀ (l : List I) (p₀ : G) (v : I → G) (a b : I → ℝ),
    l.length ≤ n → (∀ i ∈ l, 0 ≤ a i) → (∀ i ∈ l, 0 ≤ b i) →
    (∀ i ∈ l, ∀ j ∈ l, dist (v i) (v j) ≤ D) →
    min (listMass a l) (listMass b l) *
        dist (orderedCenter c p₀ v a l) (orderedCenter c p₀ v b l) ≤
      K * listVariation a b l

/-- On lists of bounded length and bounded image diameter, ordered
interpolation is uniformly Lipschitz on probability weights. The stronger
weighted estimate also covers vanishing tail masses in the recursion. -/
theorem exists_interpolation_weight_control (c : ControlledContraction G)
    {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ InterpolationWeightControl (I := I) c D n K := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro l p₀ v a b hlen ha hb hdiam
    have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    simp [hl, listMass, listVariation]
  | succ n ih =>
    obtain ⟨K, hK, hweight⟩ := ih
    obtain ⟨R, hR, hrad⟩ := exists_interpolation_radius (I := I) c hD n
    obtain ⟨C, hC, hcontrol⟩ := c.bounds R hR
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    refine ⟨C * (2 + K), mul_nonneg hC0 (by linarith), ?_⟩
    intro l p₀ v a b hlen ha hb hdiam
    cases l with
    | nil => simp [listMass, listVariation]
    | cons i l =>
      cases l with
      | nil =>
        simp only [orderedCenter_singleton, dist_self, mul_zero]
        exact mul_nonneg (mul_nonneg hC0 (by linarith)) (listVariation_nonneg a b [i])
      | cons j tail =>
        let l := j :: tail
        have hlt : l.length ≤ n := by
          change (j :: tail).length ≤ n
          simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen
        have hat : ∀ k ∈ l, 0 ≤ a k := fun k hk => ha k (List.mem_cons_of_mem i hk)
        have hbt : ∀ k ∈ l, 0 ≤ b k := fun k hk => hb k (List.mem_cons_of_mem i hk)
        have hdiamt : ∀ k ∈ l, ∀ m ∈ l, dist (v k) (v m) ≤ D :=
          fun k hk m hm => hdiam k (List.mem_cons_of_mem i hk) m (List.mem_cons_of_mem i hm)
        have hi : ∀ k ∈ l, dist (v k) (v i) ≤ D :=
          fun k hk => hdiam k (List.mem_cons_of_mem i hk) i (by simp)
        have hra := hrad l p₀ v a (by simp [l]) hlt hat hdiamt (v i) hi
        have hrb := hrad l p₀ v b (by simp [l]) hlt hbt hdiamt (v i) hi
        have hA := listMass_nonneg a (i :: l) ha
        have hB := listMass_nonneg b (i :: l) hb
        have hU := listMass_nonneg a l hat
        have hV := listMass_nonneg b l hbt
        have hδ := listVariation_nonneg a b (i :: l)
        change min (listMass a (i :: l)) (listMass b (i :: l)) *
          dist (orderedCenter c p₀ v a (i :: l)) (orderedCenter c p₀ v b (i :: l)) ≤ _
        by_cases hAz : listMass a (i :: l) = 0
        · rw [hAz, min_eq_left hB, zero_mul]
          exact mul_nonneg (mul_nonneg hC0 (by linarith)) hδ
        by_cases hBz : listMass b (i :: l) = 0
        · rw [hBz, min_eq_right hA, zero_mul]
          exact mul_nonneg (mul_nonneg hC0 (by linarith)) hδ
        have hAp : 0 < listMass a (i :: l) := lt_of_le_of_ne hA (Ne.symm hAz)
        have hBp : 0 < listMass b (i :: l) := lt_of_le_of_ne hB (Ne.symm hBz)
        have huA : listMass a l ≤ listMass a (i :: l) := by
          change _ ≤ a i + listMass a l
          exact le_add_of_nonneg_left (ha i (by simp))
        have hvB : listMass b l ≤ listMass b (i :: l) := by
          change _ ≤ b i + listMass b l
          exact le_add_of_nonneg_left (hb i (by simp))
        have hsa := listMass_tail_fraction_mem a i l ha
        have hsb := listMass_tail_fraction_mem b i l hb
        have hc := hcontrol (v i) (orderedCenter c p₀ v a l) (orderedCenter c p₀ v b l)
          hra hrb _ hsa _ hsb
        have hm : 0 ≤ min (listMass a (i :: l)) (listMass b (i :: l)) := le_min hA hB
        have htime := min_mass_mul_abs_fraction_sub_le hAp hBp hU huA hV hvB
        have htime' : min (listMass a (i :: l)) (listMass b (i :: l)) *
            |listMass a l / listMass a (i :: l) - listMass b l / listMass b (i :: l)| ≤
            2 * listVariation a b (i :: l) := by
          have h₁ := abs_listMass_sub_le a b l
          have h₂ := abs_listMass_sub_le a b (i :: l)
          have htail : listVariation a b l ≤ listVariation a b (i :: l) := by
            change _ ≤ |a i - b i| + listVariation a b l
            exact le_add_of_nonneg_left (abs_nonneg _)
          linarith
        have hspace := min_mass_mul_min_fraction_le hAp hBp hU hV
        have hspace' : min (listMass a (i :: l)) (listMass b (i :: l)) *
            min (listMass a l / listMass a (i :: l)) (listMass b l / listMass b (i :: l)) *
              dist (orderedCenter c p₀ v a l) (orderedCenter c p₀ v b l) ≤
            K * listVariation a b l := by
          exact (mul_le_mul_of_nonneg_right hspace dist_nonneg).trans
            (hweight l p₀ v a b hlt hat hbt hdiamt)
        have htail : listVariation a b l ≤ listVariation a b (i :: l) := by
          change _ ≤ |a i - b i| + listVariation a b l
          exact le_add_of_nonneg_left (abs_nonneg _)
        have hc' := mul_le_mul_of_nonneg_left hc hm
        change min (listMass a (i :: l)) (listMass b (i :: l)) *
          dist (c.contract (v i) _ _) (c.contract (v i) _ _) ≤ _
        calc
          _ ≤ C * (2 * listVariation a b (i :: l) + K * listVariation a b l) := by
            nlinarith only [hc', mul_le_mul_of_nonneg_left htime' hC0,
              mul_le_mul_of_nonneg_left hspace' hC0]
          _ ≤ C * (2 + K) * listVariation a b (i :: l) := by
            nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hK) hC0]

end PolycyclicRecognition

end OAI
