import OAI.MeasureTheory.Falconer.Angular.CircleMaskSupport

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

noncomputable def occupiedAnchorPaths (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ) : Finset CellPath := by
  classical
  exact (dyadicPaths n).filter fun P => 0 < ρ (Q.descendant P).carrier

noncomputable def spatialAnchorMask (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (dir : UnitCircle) : ℝ := by
  classical
  exact ∑ P ∈ occupiedAnchorPaths Q ρ n,
    if x ∈ (Q.descendant P).carrier then circleTestMask (G P) d hd dir else 0

theorem spatialAnchorMask_eq (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) {P : CellPath}
    (hP : P ∈ occupiedAnchorPaths Q ρ n) {x : Plane} (hx : x ∈ (Q.descendant P).carrier)
    (dir : UnitCircle) : spatialAnchorMask Q ρ n G d hd x dir = circleTestMask (G P) d hd dir := by
  classical
  unfold spatialAnchorMask
  rw [Finset.sum_eq_single P]
  · simp [hx]
  · intro c hc hcP
    have hdj := Q.descendants_disjoint hQ
      (((mem_dyadicPaths n c).mp (Finset.mem_filter.mp hc).1).trans
        ((mem_dyadicPaths n P).mp (Finset.mem_filter.mp hP).1).symm) hcP
    have hx' : x ∉ (Q.descendant c).carrier := fun h => Set.disjoint_left.mp hdj h hx
    simp [hx']
  · intro h; exact (h hP).elim

theorem spatialAnchorMask_zero (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) {x : Plane}
    (hx : ∀ P ∈ occupiedAnchorPaths Q ρ n, x ∉ (Q.descendant P).carrier) (dir : UnitCircle) :
    spatialAnchorMask Q ρ n G d hd x dir = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro P hP
  simp [hx P hP]

theorem spatialAnchorMask_bounds (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (dir : UnitCircle) :
    0 ≤ spatialAnchorMask Q ρ n G d hd x dir ∧ spatialAnchorMask Q ρ n G d hd x dir ≤ 1 := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    rw [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx]
    exact circleTestMask_bounds _ _ _ _
  · push Not at hx
    rw [spatialAnchorMask_zero Q ρ n G d hd hx]
    norm_num

@[fun_prop] theorem measurable_spatialAnchorMask (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Measurable (fun z : Plane × UnitCircle => spatialAnchorMask Q ρ n G d hd z.1 z.2) := by
  classical
  apply Finset.measurable_sum
  intro P _
  exact Measurable.ite ((Q.descendant P).measurable.preimage measurable_fst)
    ((measurable_circleTestMask _ _ _).comp measurable_snd) measurable_const

theorem spatialAnchorMask_contDiff (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) :
    ContDiff ℝ ∞ (fun θ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection θ)) := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    simpa only [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx] using circleTestMask_angular_contDiff (G P) d hd
  · push Not at hx
    simp only [spatialAnchorMask_zero Q ρ n G d hd hx]
    exact contDiff_const

theorem ae_occupied_anchor (Q : DyadicSquare) (ρ : Measure Plane) (hcarry : ρ Q.carrierᶜ = 0) (n : ℕ) :
    ∀ᵐ x ∂ρ, ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier := by
  have hroot : ∀ᵐ x ∂ρ, x ∈ Q.carrier := ae_iff.mpr hcarry
  have hz : ∀ᵐ x ∂ρ, ∀ P : CellPath, ρ (Q.descendant P).carrier = 0 → x ∉ (Q.descendant P).carrier := by
    apply ae_all_iff.mpr
    intro P
    by_cases h : ρ (Q.descendant P).carrier = 0
    · filter_upwards [show ∀ᵐ x ∂ρ, x ∉ (Q.descendant P).carrier from by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using h] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall (fun _ h' => (h h').elim)
  filter_upwards [hroot,hz] with x hx hzero
  obtain ⟨P,hP,hx⟩ := Q.mem_descendant_at_depth n hx
  refine ⟨P,Finset.mem_filter.mpr ⟨hP,?_⟩,hx⟩
  exact bot_lt_iff_ne_bot.mpr (fun he => hzero P he hx)

end PlanarFalconer

end OAI
