import OAI.MeasureTheory.Falconer.Recursion.ProfilePacking

namespace OAI

/-! # Ball bounds obtained from actual occupied-cell profile estimates -/

namespace Falconer.Regularization
open MeasureTheory Set Metric
open scoped ENNReal
variable {d : ℕ}

noncomputable def cellsMeetingBall (Q : DyadicCube d) (n : ℕ) (x : Space d) (r : ℝ) :
    Finset (CellPath d) := by
  classical
  exact (cubePaths d n).filter fun p => ∃ y ∈ (Q.descendant p).carrier, y ∈ ball x r

theorem cellsMeetingBall_card (Q : DyadicCube d) (hQ : 0 < Q.side)
    (n : ℕ) (x : Space d) {r C : ℝ} (hC : 0 ≤ C) (hr : r ≤ C*(Q.side/(2:ℝ)^n)) :
    (cellsMeetingBall Q n x r).card ≤ (2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d := by
  classical
  let S := cellsMeetingBall Q n x r
  have hS (p) (hp : p ∈ S) : p.length = n :=
    (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
  have hcenter (p) (hp : p ∈ S) :
      dist (Q.descendant p).center x ≤ (C+Real.sqrt d)*(Q.side/(2:ℝ)^n) := by
    obtain ⟨y,hy,hyb⟩ := (Finset.mem_filter.mp hp).2
    have hc := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le
      ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p)) hy
    rw [Q.descendant_side,hS p hp] at hc
    have hb := (mem_ball.mp hyb).le
    have hh := (dist_triangle (Q.descendant p).center y x).trans (add_le_add hc hb)
    nlinarith
  have hh := dyadic_ancestor_ball_count Q hQ S hS (le_refl n) x
    (C := C+Real.sqrt d) (by positivity) (le_refl _) hcenter
  have he : S.image (List.take n) = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      simpa only [List.take_of_length_le (hS q hq).le] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨p,hp,List.take_of_length_le (hS p hp).le⟩
  rw [he] at hh
  have hc : 2*(C+Real.sqrt d)+2*Real.sqrt d = 2*C+4*Real.sqrt d := by ring
  simpa only [hc] using hh

theorem measure_ball_le_cell_count (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (hcarry : ρ Q.carrierᶜ = 0)
    (n : ℕ) (x : Space d) (r : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hcell : ∀ p ∈ cubePaths d n, 0 < ρ (Q.descendant p).carrier →
      (ρ (Q.descendant p).carrier).toReal ≤ M) :
    (ρ (ball x r)).toReal ≤ (cellsMeetingBall Q n x r).card*M := by
  classical
  let S := cellsMeetingBall Q n x r
  have hcover : ball x r ⊆ leafUnion Q S ∪ Q.carrierᶜ := by
    intro y hy
    by_cases hyQ : y ∈ Q.carrier
    · obtain ⟨p,hp,hyp⟩ := Q.mem_descendant_at_depth n hyQ
      exact Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,y,hyp,hy⟩,hyp⟩)
    · exact Or.inr hyQ
  have hmass : ρ (ball x r) ≤ ρ (leafUnion Q S) := by
    apply (measure_mono hcover).trans
    have hh := measure_union_le (leafUnion Q S) Q.carrierᶜ (μ := ρ)
    rwa [hcarry,add_zero] at hh
  calc
    _ ≤ (ρ (leafUnion Q S)).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hmass
    _ = ∑ p ∈ S, (ρ (Q.descendant p).carrier).toReal :=
      restriction_total_mass_real Q hQ ρ (Finset.filter_subset _ _)
    _ ≤ ∑ _p ∈ S, M := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpos : 0 < ρ (Q.descendant p).carrier
      · exact hcell p (Finset.mem_filter.mp hp).1 hpos
      · rw [nonpos_iff_eq_zero.mp (le_of_not_gt hpos),ENNReal.toReal_zero]
        exact hM
    _ = _ := by simp [S]

theorem sourceClass_root_null (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) (p : CellPath d) :
    sourceClass Q μ N B p Q.carrierᶜ = 0 := by
  simp only [sourceClass,normalizedClass,classMeasure,Measure.smul_apply,smul_eq_mul]
  rw [Measure.restrict_apply Q.measurable.compl]
  have he : Q.carrierᶜ ∩ leafUnion Q
      (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
        (regularizationLabel Q μ N B p)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (leafUnion_subset Q hQ _ hx.2)
  rw [he,measure_empty,mul_zero]

theorem sourceClass_ball_upper (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {n : ℕ} (hn : n ≤ N) (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    (sourceClass Q μ N B p₀ (ball x (C*(Q.side/(2:ℝ)^n)))).toReal ≤
      ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)*
        (((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p₀ n)) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  have hh := measure_ball_le_cell_count Q hQ (sourceClass Q μ N B p₀)
    (sourceClass_root_null Q hQ μ N B p₀) n x (C*(Q.side/(2:ℝ)^n)) (by positivity)
    (fun p hp hpos => (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ hn
      ((mem_cubePaths _ _ _).mp hp) hpos).2)
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast cellsMeetingBall_card Q hQ n x hC (le_refl _)

end Falconer.Regularization

end OAI
