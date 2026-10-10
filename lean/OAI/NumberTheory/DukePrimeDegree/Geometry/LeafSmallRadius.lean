import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafLusin

namespace OAI

/-!
# Uniform small-radius control of nonatomic root leaves

The set denoted `X_ρ` in EKL (2006), Section 4.3, can have arbitrarily
large measure. The proof uses continuity from above twice: first on each
locally finite leaf, and then on the decreasing sets of bad base points.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_small_ball_mass_of_zero_atom (ν : Measure ℝ)
    (hfinite : ν (Metric.ball 0 1) ≠ ∞) (hzero : ν {0} = 0)
    (c : ℝ≥0∞) (hc : 0 < c) :
    ∃ m : ℕ, ν (Metric.ball 0 ((m + 1 : ℝ)⁻¹)) < c := by
  have hanti : Antitone (fun m : ℕ => Metric.ball (0 : ℝ) ((m + 1 : ℝ)⁻¹)) := by
    intro a b hab
    apply Metric.ball_subset_ball
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hmass : (⨅ m : ℕ, ν (Metric.ball 0 ((m + 1 : ℝ)⁻¹))) = 0 := by
    rw [← hanti.measure_iInter
      (fun _ => Metric.isOpen_ball.measurableSet.nullMeasurableSet)
      ⟨0, by simpa using hfinite⟩, real_iInter_ball_inv_nat, hzero]
  by_contra h
  push Not at h
  have : c ≤ 0 := hmass ▸ le_iInf h
  exact hc.not_ge this

/-- One radius works outside an arbitrarily small set of base points. -/
theorem exists_uniform_small_kernel_ball
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y ℝ)
    (hfinite : ∀ᵐ x ∂μ, κ x (Metric.ball 0 1) ≠ ∞)
    (hzero : ∀ᵐ x ∂μ, κ x {0} = 0)
    (c ε : ℝ≥0∞) (hc : 0 < c) (hε : ε ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧
      μ {x | c ≤ κ x (Metric.ball 0 ρ)} < ε := by
  let B : ℕ → Set Y := fun m => {x | c ≤ κ x (Metric.ball 0 ((m + 1 : ℝ)⁻¹))}
  have hBmeas (m : ℕ) : MeasurableSet (B m) :=
    measurableSet_le measurable_const (κ.measurable_coe Metric.isOpen_ball.measurableSet)
  have hBanti : Antitone B := by
    intro a b hab x hx
    exact hx.trans (measure_mono (Metric.ball_subset_ball
      (inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1))))
  have hnull : μ (⋂ m, B m) = 0 := by
    have hae : ∀ᵐ x ∂μ, x ∉ ⋂ m, B m := by
      filter_upwards [hfinite, hzero] with x hxfinite hxzero
      obtain ⟨m, hm⟩ := exists_small_ball_mass_of_zero_atom (κ x) hxfinite hxzero c hc
      intro hx
      exact hm.not_ge (mem_iInter.mp hx m)
    simpa only [not_not, ofPred_mem_eq] using ae_iff.mp hae
  have hmass : (⨅ m, μ (B m)) = 0 := by
    rw [← hBanti.measure_iInter (fun m => (hBmeas m).nullMeasurableSet)
      ⟨0, measure_ne_top μ _⟩, hnull]
  have hex : ∃ m, μ (B m) < ε := by
    by_contra h
    push Not at h
    have : ε ≤ 0 := hmass ▸ le_iInf h
    exact hε (le_antisymm this bot_le)
  obtain ⟨m, hm⟩ := hex
  refine ⟨(m + 3 : ℝ)⁻¹, by positivity, ?_, ?_⟩
  · rw [inv_lt_comm₀ (by positivity) (by positivity)]
    norm_num
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · apply lt_of_le_of_lt (measure_mono ?_) hm
    intro x hx
    change c ≤ κ x (Metric.ball 0 ((m + 1 : ℝ)⁻¹))
    change c ≤ κ x (Metric.ball 0 ((m + 3 : ℝ)⁻¹)) at hx
    apply hx.trans
    apply measure_mono
    apply Metric.ball_subset_ball
    exact inv_anti₀ (by positivity) (by linarith)

/-- The uniform-radius set for the actual intrinsic root leaves. -/
theorem exists_uniform_small_rootLeaf_ball
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (c ε : ℝ≥0∞) (hc : 0 < c) (hε : ε ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧
      μ {x | c ≤ intrinsicRootLeaf hij μ x (Metric.ball 0 ρ)} < ε := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    ae_intrinsicRootKernel_eq hij μ hfree
  have hzero : ∀ᵐ x ∂μ, κ x {0} = 0 := by
    filter_upwards [heq, hnontrivial,
      ae_intrinsicRootLeaf_zero_atom_or_trivial d hij μ hA] with x hx hn hz
    rw [hx]
    exact hz.resolve_right hn
  obtain ⟨ρ, hρ, hρhalf, hsmall⟩ := exists_uniform_small_kernel_ball μ κ
    (Filter.Eventually.of_forall fun x => measure_ball_lt_top.ne) hzero c ε hc hε
  refine ⟨ρ, hρ, hρhalf, ?_⟩
  have hcongr : {x | c ≤ intrinsicRootLeaf hij μ x (Metric.ball 0 ρ)} =ᵐ[μ]
      {x | c ≤ κ x (Metric.ball 0 ρ)} := by
    filter_upwards [heq] with x hx
    simp only [hx]
  rwa [measure_congr hcongr]

end DukePrimeDegree

end

end OAI
