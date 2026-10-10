import OAI.Analysis.KadisonKastler.WeakCPLimits

namespace OAI

/-! # Passing unit-ball approximation through weakly dense tests

A bounded target family has a weak operator ultralimit. The same
uniform approximation bound survives this limit, allowing bounds on
weakly dense unit-ball tests to control the full Kadison--Kastler gap.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A uniform approximation by the target unit ball survives an arbitrary
nontrivial coefficientwise convergent net. -/
theorem exists_unitBall_approx_of_weak_limit
    {ι : Type*} {l : Filter ι} [l.NeBot] (N : VonNeumannAlgebra H)
    (T : ι → H →L[ℂ] H) (a : H →L[ℂ] H)
    (hlim : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l
      (𝓝 (inner ℂ y (a x))))
    {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ i, ∃ b ∈ unitBall N, ‖T i - b‖ ≤ r) :
    ∃ b ∈ unitBall N, ‖a - b‖ ≤ r := by
  choose b hb hdist using hnear
  let ω : Ultrafilter ι := Ultrafilter.of l
  have hω : (ω : Filter ι) ≤ l := Ultrafilter.of_le l
  obtain ⟨c, hcn, hc⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω b 1
    zero_le_one (fun i => (hb i).2)
  have hcN : c ∈ N := Generator.Tracial.weak_operator_limit_mem N
    (fun i => ⟨b i, (hb i).1⟩) c hc
  refine ⟨c, ⟨hcN, hcn⟩, ?_⟩
  apply norm_le_of_weak_limit (l := (ω : Filter ι)) (fun i => T i - b i) (a - c) hr hdist
  intro x y
  simpa only [sub_apply, inner_sub_right] using
    ((hlim x y).mono_left hω).sub (hc x y)

/-- A family of contractions whose coefficientwise limits cover the
whole unit ball. No metrizability or choice of a sequence is required. -/
def WeakUnitBallDense {ι : Type*} (T : ι → H →L[ℂ] H) (M : VonNeumannAlgebra H) : Prop :=
  (∀ i, T i ∈ unitBall M) ∧
    ∀ a ∈ unitBall M, ∃ l : Filter ι, l.NeBot ∧
      ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (a x)))

theorem exists_unitBall_approx_of_weakly_dense_tests
    {ι : Type*} {M N : VonNeumannAlgebra H} (T : ι → H →L[ℂ] H)
    (hT : WeakUnitBallDense T M) {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ i, ∃ b ∈ unitBall N, ‖T i - b‖ ≤ r)
    (a : H →L[ℂ] H) (ha : a ∈ unitBall M) :
    ∃ b ∈ unitBall N, ‖a - b‖ ≤ r := by
  obtain ⟨l, hl, hlim⟩ := hT.2 a ha
  let : l.NeBot := hl
  exact exists_unitBall_approx_of_weak_limit N T a hlim hr hnear

/-- Two weakly dense test families suffice to bound the full gap. -/
theorem kkDistance_le_of_weakly_dense_tests
    {ι κ : Type*} (M N : VonNeumannAlgebra H)
    (T : ι → H →L[ℂ] H) (S : κ → H →L[ℂ] H)
    (hT : WeakUnitBallDense T M) (hS : WeakUnitBallDense S N)
    {r : ℝ} (hr : 0 ≤ r)
    (hTN : ∀ i, ∃ b ∈ unitBall N, ‖T i - b‖ ≤ r)
    (hSM : ∀ j, ∃ a ∈ unitBall M, ‖S j - a‖ ≤ r) :
    kkDistance M N ≤ r := by
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · intro a ha
    obtain ⟨b, hb, hab⟩ := exists_unitBall_approx_of_weakly_dense_tests T hT hr hTN a ha
    exact ⟨b, hb, by simpa only [dist_eq_norm] using hab⟩
  · intro b hb
    obtain ⟨a, ha, hba⟩ := exists_unitBall_approx_of_weakly_dense_tests S hS hr hSM b hb
    exact ⟨a, ha, by simpa only [dist_eq_norm] using hba⟩

end

end KadisonKastler

end OAI
