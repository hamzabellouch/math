import OAI.Analysis.IrrationalRotation.Sampling.SamplingTestContinuity
import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingLimit
import OAI.Analysis.IrrationalRotation.Sampling.CharacterPhaseRealization

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Invariant233.SamplingTests

theorem tendsto_integral_errorSq (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : Finset ℕ) (q : ℕ → ℕ → ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < d → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Fin d → ℝ} {τ : Fin d → ℝ} (ha : Tendsto a atTop (𝓝 τ))
    (hphase : ∀ n ∈ s, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0) :
    Tendsto (fun j => ∫ x : Circle,
      errorSq endpoint m d s (a j, fun i : Fin d => (q j i.val : ℤ) • x)) atTop
      (𝓝 (∫ y : UnitAddTorus (Fin d), errorSq endpoint m d s (τ,y))) := by
  exact CharacterLaws.tendsto_integral_character_phase_of_ae_continuous
    q d hq hmono hgap ha (measurable_errorSq endpoint m d s)
    (ae_joint_continuousAt_errorSq endpoint hm d s τ hphase)
    (sq_nonneg _) (fun z => (errorSq_bounds endpoint (by omega) d s z).2)

theorem eventually_integral_errorSq_lt (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : Finset ℕ) (q : ℕ → ℕ → ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < d → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Fin d → ℝ} {τ : Fin d → ℝ} (ha : Tendsto a atTop (𝓝 τ))
    (hphase : ∀ n ∈ s, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0)
    {δ : ℝ} (hδ : (∫ y : UnitAddTorus (Fin d), errorSq endpoint m d s (τ,y)) < δ) :
    ∀ᶠ j in atTop, (∫ x : Circle,
      errorSq endpoint m d s (a j, fun i : Fin d => (q j i.val : ℤ) • x)) < δ :=
  (tendsto_integral_errorSq endpoint hm d s q hq hmono hgap ha hphase).eventually_lt_const hδ

theorem eventually_simultaneous_errorSq_lt {ι : Type*} [Finite ι]
    {m : ℕ} (hm : 200 ≤ m) (d : ℕ) (s : ι → Finset ℕ)
    (q : ℕ → ℕ → ℕ) (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < d → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Fin d → ℝ} {τ : Fin d → ℝ} (ha : Tendsto a atTop (𝓝 τ))
    (hphase : ∀ r, ∀ n ∈ s r, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0)
    (δ : ι → Bool → ℝ)
    (hδ : ∀ r endpoint, (∫ y : UnitAddTorus (Fin d),
      errorSq endpoint m d (s r) (τ,y)) < δ r endpoint) :
    ∀ᶠ j in atTop, ∀ r endpoint, (∫ x : Circle,
      errorSq endpoint m d (s r) (a j, fun i : Fin d => (q j i.val : ℤ) • x)) <
        δ r endpoint := by
  apply Filter.eventually_all.mpr
  intro r
  apply Filter.eventually_all.mpr
  intro endpoint
  exact eventually_integral_errorSq_lt endpoint hm d (s r) q hq hmono hgap ha
    (hphase r) (hδ r endpoint)

theorem exists_character_sampling_block {ι : Type*} [Finite ι]
    {θ : ℝ} (hθ : Irrational θ) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : ι → Finset ℕ) (τ : Fin d → ℝ)
    (hτ : ∀ i, 0 < τ i ∧ τ i < 1)
    (hphase : ∀ r, ∀ n ∈ s r, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0)
    (δ : ι → Bool → ℝ)
    (hδ : ∀ r endpoint, (∫ y : UnitAddTorus (Fin d),
      errorSq endpoint m d (s r) (τ,y)) < δ r endpoint)
    (U : Set (Fin d → ℝ)) (hU : U ∈ 𝓝 τ) (R : ℝ)
    {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧
      (∀ i < d, R ≤ (q (i + 1) : ℝ) / q i) ∧
      (fun i : Fin d => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∈ U ∧
      ∀ r endpoint, (∫ x : Circle, errorSq endpoint m d (s r)
        ((fun i : Fin d => Int.fract ((q (i.val + 1) : ℝ) * θ)),
         (fun i : Fin d => (q (i.val + 1) : ℤ) • x))) < δ r endpoint := by
  classical
  let target : ℕ → ℝ := fun i => if hi : i < d then τ ⟨i,hi⟩ else 1/2
  have ht0 : ∀ i, 0 < target i := by
    intro i
    dsimp [target]
    split_ifs with hi
    · exact (hτ ⟨i,hi⟩).1
    · norm_num
  have ht1 : ∀ i, target i < 1 := by
    intro i
    dsimp [target]
    split_ifs with hi
    · exact (hτ ⟨i,hi⟩).2
    · norm_num
  obtain ⟨q, hzero, hpos, hstrict, hdiv, hgap, hlimit⟩ :=
    PrescribedPhaseRealization.exists_phase_approximation_family hθ target ht0 ht1 hq₀
  let a : ℕ → Fin d → ℝ := fun j i => Int.fract ((q j (i.val + 1) : ℝ) * θ)
  have ha : Tendsto a atTop (𝓝 τ) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [target, dite_eq_left i.isLt] using hlimit i.val
  have htests := eventually_simultaneous_errorSq_lt hm d s
    (fun j i => q j (i+1)) (fun j i => hpos j (i+1))
    (fun j => (hstrict j).monotone.comp (fun i k hik => Nat.add_le_add_right hik 1))
    (fun i _ => hgap (i+1)) ha hphase δ hδ
  have hratios : ∀ᶠ j in atTop, ∀ i ∈ Finset.range d,
      R ≤ (q j (i+1) : ℝ) / q j i := by
    rw [Finset.eventually_all]
    intro i hi
    exact (hgap i).eventually_ge_atTop R
  obtain ⟨j, hjtest, hjU, hjR⟩ := (htests.and ((ha.eventually hU).and hratios)).exists
  refine ⟨q j, hzero j, hpos j, hstrict j, hdiv j, ?_, hjU, hjtest⟩
  intro i hi
  exact hjR i (Finset.mem_range.mpr hi)

end Invariant233.SamplingTests

end

end OAI
