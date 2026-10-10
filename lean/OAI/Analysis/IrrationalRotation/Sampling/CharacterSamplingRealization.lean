import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingTests
import OAI.Analysis.IrrationalRotation.Sampling.CharacterPhaseRealization

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace Invariant233.CharacterSampling

theorem exists_realized_sampling_block {θ : ℝ} (hθ : Irrational θ)
    {m : ℕ} (hm : 200 ≤ m) (target : Fin m → ℝ)
    (htarget0 : ∀ i, 0 < target i) (htarget1 : ∀ i, target i < 1)
    {q₀ : ℕ} (hq₀ : 0 < q₀) (R : ℝ)
    (U : Set (Fin m → ℝ)) (hU : U ∈ 𝓝 target)
    (r : ℕ) (powers : Fin r → Finset ℕ) (δ : Fin r → Bool → ℝ)
    (hcut : ∀ k, ∀ n ∈ powers k, ∀ i, Int.fract ((n : ℝ) * target i) ≠ 0)
    (hbound : ∀ k endpoint,
      (∫ y : UnitAddTorus (Fin m), squaredError m (powers k) endpoint (target,y)) < δ k endpoint) :
    ∃ q : ℕ → ℕ,
      q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧
      (∀ i < m, R ≤ (q (i + 1) : ℝ) / (q i : ℝ)) ∧
      (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∈ U ∧
      ∀ k endpoint,
        (∫ x : UnitAddCircle, squaredError m (powers k) endpoint
          ((fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)),
            fun i : Fin m => (q (i.val + 1) : ℤ) • x)) < δ k endpoint := by
  classical
  let target' : ℕ → ℝ := fun i => if h : i < m then target ⟨i,h⟩ else 1/2
  have ht0 : ∀ i, 0 < target' i := by
    intro i
    dsimp only [target']
    split_ifs with hi
    · exact htarget0 ⟨i,hi⟩
    · norm_num
  have ht1 : ∀ i, target' i < 1 := by
    intro i
    dsimp only [target']
    split_ifs with hi
    · exact htarget1 ⟨i,hi⟩
    · norm_num
  obtain ⟨Q, hzero, hpos, hstrict, hdiv, hgap, hphase'⟩ :=
    PrescribedPhaseRealization.exists_phase_approximation_family hθ target' ht0 ht1 hq₀
  let phase : ℕ → Fin m → ℝ := fun j i => Int.fract ((Q j (i.val + 1) : ℝ) * θ)
  have hphase : Tendsto phase atTop (𝓝 target) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [phase, target', dite_eq_left i.isLt] using hphase' i.val
  have hratios : ∀ᶠ j in atTop, ∀ i < m,
      R ≤ (Q j (i + 1) : ℝ) / (Q j i : ℝ) := by
    have hfinite : ∀ᶠ j in atTop, ∀ i ∈ Finset.range m,
        R ≤ (Q j (i + 1) : ℝ) / (Q j i : ℝ) := by
      rw [Finset.eventually_all]
      intro i hi
      exact (hgap i).eventually_ge_atTop R
    simpa only [Finset.mem_range] using hfinite
  have htests : ∀ᶠ j in atTop, ∀ k endpoint,
      (∫ x : UnitAddCircle, squaredError m (powers k) endpoint
        (phase j, fun i : Fin m => (Q j (i.val + 1) : ℤ) • x)) < δ k endpoint := by
    apply Filter.eventually_all.mpr
    intro k
    apply Filter.eventually_all.mpr
    intro endpoint
    have hlim := tendsto_integral_squaredError hm (powers k) endpoint
      (fun j i => Q j (i + 1)) (fun j i => hpos j (i + 1))
      (fun j i l hil => (hstrict j).monotone (Nat.add_le_add_right hil 1))
      (fun i _ => hgap (i + 1)) hphase (hcut k)
    exact hlim.eventually_lt_const (hbound k endpoint)
  obtain ⟨j, ⟨⟨hjratio, hjU⟩, hjtests⟩⟩ :=
    ((hratios.and (hphase.eventually hU)).and htests).exists
  exact ⟨Q j, hzero j, hpos j, hstrict j, hdiv j, hjratio, hjU, hjtests⟩

end Invariant233.CharacterSampling

end

end OAI
