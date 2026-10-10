import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferFirstFailure
import OAI.Probability.Ballisticity.Estimates.PairUpwardRetention

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma hitKernel_height_zero {d : ℕ} (ℓ : Vector d) (x : Lattice d) (ω : Environment d) :
    hitKernel (Strip ℓ x 0) (Upper ℓ x 0) (ω,x) = Measure.dirac x := by
  apply Measure.ext
  intro U hU
  rw [hitKernel_apply_eq_hit (disjoint_strip_upper _ _ _)]
  have heq : Hit (Strip ℓ x 0) (Upper ℓ x 0 ∩ U) =ᵐ[quenchedKernel (ω,x)]
      (fun _ : Path d => x∈U) := by
    filter_upwards [quenched_initial_ae (ω,x)] with X hX
    apply propext
    constructor
    · intro h
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp h
      have hn0 : n=0 := by
        by_contra hn0
        have hh := hn.2 0 (Nat.pos_of_ne_zero hn0)
        exact (not_lt_of_ge hh.1) (by simpa only [add_zero] using hh.2)
      subst n
      have hxU : x∈U := by simpa only [hX] using hn.1.2
      exact hxU
    · intro h
      have hxU : x∈U := h
      apply Set.mem_iUnion.mpr
      refine ⟨0,⟨?_,?_⟩,by intro j hj; omega⟩
      · change dot (realPosition x) ℓ+0 ≤ dot (realPosition (X 0)) ℓ
        simp only [hX,add_zero,le_refl]
      · simpa only [hX] using hxU
  rw [measure_congr heq,Measure.dirac_apply' _ hU]
  by_cases hu : x∈U <;> simp [hu]
  · change (quenchedKernel (ω,x)) Set.univ = 1
    simp
  · change (quenchedKernel (ω,x)) ∅ = 0
    simp

lemma rawPairEndpointLaw_zero {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d × Lattice d) : rawPairEndpointLaw ℓ 0 ω x = Measure.dirac x := by
  simp only [rawPairEndpointLaw,Nat.cast_zero,hitKernel_height_zero,Measure.dirac_prod_dirac,Prod.mk.eta]

lemma rawPairMixture_zero {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (π : Measure (Lattice d × Lattice d)) : rawPairMixture ℓ 0 π ω = π := by
  unfold rawPairMixture
  change π.bind (fun x => rawPairEndpointLaw ℓ 0 ω x) = π
  simp_rw [rawPairEndpointLaw_zero]
  exact Measure.bind_dirac

lemma pairKernelMass_zero_of_supported {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (z : ℝ) (hπ : ∀ᵐ x ∂π, z ≤ signedCoordinate f (x.2-x.1)) :
    pairKernelMass ℓ f 0 z π ω = 1 := by
  unfold pairKernelMass
  rw [←rawPairMixture_apply,rawPairMixture_zero]
  exact (mem_ae_iff_prob_eq_one (Set.to_countable _ |>.measurableSet)).mp hπ
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferStageRetainedLaw {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (H : ℕ) (ω : Environment d) (κ : ℝ≥0) : Measure (Lattice d × Lattice d) :=
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  let j := bufferFirstFailure ℓ f a z g π H ω
  if pairKernelMass ℓ f j z (π ω).val ω < ENNReal.ofReal g then
    upwardRetainedLaw e f (j-1) z (π ω).val ω κ
  else if ENNReal.ofReal g ≤ pairKernelMass ℓ f H (z₀+(1+α)*r) (π ω).val ω then
    retainedPairLaw ℓ f H (z₀+(1+α)*r) (π ω).val ω
  else retainedPairLaw ℓ f H z (π ω).val ω

lemma bufferFirstFailure_eq_top_of_pass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (a z g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d)
    (hp : ENNReal.ofReal g ≤ pairKernelMass ℓ f (bufferFirstFailure ℓ f a z g π H ω) z (π ω).val ω) :
    bufferFirstFailure ℓ f a z g π H ω = H := by
  have hb := bufferFirstFailure_bounds ℓ f a z g π hH ω
  apply le_antisymm hb.2
  by_contra hn
  have hlt : bufferFirstFailure ℓ f a z g π H ω < H := lt_of_not_ge hn
  exact (not_lt_of_ge hp) (bufferFirstFailure_fails_of_lt ℓ f a z g π hH ω hlt)

lemma bufferStageEvent_iff_last_tests {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    BufferStageEvent ℓ f H z₀ r ε α g (π ω).val ω ↔
      ENNReal.ofReal g ≤ pairKernelMass ℓ f
        (bufferFirstFailure ℓ f a (z₀+(1-ε)*r) g π H ω) (z₀+(1-ε)*r) (π ω).val ω ∧
      ENNReal.ofReal g ≤ pairKernelMass ℓ f H (z₀+(1+α)*r) (π ω).val ω := by
  constructor
  · intro h
    have hb := bufferFirstFailure_bounds ℓ f a (z₀+(1-ε)*r) g π hH ω
    exact ⟨h.1 _ hb.1 hb.2,h.2⟩
  · rintro ⟨hp,hg⟩
    refine ⟨?_,hg⟩
    intro j hj hjH
    have heq := bufferFirstFailure_eq_top_of_pass ℓ f a (z₀+(1-ε)*r) g π hH ω hp
    rcases lt_or_eq_of_le hjH with hlt|rfl
    · apply before_bufferFirstFailure_pass ℓ f a (z₀+(1-ε)*r) g π H ω hj
      simpa only [heq] using hlt
    · simpa only [heq] using hp

lemma bufferStageRetainedLaw_le {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) :
    bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ ≤
      rawPairMixture (realPosition (step e))
        (bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω) (π ω).val ω := by
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  let j := bufferFirstFailure ℓ f a z g π H ω
  have hj : 1 ≤ j := (bufferFirstFailure_bounds ℓ f a z g π hH ω).1
  unfold bufferStageRetainedLaw
  dsimp only
  split
  · have hn : j-1+1=j := by omega
    simpa only [hn] using upwardRetainedLaw_le e f (j-1) z (π ω).val ω hκ
  · rename_i hp
    have hjH : j=H := bufferFirstFailure_eq_top_of_pass ℓ f a z g π hH ω (le_of_not_gt hp)
    change _ ≤ rawPairMixture ℓ j (π ω).val ω
    rw [hjH]
    split <;> exact retainedPairLaw_le _ _ _ _ _ _

lemma bufferStageRetainedLaw_mass_lower {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0)
    (hκ1 : κ ≤ 1) (hg1 : g ≤ 1) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    [IsProbabilityMeasure (π ω).val]
    (hgap : ∀ᵐ x ∂(π ω).val, z₀+r ≤ signedCoordinate f (x.2-x.1)) :
    (κ : ℝ≥0∞)^2 * ENNReal.ofReal g ≤ bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ Set.univ := by
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  let j := bufferFirstFailure ℓ f a z g π H ω
  have hj : 1 ≤ j := (bufferFirstFailure_bounds ℓ f a z g π hH ω).1
  have hκ2 : (κ : ℝ≥0∞)^2 ≤ 1 := by
    have hc : (κ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hκ1
    simpa only [one_pow] using pow_le_pow_left' hc 2
  have hsmall : (κ : ℝ≥0∞)^2 * ENNReal.ofReal g ≤ ENNReal.ofReal g := by
    calc
      _ ≤ 1*ENNReal.ofReal g := mul_le_mul_left hκ2 _
      _ = _ := one_mul _
  unfold bufferStageRetainedLaw
  dsimp only
  split
  · rw [upwardRetainedLaw_mass]
    apply mul_le_mul_right
    by_cases hz : j-1=0
    · change ENNReal.ofReal g ≤ pairKernelMass ℓ f (j-1) z (π ω).val ω
      rw [hz,pairKernelMass_zero_of_supported ℓ f ω (π ω).val z]
      · exact ENNReal.ofReal_le_one.mpr hg1
      · filter_upwards [hgap] with x hx
        dsimp [z]
        nlinarith
    · apply before_bufferFirstFailure_pass ℓ f a z g π H ω (Nat.pos_of_ne_zero hz)
      change j-1<j
      omega
  · rename_i hp
    have hjH : j=H := bufferFirstFailure_eq_top_of_pass ℓ f a z g π hH ω (le_of_not_gt hp)
    split
    · rename_i hg
      rw [retainedPairLaw_mass]
      exact hsmall.trans hg
    · rw [retainedPairLaw_mass]
      apply hsmall.trans
      have hh : ENNReal.ofReal g ≤ pairKernelMass ℓ f j z (π ω).val ω := le_of_not_gt hp
      change ENNReal.ofReal g ≤ pairKernelMass ℓ f H z (π ω).val ω
      simpa only [hjH] using hh
end DirectionalTransience

end

end

end OAI
