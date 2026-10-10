import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferExcess
import OAI.Probability.Ballisticity.Geometry.BufferElapsedHeight

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem actual_buffer_stage_count {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ (κ : ℝ≥0) (α s g R C : ℝ), 0 < κ ∧ κ ≤ 1 ∧ (∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u) ∧ 0 < α ∧ 0 < s ∧
      0 < g ∧ g ≤ 1 ∧ 1 ≤ R ∧ 0 < C ∧
      ∀ (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a),
      let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
      let root := bufferRootNode e f hef R a x hx
      ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
        Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
        (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ 1+(1-Real.exp (-s/4))⁻¹ ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ,
          (s*Real.log (1+α)/8)*(n:ℝ) ≤ Real.log C +
            Real.log ((bufferWordHeight (bufferHistory e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
              (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root ω n):ℝ)+1) +
            W ω*(Real.log (1+α)+s*Real.log (1+α)/8)) := by
  obtain ⟨κ,α,s,g,R,hκ,hκ1,hκae,hα,hs,hg,hg1,hR,hdata⟩ := actual_buffer_excess ν hue e f hef htrans
  obtain ⟨M,hM,hplan⟩ := positiveBufferPlan_linear_lower ν hue e f hef htrans
  let C := max R ((1+α)*M)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hC : 0 < C := hRpos.trans_le (le_max_left _ _)
  refine ⟨κ,α,s,g,R,C,hκ,hκ1,hκae,hα,hs,hg,hg1,hR,hC,?_⟩
  intro a x hx
  let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
  let root := bufferRootNode e f hef R a x hx
  obtain ⟨W,hW,hW0,hWi,hWe,hWb,hgrowth⟩ := hdata a x hx
  refine ⟨W,hW,hW0,hWi,hWb,?_⟩
  filter_upwards [hgrowth] with ω hω
  intro n
  let l := bufferHistory e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root ω n
  have ha : ω ∈ (bufferNodeAt e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
      (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root l).active := by
    rw [bufferNodeAt_active_iff_history,bufferHistory_length]
    exact ⟨Set.mem_univ _,rfl⟩
  have hupper := bufferNodeAt_radius_elapsed e f hef hRpos
    (buffer_contraction_choice hα hs).1.le hα.le hM (le_max_left R ((1+α)*M))
    (le_max_right R ((1+α)*M)) (signedCoordinate f (x.2-x.1)) g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f)
    (fun r hr => hplan r (hRpos.trans_le hr)) root rfl ω l ha
  have hp := hRpos.trans_le (bufferNodeAt_radius e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root le_rfl l)
  have hu := Real.log_le_log hp hupper
  have ht : 0 < (bufferWordHeight l:ℝ)+1 := by positivity
  rw [Real.log_mul hC.ne' ht.ne'] at hu
  have hl := hω n
  have hrlog := Real.log_nonneg hR
  change Real.log R+_ - _ ≤ Real.log (bufferNodeAt e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root l).radius at hl
  linarith
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma rawPairMixture_mono {d : ℕ} (ℓ : Vector d) (H : ℕ) (ω : Environment d)
    {π ρ : Measure (Lattice d × Lattice d)} (h : π ≤ ρ) :
    rawPairMixture ℓ H π ω ≤ rawPairMixture ℓ H ρ ω := by
  intro U
  simp only [rawPairMixture_apply]
  exact lintegral_mono' h le_rfl

lemma rawPairMixture_smul {d : ℕ} (ℓ : Vector d) (H : ℕ) (ω : Environment d)
    (π : Measure (Lattice d × Lattice d)) (c : ℝ≥0∞) :
    rawPairMixture ℓ H (c • π) ω = c • rawPairMixture ℓ H π ω := by
  ext U hU
  simp only [rawPairMixture_apply,lintegral_smul_measure,Measure.smul_apply,smul_eq_mul]

lemma normalizedMeasure_smul_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≤ μ Set.univ) :
    c • normalizedMeasure μ ≤ μ := by
  calc
    c • normalizedMeasure μ ≤ μ Set.univ • normalizedMeasure μ := by
      intro U
      simp only [Measure.smul_apply,smul_eq_mul]
      gcongr
    _ = μ := mass_smul_normalizedMeasure μ
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma bufferRestoreLength_le {R₀ r ε α : ℝ} (hr : 0 ≤ r) (hε : ε ≤ 1) (hα : 0 ≤ α)
    (b : Bool) : bufferRestoreLength R₀ r ε α b ≤ ⌈max 0 R₀⌉₊ := by
  apply Nat.ceil_mono
  apply max_le_max le_rfl
  have hc : 0 ≤ (if b then 1+α else 1-ε)*r := by
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> positivity
  linarith

lemma bufferStageStoppedProbability_retained {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (H : ℕ) (hH : 0 < H) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) (hκ1 : κ ≤ 1) (hg1 : g ≤ 1)
    (hr : 0 ≤ r) (hε : 0 ≤ ε) [IsProbabilityMeasure (π ω).val]
    (hgap : ∀ᵐ x ∂(π ω).val, z₀+r ≤ signedCoordinate f (x.2-x.1))
    (k : ℕ) (hk : bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω=k) :
    ((κ : ℝ≥0∞)^2*ENNReal.ofReal g) • (bufferStageStoppedProbability e f a z₀ r ε α g π H hH κ k ω).val ≤
      rawPairMixture (realPosition (step e)) k (π ω).val ω := by
  let μ := bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ
  have hle := bufferStageRetainedLaw_le e f a z₀ r ε α g π hH ω hκ
  have hl := bufferStageRetainedLaw_mass_lower e f a z₀ r ε α g π hH ω κ hκ1 hg1 hr hε hgap
  have hm : μ Set.univ ≤ 1 := (hle _).trans (rawPairMixture_le_one _ _ _ _)
  let : IsFiniteMeasure μ := ⟨lt_of_le_of_lt hm ENNReal.one_lt_top⟩
  have hh : ((κ : ℝ≥0∞)^2*ENNReal.ofReal g) • normalizedMeasure μ ≤ μ :=
    normalizedMeasure_smul_lower μ hl
  have hh' := hh.trans hle
  simpa only [bufferStageStoppedProbability,ite_eq_left hk,hk,↓reduceIte] using hh'

lemma bufferChildNode_retained_composed {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) {κ : ℝ≥0} (hκ1 : κ ≤ 1) (hg1 : g ≤ 1) (hε : 0 ≤ ε)
    (N : AdaptedBufferNode e) (hr : 0 ≤ N.radius) (hN : BufferNodeValid e f z₀ κ N)
    (H : ℕ) (hH : 0 < H) (k : ℕ) (b : Bool) (ω : Environment d)
    (hκ : ∀ y u, κ ≤ (ω y).1 u)
    (ha : ω ∈ (bufferChildNode e f hef R₀ z₀ ε α g κ N H hH k b).active) :
    (((κ : ℝ≥0∞)^2*ENNReal.ofReal g)*(κ : ℝ≥0∞)^(bufferRestoreLength R₀ N.radius ε α b+2)) •
      ((bufferChildNode e f hef R₀ z₀ ε α g κ N H hH k b).law ω).val ≤
      rawPairMixture (realPosition (step e)) 1
        (rawPairMixture (realPosition (step e)) k (N.law ω).val ω) ω := by
  obtain ⟨hp,hgap⟩ := hN ω hκ ha.1
  let := hp
  let π := (bufferStageStoppedProbability e f N.level z₀ N.radius ε α g N.law H hH κ k ω).val
  let c := (κ : ℝ≥0∞)^2*ENNReal.ofReal g
  have hstage : c • π ≤ rawPairMixture (realPosition (step e)) k (N.law ω).val ω :=
    bufferStageStoppedProbability_retained e f N.level z₀ N.radius ε α g N.law H hH ω
      (fun y => hκ y e) hκ1 hg1 hr hε hgap k ha.2.1
  have hscript := bufferRestorationLaw_le e f hef (bufferRestoreLength R₀ N.radius ε α b) ω π hκ
  have hs : c • bufferRestorationLaw e f (bufferRestoreLength R₀ N.radius ε α b) π κ ≤
      c • rawPairMixture (realPosition (step e)) 1 π ω := by
    intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    gcongr
  rw [←rawPairMixture_smul] at hs
  have hh := hs.trans (rawPairMixture_mono (realPosition (step e)) 1 ω hstage)
  simpa only [bufferRestorationLaw,smul_smul,bufferChildNode,restoredStoppedLaw,c,π] using hh
end DirectionalTransience

end

end

end OAI
