import Mathlib
import OAI.Analysis.HardSphere.Paths.AdmissiblePair

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice
open MeasureTheory ProbabilityTheory

abbrev SimplePath {K : ℕ} (x y : DiscreteTorus K) :=
  {p : (torusNearestGraph K).Walk x y // p.IsPath}

instance simplePathMeasurableSpace {K : ℕ} (x y : DiscreteTorus K) :
    MeasurableSpace (SimplePath x y) := ⊤

instance simplePathCountable {K : ℕ} [NeZero K] (x y : DiscreteTorus K) :
    Countable (SimplePath x y) := by
  let : Countable ((torusNearestGraph K).Walk x y) := SimpleGraph.Walk.support_injective.countable
  infer_instance

instance environmentMeasurableSpace (K : ℕ) : MeasurableSpace (Finset (DiscreteTorus K)) := ⊤

def forgetGood {K : ℕ} {B : Finset (DiscreteTorus K)} {x y : DiscreteTorus K}
    (p : SimpleGoodPath B x y) : SimplePath x y := ⟨p.val,p.property.1⟩

def simpleEncounter {K : ℕ} (R : ℕ) {x y : DiscreteTorus K} (p q : SimplePath x y) : ℕ :=
  (encounterSet (torusNear K R) p.val.support.toFinset q.val.support.toFinset).card

def simplePathGood {K : ℕ} (B : Finset (DiscreteTorus K)) {x y : DiscreteTorus K}
    (p : SimplePath x y) : Prop := ∀ z∈p.val.support, z∉B

lemma pmf_lintegral_discrete {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : PMF α) (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂μ.toMeasure)=∑' x, μ x*f x := by
  rw [lintegral_countable']
  apply tsum_congr
  intro x
  rw [μ.toMeasure_apply_singleton x (measurableSet_singleton x),mul_comm]

lemma pmf_event_discrete {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : PMF α) (E : α → Prop) [DecidablePred E] :
    μ.toMeasure {x | E x}=∑' x, if E x then μ x else 0 := by
  rw [μ.toMeasure_apply MeasurableSet.of_discrete]
  apply tsum_congr
  intro x
  exact Set.indicator_apply _ _ _

lemma forgetGood_full_mass {K : ℕ} {B : Finset (DiscreteTorus K)} {x y : DiscreteTorus K}
    (ν : PMF (SimpleGoodPath B x y)) :
    (ν.map forgetGood).toMeasure {p | simplePathGood B p}=1 := by
  apply (PMF.toMeasure_apply_eq_one_iff _ MeasurableSet.of_discrete).mpr
  intro p hp
  obtain ⟨q,_,rfl⟩ := (PMF.mem_support_map_iff forgetGood ν p).mp hp
  exact q.property.2

lemma forgetGood_double_moment {K : ℕ} [NeZero K] (R : ℕ) (κ : ℝ)
    {B : Finset (DiscreteTorus K)} {x y : DiscreteTorus K} (ν : PMF (SimpleGoodPath B x y)) :
    (∫⁻ p, ∫⁻ q, ENNReal.ofReal (Real.exp (κ*(simpleEncounter R p q:ℝ)))
      ∂(ν.map forgetGood).toMeasure ∂(ν.map forgetGood).toMeasure)=pathKernelMoment R κ ν := by
  simp_rw [pmf_lintegral_discrete,pmf_map_expectation]
  rfl

lemma mapped_bad_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (b : Ω → Finset (DiscreteTorus K)) (hb : Measurable b)
    (p : ℝ≥0∞) (hbad : ∀ A : Finset (DiscreteTorus K), P {d | A⊆b d}≤p^A.card) :
    let := (Measure.isProbabilityMeasure_map_iff (μ := P) hb.aemeasurable).mpr inferInstance
    JointBadLaw (P.map b).toPMF p := by
  dsimp only
  let := (Measure.isProbabilityMeasure_map_iff (μ := P) hb.aemeasurable).mpr inferInstance
  intro A
  rw [← pmf_event_discrete (P.map b).toPMF (fun B ↦ A⊆B),Measure.toPMF_toMeasure,
    Measure.map_apply (μ := P) hb MeasurableSet.of_discrete]
  exact hbad A

lemma finite_datum_expectation {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [Countable α] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : Ω → α) (hb : Measurable b) (f : α → ℝ≥0∞) :
    let := (Measure.isProbabilityMeasure_map_iff (μ := P) hb.aemeasurable).mpr inferInstance
    (∫⁻ d, f (b d) ∂P)=∑' a, (P.map b).toPMF a*f a := by
  dsimp only
  let := (Measure.isProbabilityMeasure_map_iff (μ := P) hb.aemeasurable).mpr inferInstance
  rw [← pmf_lintegral_discrete,Measure.toPMF_toMeasure,lintegral_map Measurable.of_discrete hb]

theorem good_paths_measurable (R : ℕ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      ∀ {Ω : Type*} [MeasurableSpace Ω], ∀ P : Measure Ω, ∀ _ : IsProbabilityMeasure P,
      ∀ b : Ω → Finset (DiscreteTorus K), Measurable b →
      ∀ p : ℝ, 0≤p → p≤p₀ →
      (∀ A : Finset (DiscreteTorus K), P {d | A⊆b d}≤(ENNReal.ofReal p)^A.card) →
      ∀ x y : DiscreteTorus K, admissiblePair x y →
      ∃ E : Set Ω, MeasurableSet E ∧ (1/2:ℝ≥0∞)≤P E ∧
      ∃ ν : Kernel Ω (SimplePath x y), IsMarkovKernel ν ∧
        (∀ d∈E, ν d {q | simplePathGood (b d) q}=1) ∧
        (∫⁻ d, E.indicator (fun d ↦ ∫⁻ q, ∫⁻ q',
          ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ))) ∂ν d ∂ν d) d ∂P)≤2 := by
  obtain ⟨p₀,κ,hp₀,hκ,K₀,hall⟩ := admissible_good_paths R
  refine ⟨p₀,κ,hp₀,hκ,K₀,?_⟩
  intro K hK inst Ω mΩ P hP b hb p hp hpp hbad x y hxy
  let := (Measure.isProbabilityMeasure_map_iff (μ := P) hb.aemeasurable).mpr inferInstance
  let μ := (P.map b).toPMF
  obtain ⟨E,η,hmass,hmoment⟩ := hall K hK inst μ p hp hpp (mapped_bad_law P b hb _ hbad) x y hxy
  have hex : ∃ B, E B := by
    by_contra hn
    have hn' : ∀ B, ¬E B := not_exists.mp hn
    simp only [ite_eq_right (hn' _),tsum_zero] at hmass
    norm_num at hmass
  obtain ⟨B₀,hB₀⟩ := hex
  obtain ⟨q₀,_⟩ := (η B₀ hB₀).support_nonempty
  let η' (B : Finset (DiscreteTorus K)) : PMF (SimplePath x y) :=
    if hB : E B then (η B hB).map forgetGood else PMF.pure (forgetGood q₀)
  let ν₀ : Kernel (Finset (DiscreteTorus K)) (SimplePath x y) :=
    ⟨fun B ↦ (η' B).toMeasure,Measurable.of_discrete⟩
  let ν := ν₀.comap b hb
  have hmE : MeasurableSet {d | E (b d)} := hb MeasurableSet.of_discrete
  refine ⟨{d | E (b d)},hmE,?_,ν,?_,?_,?_⟩
  · change (1/2:ℝ≥0∞) ≤ P (b ⁻¹' {B | E B})
    rw [← Measure.map_apply (μ := P) hb (s:={B | E B}) MeasurableSet.of_discrete,
      ← Measure.toPMF_toMeasure (P.map b),pmf_event_discrete]
    exact hmass
  · constructor
    intro d
    change IsProbabilityMeasure (η' (b d)).toMeasure
    infer_instance
  · intro d hd
    change E (b d) at hd
    change (η' (b d)).toMeasure {q | simplePathGood (b d) q}=1
    simp only [η',dite_eq_left hd]
    exact forgetGood_full_mass _
  · have hpoint (d : Ω) :
        {d | E (b d)}.indicator (fun d ↦ ∫⁻ q, ∫⁻ q',
          ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ))) ∂ν d ∂ν d) d =
        (if hB : E (b d) then pathKernelMoment R κ (η (b d) hB) else 0) := by
      by_cases hd : E (b d)
      · rw [Set.indicator_of_mem (s := {d | E (b d)}) (a := d) hd,dite_eq_left hd]
        change (∫⁻ q, ∫⁻ q', ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ)))
          ∂(η' (b d)).toMeasure ∂(η' (b d)).toMeasure)=_
        simp only [η',dite_eq_left hd]
        exact forgetGood_double_moment R κ _
      · rw [Set.indicator_of_notMem (s := {d | E (b d)}) (a := d) hd,dite_eq_right hd]
    simp_rw [hpoint]
    rw [finite_datum_expectation P b hb (fun B ↦ if hB : E B then pathKernelMoment R κ (η B hB) else 0)]
    exact hmoment

end HardSphere.Lattice

end

end OAI
