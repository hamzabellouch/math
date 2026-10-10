import Mathlib
import OAI.Probability.Perceptron.Variational.RoundedMarkedSelection

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction

def orderedLevelCode {k : ℕ} (v : Fin (k+1) → ℝ) (x : ℝ) : Fin (k+1) :=
  (Finset.univ.filter (fun i => v i ≤ x)).sup id

lemma orderedLevelCode_mono {k : ℕ} (v : Fin (k+1) → ℝ) :
    Monotone (orderedLevelCode v) := by
  intro x y hxy
  apply Finset.sup_mono
  intro i hi
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  exact hi.trans hxy

lemma orderedLevelCode_value {k : ℕ} (v : Fin (k+1) → ℝ) (hv : StrictMono v)
    (j : Fin (k+1)) : orderedLevelCode v (v j) = j := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi
    exact hv.le_iff_le.mp hi
  · exact Finset.le_sup (f := id) (by simp)

lemma orderedLevelCode_top {k : ℕ} (v : Fin (k+1) → ℝ) (x : ℝ)
    (hv : v (Fin.last k) ≤ x) : orderedLevelCode v x = Fin.last k := by
  apply le_antisymm (Fin.le_last _)
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)

lemma orderedLevelCode_measurable {k : ℕ} (v : Fin (k+1) → ℝ) :
    Measurable (orderedLevelCode v) := (orderedLevelCode_mono v).measurable

lemma roundLower_one (n : ℕ) : roundLower n 1 = 1 := by
  unfold roundLower
  simp only [mul_one,Nat.floor_natCast]
  exact div_self (by positivity)

lemma orderedRoundCode_label (q : BoundedField 1) (n : ℕ) :
    (fun u => orderedLevelCode (strictRoundModel q n).value (roundLower n (q u)))
      =ᵐ[timeLaw] (strictRoundModel q n).label := by
  filter_upwards [(strictRoundModel q n).agrees] with u hu
  change (strictRoundModel q n).value ((strictRoundModel q n).label u) =
    roundLower n (q u) at hu
  rw [←hu,orderedLevelCode_value _ (strictRoundModel_strict q n)]

lemma orderedRoundCode_one (q : BoundedField 1) (n : ℕ) :
    orderedLevelCode (strictRoundModel q n).value (roundLower n 1) =
      Fin.last (strictRoundModel q n).depth := by
  rw [roundLower_one]
  apply orderedLevelCode_top
  exact (roundTimeValue q n _).property.2

lemma compactGG_events_general {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K))
    (n : ℕ) (hn : 0<n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ),
      compactGGDefect μ n i f g=0)
    (s : Set (CompactBlock K n)) (hs : MeasurableSet s)
    (t : Set K) (ht : MeasurableSet t) :
    (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray K | Q 0 1∈t}/n+
      (∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}))/n := by
  classical
  have he := congrArg (fun ρ : Measure (CompactBlock K n × K) =>
    ρ.real (s×ˢt)) (compactGG_joint_law μ hn i hGG)
  have hb := (compactBlock_continuous (K:=K) n).measurable
  have hm (i j : ℕ) : Measurable (fun Q : CompactArray K => Q i j) := by fun_prop
  rw [map_measureReal_apply (hb.prodMk (hm _ _)) (hs.prod ht),
    measureReal_nnreal_smul_apply,measureReal_add_apply] at he
  have hsum : (∑ j ∈ Finset.univ.erase i,
      (μ : Measure _).map (fun Q => (compactBlock n Q,Q i j))).real (s×ˢt) =
      ∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}) := by
    simp only [measureReal_def,Measure.finsetSum_apply]
    rw [ENNReal.toReal_sum (by intro _ _; finiteness)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Measure.map_apply (hb.prodMk (hm _ _)) (hs.prod ht)]
    rfl
  rw [hsum] at he
  have hprod : (((μ : Measure _).map (compactBlock n)).prod
      ((μ : Measure _).map (fun Q : CompactArray K => Q 0 1))).real (s×ˢt) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray K | Q 0 1∈t} := by
    simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      Measure.map_apply hb hs,Measure.map_apply (hm 0 1) ht]
    rfl
  rw [hprod] at he
  simp only [NNReal.coe_inv,NNReal.coe_natCast] at he
  change (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) = (n:ℝ)⁻¹*(_+_) at he
  rw [he]
  ring

variable {K L : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

def finiteCodeArray (χ : K → L) (Q : CompactArray K) :
    FiniteOverlap L := fun i j => χ (Q i j)

def finiteCodeBlock {n : ℕ} (χ : K → L) (Q : CompactBlock K n) :
    FiniteBlock L n := fun i j => χ (Q i j)

omit [TopologicalSpace K] [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
  [Fintype L] [MeasurableSingletonClass L] in
lemma finiteCodeArray_measurable {χ : K → L} (hχ : Measurable χ) :
    Measurable (finiteCodeArray χ) := by
  unfold finiteCodeArray
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hχ.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

omit [TopologicalSpace K] [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
  [Fintype L] [MeasurableSingletonClass L] in
lemma finiteCodeBlock_measurable {χ : K → L} (hχ : Measurable χ) (n : ℕ) :
    Measurable (finiteCodeBlock (n:=n) χ) := by
  unfold finiteCodeBlock
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hχ.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma compactGG_finite_pushforward_general (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ)
      (g : K →ᵇ ℝ), compactGGDefect μ n i f g=0)
    {χ : K → L} (hχ : Measurable χ) :
    FiniteGG ((μ : Measure (CompactArray K)).map (finiteCodeArray χ)) := by
  classical
  intro n hn i A c
  have hm := finiteCodeArray_measurable hχ
  have hb := finiteBlock_measurable (L:=L) n
  have he (a b : ℕ) : Measurable (fun R : FiniteOverlap L => R a b) := by fun_prop
  have hs : MeasurableSet {R : FiniteOverlap L | finiteBlock n R=A} :=
    measurableSet_eq_fun hb measurable_const
  have hv (a b : ℕ) : MeasurableSet {R : FiniteOverlap L | R a b=c} :=
    measurableSet_eq_fun (he a b) measurable_const
  have hvv (a b : ℕ) : MeasurableSet {R : FiniteOverlap L | finiteBlock n R=A ∧ R a b=c} := hs.inter (hv a b)
  rw [map_measureReal_apply hm (hvv _ _),map_measureReal_apply hm hs,
    map_measureReal_apply hm (hv 0 1)]
  simp_rw [map_measureReal_apply hm (hvv _ _)]
  exact compactGG_events_general μ n (by omega) i (hGG n i)
    ((finiteCodeBlock χ) ⁻¹' {A}) ((measurableSet_singleton A).preimage (finiteCodeBlock_measurable hχ n))
    (χ ⁻¹' {c}) ((measurableSet_singleton c).preimage hχ)

end SphericalPerceptronFreeEnergy
end

end OAI
