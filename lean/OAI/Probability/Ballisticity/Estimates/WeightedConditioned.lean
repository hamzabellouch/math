import Mathlib
import OAI.Probability.Ballisticity.Coupling.WeightedAnnealed
import OAI.Probability.Ballisticity.Estimates.FirstHighRecord

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def weightedConditioned {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) : Measure (Path d) :=
  (annealedLaw ν (NoDrop ℓ 0))⁻¹ • (weightedAnnealed ν g).restrict (NoDrop ℓ 0)

lemma weightedConditioned_le {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) (hg : Measurable g) (hgle : ∀ ω, g ω ≤ 1) :
    weightedConditioned ν ℓ g ≤ conditionedLaw ν ℓ := by
  intro A
  change (annealedLaw ν (NoDrop ℓ 0))⁻¹ * (weightedAnnealed ν g).restrict (NoDrop ℓ 0) A ≤
    (annealedLaw ν (NoDrop ℓ 0))⁻¹ * (annealedLaw ν).restrict (NoDrop ℓ 0) A
  apply mul_le_mul_right
  exact (Measure.restrict_mono le_rfl (weightedAnnealed_le ν g hg hgle)) A

lemma weightedConditioned_apply_subset {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) (A : Set (Path d)) (hA : MeasurableSet A)
    (hAD : A ⊆ NoDrop ℓ 0) :
    weightedConditioned ν ℓ g A = (annealedLaw ν (NoDrop ℓ 0))⁻¹ * weightedAnnealed ν g A := by
  simp only [weightedConditioned,Measure.smul_apply,Measure.restrict_apply hA,
    Set.inter_eq_left.mpr hAD,smul_eq_mul]

lemma weightedConditioned_highWord_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (g : Environment d → ℝ≥0∞)
    (hg : @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ g)
    (w : List (Direction d)) (A : Set (Path d)) (hA : MeasurableSet A) :
    weightedConditioned ν ℓ g (HighWordEvent ℓ J w ∩ highSuffix ℓ J ⁻¹' A) =
      weightedConditioned ν ℓ g (HighWordEvent ℓ J w) * conditionedLaw ν ℓ A := by
  have hg' : Measurable g := hg.mono (rowSigma_le _) le_rfl
  by_cases hw : AdmissibleHighWord ℓ J w
  · let F := fun X : Path d => fun j => X (w.length+j)-wordPath 0 w w.length
    have hF : Measurable F := by fun_prop
    have hFD : ∀ B : Set (Path d), B ⊆ NoDrop ℓ 0 →
        F ⁻¹' B ∩ wordCylinder 0 w ⊆ NoDrop ℓ 0 := by
      intro B hBD X hX
      exact ((highWord_characterization ℓ J w X hX.2).mpr ⟨hw,hBD hX.1⟩).1
    have hrec : ∀ y ∈ wordDepartures 0 w,
        dot (realPosition y) ℓ < dot (realPosition (wordPath 0 w w.length)) ℓ := by
      intro y hy
      obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
      exact hw.1 j hj
    have hf (B : Set (Path d)) (hB : MeasurableSet B) (hBD : B ⊆ NoDrop ℓ 0) :
        weightedConditioned ν ℓ g (F ⁻¹' B ∩ wordCylinder 0 w) =
          (∫⁻ ω, g ω * ENNReal.ofReal (wordWeight ω 0 w) ∂environmentLaw ν) *
            conditionedLaw ν ℓ B := by
      rw [weightedConditioned_apply_subset ν ℓ g _ ((hB.preimage hF).inter
        (measurableSet_wordCylinder 0 w)) (hFD B hBD),
        weightedAnnealed_apply ν g hg' _ ((hB.preimage hF).inter (measurableSet_wordCylinder 0 w)),
        weighted_record_suffix ν ℓ w J hrec hw.2.1 g hg B hB hBD,
        conditionedLaw_apply_of_subset ν ℓ B hB hBD]
      ac_rfl
    have he : HighWordEvent ℓ J w ∩ highSuffix ℓ J ⁻¹' A =
        F ⁻¹' (A ∩ NoDrop ℓ 0) ∩ wordCylinder 0 w := by
      ext X
      constructor
      · rintro ⟨hX,hXA⟩
        have hXD := (Set.ext_iff.mp (highWordEvent_eq ℓ J w hw) X).mp hX
        exact ⟨⟨by simpa only [Set.mem_preimage,highSuffix_on_highWordEvent ℓ J hJ w X hX] using hXA,hXD.1⟩,hXD.2⟩
      · rintro ⟨⟨hXA,hXD⟩,hc⟩
        have hX := (Set.ext_iff.mp (highWordEvent_eq ℓ J w hw) X).mpr ⟨hXD,hc⟩
        exact ⟨hX,by simpa only [Set.mem_preimage,highSuffix_on_highWordEvent ℓ J hJ w X hX] using hXA⟩
    have hmass : weightedConditioned ν ℓ g (HighWordEvent ℓ J w) =
        ∫⁻ ω, g ω * ENNReal.ofReal (wordWeight ω 0 w) ∂environmentLaw ν := by
      rw [highWordEvent_eq ℓ J w hw,hf _ (measurableSet_noDrop ℓ 0) Set.Subset.rfl]
      have hD : conditionedLaw ν ℓ (NoDrop ℓ 0) = 1 := by
        rw [conditionedLaw_apply_of_subset ν ℓ _ (measurableSet_noDrop ℓ 0) Set.Subset.rfl]
        exact ENNReal.inv_mul_cancel hp (measure_ne_top _ _)
      rw [hD,mul_one]
    rw [he,hf _ (hA.inter (measurableSet_noDrop ℓ 0)) Set.inter_subset_right,
      conditionedLaw_inter_noDrop ν ℓ A hA,hmass]
  · simp [highWordEvent_empty ℓ J w hw]

lemma weightedConditioned_highSuffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) (hJ : 0 ≤ J)
    (g : Environment d → ℝ≥0∞)
    (hg : @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ g)
    (hgle : ∀ ω, g ω ≤ 1) :
    (weightedConditioned ν ℓ g).map (highSuffix ℓ J) =
      weightedConditioned ν ℓ g Set.univ • conditionedLaw ν ℓ := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hle := weightedConditioned_le ν ℓ g (hg.mono (rowSigma_le _) le_rfl) hgle
  have he : ∀ᵐ X ∂weightedConditioned ν ℓ g, ∃ w, X ∈ HighWordEvent ℓ J w :=
    (Measure.absolutelyContinuous_of_le hle).ae_le (conditioned_highWord_exists ν ℓ htrans J)
  have hpart (B : Set (Path d)) (hB : MeasurableSet B) :
      weightedConditioned ν ℓ g B =
        ∑' w : List (Direction d), weightedConditioned ν ℓ g (HighWordEvent ℓ J w ∩ B) := by
    rw [← measure_iUnion (fun u v huv => (highWordEvent_disjoint ℓ J huv).mono
      Set.inter_subset_left Set.inter_subset_left)
        (fun w => (measurableSet_highWordEvent ℓ J w).inter hB)]
    apply measure_congr
    filter_upwards [he] with X ⟨w,hw⟩
    apply propext
    exact ⟨fun hX => Set.mem_iUnion.mpr ⟨w,hw,hX⟩,
      fun hX => (Set.mem_iUnion.mp hX).choose_spec.2⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_highSuffix ℓ J hJ) hA,
    hpart _ (hA.preimage (measurable_highSuffix ℓ J hJ))]
  simp_rw [weightedConditioned_highWord_factor ν ℓ J hJ hp g hg _ A hA]
  rw [ENNReal.tsum_mul_right,Measure.smul_apply,smul_eq_mul]
  have hm := hpart Set.univ MeasurableSet.univ
  simp only [Set.inter_univ] at hm
  rw [← hm]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma levyProkhorov_map_distance_le {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F G : Ω → E)
    (hF : Measurable F) (hG : Measurable G) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : μ {ω | δ ≤ dist (F ω) (G ω)} ≤ ENNReal.ofReal δ) :
    levyProkhorovDist (μ.map F) (μ.map G) ≤ δ := by
  apply levyProkhorovDist_le_of_forall_le _ _ hδ
  intro ε B hε hB
  rw [Measure.map_apply hF hB,Measure.map_apply hG Metric.isOpen_thickening.measurableSet]
  have hs : F ⁻¹' B ⊆ G ⁻¹' Metric.thickening ε B ∪ {ω | δ ≤ dist (F ω) (G ω)} := by
    intro ω hω
    by_cases hh : δ ≤ dist (F ω) (G ω)
    · exact Or.inr hh
    · exact Or.inl (Metric.mem_thickening_iff.mpr ⟨F ω,hω,by
        rw [dist_comm]; exact (lt_of_not_ge hh).trans hε⟩)
  exact (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (hbad.trans (ENNReal.ofReal_le_ofReal hε.le))))

lemma weak_map_of_varying_close {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (F G : ℕ → Ω → E) (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i))
    (ν : ProbabilityMeasure E)
    (hlim : Tendsto (fun i => ProbabilityMeasure.map (⟨μ i, inferInstance⟩ : ProbabilityMeasure Ω) (F i))
      atTop (𝓝 ν))
    (hclose : ∀ ε, 0 < ε → Tendsto (fun i => (μ i).real
      {ω | ε ≤ dist (F i ω) (G i ω)}) atTop (𝓝 0)) :
    Tendsto (fun i => ProbabilityMeasure.map (⟨μ i, inferInstance⟩ : ProbabilityMeasure Ω) (G i))
      atTop (𝓝 ν) := by
  let A i := ProbabilityMeasure.map (⟨μ i, inferInstance⟩ : ProbabilityMeasure Ω) (F i)
  let B i := ProbabilityMeasure.map (⟨μ i, inferInstance⟩ : ProbabilityMeasure Ω) (G i)
  have hd : Tendsto (fun i => dist (LevyProkhorov.ofMeasure (A i))
      (LevyProkhorov.ofMeasure (B i))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [(hclose (ε/2) (by positivity)).eventually_lt_const
      (by positivity : 0 < ε/2)] with i hi
    have hb : μ i {ω | ε/2 ≤ dist (F i ω) (G i ω)} ≤ ENNReal.ofReal (ε/2) := by
      have hh := ENNReal.ofReal_le_ofReal hi.le
      simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
    have h := levyProkhorov_map_distance_le (μ i) (F i) (G i) (hF i) (hG i) (by positivity) hb
    rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]
    exact h.trans_lt (half_lt_self hε)
  have hA := LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto ν |>.comp hlim
  have hB := hA.congr_dist hd
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto
    (LevyProkhorov.ofMeasure ν) |>.comp hB

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
