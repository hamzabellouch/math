import OAI.Analysis.RotationWeights.RationalGraphs

namespace OAI

noncomputable section

universe uX uY uι uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace CircleSampling

section
open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction
variable {X : Type uX} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

lemma graph_restriction_convergence
    (μ : ProbabilityMeasure X) (ν : ℕ → FiniteMeasure (X×X))
    (f g : ℕ → X → ℝ) (hf : ∀ j, MemLp (f j) 2 (μ:Measure X))
    (hg : ∀ j, MemLp (g j) 2 (μ:Measure X))
    (hfm : ∀ j, Measurable (f j)) (_hgm : ∀ j, Measurable (g j))
    (hfn : ∀ j x, 0 ≤ f j x) (hgn : ∀ j x, 0 ≤ g j x)
    (hfst : ∀ j, Measure.map Prod.fst (ν j : Measure (X×X))=weightedMeasure (μ:Measure X) (f j))
    (hsnd : ∀ j, Measure.map Prod.snd (ν j : Measure (X×X))=weightedMeasure (μ:Measure X) (g j))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hδb : ∀ j, 0 ≤ δ j ∧ δ j ≤ 1)
    (hfe : ∀ j, (∫ x, (f j x-1)^2 ∂(μ:Measure X)) ≤ (δ j)^2)
    (hge : ∀ j, (∫ x, (g j x-1)^2 ∂(μ:Measure X)) ≤ (δ j)^2)
    (A : ℕ → Set X) (hA : ∀ j, MeasurableSet (A j))
    (hAlim : Tendsto (fun j => (μ:Measure X).real (A j)) atTop (𝓝 0))
    (T : C(X,X)) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hsupport : ∀ j, ∀ᵐ z ∂(ν j:Measure (X×X)), dist z.2 (T z.1) ≤ r j) :
    let ν' := fun j => (ν j).restrict (Prod.fst ⁻¹' (A j)ᶜ)
    Tendsto ν' atTop (𝓝 ((μ.toFiniteMeasure).map (fun x => (x,T x)))) ∧
    (∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ d : ℝ≥0∞, d ≠ 0 ∧
      ∀ B : Set X, (μ:Measure X) B < d → ∀ j,
      (ν' j : Measure (X×X)) (Prod.fst ⁻¹' B) ≤ ε ∧
      (ν' j : Measure (X×X)) (Prod.snd ⁻¹' B) ≤ ε) := by
  let ν' := fun j => (ν j).restrict (Prod.fst ⁻¹' (A j)ᶜ)
  have hf2 (j) : (∫ x, (f j x)^2 ∂(μ:Measure X)) ≤ 2^2 := by
    exact (integral_sq_le_of_error _ (hf j) (hδb j).1 (hfe j)).trans (by nlinarith [(hδb j).1,(hδb j).2])
  have hg2 (j) : (∫ x, (g j x)^2 ∂(μ:Measure X)) ≤ 2^2 := by
    exact (integral_sq_le_of_error _ (hg j) (hδb j).1 (hge j)).trans (by nlinarith [(hδb j).1,(hδb j).2])
  have hfle (j) (B : Set X) (hB : MeasurableSet B) :
      (ν' j:Measure (X×X)).real (Prod.fst ⁻¹' B) ≤ 2*Real.sqrt ((μ:Measure X).real B) := by
    have hm : (ν' j:Measure (X×X)) (Prod.fst ⁻¹' B) ≤ (ν j:Measure (X×X)) (Prod.fst ⁻¹' B) := Measure.restrict_le_self _
    apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) hm)
    change ((ν j:Measure (X×X)) (Prod.fst ⁻¹' B)).toReal ≤ _
    rw [←Measure.map_apply measurable_fst hB,hfst j]
    exact weightedMeasure_le_sqrt _ (hf j) (hfn j) (by norm_num) (hf2 j) B hB
  have hgle (j) (B : Set X) (hB : MeasurableSet B) :
      (ν' j:Measure (X×X)).real (Prod.snd ⁻¹' B) ≤ 2*Real.sqrt ((μ:Measure X).real B) := by
    have hm : (ν' j:Measure (X×X)) (Prod.snd ⁻¹' B) ≤ (ν j:Measure (X×X)) (Prod.snd ⁻¹' B) := Measure.restrict_le_self _
    apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) hm)
    change ((ν j:Measure (X×X)) (Prod.snd ⁻¹' B)).toReal ≤ _
    rw [←Measure.map_apply measurable_snd hB,hsnd j]
    exact weightedMeasure_le_sqrt _ (hg j) (hgn j) (by norm_num) (hg2 j) B hB
  constructor
  · have hmap (j) : Measure.map Prod.fst (ν' j:Measure (X×X))=
        (weightedMeasure (μ:Measure X) (f j)).restrict (A j)ᶜ := by
      rw [←hfst j,Measure.restrict_map measurable_fst (hA j).compl]
      rfl
    apply tendsto_graph_of_fst ν' μ.toFiniteMeasure T r hr (by norm_num : (0:ℝ) ≤ 2) ?_ ?_ ?_
    · intro j
      simpa using hfle j univ MeasurableSet.univ
    · intro j
      exact ae_restrict_of_ae (hsupport j)
    · apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
      intro φ
      have hbound (j) : |(∫ x, φ x ∂((ν' j).map Prod.fst : Measure X))-(∫ x, φ x ∂(μ:Measure X))| ≤
          ‖φ‖*(δ j+2*Real.sqrt ((μ:Measure X).real (A j))) := by
        change |(∫ x, φ x ∂Measure.map Prod.fst (ν' j:Measure (X×X)))-_| ≤ _
        rw [hmap j]
        calc
          _ ≤ |(∫ x, φ x ∂(weightedMeasure (μ:Measure X) (f j)).restrict (A j)ᶜ)-
                (∫ x, φ x ∂weightedMeasure (μ:Measure X) (f j))|+
              |(∫ x, φ x ∂weightedMeasure (μ:Measure X) (f j))-(∫ x, φ x ∂(μ:Measure X))| := abs_sub_le _ _ _
          _ ≤ ‖φ‖*(weightedMeasure (μ:Measure X) (f j)).real (A j)+
              ‖φ‖*Real.sqrt (∫ x, (f j x-1)^2 ∂(μ:Measure X)) :=
            add_le_add (weightedMeasure_test_restrict _ ((hf j).integrable (by norm_num)) (hfm j) (hfn j) _ (hA j) φ)
              (weightedMeasure_l1_test _ (hf j) (hfm j) (hfn j) φ)
          _ ≤ ‖φ‖*(2*Real.sqrt ((μ:Measure X).real (A j)))+‖φ‖*δ j := by
            gcongr
            · exact weightedMeasure_le_sqrt _ (hf j) (hfn j) (by norm_num) (hf2 j) _ (hA j)
            · exact (Real.sqrt_le_left (hδb j).1).mpr (hfe j)
          _ = _ := by ring
      have ht : Tendsto (fun j => ‖φ‖*(δ j+2*Real.sqrt ((μ:Measure X).real (A j)))) atTop (𝓝 0) := by
        simpa using (hδ.add (hAlim.sqrt.const_mul 2)).const_mul ‖φ‖
      exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => abs_nonneg _) hbound ht)
  · intro ε hε
    obtain ⟨d,hd,hdf⟩ := finiteMeasure_sqrt_uc (μ:Measure X) (fun j => (ν' j:Measure (X×X))) Prod.fst measurable_fst (by norm_num : (0:ℝ)<2) hfle ε hε
    obtain ⟨e,he,heg⟩ := finiteMeasure_sqrt_uc (μ:Measure X) (fun j => (ν' j:Measure (X×X))) Prod.snd measurable_snd (by norm_num : (0:ℝ)<2) hgle ε hε
    exact ⟨min d e,ne_of_gt (lt_min (pos_iff_ne_zero.mpr hd) (pos_iff_ne_zero.mpr he)),
      fun B hB j => ⟨hdf B (hB.trans_le (min_le_left _ _)) j,heg B (hB.trans_le (min_le_right _ _)) j⟩⟩
end
open MeasureTheory Set Filter
open scoped ENNReal Topology

def orbitEquiv (n : ℤ) : CircleX ≃ᵐ CircleX := MeasurableEquiv.addRight (n•modelAngle)
lemma orbitEquiv_apply (n : ℤ) (x : CircleX) : orbitEquiv n x=CircleModel.shift modelAngle n x := rfl
lemma orbitEquiv_symm_apply (n : ℤ) (x : CircleX) : (orbitEquiv n).symm x=CircleModel.shift modelAngle (-n) x := by
  simp [orbitEquiv,CircleModel.shift]
lemma orbitEquiv_preserving (n : ℤ) : MeasurePreserving (orbitEquiv n) volume volume := measurePreserving_add_right volume _

def stageGraph (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) : FiniteMeasure (CircleX×CircleX) :=
  ⟨finiteGraphAverage volume (fun n : (scaleStep j).samples t => stageWeight true j n.val)
    (fun n => orbitEquiv n.val), finiteGraphAverage_finite _ _ _
      (fun n => (stageWeight_memLp true j n.val).integrable (by norm_num))
      (fun n x => (stageWeight_bounds true j n.val x).1)⟩
lemma stageGraph_fst (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    Measure.map Prod.fst (stageGraph j t : Measure (CircleX×CircleX))=weightedMeasure volume (stageDensity true j t) :=
  finiteGraphAverage_fst _ _ _ (fun n => stageWeight_measurable true j n.val) (fun n x => (stageWeight_bounds true j n.val x).1)
    (fun n => (orbitEquiv n.val).measurable)
lemma stageGraph_snd (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    Measure.map Prod.snd (stageGraph j t : Measure (CircleX×CircleX))=weightedMeasure volume (stageDensity false j t) := by
  have he := finiteGraphAverage_snd volume (fun n : (scaleStep j).samples t => orbitEquiv n.val)
    (fun n => orbitEquiv_preserving n.val) (fun n => stageWeight true j n.val)
    (fun n => stageWeight_measurable true j n.val) (fun n x => (stageWeight_bounds true j n.val x).1)
  change Measure.map Prod.snd (stageGraph j t : Measure (CircleX×CircleX))=_ at he
  rw [he]
  congr 1
  funext x
  apply congrArg ((Fintype.card ((scaleStep j).samples t):ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro n _
  change stageWeight true j n.val ((orbitEquiv n.val).symm x)=stageWeight false j n.val x
  rw [orbitEquiv_symm_apply,stageWeight_negative]

def translation (h : CircleX) : C(CircleX,CircleX) := ⟨fun x => x+h,continuous_id.add continuous_const⟩
lemma quotient_norm_le (δ : ℝ) : ‖(δ:CircleX)‖ ≤ |δ| := by
  exact QuotientAddGroup.norm_mk_le_norm
lemma stageGraph_support (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    ∀ᵐ z ∂(stageGraph j t:Measure (CircleX×CircleX)),
      dist z.2 (translation (gridPoint (scaleState j).1 t) z.1) ≤ gridTolerance j (scaleState j).1 := by
  have hP : MeasurableSet {z : CircleX×CircleX | dist z.2 (translation (gridPoint (scaleState j).1 t) z.1) ≤ gridTolerance j (scaleState j).1} :=
    measurableSet_le (measurable_snd.dist ((translation (gridPoint (scaleState j).1 t)).continuous.measurable.comp measurable_fst)) measurable_const
  apply finiteGraphAverage_ae volume
    (fun n : (scaleStep j).samples t => stageWeight true j n.val)
    (fun n => orbitEquiv n.val) (fun n => stageWeight_measurable true j n.val)
    (fun n => (orbitEquiv n.val).measurable) _ hP
  intro n
  apply ae_of_all
  intro x _
  obtain ⟨δ,hδ,he⟩ := (scaleStep j).orbits parameterAngle (parameterAngle_spec.2.2.2 j) t n.val n.property
  have hn : n.val•modelAngle=gridPoint (scaleState j).1 t+(δ:CircleX) := by
    change (δ:CircleX)=n.val•modelAngle-gridPoint (scaleState j).1 t at he
    exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)
  change dist (x+n.val•modelAngle) (x+gridPoint (scaleState j).1 t) ≤ _
  rw [hn,←add_assoc,dist_eq_norm,add_sub_cancel_left]
  exact ((quotient_norm_le δ).trans_eq (abs_of_pos hδ.1)).trans hδ.2.le
lemma gridTolerance_bound (j : ℕ) : 0 < gridTolerance j (scaleState j).1 ∧
    gridTolerance j (scaleState j).1 ≤ 1/((j:ℝ)+1) := by
  have hj : 0 < (j:ℝ)+1 := by positivity
  have hq : (1:ℝ) ≤ (scaleState j).1.q (scaleState j).1.d := by exact_mod_cast (scaleState j).2.qpos _ le_rfl
  have hd : 1 ≤ 1+((scaleState j).1.d:ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  constructor
  · unfold gridTolerance; positivity
  · unfold gridTolerance
    apply one_div_le_one_div_of_le hj
    calc
      _ ≤ 10*((j:ℝ)+1)^2 := by nlinarith [sq_nonneg (j:ℝ)]
      _ ≤ 10*((j:ℝ)+1)^2*(1+((scaleState j).1.d:ℝ)) := le_mul_of_one_le_right (by positivity) hd
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hq
lemma gridTolerance_tendsto : Tendsto (fun j => gridTolerance j (scaleState j).1) atTop (𝓝 0) :=
  squeeze_zero (fun j => (gridTolerance_bound j).1.le) (fun j => (gridTolerance_bound j).2)
    tendsto_one_div_add_atTop_nhds_zero_nat

def rationalPoint (D : ℕ) (a : Fin (frequency (D+1))) : CircleX := (((a.val:ℝ)/(frequency (D+1):ℝ):ℝ):CircleX)
def rationalIndex (D : ℕ) (a : Fin (frequency (D+1))) (j : ℕ) :
    Fin ((scaleState (D+1+j)).1.q (scaleState (D+1+j)).1.d) :=
  (rational_stage_index D (D+1+j) a (le_trans (by omega) (blockEnd_ge _))).choose
lemma rationalIndex_spec (D : ℕ) (a : Fin (frequency (D+1))) (j : ℕ) :
    gridPoint (scaleState (D+1+j)).1 (rationalIndex D a j)=rationalPoint D a :=
  (rational_stage_index D (D+1+j) a (le_trans (by omega) (blockEnd_ge _))).choose_spec

def rationalGraph (D : ℕ) (a : Fin (frequency (D+1))) (j : ℕ) : FiniteMeasure (CircleX×CircleX) :=
  (stageGraph (D+1+j) (rationalIndex D a j)).restrict (Prod.fst ⁻¹' (graphBad (D+1+j))ᶜ)

def circleProbability : ProbabilityMeasure CircleX := ⟨volume,inferInstance⟩
lemma rationalGraph_convergence (D : ℕ) (a : Fin (frequency (D+1))) :
    Tendsto (rationalGraph D a) atTop (𝓝 (circleProbability.toFiniteMeasure.map (fun x => (x,translation (rationalPoint D a) x)))) ∧
    (∀ ε : ℝ≥0∞, ε≠0 → ∃ d : ℝ≥0∞, d≠0 ∧ ∀ B : Set CircleX, volume B<d → ∀ j,
      (rationalGraph D a j:Measure (CircleX×CircleX)) (Prod.fst ⁻¹' B) ≤ ε ∧
      (rationalGraph D a j:Measure (CircleX×CircleX)) (Prod.snd ⁻¹' B) ≤ ε) := by
  have hs : Tendsto (fun j : ℕ => D+1+j) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat (D+1)
  apply graph_restriction_convergence circleProbability
    (fun j => stageGraph (D+1+j) (rationalIndex D a j))
    (fun j => stageDensity true (D+1+j) (rationalIndex D a j))
    (fun j => stageDensity false (D+1+j) (rationalIndex D a j))
    (fun j => stageDensity_memLp _ _ _) (fun j => stageDensity_memLp _ _ _)
    (fun j => stageDensity_measurable _ _ _) (fun j => stageDensity_measurable _ _ _)
    (fun j => stageDensity_nonneg _ _ _) (fun j => stageDensity_nonneg _ _ _)
    (fun j => stageGraph_fst _ _) (fun j => stageGraph_snd _ _)
    (fun j => 1/(((D+1+j:ℕ):ℝ)+1)) ?_ ?_ ?_ ?_
    (fun j => graphBad (D+1+j)) (fun j => graphBad_measurable _) (graphBad_tendsto.comp hs)
    (translation (rationalPoint D a)) (fun j => gridTolerance (D+1+j) (scaleState (D+1+j)).1)
    (gridTolerance_tendsto.comp hs) ?_
  · exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hs
  · intro j
    refine ⟨by positivity, ?_⟩
    simpa using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (le_add_of_nonneg_left (Nat.cast_nonneg (D+1+j))))
  · intro j
    simpa only [one_div_pow,circleProbability,ProbabilityMeasure.coe_mk] using (stageDensity_energy true (D+1+j) (rationalIndex D a j)).le
  · intro j
    simpa only [one_div_pow,circleProbability,ProbabilityMeasure.coe_mk] using (stageDensity_energy false (D+1+j) (rationalIndex D a j)).le
  · intro j
    simpa only [rationalIndex_spec] using stageGraph_support (D+1+j) (rationalIndex D a j)
end CircleSampling

open MeasureTheory Set Filter Topology TopologicalSpace
namespace ContinuousCircleWeight

section

theorem continuousOn_compact_graph {X : Type uX} {Y : Type uY} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (f : X → Y) {K : Set (X × Y)}
    (hK : IsCompact K) (hgraph : ∀ p ∈ K, p.2 = f p.1) :
    ContinuousOn f (Prod.fst '' K) := by
  let E : Set X := Prod.fst '' K
  have hpoint : ∀ x ∈ E, (x, f x) ∈ K := by
    rintro x ⟨p, hp, rfl⟩
    simpa only [← hgraph p hp, Prod.eta] using hp
  let e : K ≃ E :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩
      invFun := fun x => ⟨(x.1, f x.1), hpoint x.1 x.2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        exact Prod.ext rfl (hgraph p.1 p.2).symm
      right_inv := by intro x; rfl }
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he : Continuous e := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have he' : Continuous e.symm := he.continuous_symm_of_equiv_compact_to_t2
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_snd.comp (continuous_subtype_val.comp he')

theorem measurable_lusin_compact {X : Type uX} {Y : Type uY} [TopologicalSpace X]
    [TopologicalSpace Y] [PolishSpace X] [PolishSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → Y} (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ E : Set X, IsCompact E ∧ μ Eᶜ < ε ∧ ContinuousOn f E := by
  let g : X → X × Y := fun x => (x, f x)
  have hg : Measurable g := measurable_id.prodMk hf
  let G : Set (X × Y) := {p | p.2 = f p.1}
  have hG : MeasurableSet G := measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  let ν := μ.map g
  obtain ⟨K, hKG, hK, hsmall⟩ := hG.exists_isCompact_sdiff_lt (measure_ne_top ν G) hε
  have hpre : g ⁻¹' (G \ K) = (Prod.fst '' K)ᶜ := by
    ext x
    simp only [mem_preimage, Set.mem_sdiff, mem_ofPred_eq, g, G, mem_compl_iff,
      true_and]
    constructor
    · intro hx hproj
      obtain ⟨p, hp, hpx⟩ := hproj
      apply hx
      convert hp using 1
      exact Prod.ext hpx.symm (by simpa only [mem_ofPred_eq, G, hpx] using (hKG hp).symm)
    · intro hx hxp
      exact hx ⟨(x, f x), hxp, rfl⟩
  rw [Measure.map_apply hg (hG.diff hK.isClosed.measurableSet), hpre] at hsmall
  refine ⟨Prod.fst '' K, hK.image continuous_fst, hsmall, ?_⟩
  exact continuousOn_compact_graph f hK (fun _ hp => hKG hp)

theorem finiteMeasure_compl_le_of_tendsto {X : Type uX} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {ν : FiniteMeasure X} {νs : ℕ → FiniteMeasure X}
    (hlim : Tendsto νs atTop (𝓝 ν)) {K : Set X} (hK : IsClosed K)
    {ε : ℝ≥0∞} (hsmall : ∀ n, (νs n : Measure X) Kᶜ ≤ ε) :
    (ν : Measure X) Kᶜ ≤ ε := by
  have hmass : Tendsto (fun n => (νs n : Measure X) univ) atTop
      (𝓝 ((ν : Measure X) univ)) := by
    simpa only [← FiniteMeasure.ennreal_mass, Function.comp_def] using
      (ENNReal.continuous_coe.tendsto ν.mass).comp hlim.mass
  have hpoint : ∀ n, (νs n : Measure X) univ ≤ (νs n : Measure X) K + ε := by
    intro n
    calc
      _ = (νs n : Measure X) K + (νs n : Measure X) Kᶜ :=
        (measure_add_measure_compl hK.measurableSet).symm
      _ ≤ _ := add_le_add le_rfl (hsmall n)
  have hbound : (ν : Measure X) univ ≤ (ν : Measure X) K + ε := by
    calc
      _ = atTop.limsup (fun n => (νs n : Measure X) univ) := hmass.limsup_eq.symm
      _ ≤ atTop.limsup (fun n => (νs n : Measure X) K + ε) :=
        limsup_le_limsup (Eventually.of_forall hpoint)
      _ = atTop.limsup (fun n => (νs n : Measure X) K) + ε :=
        limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)
      _ ≤ _ := add_le_add
        (FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim hK) le_rfl
  rw [measure_compl hK.measurableSet (measure_ne_top _ _)]
  exact tsub_le_iff_right.mpr (by simpa only [add_comm] using hbound)

theorem isCompact_all_zeros {X : Type uX} {Y : Type uY} {ι : Type uι} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space Y] [Zero Y] {E : Set X} (hE : IsCompact E)
    {f : ι → X → Y} (hf : ∀ i, ContinuousOn (f i) E) :
    IsCompact {x | x ∈ E ∧ ∀ i, f i x = 0} := by
  have hc : ContinuousOn (fun x i => f i x) E := continuousOn_pi.mpr hf
  obtain ⟨C, hC, heq⟩ := continuousOn_iff_isClosed.mp hc {0} isClosed_singleton
  have hset : {x | x ∈ E ∧ ∀ i, f i x = 0} = C ∩ E := by
    rw [← heq]
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff,
      funext_iff, Pi.zero_apply, and_comm]
  rw [hset]
  exact hE.inter_left hC

theorem compact_relation_transfer {X : Type uX} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [HasOuterApproxClosed (X × X)]
    {μ : Measure X} {ν : FiniteMeasure (X × X)} {νs : ℕ → FiniteMeasure (X × X)}
    (hlim : Tendsto νs atTop (𝓝 ν)) {Z : Set (X × X)}
    (hgood : ∀ n, (νs n : Measure (X × X)) Zᶜ = 0)
    (huc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, μ A < δ → ∀ n,
        (νs n : Measure (X × X)) (Prod.fst ⁻¹' A) ≤ ε ∧
        (νs n : Measure (X × X)) (Prod.snd ⁻¹' A) ≤ ε)
    (happrox : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ E : Set X,
      μ Eᶜ < δ ∧ IsCompact ((E ×ˢ E) ∩ Z)) :
    (ν : Measure (X × X)) Zᶜ = 0 := by
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have heps : (ε : ℝ≥0∞) / 2 ≠ 0 :=
    (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hε.ne.symm)).ne.symm
  obtain ⟨δ, hδ, hδsmall⟩ := huc ((ε : ℝ≥0∞) / 2) heps
  obtain ⟨E, hEμ, hEK⟩ := happrox δ hδ
  let K := (E ×ˢ E) ∩ Z
  have hKsmall : ∀ n, (νs n : Measure (X × X)) Kᶜ ≤ ε := by
    intro n
    have hsub : Kᶜ ⊆ (Prod.fst ⁻¹' Eᶜ) ∪ (Prod.snd ⁻¹' Eᶜ) ∪ Zᶜ := by
      intro p hp
      simp only [K, mem_compl_iff, mem_inter_iff, mem_prod] at hp
      simp only [mem_union, mem_preimage, mem_compl_iff]
      tauto
    calc
      _ ≤ (νs n : Measure (X × X))
          ((Prod.fst ⁻¹' Eᶜ) ∪ (Prod.snd ⁻¹' Eᶜ) ∪ Zᶜ) := measure_mono hsub
      _ ≤ (νs n : Measure (X × X)) ((Prod.fst ⁻¹' Eᶜ) ∪ (Prod.snd ⁻¹' Eᶜ)) +
          (νs n : Measure (X × X)) Zᶜ := measure_union_le _ _
      _ ≤ ((νs n : Measure (X × X)) (Prod.fst ⁻¹' Eᶜ) +
          (νs n : Measure (X × X)) (Prod.snd ⁻¹' Eᶜ)) + 0 :=
        add_le_add (measure_union_le _ _) (hgood n).le
      _ ≤ ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) + 0 :=
        add_le_add (add_le_add (hδsmall Eᶜ hEμ n).1 (hδsmall Eᶜ hEμ n).2) le_rfl
      _ = ε := by simp
  have hlimK := finiteMeasure_compl_le_of_tendsto hlim hEK.isClosed hKsmall
  simpa only [ENNReal.bot_eq_zero, zero_add] using (measure_mono (compl_subset_compl.mpr
    (show K ⊆ Z from inter_subset_right))).trans hlimK

lemma continuous_bounded_field_apply {X : Type uX} [TopologicalSpace X]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : X → (E →L[ℂ] E)) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ x, ‖A x‖ ≤ C) (hA : ∀ u, Continuous (fun x ↦ A x u))
    {v : X → E} (hv : Continuous v) : Continuous (fun x ↦ A x (v x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hzero : Tendsto (fun y ↦ A y (v y-v x)) (𝓝 x) (𝓝 0) := by
    apply squeeze_zero_norm (a := fun y ↦ C * ‖v y-v x‖)
    · intro y
      exact (A y).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _))
    · have ht : Tendsto (fun y ↦ ‖v y-v x‖) (𝓝 x) (𝓝 0) := by
        simpa only [sub_self, norm_zero] using ((hv.tendsto x).sub_const (v x)).norm
      simpa only [mul_zero] using tendsto_const_nhds.mul ht
  have hsum := hzero.add (hA (v x)).continuousAt
  change Tendsto (fun y ↦ A y (v y)) (𝓝 x) (𝓝 (A x (v x)))
  simpa only [map_sub, sub_add_cancel, zero_add] using hsum

def cappedRatio {X : Type uX} (F : ℤ → X → ℝ) (B : ℝ≥0) (x y : X) (k : ℤ) : ℝ :=
  min (B : ℝ) (max 0 (F k y / F k x))

lemma cappedRatio_bounds {X : Type uX} (F : ℤ → X → ℝ) (B : ℝ≥0)
    (x y : X) (k : ℤ) : 0 ≤ cappedRatio F B x y k ∧ cappedRatio F B x y k ≤ B :=
  ⟨le_min B.coe_nonneg (le_max_left _ _), min_le_left _ _⟩

def cappedDiagonal {X : Type uX} (F : ℤ → X → ℝ) (B : ℝ≥0) (x y : X) : FiberOperator :=
  lpDiagonal (fun k ↦ (cappedRatio F B x y k : ℂ)) B (fun k ↦ by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cappedRatio_bounds F B x y k).1] using (cappedRatio_bounds F B x y k).2)

lemma continuous_cappedDiagonal {X : Type uX} [TopologicalSpace X]
    (F : ℤ → X → ℝ) (hF : ∀ k, Continuous (F k)) (hp : ∀ k x, 0 < F k x)
    (B : ℝ≥0) (u : FiberHilbert) :
    Continuous (fun z : X × X ↦ cappedDiagonal F B z.1 z.2 u) := by
  apply continuous_bounded_lp_field _ B.coe_nonneg (fun _ ↦ lpDiagonal_norm_le _ _) _ u
  intro k
  have he : (fun z : X × X ↦ cappedDiagonal F B z.1 z.2 (lp.single 2 k 1)) =
      (fun z ↦ (cappedRatio F B z.1 z.2 k : ℂ) • lp.single 2 k 1) := by
    funext z
    ext i
    simp only [cappedDiagonal, lpDiagonal_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i=k
    · subst i; simp
    · simp [lp.single_apply, hi]
  change Continuous (fun z : X × X ↦ cappedDiagonal F B z.1 z.2 (lp.single 2 k 1))
  rw [he]
  have hr : Continuous (fun z : X × X ↦ cappedRatio F B z.1 z.2 k) :=
    continuous_const.min (continuous_const.max
      (((hF k).comp continuous_snd).div ((hF k).comp continuous_fst) (fun z ↦ (hp k z.1).ne')))
  exact (Complex.continuous_ofReal.comp hr).smul
    (continuous_const : Continuous (fun _ : X × X ↦ (lp.single 2 k 1 : FiberHilbert)))

instance fiberSeparable : SeparableSpace FiberHilbert := by
  let b := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ FiberHilbert)
  apply isSeparable_univ_iff.mp
  have hs := ((countable_range (b : ℤ → FiberHilbert)).isSeparable.span (R := ℂ)).closure
  rw [← Submodule.topologicalClosure_coe, b.dense_span] at hs
  exact hs

local instance fiberMeasurable : MeasurableSpace FiberHilbert := borel FiberHilbert
local instance fiberBorel : BorelSpace FiberHilbert := ⟨rfl⟩

def cappedPairRelation {X : Type uX} (p : X → FiberOperator) (F : ℤ → X → ℝ)
    (B : ℝ≥0) : Set (X × X) :=
  {z | ∀ k : ℤ, (1-p z.2) (cappedDiagonal F B z.1 z.2 (p z.1 (lp.single 2 k 1)))=0}

lemma cappedPairRelation_iff {X : Type uX} (p : X → FiberOperator) (F : ℤ → X → ℝ)
    (B : ℝ≥0) (x y : X) :
    (x,y) ∈ cappedPairRelation p F B ↔ (1-p y)*cappedDiagonal F B x y*p x=0 := by
  constructor
  · intro h
    apply lp.ext_continuousLinearMap (by norm_num)
    intro k
    apply ContinuousLinearMap.ext
    intro a
    have he : lp.single (E := fun _ : ℤ ↦ ℂ) 2 k a = a • lp.single 2 k (1 : ℂ) := by
      simpa using (lp.single_smul (E := fun _ : ℤ ↦ ℂ) 2 k a (1 : ℂ))
    change (1-p y) (cappedDiagonal F B x y (p x (lp.single 2 k a))) = 0
    simp only [he, map_smul]
    change a • ((1-p y) (cappedDiagonal F B x y (p x (lp.single 2 k 1)))) = 0
    rw [h k, smul_zero]
  · intro h k
    have he := congrArg (fun a : FiberOperator ↦ a (lp.single 2 k 1)) h
    exact he

lemma cappedPairRelation_compact_approx {X : Type uX} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (p : X → FiberOperator) (hp : ∀ x, ‖p x‖ ≤ 1)
    (hpm : ∀ k : ℤ, Measurable (fun x ↦ p x (lp.single 2 k 1)))
    (F : ℤ → X → ℝ) (hFm : ∀ k, Measurable (F k)) (hFp : ∀ k x, 0 < F k x)
    (B : ℝ≥0) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ E : Set X, μ Eᶜ < δ ∧ IsCompact ((E ×ˢ E) ∩ cappedPairRelation p F B) := by
  let f : X → (ℤ → FiberHilbert) × (ℤ → ℝ) :=
    fun x ↦ ((fun k ↦ p x (lp.single 2 k 1)), fun k ↦ F k x)
  have hfm : Measurable f := (Measurable.of_eval hpm).prodMk (Measurable.of_eval hFm)
  obtain ⟨E,hEc,hEμ,hEf⟩ := measurable_lusin_compact hfm (μ := μ) hδ
  refine ⟨E,hEμ,?_⟩
  let : CompactSpace E := isCompact_iff_compactSpace.mp hEc
  have hfc : Continuous (fun x : E ↦ f x) := continuousOn_iff_continuous_domRestrict.mp hEf
  have hpc : ∀ k, Continuous (fun x : E ↦ p x (lp.single 2 k 1)) :=
    fun k ↦ (continuous_apply k).comp hfc.fst
  have hFc : ∀ k, Continuous (fun x : E ↦ F k x) :=
    fun k ↦ (continuous_apply k).comp hfc.snd
  have hpstrong : ∀ u : FiberHilbert, Continuous (fun x : E ↦ p x u) :=
    continuous_bounded_lp_field (fun x : E ↦ p x) zero_le_one (fun x ↦ hp x) hpc
  have hDc : ∀ u : FiberHilbert, Continuous (fun z : E × E ↦ cappedDiagonal F B z.1 z.2 u) :=
    continuous_cappedDiagonal (fun k (x : E) ↦ F k x) hFc (fun k x ↦ hFp k x) B
  have hqc : ∀ u : FiberHilbert, Continuous (fun z : E × E ↦ (1-p z.2) u) := by
    intro u
    change Continuous (fun z : E × E ↦ u-p z.2 u)
    exact continuous_const.sub ((hpstrong u).comp continuous_snd)
  have hqb : ∀ z : E × E, ‖1-p z.2‖ ≤ 2 := by
    intro z
    calc
      ‖1-p z.2‖ ≤ ‖(1 : FiberOperator)‖ + ‖p z.2‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (ContinuousLinearMap.norm_id_le) (hp z.2)
      _ = 2 := by norm_num
  let T : ℤ → E × E → FiberHilbert :=
    fun k z ↦ (1-p z.2) (cappedDiagonal F B z.1 z.2 (p z.1 (lp.single 2 k 1)))
  have hTc : ∀ k, Continuous (T k) := by
    intro k
    apply continuous_bounded_field_apply (fun z : E × E ↦ 1-p z.2) (by norm_num) hqb hqc
    apply continuous_bounded_field_apply (fun z : E × E ↦ cappedDiagonal F B z.1 z.2)
      B.coe_nonneg (fun _ ↦ lpDiagonal_norm_le _ _) hDc
    exact (hpc k).comp continuous_fst
  have hK : IsCompact {z : E × E | ∀ k, T k z=0} := by
    have hc : IsClosed {z : E × E | ∀ k, T k z=0} := by
      simpa only [funext_iff, Pi.zero_apply] using
        (isClosed_eq (continuous_pi hTc)
          (continuous_const : Continuous (fun _ : E × E ↦ (0 : ℤ → FiberHilbert))))
    exact hc.isCompact
  let e : E × E → X × X := fun z ↦ (z.1.val,z.2.val)
  have he : Continuous e :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hset : (E ×ˢ E) ∩ cappedPairRelation p F B = e '' {z : E × E | ∀ k,T k z=0} := by
    ext z
    constructor
    · rintro ⟨⟨hx,hy⟩,hz⟩
      exact ⟨(⟨z.1,hx⟩,⟨z.2,hy⟩),hz,rfl⟩
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact ⟨⟨x.property,y.property⟩,hxy⟩
  rw [hset]
  exact hK.image he

theorem capped_pair_identity_transfer {X : Type uX} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (p : X → FiberOperator) (hp : ∀ x, ‖p x‖ ≤ 1)
    (hpm : ∀ k : ℤ, Measurable (fun x ↦ p x (lp.single 2 k 1)))
    (F : ℤ → X → ℝ) (hFm : ∀ k, Measurable (F k)) (hFp : ∀ k x, 0 < F k x)
    (B : ℝ≥0) {ν : FiniteMeasure (X × X)} {νs : ℕ → FiniteMeasure (X × X)}
    (hlim : Tendsto νs atTop (𝓝 ν))
    (hgood : ∀ n, ∀ᵐ z ∂(νs n : Measure (X × X)),
      (1-p z.2)*cappedDiagonal F B z.1 z.2*p z.1=0)
    (huc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, μ A < δ → ∀ n,
        (νs n : Measure (X × X)) (Prod.fst ⁻¹' A) ≤ ε ∧
        (νs n : Measure (X × X)) (Prod.snd ⁻¹' A) ≤ ε) :
    ∀ᵐ z ∂(ν : Measure (X × X)), (1-p z.2)*cappedDiagonal F B z.1 z.2*p z.1=0 := by
  have hr : (ν : Measure (X × X)) (cappedPairRelation p F B)ᶜ=0 := by
    apply compact_relation_transfer hlim (μ := μ) ?_ huc
      (fun _ hδ ↦ cappedPairRelation_compact_approx p hp hpm F hFm hFp B hδ)
    intro n
    have hg : ∀ᵐ z ∂(νs n : Measure (X × X)), z ∈ cappedPairRelation p F B :=
      (hgood n).mono fun z hz ↦ (cappedPairRelation_iff p F B z.1 z.2).mpr hz
    exact ae_iff.mp hg
  have hg : ∀ᵐ z ∂(ν : Measure (X × X)), z ∈ cappedPairRelation p F B := ae_iff.mpr hr
  exact hg.mono fun z hz ↦ (cappedPairRelation_iff p F B z.1 z.2).mp hz

end

open MeasureTheory Set
open scoped ComplexConjugate

lemma cappedDiagonal_apply_of_bound {X : Type uX} (F : ℤ → X → ℝ) (hF : ∀ k x, 0 < F k x)
    (B : ℝ≥0) (x y : X) (hb : ∀ k, F k y/F k x ≤ B) (v : FiberHilbert) (k : ℤ) :
    cappedDiagonal F B x y v k=(F k y/F k x:ℝ)*v k := by
  change (cappedRatio F B x y k:ℂ)*v k=_
  rw [cappedRatio,max_eq_right (div_pos (hF k y) (hF k x)).le,min_eq_right (hb k)]

lemma positive_orbit_capped_pair {X : Type uX} (F : ℤ → X → ℝ) (hF : ∀ k x,0 < F k x)
    (hmono : ∀ x,Antitone (fun k => F k x)) (x y : X) (n : ℕ)
    (hrel : ∀ k, F (k+n) x=F k y*F n x)
    (p q : FiberOperator) (hp : IsStarProjection p)
    (hinv : (1-p)*fiberCocycleShift (fun k => F k x) (fun k => hF k x) (hmono x)*p=0)
    (hcov : p*(fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap=
      (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap*q)
    (B : ℝ≥0) (hb : ∀ k,F k y/F k x ≤ B) :
    (1-q)*cappedDiagonal F B x y*p=0 := by
  have he (v : FiberHilbert) : fiberShift n (cappedDiagonal F B x y v)=
      ((F n x)⁻¹:ℂ) • (fiberCocycleShift (fun k => F k x) (fun k => hF k x) (hmono x)^n) v := by
    apply lp.ext
    funext k
    rw [fiberShift_apply,cappedDiagonal_apply_of_bound F hF B x y hb,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      fiberCocycleShift_pow_apply]
    have hr := hrel (k-n)
    rw [sub_add_cancel] at hr
    rw [hr]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (hF (n:ℤ) x).ne', Complex.ofReal_ne_zero.mpr (hF (k-n) x).ne']
  apply ContinuousLinearMap.ext
  intro v
  change cappedDiagonal F B x y (p v)-q (cappedDiagonal F B x y (p v))=0
  apply sub_eq_zero.mpr
  apply (fiberShift n).injective
  have hv : p (p v)=p v := by
    have h := congrArg (fun A : FiberOperator => A v) hp.isIdempotentElem
    exact h
  have hfix := invariant_fixed_vector_pow hinv hv n
  have hc := congrArg (fun A : FiberOperator => A (cappedDiagonal F B x y (p v))) hcov
  change p (fiberShift n (cappedDiagonal F B x y (p v)))=
    fiberShift n (q (cappedDiagonal F B x y (p v))) at hc
  rw [he,map_smul,hfix] at hc
  exact (he (p v)).trans hc
end ContinuousCircleWeight

end

end OAI
