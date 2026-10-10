import OAI.InformationTheory.SecretKey.KeyRate

namespace OAI

noncomputable section

namespace UnrestrictedQuantum

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v11816_0 v11816_1 v11816_2

variable {K : Type v11816_0} {A : Type v11816_1} {ι : Type v11816_2} [inst11816_0 : MeasurableSpace K] [inst11816_1 : MeasurableSingletonClass K] [inst11816_2 : DecidableEq K]
  [inst11816_3 : AddCommGroup A] [inst11816_4 : Module ℂ A] [inst11816_5 : One A] [inst11816_6 : Preorder A]
  [inst11816_7 : Fintype ι] [inst11816_8 : DecidableEq ι]

def deterministicInstrument (k : K) : ObservableInstrument K A A := by
  classical
  exact {
    operation := fun E => if k ∈ E then LinearMap.id else 0
    positive := by
      intro E hE x hx
      by_cases h : k ∈ E
      · simpa only [h, ite_eq_left, LinearMap.id_apply] using hx
      · simp only [h]; exact le_rfl
    total_unit := by simp
  }

def deterministicRun (k : K) (S : ReferenceFunctional A ι)
    (hS : PositiveFunctional S) (hn : trace (S 1) = 1) :
    InstrumentRun (deterministicInstrument (A := A) k) S where
  law := Measure.dirac k
  probability := inferInstance
  posterior _ := S
  posterior_positive _ := hS
  posterior_trace _ := hn
  integrable _ _ _ := integrable_const _
  update E hE x i j := by
    by_cases h : k ∈ E
    · simp [deterministicInstrument,h,Measure.real, Measure.dirac_apply', hE]
    · simp [deterministicInstrument,h,Measure.real, Measure.dirac_apply', hE]

omit inst11816_1 inst11816_7 inst11816_8 in
lemma deterministic_event [MeasurableSingletonClass K] [Fintype ι] [DecidableEq ι] (k l : K) (S : ReferenceFunctional A ι) :
    S ((deterministicInstrument (A := A) k).operation {l} 1) =
      if k = l then S 1 else 0 := by
  by_cases h : k = l <;> simp [deterministicInstrument,h]

universe v11853_0

variable {Ω : Type v11853_0} {L : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} {F : Filtration ℕ mΩ} {U : ℕ → Ω → Matrix ι ι ℂ}

def scalarReference (G : Matrix ι ι ℂ) : ReferenceFunctional ℂ ι where
  toFun z := z • G
  map_add' z w := add_smul z w G
  map_smul' z w := by simp [smul_smul]

omit inst11816_7 inst11816_8 in
lemma scalarReference_positive [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.PosSemidef) :
    PositiveFunctional (scalarReference G) := by
  intro z hz
  exact hG.smul hz

omit inst11816_7 inst11816_8 in
@[simp] lemma scalarReference_one [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) : scalarReference G 1 = G := one_smul _ _

def scalarIncoming (G : Ω → Matrix ι ι ℂ)
    (hG : ∀ x, ZeroKey.Density (G x)) (hm : Measurable[L] G)
    (hc : ∀ n E, MeasurableSet[F n] E →
      (∫ x in E, G x ∂μ) = ∫ x in E, U n x ∂μ) :
    IncomingObservableProcess (L := L) (A := ℂ) μ F U where
  state x := scalarReference (G x)
  positive x := scalarReference_positive (hG x).1
  positive_unit := zero_le_one
  normalized x := by simpa using (hG x).2
  local_measurable := by simpa using hm
  causality := by simpa using hc

namespace IncomingObservableProcess

variable (e : IncomingObservableProcess (L := L) (A := A) μ F U)
  [inst11884_0 : Fintype K] [inst11884_1 : Nonempty K]

def classicalReadout (f : Ω → K) (hf : Measurable[L] f) : e.FiniteReadout (K := K) (B := A) where
  instrument x := deterministicInstrument (f x)
  run x := deterministicRun (f x) (e.state x) (e.positive x) (e.normalized x)
  positive_unit := e.positive_unit
  local_measurable k := by
    simp_rw [deterministic_event]
    exact e.local_measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const

omit inst11884_1 in
lemma classicalReadout_value [Nonempty K] (f : Ω → K) (hf : Measurable[L] f) (k : K) (x : Ω) :
    (e.classicalReadout f hf).value k x = if f x = k then e.state x 1 else 0 :=
  deterministic_event _ _ _

end IncomingObservableProcess

end UnrestrictedQuantum

namespace ZeroKey

section

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ProbabilityTheory ENNReal NNReal Topology

universe v11915_0 v11915_1

variable {Ω : Type v11915_0} {ι : Type v11915_1} {mΩ : MeasurableSpace Ω} [inst11915_0 : Fintype ι] [inst11915_1 : DecidableEq ι]
  {μ : Measure Ω} [inst11915_2 : IsFiniteMeasure μ] (F : Filtration ℕ mΩ)

structure ConsistentReferenceHistory where
  finiteMeasure : (n : ℕ) → @PositiveMatrixMeasure Ω ι (F n) _
  traceLaw : ∀ n, @PositiveMatrixMeasure.traceMeasure Ω ι (F n) _ (finiteMeasure n) = μ.trim (F.le n)
  consistency : ∀ n k, n ≤ k → ∀ S, MeasurableSet[F n] S →
    @PositiveMatrixMeasure.value Ω ι (F n) _ (finiteMeasure n) S =
      @PositiveMatrixMeasure.value Ω ι (F k) _ (finiteMeasure k) S

namespace ConsistentReferenceHistory

variable {F}

variable (H : ConsistentReferenceHistory (ι := ι) (μ := μ) F)

def finiteValue (n : ℕ) (S : Set Ω) : Matrix ι ι ℂ :=
  @PositiveMatrixMeasure.value Ω ι (F n) _ (H.finiteMeasure n) S

def density (n : ℕ) : Ω → Matrix ι ι ℂ :=
  @PositiveMatrixMeasure.density Ω ι (F n) _ (H.finiteMeasure n) (μ.trim (F.le n))

omit inst11915_2 in
lemma measurable_density [IsFiniteMeasure μ] (n : ℕ) : Measurable[F n] (H.density n) :=
  @PositiveMatrixMeasure.measurable_density Ω ι (F n) _ _ (H.finiteMeasure n) _

lemma measurable_entry (n : ℕ) (i j : ι) : Measurable[F n] (fun ω => H.density n ω i j) := by
  let L : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  exact L.continuous.measurable.comp (H.measurable_density n)

omit inst11915_2 in
lemma integrable_entry [IsFiniteMeasure μ] (n : ℕ) (i j : ι) : Integrable (fun ω => H.density n ω i j) μ :=
  integrable_of_integrable_trim (F.le n)
    (@PositiveMatrixMeasure.integrable_entry Ω ι (F n) _ _ (H.finiteMeasure n) _ i j)

lemma integral_entry (n : ℕ) (S : Set Ω) (hS : MeasurableSet[F n] S) (i j : ι) :
    (∫ ω in S, H.density n ω i j ∂μ) = H.finiteValue n S i j := by
  rw [setIntegral_trim (F.le n) (H.measurable_entry n i j).stronglyMeasurable hS]
  let : MeasurableSpace Ω := F n
  apply (H.finiteMeasure n).integral_density_entry _ _ S hS i j
  intro T hT hμ
  apply (H.finiteMeasure n).value_zero_of_traceMeasure_zero T hT
  rwa [H.traceLaw n]

lemma density_pos (n : ℕ) : ∀ᵐ ω ∂μ, (H.density n ω).PosSemidef := by
  apply ae_of_ae_trim (F.le n)
  let : MeasurableSpace Ω := F n
  apply density_posSemidef_ae (H.finiteMeasure n)
  intro S hS hs
  apply (H.finiteMeasure n).value_zero_of_traceMeasure_zero S hS
  rwa [H.traceLaw n]

lemma density_trace (n : ℕ) : ∀ᵐ ω ∂μ, (trace (H.density n ω)).re = 1 := by
  apply ae_of_ae_trim (F.le n)
  let : MeasurableSpace Ω := F n
  let W := H.finiteMeasure n
  let ν := μ.trim (F.le n)
  have hi := (W.integrable_trace_density ν).re
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi (integrable_const (1 : ℝ))
  intro S hS _
  change (∫ ω in S, RCLike.re (trace (W.density ν ω)) ∂ν) = _
  rw [integral_re (W.integrable_trace_density ν).integrableOn]
  have hAC : ∀ T, MeasurableSet[F n] T → ν T = 0 → W.value T = 0 := by
    intro T hT hμ
    apply W.value_zero_of_traceMeasure_zero T hT
    rwa [H.traceLaw n]
  rw [W.integral_trace_density ν hAC S hS,integral_const]
  simp only [smul_eq_mul,mul_one]
  change (trace (W.value S)).re = (ν.restrict S).real Set.univ
  rw [← W.traceMeasure_real S hS,H.traceLaw n]
  simp only [Measure.real,Measure.restrict_apply_univ]
  rfl

lemma density_entry_martingale_re (i j : ι) :
    Martingale (fun n ω => (H.density n ω i j).re) F μ := by
  refine ⟨fun n => ((H.measurable_entry n i j).re).stronglyMeasurable, ?_⟩
  intro n k hnk
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le n) ((H.integrable_entry k i j).re)
  · intro S _ _
    exact (H.integrable_entry n i j).re.integrableOn
  · intro S hS _
    change (∫ ω in S, RCLike.re (H.density n ω i j) ∂μ) =
      ∫ ω in S, RCLike.re (H.density k ω i j) ∂μ
    rw [integral_re (H.integrable_entry n i j).integrableOn,
      integral_re (H.integrable_entry k i j).integrableOn,
      H.integral_entry n S hS i j,
      H.integral_entry k S ((F.mono hnk) S hS) i j]
    exact congrArg (fun Z : Matrix ι ι ℂ => (Z i j).re) (H.consistency n k hnk S hS)
  · exact ((H.measurable_entry n i j).re).stronglyMeasurable.aestronglyMeasurable

lemma density_entry_martingale_im (i j : ι) :
    Martingale (fun n ω => (H.density n ω i j).im) F μ := by
  refine ⟨fun n => ((H.measurable_entry n i j).im).stronglyMeasurable, ?_⟩
  intro n k hnk
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le n) ((H.integrable_entry k i j).im)
  · intro S _ _
    exact (H.integrable_entry n i j).im.integrableOn
  · intro S hS _
    change (∫ ω in S, RCLike.im (H.density n ω i j) ∂μ) =
      ∫ ω in S, RCLike.im (H.density k ω i j) ∂μ
    rw [integral_im (H.integrable_entry n i j).integrableOn,
      integral_im (H.integrable_entry k i j).integrableOn,
      H.integral_entry n S hS i j,
      H.integral_entry k S ((F.mono hnk) S hS) i j]
    exact congrArg (fun Z : Matrix ι ι ℂ => (Z i j).im) (H.consistency n k hnk S hS)
  · exact ((H.measurable_entry n i j).im).stronglyMeasurable.aestronglyMeasurable

theorem full_reference_measure : ∃ V : PositiveMatrixMeasure Ω ι,
    ∀ n S, MeasurableSet[F n] S → V.value S = H.finiteValue n S := by
  obtain ⟨V,hV⟩ := positive_matrix_martingale_extension (H.density)
    H.density_entry_martingale_re H.density_entry_martingale_im H.density_pos
    (fun n => (H.density_trace n).mono (fun _ h => le_of_eq h))
  refine ⟨V,fun n S hS => ?_⟩
  rw [hV n S hS]
  ext i j
  exact H.integral_entry n S hS i j

end ConsistentReferenceHistory

end

section

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section

namespace PositiveMatrixMeasure

universe v12052_0 v12052_1 v12052_2

variable {Ω : Type v12052_0} {T : Type v12052_1} {ι : Type v12052_2} {mΩ : MeasurableSpace Ω} [inst12052_0 : MeasurableSpace T]
  [inst12052_1 : Fintype ι] [inst12052_2 : DecidableEq ι]

def restrictEvent (W : PositiveMatrixMeasure Ω ι) (A : Set Ω) (hA : MeasurableSet A) :
    PositiveMatrixMeasure Ω ι where
  entry i j := (W.entry i j).restrict A
  positive S hS := by
    simpa only [VectorMeasure.restrict_apply _ hA hS] using W.positive (S ∩ A) (hS.inter hA)

omit inst12052_2 in
lemma restrictEvent_value [DecidableEq ι] (W : PositiveMatrixMeasure Ω ι) (A : Set Ω)
    (hA : MeasurableSet A) (S : Set Ω) (hS : MeasurableSet S) :
    (W.restrictEvent A hA).value S = W.value (S ∩ A) := by
  ext i j
  exact VectorMeasure.restrict_apply _ hA hS

omit inst12052_2 in
lemma eq_of_value [DecidableEq ι] (W V : PositiveMatrixMeasure Ω ι)
    (h : ∀ S, MeasurableSet S → W.value S = V.value S) : W = V := by
  have he : W.entry = V.entry := by
    funext i j
    apply VectorMeasure.ext
    intro S hS
    exact congrArg (fun X : Matrix ι ι ℂ => X i j) (h S hS)
  cases W
  cases V
  cases he
  rfl

universe v12080_0

lemma restrictEvent_filter {κ : Type v12080_0} [Fintype κ] [DecidableEq κ]
    (W : PositiveMatrixMeasure Ω ι) (A : Set Ω) (hA : MeasurableSet A)
    (K : Matrix κ ι ℂ) :
    (W.filter K).restrictEvent A hA = (W.restrictEvent A hA).filter K := by
  apply eq_of_value
  intro S hS
  rw [restrictEvent_value _ _ _ _ hS,filter_value,filter_value,
    restrictEvent_value _ _ _ _ hS]

def testMeasure (W : PositiveMatrixMeasure Ω ι) (E : Matrix ι ι ℂ) : Measure Ω :=
  (W.filter (CFC.sqrt E)).traceMeasure

instance testMeasure_finite (W : PositiveMatrixMeasure Ω ι) (E : Matrix ι ι ℂ) :
    IsFiniteMeasure (W.testMeasure E) := inferInstanceAs (IsFiniteMeasure (W.filter (CFC.sqrt E)).traceMeasure)

lemma testMeasure_real (W : PositiveMatrixMeasure Ω ι) (E : Matrix ι ι ℂ)
    (hE : E.PosSemidef) (S : Set Ω) (hS : MeasurableSet S) :
    (W.testMeasure E).real S = (trace (E * W.value S)).re := by
  rw [testMeasure,traceMeasure_real _ S hS,filter_value]
  have hs : (CFC.sqrt E)ᴴ = CFC.sqrt E := (CFC.sqrt_nonneg E).isSelfAdjoint.isHermitian.eq
  rw [hs,Matrix.trace_mul_cycle]
  rw [CFC.sqrt_mul_sqrt_self E hE.nonneg]

def bitReadout (W : PositiveMatrixMeasure Ω ι) (record : Ω → T) (hr : Measurable record)
    (a b : Ω → Bool) (ha : Measurable a) (hb : Measurable b) (i j : Bool) :
    PositiveMatrixMeasure T ι :=
  (W.restrictEvent ((a ⁻¹' {i}) ∩ (b ⁻¹' {j}))
    ((ha (measurableSet_singleton i)).inter (hb (measurableSet_singleton j)))).pushforward record hr

lemma bitReadout_value (W : PositiveMatrixMeasure Ω ι) (record : Ω → T) (hr : Measurable record)
    (a b : Ω → Bool) (ha : Measurable a) (hb : Measurable b) (i j : Bool)
    (S : Set T) (hS : MeasurableSet S) :
    (W.bitReadout record hr a b ha hb i j).value S =
      W.value ((record ⁻¹' S) ∩ ((a ⁻¹' {i}) ∩ (b ⁻¹' {j}))) := by
  rw [bitReadout,pushforward_value _ _ _ S hS,
    restrictEvent_value _ _ _ _ (hr hS)]

universe v12122_0

lemma bitReadout_filter {κ : Type v12122_0} [Fintype κ] [DecidableEq κ]
    (W : PositiveMatrixMeasure Ω ι) (record : Ω → T) (hr : Measurable record)
    (a b : Ω → Bool) (ha : Measurable a) (hb : Measurable b) (i j : Bool)
    (K : Matrix κ ι ℂ) (S : Set T) (hS : MeasurableSet S) :
    ((W.filter K).bitReadout record hr a b ha hb i j).value S =
      ((W.bitReadout record hr a b ha hb i j).filter K).value S := by
  rw [bitReadout_value _ _ _ _ _ _ _ _ _ _ hS,filter_value,filter_value,
    bitReadout_value _ _ _ _ _ _ _ _ _ _ hS]

end PositiveMatrixMeasure

open MeasurableSpace

universe v12136_0

lemma scalar_measure_ext_on_filtration {Ω : Type v12136_0} {mΩ : MeasurableSpace Ω}
    (μ ν : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (hm : mΩ = ⨆ n, F n)
    (h : ∀ n S, MeasurableSet[F n] S → μ S = ν S) : μ = ν := by
  let C : Set (Set Ω) := {S | ∃ n, MeasurableSet[F n] S}
  have hc : IsPiSystem C := by
    intro S hS T hT _
    obtain ⟨n,hn⟩ := hS
    obtain ⟨k,hk⟩ := hT
    exact ⟨max n k, ((F.mono (le_max_left n k)) S hn).inter
      ((F.mono (le_max_right n k)) T hk)⟩
  have hgen : mΩ = generateFrom C := by
    rw [hm]
    apply le_antisymm
    · apply iSup_le; intro n S hS
      exact measurableSet_generateFrom ⟨n,hS⟩
    · apply generateFrom_le
      rintro S ⟨n,hn⟩
      exact (le_iSup (fun n => F n) n) S hn
  exact ext_of_generate_finite C hgen hc (fun S ⟨n,hn⟩ => h n S hn)
    (h 0 Set.univ MeasurableSet.univ)

namespace ConsistentReferenceHistory

universe v12159_0 v12159_1

variable {Ω : Type v12159_0} {ι : Type v12159_1} {mΩ : MeasurableSpace Ω} [inst12159_0 : Fintype ι] [inst12159_1 : DecidableEq ι]
  {μ : Measure Ω} [inst12159_2 : IsFiniteMeasure μ] {F : Filtration ℕ mΩ}
  (H : ConsistentReferenceHistory (ι := ι) (μ := μ) F)

theorem full_reference_born (hm : mΩ = ⨆ n, F n) :
    ∃ W : PositiveMatrixMeasure Ω ι,
      (∀ n S, MeasurableSet[F n] S → W.value S = H.finiteValue n S) ∧
      ∀ (E : Matrix ι ι ℂ), E.PosSemidef → ∀ (ν : Measure Ω) [IsFiniteMeasure ν],
        (∀ n S, MeasurableSet[F n] S →
          (trace (E * H.finiteValue n S)).re = ν.real S) → W.testMeasure E = ν := by
  obtain ⟨W,hW⟩ := H.full_reference_measure
  refine ⟨W,hW,?_⟩
  intro E hE ν hν htests
  apply scalar_measure_ext_on_filtration _ _ F hm
  intro n S hS
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (W.testMeasure E).real S = ν.real S
  rw [W.testMeasure_real E hE S (F.le n S hS),hW n S hS]
  exact htests n S hS

end ConsistentReferenceHistory

end

namespace PositiveMatrixMeasure

universe v12187_0 v12187_1 v12187_2 v12187_3

variable {Ω : Type v12187_0} {T : Type v12187_1} {ι : Type v12187_2} {α : Type v12187_3} [inst12187_0 : MeasurableSpace Ω] [inst12187_1 : MeasurableSpace T]
  [inst12187_2 : Fintype ι] [inst12187_3 : DecidableEq ι]

omit inst12187_3 in
lemma value_sum_readout [DecidableEq ι] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (W : PositiveMatrixMeasure Ω ι) (a : Ω → α) (ha : Measurable a)
    (S : Set Ω) (hS : MeasurableSet S) :
    ∑ i, W.value (S ∩ a ⁻¹' {i}) = W.value S := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset α)) (fun i => S ∩ a ⁻¹' {i}) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hm : ∀ i ∈ (Finset.univ : Finset α), MeasurableSet (S ∩ a ⁻¹' {i}) :=
    fun i _ => hS.inter (ha (measurableSet_singleton i))
  have hu : (⋃ i ∈ (Finset.univ : Finset α), S ∩ a ⁻¹' {i}) = S := by
    ext x
    simp only [Finset.mem_univ,Set.iUnion_true,Set.mem_iUnion,Set.mem_inter_iff,
      Set.mem_preimage,Set.mem_singleton_iff]
    exact ⟨fun ⟨_,hx,_⟩ => hx, fun hx => ⟨a x,hx,rfl⟩⟩
  ext i j
  simp only [Matrix.sum_apply]
  have h := (W.entry i j).of_biUnion_finset hd hm
  rw [hu] at h
  simpa only [Finset.mem_univ,ite_true,value] using h.symm

lemma bitReadout_total (W : PositiveMatrixMeasure Ω ι) (record : Ω → T) (hr : Measurable record)
    (a b : Ω → Bool) (ha : Measurable a) (hb : Measurable b)
    (S : Set T) (hS : MeasurableSet S) :
    ∑ i, ∑ j, (W.bitReadout record hr a b ha hb i j).value S = W.value (record ⁻¹' S) := by
  simp_rw [bitReadout_value _ _ _ _ _ _ _ _ _ _ hS, ← Set.inter_assoc]
  have hi (i : Bool) : (∑ j, W.value ((record ⁻¹' S ∩ a ⁻¹' {i}) ∩ b ⁻¹' {j})) =
      W.value (record ⁻¹' S ∩ a ⁻¹' {i}) :=
    W.value_sum_readout b hb _ ((hr hS).inter (ha (measurableSet_singleton i)))
  simp_rw [hi]
  exact W.value_sum_readout a ha _ (hr hS)

theorem filtered_bitReadout_normalized [Nonempty ι]
    (W : PositiveMatrixMeasure Ω ι)
    (hprobe : W.value Set.univ = keepReference (outer (localProbe (ι := ι)) localProbe))
    (record : Ω → T) (hr : Measurable record)
    (a b : Ω → Bool) (ha : Measurable a) (hb : Measurable b)
    (R : Matrix ι ι ℂ) (hR : Density R) :
    (trace (∑ i, ∑ j,
      ((W.bitReadout record hr a b ha hb i j).filter (preparationFilter R)).value Set.univ)).re = 1 := by
  have he : (∑ i, ∑ j,
      ((W.bitReadout record hr a b ha hb i j).filter (preparationFilter R)).value Set.univ) =
      ((W.filter (preparationFilter R)).value Set.univ) := by
    simp_rw [← bitReadout_filter _ _ _ _ _ _ _ _ _ _ _ MeasurableSet.univ]
    rw [bitReadout_total _ _ _ _ _ _ _ _ MeasurableSet.univ,Set.preimage_univ]
  rw [he,filter_value,hprobe,← keepReference_filter,preparation_filter_identity,
    canonical_reference R hR.1,Matrix.trace_transpose,hR.2]
  rfl

end PositiveMatrixMeasure

end

section

open Matrix MeasureTheory ProbabilityTheory Function Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v12259_0 v12259_1 v12259_2 v12259_3 v12259_4 v12259_5 v12259_6

variable {O : Type v12259_0} {M : Type v12259_1} {ι : Type v12259_2} {η : Type v12259_3} [inst12259_0 : MeasurableSpace O] [inst12259_1 : MeasurableSpace M]
  [inst12259_2 : StandardBorelSpace O] [inst12259_3 : Nonempty O] [inst12259_4 : StandardBorelSpace M] [inst12259_5 : Nonempty M]
  [inst12259_6 : Fintype ι] [inst12259_7 : Fintype η] [inst12259_8 : DecidableEq ι] [inst12259_9 : DecidableEq η]
  {K : Type v12259_4} [inst12259_10 : MeasurableSpace K] [inst12259_11 : MeasurableSingletonClass K]
  [inst12259_12 : Fintype K] [inst12259_13 : DecidableEq K] [inst12259_14 : Nonempty K]
  (d : Discussion O M)
  (A : ℕ → Type v12259_5) (B : ℕ → Type v12259_6)
  [inst12259_15 : ∀ n, AddCommGroup (A n)] [inst12259_16 : ∀ n, Module ℂ (A n)] [inst12259_17 : ∀ n, One (A n)] [inst12259_18 : ∀ n, LE (A n)]
  [inst12259_19 : ∀ n, AddCommGroup (B n)] [inst12259_20 : ∀ n, Module ℂ (B n)] [inst12259_21 : ∀ n, One (B n)] [inst12259_22 : ∀ n, LE (B n)]

structure ClassicalProtocol where
  executionA : LocalObservableExecution (ι := ι) A d.kernelA d.sendA
  executionB : LocalObservableExecution (ι := η) B d.kernelB d.sendB
  initialA : executionA.reference 0 (Fin.elim0,Fin.elim0) =
    keepReference (outer (localProbe (ι := ι)) localProbe)
  initialB : executionB.reference 0 (Fin.elim0,Fin.elim0) =
    keepReference (outer (localProbe (ι := η)) localProbe)
  outputA : (ℕ → O) → K
  outputB : (ℕ → O) → K
  measurableA : Measurable[d.sampler.localField true] outputA
  measurableB : Measurable[d.sampler.localField false] outputB

variable {d A B}

namespace ClassicalProtocol

variable (p : ClassicalProtocol (ι := ι) (η := η) (K := K) d A B)

structure Completion where
  G : (ℕ → O) → Matrix ι ι ℂ
  H : (ℕ → O) → Matrix η η ℂ
  measurableG : Measurable[d.sampler.localField true] G
  measurableH : Measurable[d.sampler.localField false] H
  densityG : ∀ x, Density (G x)
  densityH : ∀ x, Density (H x)
  consistentG : ∀ n S, MeasurableSet[historyFiltration n] S →
    (∫ x in S, G x ∂d.probeLaw) = ∫ x in S,
      AdaptiveQuantum.globalLocalReferenceA d.sampler d.kernelA p.executionA n (historyPrefix n x) ∂d.probeLaw
  consistentH : ∀ n S, MeasurableSet[historyFiltration n] S →
    (∫ x in S, H x ∂d.probeLaw) = ∫ x in S,
      AdaptiveQuantum.globalLocalReferenceB d.sampler d.kernelB p.executionB n (historyPrefix n x) ∂d.probeLaw
  reference : PositiveMatrixMeasure (ℕ → O) (ι × η)
  reference_value : ∀ S, MeasurableSet S → reference.value S = ∫ x in S, G x ⊗ₖ H x ∂d.probeLaw
  reference_prefix : ∀ n S, MeasurableSet[historyFiltration n] S →
    reference.value S = ∫ x in S,
      AdaptiveQuantum.jointReference d.sampler d.kernelA d.kernelB p.executionA p.executionB
        n (historyPrefix n x) ∂d.probeLaw

omit inst12259_4 inst12259_5 inst12259_11 inst12259_12 inst12259_13 inst12259_14 in
lemma completion_exists [StandardBorelSpace M] [Nonempty M] [MeasurableSingletonClass K] [Fintype K] [DecidableEq K] [Nonempty K] : Nonempty p.Completion := by
  obtain ⟨G,H,hGm,hHm,hG,hH,hGc,hHc,W,hW,hWc⟩ :=
    AdaptiveQuantum.full_reference_extension d.sampler d.kernelA d.kernelB p.executionA p.executionB
      d.probeLaw d.probeLaw_prefix
  exact ⟨⟨G,H,hGm,hHm,hG,hH,hGc,hHc,W,hW,hWc⟩⟩

def completion : p.Completion := Classical.choice p.completion_exists

def toFinite : FiniteProtocol (ι := ι) (η := η) (K := K) d A B ℂ ℂ ℂ ℂ where
  executionA := p.executionA
  executionB := p.executionB
  initialA := p.initialA
  initialB := p.initialB
  incomingA := scalarIncoming p.completion.G p.completion.densityG p.completion.measurableG p.completion.consistentG
  incomingB := scalarIncoming p.completion.H p.completion.densityH p.completion.measurableH p.completion.consistentH
  readoutA := (scalarIncoming p.completion.G p.completion.densityG p.completion.measurableG
    p.completion.consistentG).classicalReadout p.outputA p.measurableA
  readoutB := (scalarIncoming p.completion.H p.completion.densityH p.completion.measurableH
    p.completion.consistentH).classicalReadout p.outputB p.measurableB

lemma completeReference_value (i j : K) (x : ℕ → O) :
    p.toFinite.completeReference i j x =
      if p.outputA x = i ∧ p.outputB x = j then p.completion.G x ⊗ₖ p.completion.H x else 0 := by
  simp only [FiniteProtocol.completeReference, toFinite,
    IncomingObservableProcess.classicalReadout_value, scalarIncoming]
  by_cases ha : p.outputA x = i <;> by_cases hb : p.outputB x = j <;>
    simp [ha,hb,scalarReference_one]

theorem output_event (i j : K) (S : Set (ℕ → M)) (hS : MeasurableSet S) :
    (p.toFinite.probeOutput i j).value S = p.completion.reference.value
      ((d.sampler.publicRecord ⁻¹' S) ∩ (p.outputA ⁻¹' {i} ∩ p.outputB ⁻¹' {j})) := by
  have ha := p.measurableA.mono (d.sampler.localField_le true) le_rfl
  have hb := p.measurableB.mono (d.sampler.localField_le false) le_rfl
  have he := (ha (measurableSet_singleton i)).inter (hb (measurableSet_singleton j))
  rw [p.toFinite.probeOutput_event i j S hS,p.completion.reference_value _
    ((d.sampler.measurable_publicRecord hS).inter he)]
  have hind : (fun x => p.toFinite.completeReference i j x) =
      (p.outputA ⁻¹' {i} ∩ p.outputB ⁻¹' {j}).indicator
        (fun x => p.completion.G x ⊗ₖ p.completion.H x) := by
    funext x
    simp only [p.completeReference_value,Set.indicator,Set.mem_inter_iff,Set.mem_preimage,
      Set.mem_singleton_iff]
  rw [hind,integral_indicator he,Measure.restrict_restrict he]
  rw [Set.inter_comm]

theorem canonicalOutput_event (R : Matrix (ι × η) (ι × η) ℂ)
    (i j : K) (S : Set (ℕ → M)) (hS : MeasurableSet S) :
    (p.toFinite.canonicalOutput R i j).value S =
      (p.completion.reference.filter (preparationFilter R)).value
        ((d.sampler.publicRecord ⁻¹' S) ∩ (p.outputA ⁻¹' {i} ∩ p.outputB ⁻¹' {j})) := by
  rw [FiniteProtocol.canonicalOutput,PositiveMatrixMeasure.filter_value,p.output_event i j S hS,
    PositiveMatrixMeasure.filter_value]

end ClassicalProtocol

end

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace PositiveMatrixMeasure

universe v12382_0 v12382_1 v12382_2

variable {Ω : Type v12382_0} {T : Type v12382_1} {ι : Type v12382_2} {mΩ : MeasurableSpace Ω} [inst12382_0 : MeasurableSpace T]
  [inst12382_1 : Fintype ι] [inst12382_2 : DecidableEq ι]

lemma value_eq_of_ae_set (W : PositiveMatrixMeasure Ω ι)
    (S U : Set Ω) (hS : MeasurableSet S) (hU : MeasurableSet U)
    (h : S =ᵐ[W.traceMeasure] U) : W.value S = W.value U := by
  ext i j
  rw [← W.integral_density_entry W.traceMeasure W.value_zero_of_traceMeasure_zero S hS i j,
    ← W.integral_density_entry W.traceMeasure W.value_zero_of_traceMeasure_zero U hU i j]
  exact setIntegral_congr_set h

theorem bitReadout_eq_off_private_null (W : PositiveMatrixMeasure Ω ι)
    (record : Ω → T) (hr : Measurable record)
    (a b a' b' : Ω → Bool) (ha : Measurable a) (hb : Measurable b)
    (ha' : Measurable a') (hb' : Measurable b')
    (N : Set Ω) (hN : W.traceMeasure N = 0)
    (hbits : ∀ x, x ∉ N → a x = a' x ∧ b x = b' x)
    (i j : Bool) :
    W.bitReadout record hr a b ha hb i j = W.bitReadout record hr a' b' ha' hb' i j := by
  apply eq_of_value
  intro S hS
  rw [bitReadout_value _ _ _ _ _ _ _ _ _ _ hS,
    bitReadout_value _ _ _ _ _ _ _ _ _ _ hS]
  apply value_eq_of_ae_set _ _ _
    ((hr hS).inter ((ha (measurableSet_singleton i)).inter (hb (measurableSet_singleton j))))
    ((hr hS).inter ((ha' (measurableSet_singleton i)).inter (hb' (measurableSet_singleton j))))
  have hn : ∀ᵐ x ∂W.traceMeasure, x ∉ N := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hN
  filter_upwards [hn] with x hx
  rcases hbits x hx with ⟨he,hf⟩
  apply propext
  change (record x ∈ S ∧ (a x = i ∧ b x = j)) ↔
    (record x ∈ S ∧ (a' x = i ∧ b' x = j))
  rw [he,hf]

universe v12423_0

theorem prepared_default_outputs {κ : Type v12423_0} [Fintype κ] [DecidableEq κ]
    (V : PositiveMatrixMeasure Ω κ) (W : PositiveMatrixMeasure Ω ι)
    (K : Matrix κ ι ℂ) (F : Filtration ℕ mΩ) (hm : mΩ = ⨆ n, F n)
    (hfinite : ∀ n S, MeasurableSet[F n] S → V.value S = K * W.value S * Kᴴ)
    (record : Ω → T) (hr : Measurable record)
    (a b a' b' : Ω → Bool) (ha : Measurable a) (hb : Measurable b)
    (ha' : Measurable a') (hb' : Measurable b')
    (N : Set Ω) (hN : V.traceMeasure N = 0)
    (hbits : ∀ x, x ∉ N → a x = a' x ∧ b x = b' x)
    (i j : Bool) :
    V.bitReadout record hr a b ha hb i j =
      (W.bitReadout record hr a' b' ha' hb' i j).filter K := by
  rw [V.bitReadout_eq_off_private_null record hr a b a' b' ha hb ha' hb' N hN hbits i j]
  have he : V = W.filter K := by
    exact W.filter_eq_of_filtration V K F hm hfinite
  rw [he]
  apply eq_of_value
  intro S hS
  exact W.bitReadout_filter record hr a' b' ha' hb' i j K S hS

end PositiveMatrixMeasure

end ZeroKey

section

open Matrix MeasureTheory ProbabilityTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker TensorProduct

namespace UnrestrictedQuantum

section Algebra

universe v12456_0 v12456_1 v12456_2 v12456_3 v12456_4 v12456_5 v12456_6

variable {A : Type v12456_0} {B : Type v12456_1} {C : Type v12456_2} {D : Type v12456_3}
  [inst12456_0 : AddCommGroup A] [inst12456_1 : Module ℂ A] [inst12456_2 : AddCommGroup B] [inst12456_3 : Module ℂ B]
  [inst12456_4 : AddCommGroup C] [inst12456_5 : Module ℂ C] [inst12456_6 : AddCommGroup D] [inst12456_7 : Module ℂ D]
  {ι : Type v12456_4} {η : Type v12456_5} {κ : Type v12456_6} [inst12456_8 : Fintype ι] [inst12456_9 : Fintype η] [inst12456_10 : Fintype κ]
  [inst12456_11 : DecidableEq ι] [inst12456_12 : DecidableEq η] [inst12456_13 : DecidableEq κ]

omit inst12456_10 inst12456_11 inst12456_12 inst12456_13 in
theorem tensor_filter_precompose [Fintype κ] [DecidableEq ι] [DecidableEq η] [DecidableEq κ]
    (S : ReferenceFunctional A ι) (T : ReferenceFunctional B η)
    (K : Matrix κ (ι × η) ℂ) (L : C →ₗ[ℂ] A) (N : D →ₗ[ℂ] B) :
    (filterFunctional K (tensorReferenceFunctional S T)).comp (TensorProduct.map L N) =
      filterFunctional K (tensorReferenceFunctional (S.comp L) (T.comp N)) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul]
  rfl

theorem tensor_filter_event [One C] [One D]
    (S : ReferenceFunctional A ι) (T : ReferenceFunctional B η)
    (K : Matrix κ (ι × η) ℂ) (L : C →ₗ[ℂ] A) (N : D →ₗ[ℂ] B) :
    ((filterFunctional K (tensorReferenceFunctional S T)).comp
      (TensorProduct.map L N)) (1 ⊗ₜ[ℂ] 1) = K * (S (L 1) ⊗ₖ T (N 1)) * Kᴴ := by
  rw [tensor_filter_precompose]
  rfl

end Algebra

universe v12490_0 v12490_1 v12490_2 v12490_3 v12490_4 v12490_5 v12490_6

variable {O : Type v12490_0} {A : Type v12490_1} {B : Type v12490_2} {C : Type v12490_3} {ι : Type v12490_4} {η : Type v12490_5} {κ : Type v12490_6} [inst12490_0 : MeasurableSpace O]
  [inst12490_1 : AddCommGroup A] [inst12490_2 : Module ℂ A] [inst12490_3 : One A] [inst12490_4 : LE A]
  [inst12490_5 : AddCommGroup B] [inst12490_6 : Module ℂ B] [inst12490_7 : One B] [inst12490_8 : LE B]
  [inst12490_9 : AddCommGroup C] [inst12490_10 : Module ℂ C] [inst12490_11 : One C]
  [inst12490_12 : Fintype ι] [inst12490_13 : Fintype η] [inst12490_14 : Fintype κ]
  [inst12490_15 : DecidableEq ι] [inst12490_16 : DecidableEq η] [inst12490_17 : DecidableEq κ]
  (J : ObservableInstrument O A B) (S : ReferenceFunctional A ι)
  (r : InstrumentRun J S) (T : ReferenceFunctional C η)

omit inst12490_11 in
theorem InstrumentRun.tensor_event [One C] (E : Set O) (hE : MeasurableSet E)
    (a : B) (b : C) :
    (∫ o in E, r.posterior o a ⊗ₖ T b ∂r.law) = S (J.operation E a) ⊗ₖ T b := by
  have hi : Integrable (fun o => r.posterior o a ⊗ₖ T b) r.law := by
    apply ZeroKey.integrable_matrix_of_entries
    intro i j
    exact (r.integrable a i.1 j.1).mul_const _
  ext i j
  rw [ZeroKey.integral_matrix_entry hi.integrableOn]
  simp only [Matrix.kroneckerMap_apply]
  rw [integral_mul_const,r.update E hE]

theorem InstrumentRun.filtered_tensor_event (K : Matrix κ (ι × η) ℂ)
    (E : Set O) (hE : MeasurableSet E) (a : B) (b : C) :
    (∫ o in E, K * (r.posterior o a ⊗ₖ T b) * Kᴴ ∂r.law) =
      K * (S (J.operation E a) ⊗ₖ T b) * Kᴴ := by
  have hi : Integrable (fun o => r.posterior o a ⊗ₖ T b) r.law := by
    apply ZeroKey.integrable_matrix_of_entries
    intro i j
    exact (r.integrable a i.1 j.1).mul_const _
  rw [ZeroKey.integral_filter _ hi.integrableOn,InstrumentRun.tensor_event J S r T E hE]

end UnrestrictedQuantum

namespace ZeroKey

open UnrestrictedQuantum

universe v12531_0 v12531_1 v12531_2 v12531_3 v12531_4 v12531_5 v12531_6 v12531_7 v12531_8 v12531_9 v12531_10

variable {O : Type v12531_0} {M : Type v12531_1} {ι : Type v12531_2} {η : Type v12531_3} {κ : Type v12531_4} [inst12531_0 : MeasurableSpace O] [inst12531_1 : MeasurableSpace M]
  [inst12531_2 : StandardBorelSpace O] [inst12531_3 : Nonempty O] [inst12531_4 : StandardBorelSpace M] [inst12531_5 : Nonempty M]
  [inst12531_6 : Fintype ι] [inst12531_7 : Fintype η] [inst12531_8 : Fintype κ] [inst12531_9 : DecidableEq ι] [inst12531_10 : DecidableEq η] [inst12531_11 : DecidableEq κ]
  {d : Discussion O M} {A : ℕ → Type v12531_5} {B : ℕ → Type v12531_6}
  [inst12531_12 : ∀ n, AddCommGroup (A n)] [inst12531_13 : ∀ n, Module ℂ (A n)] [inst12531_14 : ∀ n, One (A n)] [inst12531_15 : ∀ n, LE (A n)]
  [inst12531_16 : ∀ n, AddCommGroup (B n)] [inst12531_17 : ∀ n, Module ℂ (B n)] [inst12531_18 : ∀ n, One (B n)] [inst12531_19 : ∀ n, LE (B n)]
  {TA : Type v12531_7} {TB : Type v12531_8} {CA : Type v12531_9} {CB : Type v12531_10}
  [inst12531_20 : AddCommGroup TA] [inst12531_21 : Module ℂ TA] [inst12531_22 : One TA] [inst12531_23 : LE TA]
  [inst12531_24 : AddCommGroup TB] [inst12531_25 : Module ℂ TB] [inst12531_26 : One TB] [inst12531_27 : LE TB]
  [inst12531_28 : AddCommGroup CA] [inst12531_29 : Module ℂ CA] [inst12531_30 : One CA] [inst12531_31 : LE CA]
  [inst12531_32 : AddCommGroup CB] [inst12531_33 : Module ℂ CB] [inst12531_34 : One CB] [inst12531_35 : LE CB]
  (p : BitProtocol (ι := ι) (η := η) d A B TA TB CA CB)

theorem BitProtocol.filtered_output_event (K : Matrix κ (ι × η) ℂ)
    (i j : Bool) (E : Set (ℕ → M)) (hE : MeasurableSet E) :
    ((p.probeOutput i j).filter K).value E =
      ∫ x in d.sampler.publicRecord ⁻¹' E,
        ((filterFunctional K (tensorReferenceFunctional (p.incomingA.state x) (p.incomingB.state x))).comp
          (TensorProduct.map ((p.readoutA.instrument x).operation {i})
            ((p.readoutB.instrument x).operation {j}))) (1 ⊗ₜ[ℂ] 1) ∂d.probeLaw := by
  rw [PositiveMatrixMeasure.filter_value,p.probeOutput_event i j E hE]
  simp_rw [tensor_filter_event]
  exact (integral_filter _ (p.completeReference_integrable i j).integrableOn).symm

end ZeroKey

end

namespace ZeroKey

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open UnrestrictedQuantum

universe v12573_0 v12573_1 v12573_2 v12573_3 v12573_4 v12573_5

variable {O : Type v12573_0} {M : Type v12573_1} {ι : Type v12573_2} {η : Type v12573_3} [inst12573_0 : MeasurableSpace O] [inst12573_1 : MeasurableSpace M]
  [inst12573_2 : StandardBorelSpace O] [inst12573_3 : Nonempty O] [inst12573_4 : StandardBorelSpace M] [inst12573_5 : Nonempty M]
  [inst12573_6 : Fintype ι] [inst12573_7 : Fintype η] [inst12573_8 : DecidableEq ι] [inst12573_9 : DecidableEq η]
  {d : Discussion O M} {A : ℕ → Type v12573_4} {B : ℕ → Type v12573_5}
  [inst12573_10 : ∀ n, AddCommGroup (A n)] [inst12573_11 : ∀ n, Module ℂ (A n)] [inst12573_12 : ∀ n, One (A n)] [inst12573_13 : ∀ n, LE (A n)]
  [inst12573_14 : ∀ n, AddCommGroup (B n)] [inst12573_15 : ∀ n, Module ℂ (B n)] [inst12573_16 : ∀ n, One (B n)] [inst12573_17 : ∀ n, LE (B n)]

namespace ClassicalProtocol

variable (p : ClassicalProtocol (ι := ι) (η := η) (K := Bool) d A B)

def toBit : BitProtocol (ι := ι) (η := η) d A B ℂ ℂ ℂ ℂ := p.toFinite.toBit id

lemma toBit_completeReference (i j : Bool) (x : ℕ → O) :
    p.toBit.completeReference i j x = p.toFinite.completeReference i j x := rfl

lemma toBit_probeOutput (i j : Bool) : p.toBit.probeOutput i j = p.toFinite.probeOutput i j := by
  apply PositiveMatrixMeasure.eq_of_value
  intro S hS
  rw [p.toBit.probeOutput_event i j S hS,p.toFinite.probeOutput_event i j S hS]
  rfl

universe v12596_0

theorem toBit_purifiedOutput {κ : Type v12596_0} [Fintype κ] [DecidableEq κ]
    (K : Matrix κ (ι × η) ℂ) (i j : Bool) :
    (p.toBit.probeOutput i j).filter K =
      (p.completion.reference.filter K).bitReadout
        d.sampler.publicRecord d.sampler.measurable_publicRecord p.outputA p.outputB
        (p.measurableA.mono (d.sampler.localField_le true) le_rfl)
        (p.measurableB.mono (d.sampler.localField_le false) le_rfl) i j := by
  apply PositiveMatrixMeasure.eq_of_value
  intro S hS
  rw [PositiveMatrixMeasure.bitReadout_value _ _ _ _ _ _ _ _ _ _ hS,
    PositiveMatrixMeasure.filter_value,PositiveMatrixMeasure.filter_value,
    p.toBit_probeOutput,p.output_event i j S hS]

universe v12613_0

theorem prepared_actual_output {κ : Type v12613_0} [Fintype κ] [DecidableEq κ]
    (K : Matrix κ (ι × η) ℂ) (V : PositiveMatrixMeasure (ℕ → O) κ)
    (hfinite : ∀ n S, MeasurableSet[historyFiltration n] S →
      V.value S = K * (∫ x in S,
        AdaptiveQuantum.jointReference d.sampler d.kernelA d.kernelB p.executionA p.executionB
          n (historyPrefix n x) ∂d.probeLaw) * Kᴴ)
    (a b : (ℕ → O) → Bool) (ha : Measurable a) (hb : Measurable b)
    (N : Set (ℕ → O)) (hN : V.traceMeasure N = 0)
    (hbits : ∀ x, x ∉ N → a x = p.outputA x ∧ b x = p.outputB x)
    (i j : Bool) :
    V.bitReadout d.sampler.publicRecord d.sampler.measurable_publicRecord a b ha hb i j =
      (p.toBit.probeOutput i j).filter K := by
  have he : V = p.completion.reference.filter K := by
    apply p.completion.reference.filter_eq_of_filtration V K historyFiltration
    · exact historyFiltration_generates
    · intro n S hS
      rw [p.completion.reference_prefix n S hS]
      exact hfinite n S hS
  rw [V.bitReadout_eq_off_private_null _ _ a b p.outputA p.outputB ha hb
    (p.measurableA.mono (d.sampler.localField_le true) le_rfl)
    (p.measurableB.mono (d.sampler.localField_le false) le_rfl) N hN hbits i j,he,
    p.toBit_purifiedOutput K i j]

end ClassicalProtocol

end ZeroKey

open Matrix MeasureTheory ProbabilityTheory

open scoped ComplexOrder MatrixOrder

namespace UnrestrictedQuantum

universe v12649_0 v12649_1 v12649_2

variable {O : Type v12649_0} {A : Type v12649_1} {ι : Type v12649_2} [inst12649_0 : MeasurableSpace O]
  [inst12649_1 : AddCommGroup A] [inst12649_2 : Module ℂ A] [inst12649_3 : One A] [inst12649_4 : LE A]
  [inst12649_5 : Fintype ι] [inst12649_6 : DecidableEq ι]
  (μ : Measure O) [inst12649_7 : IsProbabilityMeasure μ]
  (positive_scaling : ∀ (r : ℝ), 0 ≤ r → ∀ a : A, 0 ≤ a → 0 ≤ (r : ℂ) • a)

def independentCoinInstrument : ObservableInstrument O A A where
  operation E := (μ.real E : ℂ) • LinearMap.id
  positive E hE a ha := positive_scaling (μ.real E) ENNReal.toReal_nonneg a ha
  total_unit := by simp [Measure.real]

def independentCoinRun (S : ReferenceFunctional A ι) (hS : PositiveFunctional S)
    (hn : trace (S 1) = 1) : InstrumentRun (independentCoinInstrument μ positive_scaling) S where
  law := μ
  probability := inferInstance
  posterior _ := S
  posterior_positive _ := hS
  posterior_trace _ := hn
  integrable _ _ _ := integrable_const _
  update E hE a i j := by
    simp only [independentCoinInstrument,LinearMap.smul_apply,LinearMap.id_apply,
      map_smul,Matrix.smul_apply,integral_const,
      smul_eq_mul,Complex.real_smul]
    simp only [Measure.real, Measure.restrict_apply_univ]

omit inst12649_6 in
lemma independentCoinRun_reference [DecidableEq ι] (S : ReferenceFunctional A ι) (hS : PositiveFunctional S)
    (hn : trace (S 1) = 1) (o : O) (a : A) :
    (independentCoinRun μ positive_scaling S hS hn).posterior o a = S a := rfl

end UnrestrictedQuantum

end

end OAI
