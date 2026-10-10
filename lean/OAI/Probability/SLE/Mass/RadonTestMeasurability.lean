import OAI.Probability.SLE.Mass.RadonTestLimitProperties
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! A Radon measure determined by measurable compact continuous tests is
a measurable measure-valued function. Local finite restrictions are used,
so no finite total-mass hypothesis is imposed. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported ENNReal

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- A fixed countable list of compact cutoffs recovers the mass of a fixed
open set simultaneously for all Radon measures. -/
theorem exists_open_cutoff_sequence (U : Set X) (hU : IsOpen U) :
    ∃ f : ℕ → C_c(X, ℝ), (∀ n x, 0 ≤ f n x ∧ f n x ≤ 1) ∧
      (∀ n, tsupport (f n) ⊆ U) ∧ ∀ (μ : Measure X), μ.Regular →
        μ U = ⨆ n, ENNReal.ofReal (∫ x, f n x ∂μ) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let A (n : ℕ) : Set X := Subtype.val '' K n
  have hAc (n : ℕ) : IsCompact (A n) := (K.isCompact n).image continuous_subtype_val
  have hAU (n : ℕ) : A n ⊆ U := by rintro _ ⟨x,_,rfl⟩; exact x.2
  have hcut (n : ℕ) := exists_continuousMap_one_of_isCompact_subset_isOpen (hAc n) hU (hAU n)
  choose f hf1 hfc hfs hf01 using hcut
  let g (n : ℕ) : C_c(X, ℝ) := ⟨f n,hfc n⟩
  have hAm : Monotone A := fun _ _ h => image_mono (K.subset h)
  have hUnion : (⋃ n, A n)=U := by
    ext x
    constructor
    · intro hx
      obtain ⟨n,hn⟩ := mem_iUnion.mp hx
      exact hAU n hn
    · intro hx
      obtain ⟨n,hn⟩ := K.exists_mem (⟨x,hx⟩ : U)
      exact mem_iUnion.mpr ⟨n,⟨⟨x,hx⟩,hn,rfl⟩⟩
  refine ⟨g,hf01,hfs,fun μ hμ => ?_⟩
  let : μ.Regular := hμ
  apply le_antisymm
  · rw [← hUnion,hAm.measure_iUnion]
    exact iSup_mono fun n => compact_measure_le_test_integral μ (g n)
      (fun x => (hf01 n x).1) (hAc n) (hf1 n)
  · exact iSup_le fun n => test_integral_le_measure μ (g n) (hf01 n) (hfs n)

/-- Measurability of all compact continuous test integrals implies
measurability of every open-set evaluation. -/
theorem measurable_open_evaluation_of_tests
    {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → Measure X)
    (hν : ∀ ω, (ν ω).Regular)
    (htest : ∀ f : C_c(X, ℝ), Measurable (fun ω => ∫ x, f x ∂ν ω))
    (U : Set X) (hU : IsOpen U) : Measurable (fun ω => ν ω U) := by
  obtain ⟨f,_,_,hf⟩ := exists_open_cutoff_sequence U hU
  have he : (fun ω => ν ω U)=(fun ω => ⨆ n, ENNReal.ofReal (∫ x, f n x ∂ν ω)) :=
    funext fun ω => hf (ν ω) (hν ω)
  rw [he]
  exact Measurable.iSup fun n => (htest (f n)).ennreal_ofReal

omit [T2Space X] in
/-- Locally finite Radon kernels are measurable once all their open-set
evaluations are measurable. -/
theorem measurable_radon_of_open_evaluations
    {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → Measure X)
    (hν : ∀ ω, (ν ω).Regular)
    (hopen : ∀ U : Set X, IsOpen U → Measurable (fun ω => ν ω U)) : Measurable ν := by
  let K := CompactExhaustion.choice X
  let U (n : ℕ) := interior (K n)
  have hU (n : ℕ) : IsOpen (U n) := isOpen_interior
  have hfinite (n : ℕ) (ω : Ω) : ν ω (U n) < ⊤ := by
    let : (ν ω).Regular := hν ω
    exact (measure_mono interior_subset).trans_lt (K.isCompact n).measure_lt_top
  have hlocal (n : ℕ) : ∀ A : Set X, MeasurableSet A →
      Measurable (fun ω => ν ω (A ∩ U n)) := by
    apply MeasurableSet.induction_on_open
    · intro A hA
      exact hopen _ (hA.inter (hU n))
    · intro A hA hm
      have he (ω : Ω) : ν ω (Aᶜ ∩ U n)=ν ω (U n)-ν ω (A ∩ U n) := by
        have hset : Aᶜ ∩ U n=U n \ (A ∩ U n) := by ext x; simp only [Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_sdiff]; tauto
        rw [hset]
        exact measure_sdiff inter_subset_right (hA.inter (hU n).measurableSet).nullMeasurableSet
          ((measure_mono inter_subset_right).trans_lt (hfinite n ω)).ne
      simp_rw [he]
      exact (hopen _ (hU n)).sub hm
    · intro A hd hA hm
      have hd' : Pairwise (fun i j => Disjoint (A i ∩ U n) (A j ∩ U n)) :=
        fun i j hij => (hd hij).mono inter_subset_left inter_subset_left
      have he (ω : Ω) : ν ω ((⋃ i, A i) ∩ U n)=∑' i, ν ω (A i ∩ U n) := by
        rw [iUnion_inter]
        exact measure_iUnion hd' (fun i => (hA i).inter (hU n).measurableSet)
      simp_rw [he]
      exact Measurable.tsum hm
  have hUnion : (⋃ n, U n)=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n,hn⟩ := K.exists_mem x
    exact mem_iUnion.mpr ⟨n+1,K.subset_interior_succ n hn⟩
  have hUm : Monotone U := fun _ _ h => interior_mono (K.subset h)
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have he (ω : Ω) : ν ω A=⨆ n, ν ω (A ∩ U n) := by
    have hmono : Monotone (fun n => A ∩ U n) := monotone_const.inter hUm
    rw [← hmono.measure_iUnion,← inter_iUnion,hUnion,inter_univ]
  simp_rw [he]
  exact Measurable.iSup fun n => hlocal n A hA

/-- A reconstruction with measurable compact-test integrals is a genuine
measurable measure-valued map, not only a collection of scalar tests. -/
theorem measurable_radon_of_tests
    {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → Measure X)
    (hν : ∀ ω, (ν ω).Regular)
    (htest : ∀ f : C_c(X, ℝ), Measurable (fun ω => ∫ x, f x ∂ν ω)) : Measurable ν :=
  measurable_radon_of_open_evaluations ν hν (measurable_open_evaluation_of_tests ν hν htest)

/-- Pointwise convergence of measurable compact-test integrals provides
measurability of the reconstructed Radon kernel. -/
theorem measurable_radon_of_test_limits
    {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Ω → Measure X) (ν : Ω → Measure X)
    (hν : ∀ ω, (ν ω).Regular)
    (hmeas : ∀ n (f : C_c(X, ℝ)), Measurable (fun ω => ∫ x, f x ∂μ n ω))
    (hlim : ∀ ω (f : C_c(X, ℝ)), Tendsto (fun n => ∫ x, f x ∂μ n ω)
      atTop (𝓝 (∫ x, f x ∂ν ω))) : Measurable ν := by
  apply measurable_radon_of_tests ν hν
  intro f
  exact measurable_of_tendsto_metrizable (fun n => hmeas n f)
    (tendsto_pi_nhds.mpr (fun ω => hlim ω f))

end SLEExactGauge

end

end OAI
