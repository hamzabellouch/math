import OAI.Probability.SLE.Mass.RadonApproximationList
import OAI.Probability.SLE.Mass.RawRadonLimit
import OAI.Probability.SLE.Mass.RadonTestDetermines
import Mathlib.MeasureTheory.Function.FactorsThrough

namespace OAI

/-! Doob--Dynkin factorization of a locally finite Radon kernel through
countably many real compact tests. The factor is regular on every input and
is reconstructed in the target data space, without ambient null-set changes. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology CompactlySupported

namespace SLEExactGauge

lemma exists_measurable_nat_choice
    {Y : Type*} [MeasurableSpace Y] (p : Y → ℕ → Prop)
    (hm : ∀ k, MeasurableSet {y | p y k}) :
    ∃ i : Y → ℕ, Measurable i ∧ ∀ y, (∃ k, p y k) → p y (i y) := by
  let q (y : Y) (k : ℕ) := (∃ j, p y j) → p y k
  have hq (y : Y) : ∃ k, q y k := by
    by_cases h : ∃ j, p y j
    · obtain ⟨k,hk⟩ := h
      exact ⟨k,fun _ => hk⟩
    · exact ⟨0,fun h' => (h h').elim⟩
  have hqm (k : ℕ) : MeasurableSet {y | q y k} := by
    have he : {y | q y k} = (⋃ j, {y | p y j})ᶜ ∪ {y | p y k} := by
      ext y
      simp only [q,mem_ofPred_eq,mem_union,mem_compl_iff,mem_iUnion]
      tauto
    rw [he]
    exact (MeasurableSet.iUnion hm).compl.union (hm k)
  exact ⟨fun y => Nat.find (hq y),measurable_find hq hqm,
    fun y hy => Nat.find_spec (hq y) hy⟩

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- Countable compact tests suffice for a raw measurable Radon factor.
The factorization equality holds at every original input. -/
theorem LocalTestFamily.measurable_radon_factor
    (D : LocalTestFamily X) {Ω Y : Type*} [MeasurableSpace Y]
    (F : Ω → Y) (μ : Ω → Measure X) (hμ : ∀ ω, (μ ω).Regular)
    (htest : ∀ j, Measurable[MeasurableSpace.comap F inferInstance]
      (fun ω => ∫ x, D.test j x ∂μ ω)) :
    ∃ ν : Y → Measure X, Measurable ν ∧ (∀ y, (ν y).Regular) ∧ ∀ ω, ν (F ω)=μ ω := by
  choose g hgm hg using fun j => (htest j).exists_eq_measurable_comp
  obtain ⟨a,ha,happrox⟩ := D.exists_countable_measure_approximants
  let p (n : ℕ) (y : Y) (k : ℕ) : Prop :=
    ∀ j < n+1, |(∫ x, D.test j x ∂a k)-g j y| < 1/(n+1:ℝ)
  have hpm (n k : ℕ) : MeasurableSet {y | p n y k} := by
    simp only [p,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using
      measurableSet_lt (measurable_const.sub (hgm j)).norm measurable_const
  choose i him hi using fun n => exists_measurable_nat_choice (p n) (hpm n)
  let μn (n : ℕ) (y : Y) := a (i n y)
  have hμnm (n : ℕ) (f : C_c(X,ℝ)) : Measurable (fun y => ∫ x, f x ∂μn n y) :=
    (measurable_of_countable (fun k => ∫ x, f x ∂a k)).comp (him n)
  have hvalid (n : ℕ) (ω : Ω) : p n (F ω) (i n (F ω)) := by
    apply hi n
    obtain ⟨k,hk⟩ := happrox (μ ω) (hμ ω) n (1/(n+1:ℝ)) (by positivity)
    refine ⟨k,fun j hj => ?_⟩
    have he : g j (F ω) = ∫ x, D.test j x ∂μ ω := congr_fun (hg j) ω |>.symm
    rw [he]
    exact hk j hj
  have hlim (ω : Ω) (j : ℕ) : Tendsto (fun n => ∫ x, D.test j x ∂μn n (F ω)) atTop
      (𝓝 (∫ x, D.test j x ∂μ ω)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε))
    refine ⟨max j N,fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hjn : j < n+1 := by omega
    have hv := hvalid n ω j hjn
    have he : g j (F ω) = ∫ x, D.test j x ∂μ ω := congr_fun (hg j) ω |>.symm
    rw [he] at hv
    exact hv.trans (hN n (le_trans (le_max_right _ _) hn))
  obtain ⟨ν,hνm,hν,hνlim⟩ := D.exists_raw_radon_limit μn (fun n y => ha (i n y)) hμnm
  refine ⟨ν,hνm,hν,fun ω => ?_⟩
  let := hν (F ω)
  let := hμ ω
  apply D.measure_eq_of_test_integrals
  intro j
  exact tendsto_nhds_unique (hνlim (F ω) (fun j => (hlim ω j).cauchySeq) (D.test j)) (hlim ω j)

end SLEExactGauge

end

end OAI
