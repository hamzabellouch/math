import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.GreenIdentities

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory Filter Topology Set CompactlySupported
open scoped ENNReal NNReal

namespace SLEExactGauge.MassVersions

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

 
theorem open_countable_tests (U : Set X) (hU : IsOpen U) :
    ∃ f : ℕ → C_c(X, ℝ),
      (∀ n x, f n x ∈ Icc 0 1) ∧ (∀ n, EqOn (f n) 0 Uᶜ) ∧
      ∀ μ : Measure X, IsFiniteMeasureOnCompacts μ →
        μ U = ⨆ n, ENNReal.ofReal (∫ x, f n x ∂μ) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let A : ℕ → Set X := fun n => Subtype.val '' K n
  have hAc (n : ℕ) : IsCompact (A n) := (K.isCompact n).image continuous_subtype_val
  have hAU (n : ℕ) : A n ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  choose g hg1 hg0 hgc hg01 using fun n =>
    exists_continuous_one_zero_of_isCompact (hAc n) hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hAU n))
  let f : ℕ → C_c(X, ℝ) := fun n => ⟨g n, hgc n⟩
  refine ⟨f, hg01, hg0, fun μ hμ => ?_⟩
  let := hμ
  have hmono : Monotone A := fun n m h => image_mono (K.subset h)
  have hcover : ⋃ n, A n = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact hAU n hn
    · intro hx
      obtain ⟨n, hn⟩ := K.exists_mem ⟨x, hx⟩
      exact mem_iUnion.mpr ⟨n, ⟨⟨x, hx⟩, hn, rfl⟩⟩
  apply le_antisymm
  · rw [← hcover, hmono.measure_iUnion]
    apply iSup_mono
    intro n
    apply (f n).integrable.measure_le_integral
    · exact Eventually.of_forall (fun x => (hg01 n x).1)
    · intro x hx
      exact le_of_eq ((hg1 n hx).symm)
  · apply iSup_le
    intro n
    exact integral_le_measure (fun x _ => (hg01 n x).2) (fun x hx => (hg0 n hx).le)

 

theorem measurable_measure_of_compact_tests {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure X) [∀ ω, IsFiniteMeasureOnCompacts (μ ω)]
    (hμ : ∀ f : C_c(X, ℝ), Measurable (fun ω => ∫ x, f x ∂μ ω)) :
    Measurable μ := by
  classical
  have hopen (U : Set X) (hU : IsOpen U) : Measurable (fun ω => μ ω U) := by
    obtain ⟨f, -, -, hf⟩ := open_countable_tests U hU
    have he (ω : Ω) := hf (μ ω) inferInstance
    simp_rw [he]
    exact Measurable.iSup (fun n => (hμ (f n)).ennreal_ofReal)
  let K := CompactExhaustion.choice X
  let V : ℕ → Set X := fun n => interior (K n)
  have hV (n : ℕ) : IsOpen (V n) := isOpen_interior
  have hVmono : Monotone V := fun n m h => interior_mono (K.subset h)
  have hVcover : ⋃ n, V n = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n+1, K.subset_interior_succ n hn⟩
  have hm (n : ℕ) : Measurable (fun ω => (μ ω).restrict (V n)) := by
    have (ω : Ω) : IsFiniteMeasure ((μ ω).restrict (V n)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact (measure_mono interior_subset).trans_lt (K.isCompact n).measure_lt_top
    refine Measurable.measure_of_isPiSystem
      (μ := fun ω => (μ ω).restrict (V n))
      (S := {s : Set X | IsOpen s}) ?_
      (fun s hs t ht _ => hs.inter ht) ?_ ?_
    · exact BorelSpace.measurable_eq (α := X)
    · intro U hU
      simp_rw [Measure.restrict_apply hU.measurableSet]
      exact hopen (U ∩ V n) (hU.inter (hV n))
    · simp_rw [Measure.restrict_apply_univ]
      exact hopen (V n) (hV n)
  apply Measure.measurable_of_measurable_coe
  intro U hU
  have he (ω : Ω) : μ ω U = ⨆ n, ((μ ω).restrict (V n)) U := by
    simp_rw [Measure.restrict_apply hU]
    have hmono : Monotone (fun n => U ∩ V n) := fun n m h => inter_subset_inter_right U (hVmono h)
    rw [← hmono.measure_iUnion, ← inter_iUnion, hVcover, inter_univ]
  simp_rw [he]
  exact Measurable.iSup (fun n => (Measure.measurable_coe hU).comp (hm n))

 
noncomputable def determiningTests : ℕ → C_c(X, ℝ) :=
  Classical.choose (ExactSLEMassExtraction.determining_tests_radon_limit X)

 

def TestConverges (L : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ)) : Prop :=
  ∀ i, ∃ v : ℝ, Tendsto (fun j => L j (determiningTests i)) atTop (𝓝 v)

lemma exists_radon_of_testConverges (L : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ))
    (h : TestConverges L) :
    ∃ μ : Measure X, IsFiniteMeasureOnCompacts μ ∧ μ.Regular ∧
      ∀ f : C_c(X, ℝ), Tendsto (fun j => L j f) atTop (𝓝 (∫ x, f x ∂μ)) :=
  (Classical.choose_spec (ExactSLEMassExtraction.determining_tests_radon_limit X)) L h

 

noncomputable def radonLimit (L : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ)) : Measure X := by
  classical
  exact if h : TestConverges L then Classical.choose (exists_radon_of_testConverges L h) else 0

lemma radonLimit_finite (L : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ)) :
    IsFiniteMeasureOnCompacts (radonLimit L) := by
  classical
  unfold radonLimit
  split_ifs with h
  · exact (Classical.choose_spec (exists_radon_of_testConverges L h)).1
  · infer_instance

lemma radonLimit_regular (L : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ)) :
    (radonLimit L).Regular := by
  classical
  unfold radonLimit
  split_ifs with h
  · exact (Classical.choose_spec (exists_radon_of_testConverges L h)).2.1
  · infer_instance

lemma tendsto_radonLimit (L : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ)) (h : TestConverges L)
    (f : C_c(X, ℝ)) :
    Tendsto (fun j => L j f) atTop (𝓝 (∫ x, f x ∂radonLimit L)) := by
  classical
  simpa only [radonLimit, dite_eq_left h] using
    (Classical.choose_spec (exists_radon_of_testConverges L h)).2.2 f

lemma radonLimit_eq (L : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ))
    (μ : Measure X) [μ.Regular]
    (h : ∀ f : C_c(X, ℝ), Tendsto (fun j => L j f) atTop (𝓝 (∫ x, f x ∂μ))) :
    radonLimit L = μ := by
  have hr := radonLimit_regular L
  have hconv : TestConverges L := fun i => ⟨_, h (determiningTests i)⟩
  exact Measure.ext_of_integral_eq_on_compactlySupported
    (fun f => tendsto_nhds_unique (tendsto_radonLimit L hconv f) (h f))

lemma measurableSet_testConverges {Ω : Type*} [MeasurableSpace Ω]
    (L : Ω → ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ))
    (hL : ∀ j (f : C_c(X, ℝ)), Measurable (fun ω => L ω j f)) :
    MeasurableSet {ω | TestConverges (L ω)} := by
  simp only [TestConverges, ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_exists_tendsto
    (fun j => hL j (determiningTests i)))

 

theorem measurable_radonLimit {Ω : Type*} [MeasurableSpace Ω]
    (L : Ω → ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ))
    (hL : ∀ j (f : C_c(X, ℝ)), Measurable (fun ω => L ω j f)) :
    Measurable (fun ω => radonLimit (L ω)) := by
  classical
  have (ω : Ω) := radonLimit_finite (L ω)
  apply measurable_measure_of_compact_tests
  intro f
  let G := {ω | TestConverges (L ω)}
  have he : (fun ω => ∫ x, f x ∂radonLimit (L ω)) =
      G.piecewise (fun ω => limsup (fun j => L ω j f) atTop) (fun _ => 0) := by
    funext ω
    by_cases h : ω ∈ G
    · rw [piecewise_eq_of_mem G _ _ h]
      exact (tendsto_radonLimit (L ω) h f).limsup_eq.symm
    · simp [radonLimit, G] at h ⊢
      simp [h]
  rw [he]
  exact (Measurable.limsup (fun j => hL j f)).piecewise
    (measurableSet_testConverges L hL) measurable_const

 

theorem radonLimit_ae_eq {Ω : Type*} [MeasurableSpace Ω] (W : Measure Ω)
    {I : Type*} (L : I → Ω → ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ))
    (μ : I → Ω → Measure X) [∀ i ω, (μ i ω).Regular]
    (h : ∀ᵐ ω ∂W, ∀ i (f : C_c(X, ℝ)),
      Tendsto (fun j => L i ω j f) atTop (𝓝 (∫ x, f x ∂μ i ω))) :
    ∀ᵐ ω ∂W, ∀ i, radonLimit (L i ω) = μ i ω := by
  filter_upwards [h] with ω hω
  exact fun i => radonLimit_eq (L i ω) (μ i ω) (hω i)

end SLEExactGauge.MassVersions
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma level_step_le_one (a : ℝ) (ha : 1/4 < a) (j : ℕ) :
    Real.exp (-2*a*((j:ℝ)+1)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have ha0 : 0 < a := by linarith
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  nlinarith

 
noncomputable def actualMassFunctionals (a : ℝ) (ha : 1/4 < a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j ∈ s k → 0 ≤ c k j)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : ℕ → (C_c(UpperPlane, ℝ) →ₚ[ℝ] ℝ) :=
  fun k => positive_mass_combination
    (fun j => actualUpperMass a (Real.exp (-2*a*((j:ℝ)+1))) t b)
    (fun j => actualUpperMass_finiteOnCompacts a ha _ (Real.exp_pos _)
      (level_step_le_one a ha j) t b) (s k) (c k) (hc k)

lemma actualMassFunctionals_apply (a : ℝ) (ha : 1/4 < a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j ∈ s k → 0 ≤ c k j)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (k : ℕ) (f : C_c(UpperPlane, ℝ)) :
    actualMassFunctionals a ha s c hc t b k f =
      ∑ j ∈ s k, c k j * ∫ z, f z ∂actualUpperMass a (Real.exp (-2*a*((j:ℝ)+1))) t b :=
  positive_mass_combination_apply _ _ _ _ _ _

 

noncomputable def recoveredMass (a : ℝ) (ha : 1/4 < a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j ∈ s k → 0 ≤ c k j)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : Measure UpperPlane :=
  radonLimit (actualMassFunctionals a ha s c hc t b)

lemma recoveredMass_measurable (a : ℝ) (ha : 1/4 < a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j ∈ s k → 0 ≤ c k j)
    (t : ℝ≥0∞) : Measurable (recoveredMass a ha s c hc t) := by
  apply measurable_radonLimit
  intro k f
  simp_rw [actualMassFunctionals_apply]
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul (actualUpperMass_eval_measurable a ha _ (Real.exp_pos _)
    (level_step_le_one a ha j) t f)

lemma recoveredMass_raw_measurable (a : ℝ) (ha : 1/4 < a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j ∈ s k → 0 ≤ c k j)
    (t : ℝ≥0) : Measurable[rawFiltration t] (recoveredMass a ha s c hc t) := by
  apply @measurable_radonLimit _ _ _ _ _ _ _ _ (rawFiltration t)
  intro k f
  simp_rw [actualMassFunctionals_apply]
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul (actualUpperMass_eval_raw_measurable a ha _ (Real.exp_pos _)
    (level_step_le_one a ha j) t f)

 

theorem actual_radon_measurable_conditional (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
      (μ : ExactSLEGenerator.Driver → ℕ → Measure UpperPlane),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k j, j∈s k → 0≤coeff k j) ∧
      (∀ k, ∑ j∈s k, coeff k j=1) ∧
      (∀ b i, IsFiniteMeasureOnCompacts (μ b i) ∧ (μ b i).Regular) ∧
      (∀ i, Measurable (fun b => μ b i)) ∧
      (∀ i (t₀ : ℝ≥0), t i=t₀ → Measurable[rawFiltration t₀] (fun b => μ b i)) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ b i) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, coeff k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ b i) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → ∀ f : C_c(UpperPlane,ℝ),
        (∫b, (∫z,f z∂μ b i) ∂W) = ∫z : UpperPlane,
          f z * (Real.exp (-alpha a*Real.log 2)*physicalGreen a (z.1,0)) ∂upperArea) ∧
      (∀ i j (t₀ : ℝ≥0), t i=t₀ → t j=∞ → ∀ f : C_c(UpperPlane,ℝ),
        ∀ U : Set ExactSLEGenerator.Driver, MeasurableSet[rawFiltration t₀] U →
        (∫b in U, (∫z,f z∂μ b j)-(∫z,f z∂μ b i) ∂W) =
          ∫b in U, (∫z : UpperPlane,f z*survivingGreen a t₀ b z.1 ∂upperArea) ∂W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i ≤ t j → μ b i ≤ μ b j) ∧
        (∀ i (f : C_c(UpperPlane, ℝ)),
          Tendsto (fun k => ∑ j∈s k, coeff k j *
            ∫ z, f z ∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫ z, f z ∂μ b i))) := by
  obtain ⟨s,c,ν,hs,hc,hsum,hν,hmom,hL1,hmean,-,hcond,h⟩ :=
    actual_radon_compact_conditional a ha W hW t
  let μ := fun b i => recoveredMass a ha s c hc (t i) b
  have he : ∀ᵐ b ∂W, ∀ i, μ b i = ν b i := by
    filter_upwards [h] with b hb
    intro i
    have := (hν b i).2
    apply radonLimit_eq
    intro f
    simpa only [actualMassFunctionals_apply] using hb.2 i f
  have heI (i : ℕ) (f : C_c(UpperPlane, ℝ)) :
      (fun b => ∫z, f z∂μ b i) =ᵐ[W] (fun b => ∫z, f z∂ν b i) := by
    filter_upwards [he] with b hb
    rw [hb i]
  refine ⟨s,c,μ,hs,hc,hsum,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun b i => ⟨radonLimit_finite _, radonLimit_regular _⟩
  · exact fun i => recoveredMass_measurable a ha s c hc (t i)
  · intro i t₀ hi
    dsimp [μ]
    rw [hi]
    exact recoveredMass_raw_measurable a ha s c hc t₀
  · intro i f m
    exact ((memLp_congr_ae (heI i f)).mpr (hmom i f m))
  · intro i f
    have hnorm (k : ℕ) :
        eLpNorm (fun b => (∑ j∈s k, c k j *
          ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b) - ∫z,f z∂μ b i) 1 W =
        eLpNorm (fun b => (∑ j∈s k, c k j *
          ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b) - ∫z,f z∂ν b i) 1 W :=
      eLpNorm_congr_ae (EventuallyEq.sub (Filter.EventuallyEq.refl _ _) (heI i f))
    simpa only [hnorm] using hL1 i f
  · intro i hi f
    exact (integral_congr_ae (heI i f)).trans (hmean i hi f)
  · intro i j t₀ hi hj f U hU
    exact (integral_congr_ae (ae_restrict_of_ae ((heI j f).sub (heI i f)))).trans
      (hcond i j t₀ hi hj f U hU)
  · filter_upwards [he,h] with b hb hb'
    simpa only [hb] using hb'

end ExactSLEGreen
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 
lemma timeMassDensity_joint_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) :
    Measurable (fun p : (ℝ≥0∞ × ExactSLEGenerator.Driver) × ℂ =>
      timeMassDensity a q p.1.1 p.1.2 p.2) := by
  let U : Set ((ℝ≥0∞ × ExactSLEGenerator.Driver) × ℂ) := {p | 0<p.2.im}
  have hU : MeasurableSet U :=
    measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)
  have hm : Measurable (fun p : U => ENNReal.ofReal (Real.exp (-alpha a*Real.log 2)*
      (if radialTime a p.1.1.2.1 p.1.2 (p.1.2.im*q)≤p.1.1.1 then
        radialWeight a p.1.1.2.1 p.1.2 (p.1.2.im*q) else 0))) := by
    have hp : Measurable (fun p : U =>
        ((p.1.1.2, (⟨p.1.2,p.2⟩ : {z : ℂ // 0<z.im})),p.1.1.1)) := by fun_prop
    exact (measurable_const.mul
      ((joint_radial_approximant_measurable a ha q hq hq1).comp hp)).ennreal_ofReal
  have h := hm.dite (g:=fun _ => 0) measurable_const hU
  convert h using 1
  funext p
  have he : 2*p.2.im*q/2=p.2.im*q := by ring
  by_cases hz : 0<p.2.im <;>
    by_cases ht : radialTime a p.1.2.1 p.2 (p.2.im*q)≤p.1.1 <;>
    simp [timeMassDensity,massDensity,fullRadialDensity,U,hz,ht,he]

 

lemma timeMassDensity_raw_progressive_joint (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) (T : ℝ≥0) :
    letI : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration T
    Measurable (fun p : (Iic T × ExactSLEGenerator.Driver) × ℂ =>
      timeMassDensity a q p.1.1.1 p.1.2 p.2) := by
  have h := timeMassDensity_joint_measurable a ha q hq hq1
  have hb := pastDriver_raw_measurable T
  let mD : MeasurableSpace ExactSLEGenerator.Driver := inferInstance
  let : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration T
  have hp : @Measurable ((Iic T × ExactSLEGenerator.Driver) × ℂ)
      ((ℝ≥0∞ × ExactSLEGenerator.Driver) × ℂ) inferInstance
      ((ENNReal.measurableSpace.prod mD).prod (borel ℂ))
      (fun p => (((p.1.1.1 : ℝ≥0∞), pastDriver T p.1.2),p.2)) :=
    (((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).coe_nnreal_ennreal).prodMk
      (hb.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
  convert h.comp hp using 1
  funext p
  exact timeMassDensity_driver_congr a (by linarith) q hq hq1
    p.1.2 (pastDriver T p.1.2) p.1.1.1
    (fun s hs => (pastDriver_eq T p.1.2 s (hs.trans p.1.1.2)).symm) p.2

lemma actualMassEval_progressive (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) (K : Set ℂ) (f : ℂ → ℝ) (hf : Measurable f) :
    IsProgressive rawFiltration (fun t : ℝ≥0 => actualMassEval a q t K f) := by
  intro T
  have hD := timeMassDensity_raw_progressive_joint a ha q hq hq1 T
  let : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration T
  have hm : Measurable (fun p : (Iic T × ExactSLEGenerator.Driver) × ℂ =>
      f p.2*(timeMassDensity a q p.1.1.1 p.1.2 p.2).toReal) :=
    (hf.comp measurable_snd).mul hD.ennreal_toReal
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma actualUpperMass_eval_progressive (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) (f : C_c(UpperPlane,ℝ)) :
    IsProgressive rawFiltration
      (fun t : ℝ≥0 => fun b => ∫z, f z ∂actualUpperMass a q t b) := by
  simp_rw [actualUpperMass_eval a ha q hq hq1]
  exact actualMassEval_progressive a ha q hq hq1 _ _ (upperExtension_measurable f)

 

theorem recoveredMass_progressive (a : ℝ) (ha : 1/4 < a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j∈s k → 0≤c k j) :
    IsProgressive rawFiltration
      (fun t : ℝ≥0 => recoveredMass a ha s c hc t) := by
  intro T
  apply @measurable_radonLimit _ _ _ _ _ _ _ _
    (Subtype.instMeasurableSpace.prod (rawFiltration T))
  intro k f
  simp_rw [actualMassFunctionals_apply]
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul
    (actualUpperMass_eval_progressive a ha _ (Real.exp_pos _)
      (level_step_le_one a ha j) f T)

end ExactSLEGreen
end

end OAI
