import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.TracePastSupport
import OAI.Probability.SLEGauge.BrownianGerm

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 

theorem terminal_avoids_eternal_survival (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (μ : ℕ → Kernel ExactSLEGenerator.Driver UpperPlane)
    (ν : Kernel ExactSLEGenerator.Driver UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (ν b)]
    (hpast : ∀ᵐ b ∂W, ∀ n : ℕ, μ n b {z : UpperPlane | alive a b.1 n z.1}=0)
    (hkernel : ∀ n : ℕ, ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
      Measurable[(rawFiltration (n : ℝ≥0)).prod (inferInstance : MeasurableSpace UpperPlane)] H →
      (∫⁻b, ∫⁻z, H (b,z) ∂ν b ∂W) = (∫⁻b, ∫⁻z, H (b,z) ∂μ n b ∂W) +
        ∫⁻b, ∫⁻z, H (b,z)*ENNReal.ofReal (survivingGreen a n b z.1) ∂upperArea ∂W) :
    ∀ᵐ b ∂W, ν b {z : UpperPlane | ∀ n : ℕ, alive a b.1 n z.1}=0 := by
  have := isSFiniteKernel_of_locally_finite ν
  let U : ℕ → Set (ExactSLEGenerator.Driver × UpperPlane) :=
    fun n => {p | alive a p.1.1 n p.2.1}
  have hU (n : ℕ) :
      MeasurableSet[(rawFiltration (n : ℝ≥0)).prod (inferInstance : MeasurableSpace UpperPlane)]
        (U n) := by
    simpa only [compl_ofPred,not_not] using (deadSet_raw_measurable a ha n).compl
  have hU₀ (n : ℕ) : MeasurableSet (U n) := prod_sigma_le (rawFiltration.le n) _ _ (hU n)
  let D := ⋂ n, U n
  have hD : MeasurableSet D := MeasurableSet.iInter hU₀
  have hbound (K : Set UpperPlane) (hK : IsCompact K) (n : ℕ) :
      (∫⁻b, ν b ({z | (b,z)∈D}∩K) ∂W) ≤ ∫⁻b, ∫⁻z in K,
        ENNReal.ofReal (survivingGreen a n b z.1) ∂upperArea ∂W := by
    let E : Set (ExactSLEGenerator.Driver × UpperPlane) := U n ∩ Prod.snd ⁻¹' K
    have hE : MeasurableSet[(rawFiltration (n : ℝ≥0)).prod
        (inferInstance : MeasurableSpace UpperPlane)] E :=
      (hU n).inter (measurable_snd hK.measurableSet)
    have hE₀ : MeasurableSet E := prod_sigma_le (rawFiltration.le n) _ _ hE
    let H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞ := E.indicator (fun _ => 1)
    have hH : Measurable[(rawFiltration (n : ℝ≥0)).prod
        (inferInstance : MeasurableSpace UpperPlane)] H := measurable_const.indicator hE
    have hev (ρ : Measure UpperPlane) (b : ExactSLEGenerator.Driver) :
        (∫⁻z, H (b,z) ∂ρ) = ρ ({z | (b,z)∈U n}∩K) := by
      have hh := lintegral_indicator_const_comp (μ := ρ)
        ((measurable_const (a := b)).prodMk measurable_id) hE₀ (1 : ℝ≥0∞)
      have hs : (fun z : UpperPlane => (b,id z)) ⁻¹' E = {z | (b,z)∈U n}∩K := by
        ext z
        rfl
      rw [hs,one_mul] at hh
      exact hh
    have hzero : (∫⁻b, ∫⁻z, H (b,z) ∂μ n b ∂W)=0 := by
      have h : (fun b => ∫⁻z, H (b,z) ∂μ n b) =ᵐ[W] (fun _ => 0) := by
        filter_upwards [hpast] with b hb
        rw [hev]
        exact measure_mono_null inter_subset_left (hb n)
      rw [lintegral_congr_ae h,lintegral_zero]
    calc
      _ ≤ ∫⁻b, ∫⁻z, H (b,z) ∂ν b ∂W := by
        apply lintegral_mono
        intro b
        dsimp only
        rw [hev]
        exact measure_mono (inter_subset_inter_left K (fun z hz => mem_iInter.mp hz n))
      _ = ∫⁻b, ∫⁻z, H (b,z)*ENNReal.ofReal (survivingGreen a n b z.1) ∂upperArea ∂W := by
        rw [hkernel n H hH,hzero,zero_add]
      _ ≤ _ := by
        apply lintegral_mono
        intro b
        dsimp only
        rw [← lintegral_indicator hK.measurableSet]
        apply lintegral_mono
        intro z
        by_cases hz : z∈K
        · rw [indicator_of_mem hz]
          by_cases he : (b,z)∈E
          · simp only [H,indicator_of_mem he,one_mul,le_refl]
          · simp only [H,indicator_of_notMem he,zero_mul,zero_le]
        · have he : (b,z)∉E := fun he => hz he.2
          simp only [H,indicator_of_notMem he,indicator_of_notMem hz,zero_mul,le_refl]
  let K := CompactExhaustion.choice UpperPlane
  have hnull (k : ℕ) : ∀ᵐ b ∂W, ν b ({z | (b,z)∈D}∩K k)=0 := by
    apply (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left
      (hD.inter (measurable_snd (K.isCompact k).measurableSet)))).mp
    apply le_antisymm _ (bot_le)
    exact ge_of_tendsto' (survivingGreen_compact_mean_tendsto_zero a ha W hW (K k)
      (K.isCompact k)) (hbound (K k) (K.isCompact k))
  filter_upwards [ae_all_iff.mpr hnull] with b hb
  have he : (⋃ k, {z : UpperPlane | (b,z)∈D}∩K k) =
      {z : UpperPlane | ∀ n : ℕ, alive a b.1 n z.1} := by
    rw [← inter_iUnion,K.iUnion_eq,inter_univ]
    ext z
    simp only [D,U,mem_ofPred_eq,mem_iInter]
  rw [← he]
  exact measure_iUnion_null hb

end ExactSLEGreen
end
end
 

 
section
 
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.MassVersions

variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace X] [T2Space X] [BorelSpace X] in
lemma restriction_exhaustion (ν : Measure X) (D : ℕ → Set X)
    (hmono : Monotone D) (hnull : ν (⋃ n, D n)ᶜ=0) :
    ∀ A : Set X, MeasurableSet A →
      Tendsto (fun n => ν.restrict (D n) A) atTop (𝓝 (ν A)) := by
  have hfull : ν.restrict (⋃ n, D n)=ν :=
    Measure.restrict_eq_self_of_ae_mem (by
      simpa only [mem_compl_iff,not_not] using measure_eq_zero_iff_ae_notMem.mp hnull)
  intro A hA
  have hm : Monotone (fun n => A∩D n) :=
    fun i j hij => inter_subset_inter_right A (hmono hij)
  have ht := tendsto_measure_iUnion_atTop (μ := ν) hm
  have hset : (⋃ n, A∩D n)=A∩⋃ n, D n := by rw [inter_iUnion]
  simp only [Function.comp_def,hset,← Measure.restrict_apply hA,hfull] at ht
  exact ht

lemma locally_finite_sub_restrict_apply (ν : Measure X)
    [IsFiniteMeasureOnCompacts ν] (D : Set X) (hD : MeasurableSet D)
    (K : Set X) (hK : IsCompact K) :
    (ν-ν.restrict D) K=ν (K∩Dᶜ) := by
  let : IsFiniteMeasure (ν.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := ν)⟩
  have he : (ν-ν.restrict D).restrict K = ν.restrict K - (ν.restrict K).restrict D := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hK.measurableSet,
      Measure.restrict_comm hK.measurableSet]
  calc
    _ = (ν.restrict K - (ν.restrict K).restrict D) univ := by
      rw [← he,Measure.restrict_apply_univ]
    _ = ν K - ν (K∩D) := by
      rw [Measure.sub_apply MeasurableSet.univ Measure.restrict_le_self]
      simp only [Measure.restrict_apply_univ,Measure.restrict_apply hD,inter_comm]
    _ = ν (K∩Dᶜ) := by
      have hfin : ν (K∩D) ≠ ∞ := (measure_mono inter_subset_left |>.trans_lt hK.measure_lt_top).ne
      rw [← measure_inter_add_sdiff K hD,ENNReal.add_sub_cancel_left hfin]
      rfl

 

lemma remaining_restriction_tendsto_zero (ν : Measure X)
    [IsFiniteMeasureOnCompacts ν] (D : ℕ → Set X)
    (hD : ∀ n, MeasurableSet (D n)) (hmono : Monotone D)
    (hnull : ν (⋃ n, D n)ᶜ=0) :
    ∀ K : Set X, IsCompact K →
      Tendsto (fun n => (ν-ν.restrict (D n)) K) atTop (𝓝 0) := by
  intro K hK
  let U := fun n => K∩(D n)ᶜ
  have hU (n : ℕ) : MeasurableSet (U n) := hK.measurableSet.inter (hD n).compl
  have hm : Antitone U := fun i j hij => inter_subset_inter_right K (compl_subset_compl.mpr (hmono hij))
  have hf : ∃ n, ν (U n) ≠ ∞ := ⟨0,
    (measure_mono inter_subset_left |>.trans_lt hK.measure_lt_top).ne⟩
  have he : (⋂ n, U n)=K∩(⋃ n, D n)ᶜ := by
    ext x
    simp only [U,mem_iInter,mem_inter_iff,mem_compl_iff,mem_iUnion,not_exists,forall_and]
    simp only [forall_const]
  have hzero : ν (⋂ n, U n)=0 := by
    rw [he]
    exact measure_mono_null inter_subset_right hnull
  have ht := tendsto_measure_iInter_atTop (fun n => (hU n).nullMeasurableSet) hm hf
  simpa only [Function.comp_def,hzero,locally_finite_sub_restrict_apply ν _ (hD _) K hK]
    using ht

end SLEExactGauge.MassVersions
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 

theorem actual_raw_mass_exhaustion (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) (idx : ℕ → ℕ)
    (hidx : ∀ n : ℕ, t (idx n) = (n : ℝ≥0)) (j : ℕ) (hj : t j=∞) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
      (hc : ∀ k j, j∈s k → 0≤c k j),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k, ∑ j∈s k, c k j=1) ∧
      let μ := recoveredMass a ha s c hc
      (∀ v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀ b, μ 0 b=0) ∧
      (∀ v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ (t i) b) (m : ℝ≥0∞) W) ∧
      (∀ i (K : Set UpperPlane), IsCompact K → ∀ m : ℕ,
        MemLp (fun b => (μ (t i) b K).toReal) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, c k j * ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ (t i) b) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → μ (t i) ∘ₘ W=initialGreenMeasure a) ∧
      (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
        ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
        Measurable[(rawFiltration v).prod (inferInstance : MeasurableSpace UpperPlane)] H →
        (∫⁻b, ∫⁻z, H (b,z) ∂μ (t j) b ∂W) = (∫⁻b, ∫⁻z, H (b,z) ∂μ (t i) b ∂W) +
          ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen a v b z.1) ∂upperArea ∂W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i≤t j → μ (t i) b≤μ (t j) b) ∧
        (∀ i (f : C_c(UpperPlane,ℝ)),
          Tendsto (fun k => ∑ j∈s k, c k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫z,f z∂μ (t i) b))) ∧
        (∀ i, NullSingletonClass (μ (t i) b)) ∧
        (∀ i (v : ℝ≥0), t i=v → μ (t i) b {z : UpperPlane | alive a b.1 v z.1}=0) ∧
        (∀ i j, t i≠∞ → t j=∞ →
          (μ (t j) b-μ (t i) b) {z : UpperPlane | ¬alive a b.1 (t i).toNNReal z.1}=0) ∧
        (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
          μ (t i) b=(μ (t j) b).restrict {z : UpperPlane | ¬alive a b.1 v z.1}) ∧
        μ ∞ b {z : UpperPlane | ∀ n : ℕ, alive a b.1 n z.1}=0 ∧
        (∀ A : Set UpperPlane, MeasurableSet A →
          Tendsto (fun n : ℕ => μ (n : ℝ≥0) b A) atTop (𝓝 (μ ∞ b A))) ∧
        (∀ K : Set UpperPlane, IsCompact K →
          Tendsto (fun n : ℕ => (μ ∞ b-μ (n : ℝ≥0) b) K) atTop (𝓝 0)) := by
  obtain ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,hconv⟩ :=
    actual_raw_mass_hull_accounting a ha W hW t
  let μ := recoveredMass a ha s c hc
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ v b) := (hμ v b).1
  let ν : Kernel ExactSLEGenerator.Driver UpperPlane := ⟨μ ∞,hmeas ∞⟩
  let θ : ℕ → Kernel ExactSLEGenerator.Driver UpperPlane :=
    fun n => ⟨μ (n : ℝ≥0),hmeas (n : ℝ≥0)⟩
  have (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (ν b) := hμ ∞ b |>.1
  have hpast : ∀ᵐ b ∂W, ∀ n : ℕ, θ n b {z : UpperPlane | alive a b.1 n z.1}=0 := by
    filter_upwards [hconv] with b hb
    intro n
    have h := hb.2.2.2.1 (idx n) n (hidx n)
    simpa only [hidx n,θ,ν,Kernel.coe_mk,μ] using h
  have he : ∀ n : ℕ, ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
      Measurable[(rawFiltration (n : ℝ≥0)).prod (inferInstance : MeasurableSpace UpperPlane)] H →
      (∫⁻b, ∫⁻z, H (b,z) ∂ν b ∂W) = (∫⁻b, ∫⁻z, H (b,z) ∂θ n b ∂W) +
        ∫⁻b, ∫⁻z, H (b,z)*ENNReal.ofReal (survivingGreen a n b z.1) ∂upperArea ∂W := by
    intro n H hH₀
    simpa only [hidx n,hj,θ,ν,Kernel.coe_mk,μ] using hH (idx n) j n (hidx n) hj H hH₀
  have havoid := terminal_avoids_eternal_survival a ha W hW θ ν hpast he
  refine ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,?_⟩
  filter_upwards [hconv,havoid] with b hb hbavoid
  rcases hb with ⟨horder,hvague,hatom,hpast,hfuture,hrestrict⟩
  let D : ℕ → Set UpperPlane := fun n => {z | ¬alive a b.1 n z.1}
  have hD (n : ℕ) : MeasurableSet (D n) :=
    ((isOpen_alive b.1.continuous n).preimage
      (continuous_subtype_val : Continuous (Subtype.val : UpperPlane → ℂ))).measurableSet.compl
  have hm : Monotone D := by
    intro n m hnm z hz hn
    exact hz (alive_mono hn (Nat.cast_le.mpr hnm))
  have hnull : μ ∞ b (⋃ n, D n)ᶜ=0 := by
    have hset : (⋃ n, D n)ᶜ={z : UpperPlane | ∀ n : ℕ, alive a b.1 n z.1} := by
      ext z
      simp only [D,mem_compl_iff,mem_iUnion,mem_ofPred_eq,not_exists,not_not]
    rw [hset]
    exact hbavoid
  have hr (n : ℕ) : μ (n : ℝ≥0) b=(μ ∞ b).restrict (D n) := by
    simpa only [hidx n,hj] using hrestrict (idx n) j n (hidx n) hj
  refine ⟨horder,hvague,hatom,hpast,hfuture,hrestrict,hbavoid,?_,?_⟩
  · change ∀ A : Set UpperPlane, MeasurableSet A →
      Tendsto (fun n : ℕ => μ (n : ℝ≥0) b A) atTop (𝓝 (μ ∞ b A))
    simp only [hr]
    exact restriction_exhaustion (μ ∞ b) D hm hnull
  · change ∀ K : Set UpperPlane, IsCompact K →
      Tendsto (fun n : ℕ => (μ ∞ b-μ (n : ℝ≥0) b) K) atTop (𝓝 0)
    simp only [hr]
    exact remaining_restriction_tendsto_zero (μ ∞ b) D hD hm hnull

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions
open SLEExactGauge.LoewnerScaling SLEExactGauge.GermPositivity

lemma upperArea_univ_pos : 0<upperArea univ := by
  rw [upperArea,upper_embedding.comap_apply,image_univ,Subtype.range_val_subtype]
  exact upperPlane_open.measure_pos volume ⟨Complex.I,by simp⟩

lemma initialGreenMeasure_univ_pos (a : ℝ) : 0 < initialGreenMeasure a univ := by
  rw [initialGreenMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [lintegral_pos_iff_support (initialGreen_continuous a).measurable.ennreal_ofReal]
  have he : Function.support (fun z : UpperPlane => ENNReal.ofReal (initialGreen a z))=univ := by
    ext z
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (ENNReal.ofReal_pos.mpr (initialGreen_pos a z)).ne'
  rw [he]
  exact upperArea_univ_pos

 

lemma positive_probability_of_exhaustion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : ℝ≥0∞ → Ω → Measure X)
    (hm : Measurable (μ ∞)) (hz : ∀ ω, μ 0 ω=0)
    (hmean : 0<(μ ∞ ∘ₘ P) univ)
    (hex : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => μ (n : ℝ≥0) ω univ)
      atTop (𝓝 (μ ∞ ω univ))) :
    ∃ n : ℕ, 0<n ∧ 0<P {ω | 0<μ (n : ℝ≥0) ω univ} := by
  by_contra! h
  have hzero (n : ℕ) : ∀ᵐ ω ∂P, μ (n : ℝ≥0) ω univ=0 := by
    by_cases hn : n=0
    · subst n
      exact Eventually.of_forall (fun ω => by simp only [Nat.cast_zero,ENNReal.coe_zero,hz]; rfl)
    · rw [ae_iff]
      simpa only [pos_iff_ne_zero] using le_antisymm (h n (Nat.pos_of_ne_zero hn)) bot_le
  have hzTerminal : ∀ᵐ ω ∂P, μ ∞ ω univ=0 := by
    filter_upwards [ae_all_iff.mpr hzero,hex] with ω hω he
    have hh : Tendsto (fun n : ℕ => μ (n : ℝ≥0) ω univ) atTop (𝓝 0) := by
      simpa only [hω] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
    exact tendsto_nhds_unique he hh
  have hzmean : (μ ∞ ∘ₘ P) univ=0 := by
    rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
    rw [lintegral_congr_ae hzTerminal,lintegral_zero]
  exact hmean.ne' hzmean

 

lemma recoveredMass_ae_smallTime_positive (a : ℝ) (ha : 1/4<a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j∈s k → 0≤c k j)
    (W : Measure ExactSLEGenerator.Driver)
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (hmean : recoveredMass a ha s c hc ∞ ∘ₘ W=initialGreenMeasure a)
    (hex : ∀ᵐ b ∂W, Tendsto
      (fun n : ℕ => recoveredMass a ha s c hc (n : ℝ≥0) b univ)
      atTop (𝓝 (recoveredMass a ha s c hc ∞ b univ)))
    (hanti : ∀ᵐ b ∂W, Antitone (fun n => recoveredMass a ha s c hc (smallTime n) b univ)) :
    ∀ᵐ b ∂W, ∀ n : ℕ, 0<recoveredMass a ha s c hc (smallTime n) b univ := by
  let μ := recoveredMass a ha s c hc
  obtain ⟨u,hu,hp⟩ := positive_probability_of_exhaustion W μ
    (recoveredMass_measurable a ha s c hc ∞) (recoveredMass_zero a ha s c hc)
    (by rw [hmean]; exact initialGreenMeasure_univ_pos a) hex
  let E (n : ℕ) : Set ExactSLEGenerator.Driver := {b | 0<μ (smallTime n) b univ}
  have hE (n : ℕ) : MeasurableSet[rawFiltration (smallTime n)] (E n) :=
    measurableSet_lt measurable_const ((Measure.measurable_coe MeasurableSet.univ).comp
      (recoveredMass_raw_measurable a ha s c hc (smallTime n)))
  have heAnti : ∀ᵐ b ∂W, Antitone (fun n => b∈E n) := by
    filter_upwards [hanti] with b hb n m hnm hmem
    exact hmem.trans_le (hb hnm)
  have hlower (n : ℕ) : W {b | 0<μ (u : ℝ≥0) b univ}≤W (E n) := by
    exact (recoveredMass_positivity_probability a ha s c hc W hW
      (u : ℝ≥0) (smallTime n) (Nat.cast_pos.mpr hu) (smallTime_pos n)).le
  exact ae_all_mem (fun t (b : ExactSLEGenerator.Driver) => b.1 t)
    driver_eval_measurable (fun b => b.1.continuous) (fun b => b.2)
    W hW.toIsPreBrownianReal smallTime tendsto_smallTime E hE heAnti hp hlower

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions
open SLEExactGauge.GermPositivity

theorem actual_raw_mass_positive (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) (idx : ℕ → ℕ)
    (hidx : ∀ n : ℕ, t (idx n) = (n : ℝ≥0))
    (is : ℕ → ℕ) (his : ∀ n : ℕ, t (is n)=(smallTime n : ℝ≥0∞))
    (j : ℕ) (hj : t j=∞) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
      (hc : ∀ k j, j∈s k → 0≤c k j),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k, ∑ j∈s k, c k j=1) ∧
      let μ := recoveredMass a ha s c hc
      (∀ v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀ b, μ 0 b=0) ∧
      (∀ v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ (t i) b) (m : ℝ≥0∞) W) ∧
      (∀ i (K : Set UpperPlane), IsCompact K → ∀ m : ℕ,
        MemLp (fun b => (μ (t i) b K).toReal) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, c k j * ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ (t i) b) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → μ (t i) ∘ₘ W=initialGreenMeasure a) ∧
      (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
        ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
        Measurable[(rawFiltration v).prod (inferInstance : MeasurableSpace UpperPlane)] H →
        (∫⁻b, ∫⁻z, H (b,z) ∂μ (t j) b ∂W) = (∫⁻b, ∫⁻z, H (b,z) ∂μ (t i) b ∂W) +
          ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen a v b z.1) ∂upperArea ∂W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i≤t j → μ (t i) b≤μ (t j) b) ∧
        (∀ i (f : C_c(UpperPlane,ℝ)),
          Tendsto (fun k => ∑ j∈s k, c k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫z,f z∂μ (t i) b))) ∧
        (∀ i, NullSingletonClass (μ (t i) b)) ∧
        (∀ i (v : ℝ≥0), t i=v → μ (t i) b {z : UpperPlane | alive a b.1 v z.1}=0) ∧
        (∀ i j, t i≠∞ → t j=∞ →
          (μ (t j) b-μ (t i) b) {z : UpperPlane | ¬alive a b.1 (t i).toNNReal z.1}=0) ∧
        (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
          μ (t i) b=(μ (t j) b).restrict {z : UpperPlane | ¬alive a b.1 v z.1}) ∧
        μ ∞ b {z : UpperPlane | ∀ n : ℕ, alive a b.1 n z.1}=0 ∧
        (∀ A : Set UpperPlane, MeasurableSet A →
          Tendsto (fun n : ℕ => μ (n : ℝ≥0) b A) atTop (𝓝 (μ ∞ b A))) ∧
        (∀ K : Set UpperPlane, IsCompact K →
          Tendsto (fun n : ℕ => (μ ∞ b-μ (n : ℝ≥0) b) K) atTop (𝓝 0)) ∧
        (∀ i, 0<t i → 0<μ (t i) b univ) ∧
        (∀ i, 0<t i → ∃ K : Set UpperPlane, IsCompact K ∧
          0<μ (t i) b K ∧ μ (t i) b K<∞) := by
  obtain ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,hconv⟩ :=
    actual_raw_mass_exhaustion a ha W hW t idx hidx j hj
  let μ := recoveredMass a ha s c hc
  have hanti : ∀ᵐ b ∂W, Antitone (fun n => μ (smallTime n) b univ) := by
    filter_upwards [hconv] with b hb n m hnm
    have ht : t (is m)≤t (is n) := by
      rw [his,his]
      exact_mod_cast smallTime_antitone hnm
    have hh := hb.1 (is m) (is n) ht
    rw [his,his] at hh
    exact Measure.le_iff'.mp hh univ
  have hex : ∀ᵐ b ∂W, Tendsto (fun n : ℕ => μ (n : ℝ≥0) b univ)
      atTop (𝓝 (μ ∞ b univ)) := by
    filter_upwards [hconv] with b hb
    exact hb.2.2.2.2.2.2.2.1 univ MeasurableSet.univ
  have hmean' : μ ∞ ∘ₘ W=initialGreenMeasure a := by
    simpa only [hj] using hmean j hj
  have hpos := recoveredMass_ae_smallTime_positive a ha s c hc W hW hmean' hex hanti
  refine ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,?_⟩
  filter_upwards [hconv,hpos] with b hb hpb
  have hpositive (i : ℕ) (hi : 0<t i) : 0<μ (t i) b univ := by
    have hlim : Tendsto (fun n => (smallTime n : ℝ≥0∞)) atTop (𝓝 0) :=
      ENNReal.continuous_coe.tendsto 0 |>.comp tendsto_smallTime
    obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hi)).exists
    have hh := hb.1 (is n) i (by simpa only [his] using hn.le)
    rw [his] at hh
    exact (hpb n).trans_le (Measure.le_iff'.mp hh univ)
  rcases hb with ⟨ho,hv,hat,hpa,hfu,hr,he,hx,hk⟩
  refine ⟨ho,hv,hat,hpa,hfu,hr,he,hx,hk,hpositive,?_⟩
  intro i hi
  let : (μ (t i) b).Regular := (hμ _ _).2
  let : IsFiniteMeasureOnCompacts (μ (t i) b) := (hμ _ _).1
  obtain ⟨K,-,hK,hpK⟩ := isOpen_univ.exists_lt_isCompact (hpositive i hi)
  exact ⟨K,hK,hpK,hK.measure_lt_top⟩

end ExactSLEGreen
end
end

end OAI
