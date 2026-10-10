import Mathlib
import OAI.Probability.JammingConcavity.CascadeGenealogyBase

namespace OAI

/-! Stable Law Scaling. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma coloredStable_scaled_identDistrib {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {Y Y₀ : A → ℝ≥0} (hY : Measurable Y) (hY₀ : Measurable Y₀)
    (hi : Integrable (fun a => (Y a:ℝ)^m) ν) (hi₀ : Integrable (fun a => (Y₀ a:ℝ)^m) ν)
    (hp : 0 < ∫ a, (Y a:ℝ)^m ∂ν) (hp₀ : 0 < ∫ a, (Y₀ a:ℝ)^m ∂ν)
    {r : ℝ} (hM : (∫ a, (Y a:ℝ)^m ∂ν) = Real.exp (m*r)*(∫ a, (Y₀ a:ℝ)^m ∂ν)) :
    IdentDistrib (coloredStableSum m Y)
      (fun ω => ENNReal.ofReal (Real.exp r)*coloredStableSum m Y₀ ω)
      (pointCloudLaw ν) (pointCloudLaw ν) := by
  have hX := measurable_coloredStableSum m hY
  have hS := measurable_coloredStableSum m hY₀
  have hZ : Measurable (fun ω => ENNReal.ofReal (Real.exp r)*coloredStableSum m Y₀ ω) :=
    measurable_const.mul hS
  refine ⟨hX.aemeasurable, hZ.aemeasurable, ?_⟩
  apply law_eq_of_real_laplace _ _ hX hZ
  · exact ((coloredStable_properties ν hm hm1 hY hi hp).1).mono (fun _ h => h.2.ne)
  · filter_upwards [(coloredStable_properties ν hm hm1 hY₀ hi₀ hp₀).1] with ω hω
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.2.ne
  · intro t ht
    have he (ω : PointCloud A) :
        Real.exp (-t*(ENNReal.ofReal (Real.exp r)*coloredStableSum m Y₀ ω).toReal) =
          Real.exp (-(t*Real.exp r)*(coloredStableSum m Y₀ ω).toReal) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      congr 1; ring
    simp_rw [he]
    rw [coloredStable_laplace ν hm hm1 hY hi hp ht,
      coloredStable_laplace ν hm hm1 hY₀ hi₀ hp₀ (mul_nonneg ht (Real.exp_pos _).le),
      Real.mul_rpow ht (Real.exp_pos _).le, ← Real.exp_mul, hM]
    rw [mul_comm r m]
    congr 1; ring
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def extendedStableSum {A : Type*} (m : ℝ) (F : A → ℝ≥0∞) : PointCloud A → ℝ≥0∞ :=
  pointCloudFunctional (fun z => ENNReal.ofReal (z.1^(-1/m))*F z.2)

lemma measurable_extendedStableSum {A : Type*} [MeasurableSpace A] (m : ℝ)
    {F : A → ℝ≥0∞} (hF : Measurable F) : Measurable (extendedStableSum m F) := by
  apply measurable_pointCloudFunctional
  exact (by fun_prop : Measurable (fun z : ℝ × A => ENNReal.ofReal (z.1^(-1/m)))).mul
    (hF.comp measurable_snd)

lemma extendedStableSum_colored {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (m : ℝ) {F : A → ℝ≥0∞}
    (hfin : ∀ᵐ a ∂ν, F a < ∞) : extendedStableSum m F =ᵐ[pointCloudLaw ν]
      coloredStableSum m (fun a => (F a).toNNReal) := by
  apply pointCloudFunctional_mark_congr ν
  filter_upwards [hfin] with a ha
  intro x
  rw [ENNReal.ofReal_mul' (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_toNNReal ha.ne]

lemma extendedStable_scaled_identDistrib {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {F G : A → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (hf : ∀ᵐ a ∂ν, F a < ∞) (hg : ∀ᵐ a ∂ν, G a < ∞)
    (hi : Integrable (fun a => (F a).toReal^m) ν)
    (hi₀ : Integrable (fun a => (G a).toReal^m) ν)
    (hp : 0 < ∫ a, (F a).toReal^m ∂ν) (hp₀ : 0 < ∫ a, (G a).toReal^m ∂ν)
    {r : ℝ} (hM : (∫ a, (F a).toReal^m ∂ν) = Real.exp (m*r)*(∫ a, (G a).toReal^m ∂ν)) :
    IdentDistrib (extendedStableSum m F) (fun ω => ENNReal.ofReal (Real.exp r)*extendedStableSum m G ω)
      (pointCloudLaw ν) (pointCloudLaw ν) := by
  have heF := IdentDistrib.of_ae_eq (measurable_extendedStableSum m hF).aemeasurable
    (extendedStableSum_colored ν m hf)
  have heG := IdentDistrib.of_ae_eq (measurable_extendedStableSum m hG).aemeasurable
    (extendedStableSum_colored ν m hg)
  have hs := coloredStable_scaled_identDistrib ν hm hm1 hF.ennreal_toNNReal hG.ennreal_toNNReal
    hi hi₀ hp hp₀ hM
  exact heF.trans (hs.trans (heG.symm.comp (measurable_const.mul measurable_id)))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma scaledENN_rpow (r p : ℝ) (x : ℝ≥0∞) :
    (ENNReal.ofReal (Real.exp r)*x).toReal^p = Real.exp (p*r)*x.toReal^p := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.mul_rpow (Real.exp_pos _).le ENNReal.toReal_nonneg, ← Real.exp_mul]
  rw [mul_comm r p]

lemma scaledENN_log {r : ℝ} {x : ℝ≥0∞} (hx : 0 < x) (hf : x < ∞) :
    Real.log (ENNReal.ofReal (Real.exp r)*x).toReal = r+Real.log x.toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul (Real.exp_ne_zero _) (ENNReal.toReal_pos hx.ne' hf.ne).ne', Real.log_exp]

lemma scaledLaw_rpow {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {X S : A → ℝ≥0∞} {r p : ℝ}
    (h : IdentDistrib X (fun a => ENNReal.ofReal (Real.exp r)*S a) μ μ)
    (hi : Integrable (fun a => (S a).toReal^p) μ) :
    Integrable (fun a => (X a).toReal^p) μ ∧
      (∫ a, (X a).toReal^p ∂μ) = Real.exp (p*r)*(∫ a, (S a).toReal^p ∂μ) := by
  have hd := h.comp (by fun_prop : Measurable (fun x : ℝ≥0∞ => x.toReal^p))
  have hie : Integrable (fun a => (ENNReal.ofReal (Real.exp r)*S a).toReal^p) μ := by
    simpa only [scaledENN_rpow] using hi.const_mul (Real.exp (p*r))
  refine ⟨hd.integrable_iff.mpr hie, ?_⟩
  have hv := hd.integral_eq
  simpa only [Function.comp_def, scaledENN_rpow, integral_const_mul] using hv

lemma scaledLaw_positive {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {X S : A → ℝ≥0∞} {r : ℝ}
    (h : IdentDistrib X (fun a => ENNReal.ofReal (Real.exp r)*S a) μ μ)
    (hs : ∀ᵐ a ∂μ, 0 < S a ∧ S a < ∞) : ∀ᵐ a ∂μ, 0 < X a ∧ X a < ∞ := by
  have he : ∀ᵐ a ∂μ, ENNReal.ofReal (Real.exp r)*S a ∈ Set.Ioo 0 ∞ := by
    filter_upwards [hs] with a ha
    exact ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ha.1.ne',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ha.2⟩
  exact h.symm.ae_mem_snd measurableSet_Ioo he

lemma scaledLaw_centered_log {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {X S : A → ℝ≥0∞} {r : ℝ}
    (h : IdentDistrib X (fun a => ENNReal.ofReal (Real.exp r)*S a) μ μ)
    (hs : ∀ᵐ a ∂μ, 0 < S a ∧ S a < ∞) :
    IdentDistrib (fun a => Real.log (X a).toReal-r) (fun a => Real.log (S a).toReal) μ μ := by
  have hd := h.comp (by fun_prop : Measurable (fun x : ℝ≥0∞ => Real.log x.toReal-r))
  have he : (fun a => Real.log (ENNReal.ofReal (Real.exp r)*S a).toReal-r) =ᵐ[μ]
      (fun a => Real.log (S a).toReal) := by
    filter_upwards [hs] with a ha
    rw [scaledENN_log ha.1 ha.2]; ring
  exact hd.trans (IdentDistrib.of_ae_eq hd.aemeasurable_snd he)
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma integral_pos_of_positive_ae {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [IsProbabilityMeasure μ] {f : A → ℝ} (hi : Integrable f μ) (hp : ∀ᵐ a ∂μ, 0 < f a) :
    0 < ∫ a, f a ∂μ := by
  have hn := integral_nonneg_of_ae (hp.mono (fun _ h => h.le))
  apply lt_of_le_of_ne hn
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae (hp.mono (fun _ h => h.le)) hi).mp he.symm
  obtain ⟨a,ha,hz'⟩ := (hp.and hz).exists
  exact ha.ne' hz'

lemma scaled_family_rpow {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ≥0∞} {S : B → ℝ≥0∞} {r : A → ℝ} {p : ℝ}
    (hF : Measurable F)
    (h : ∀ a, IdentDistrib (fun b => F (a,b)) (fun b => ENNReal.ofReal (Real.exp (r a))*S b) ν ν)
    (hiS : Integrable (fun b => (S b).toReal^p) ν)
    (hir : Integrable (fun a => Real.exp (p*r a)) μ) :
    Integrable (fun z => (F z).toReal^p) (μ.prod ν) ∧
      (∫ z, (F z).toReal^p ∂μ.prod ν) =
        (∫ a, Real.exp (p*r a) ∂μ)*(∫ b, (S b).toReal^p ∂ν) := by
  have hk (a : A) := scaledLaw_rpow ν (h a) hiS
  have hm : Measurable (fun z => (F z).toReal^p) := by fun_prop
  have hn (a : A) : (∫ b, ‖(F (a,b)).toReal^p‖ ∂ν) =
      Real.exp (p*r a)*(∫ b, (S b).toReal^p ∂ν) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg p)]
      using (hk a).2
  have hi : Integrable (fun z => (F z).toReal^p) (μ.prod ν) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun a => (hk a).1), ?_⟩
    simp_rw [hn]
    exact hir.mul_const _
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  simp_rw [(fun a => (hk a).2)]
  exact integral_mul_const _ _
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
variable {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]

lemma familyLeafTotal_identDistrib (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (ν : ℕ → Measure E)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) {u : E → ℝ} (hu : Measurable u)
    (hfin : FamilyMomentsFinite ms ν u) (x : E) :
    IdentDistrib (familyLeafTotal ms u x)
      (fun ω => ENNReal.ofReal (Real.exp (familyRecursion ms ν u x))*familyUnmarkedTotal ms ω)
      (familyCascadeLaw ms.length ν) (familyCascadeLaw ms.length ν) := by
  induction ms generalizing ν x with
  | nil =>
    change IdentDistrib (fun _ : Unit => ENNReal.ofReal (Real.exp (u x)))
      (fun _ : Unit => ENNReal.ofReal (Real.exp (u x))*1) (Measure.dirac ()) (Measure.dirac ())
    simp only [mul_one]
    exact IdentDistrib.refl measurable_const.aemeasurable
  | cons m ms ih =>
    obtain ⟨hm,hm1⟩ := h01 m (List.mem_cons_self)
    have hs := List.pairwise_cons.mp hms
    have h01t := fun a ha => h01 a (List.mem_cons_of_mem m ha)
    let η := familyCascadeLaw ms.length (fun j => ν (j+1))
    let := hν 0
    let := familyCascadeLaw_probability ms.length (fun j => ν (j+1)) (fun j => hν (j+1))
    have hη : IsProbabilityMeasure η := inferInstance
    let := hη
    have ht := familyUnmarkedTotal_properties ms hs.2 h01t (fun j => ν (j+1)) (fun j => hν (j+1))
    have hiS : Integrable (fun ω => (familyUnmarkedTotal ms ω).toReal^m) η := ht.2.1 m hm hs.1
    have hpS : 0 < ∫ ω, (familyUnmarkedTotal ms ω).toReal^m ∂η :=
      integral_pos_of_positive_ae η hiS (ht.1.mono (fun _ h =>
        Real.rpow_pos_of_pos (ENNReal.toReal_pos h.1.ne' h.2.ne) _))
    let F : E × FamilyCascadeTree E ms.length → ℝ≥0∞ :=
      fun z => familyLeafTotal ms u (x+z.1) z.2
    let G : E × FamilyCascadeTree E ms.length → ℝ≥0∞ := fun z => familyUnmarkedTotal ms z.2
    have hF : Measurable F := (measurable_familyLeafTotal ms hu).comp
      (show Measurable (fun z : E × FamilyCascadeTree E ms.length => (x+z.1,z.2)) by fun_prop)
    have hG : Measurable G := (measurable_familyUnmarkedTotal ms).comp measurable_snd
    have hl (a : E) : IdentDistrib (fun ω => F (a,ω)) (fun ω =>
        ENNReal.ofReal (Real.exp (familyRecursion ms (fun j => ν (j+1)) u (x+a)))*
          familyUnmarkedTotal ms ω) η η :=
      ih hs.2 h01t (fun j => ν (j+1)) (fun j => hν (j+1)) hfin.2 (x+a)
    have hfp : ∀ᵐ z ∂(ν 0).prod η, F z < ∞ := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hF measurable_const)).mpr
      exact Eventually.of_forall (fun a => (scaledLaw_positive η (hl a) ht.1).mono (fun _ h => h.2))
    have hgp : ∀ᵐ z ∂(ν 0).prod η, G z < ∞ := by
      exact (measurePreserving_snd (μ := ν 0) (ν := η)).quasiMeasurePreserving.ae
        (ht.1.mono (fun _ h => h.2))
    have hiG : Integrable (fun z => (G z).toReal^m) ((ν 0).prod η) := hiS.comp_snd _
    have hGs : (∫ z, (G z).toReal^m ∂(ν 0).prod η) =
        ∫ ω, (familyUnmarkedTotal ms ω).toReal^m ∂η := by
      simpa only [probReal_univ, one_smul] using
        (integral_fun_snd (μ := ν 0) (ν := η) (fun ω => (familyUnmarkedTotal ms ω).toReal^m))
    have hk := scaled_family_rpow (ν 0) η hF hl hiS (hfin.1 x)
    have hpE := integral_exp_pos (hfin.1 x)
    have hpF : 0 < ∫ z, (F z).toReal^m ∂(ν 0).prod η := by rw [hk.2]; exact mul_pos hpE hpS
    have hpG : 0 < ∫ z, (G z).toReal^m ∂(ν 0).prod η := by rwa [hGs]
    have hr : Real.exp (m*familyRecursion (m::ms) ν u x) =
        ∫ a, Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a)) ∂ν 0 := by
      have he : m*(1/m) = 1 := by field_simp
      rw [familyRecursion, ← mul_assoc, he, one_mul, Real.exp_log hpE]
    have hM : (∫ z, (F z).toReal^m ∂(ν 0).prod η) =
        Real.exp (m*familyRecursion (m::ms) ν u x)*(∫ z, (G z).toReal^m ∂(ν 0).prod η) := by
      rw [hk.2, hr, hGs]
    have hz := extendedStable_scaled_identDistrib ((ν 0).prod η) hm hm1 hF hG hfp hgp hk.1 hiG hpF hpG hM
    exact hz
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma familyLeafTotal_zero {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (x : E) (ω : FamilyCascadeTree E ms.length) :
    familyLeafTotal ms (fun _ => 0) x ω = familyUnmarkedTotal ms ω := by
  induction ms generalizing x with
  | nil => simp [familyLeafTotal, familyUnmarkedTotal, cascadeTotal]
  | cons m ms ih =>
    rw [familyLeafTotal, familyUnmarkedTotal_cons]
    congr 1
    funext z
    rw [ih]

theorem familyCascadeLog : FamilyCascadeLogStatement := by
  intro E _ _ _ ms hms h01 ν hν u hu hfin x
  let μ := familyCascadeLaw ms.length ν
  let := familyCascadeLaw_probability ms.length ν hν
  have hμ : IsProbabilityMeasure μ := inferInstance
  let := hμ
  have hp := familyUnmarkedTotal_properties ms hms h01 ν hν
  have hd := familyLeafTotal_identDistrib ms hms h01 ν hν hu hfin x
  have hpos := scaledLaw_positive μ hd hp.1
  have hc := scaledLaw_centered_log μ hd hp.1
  have hS := measurable_familyUnmarkedTotal (E := E) ms
  have hC : Measurable (fun ω => Real.log (familyLeafTotal ms u x ω).toReal-familyRecursion ms ν u x) := by
    exact (Real.measurable_log.comp ((measurable_familyLeafTotal ms hu).comp
      (measurable_const.prodMk measurable_id)).ennreal_toReal).sub measurable_const
  have hic : Integrable (fun ω => (Real.log (familyLeafTotal ms u x ω).toReal-familyRecursion ms ν u x)^2) μ := by
    have hsq : Integrable (fun ω => (Real.log (familyUnmarkedTotal ms ω).toReal)^2) μ := by
      simpa only [sq_abs] using hp.2.2
    exact (hc.comp (by fun_prop : Measurable (fun z : ℝ => z^2))).integrable_iff.mpr hsq
  have hc2 := (memLp_two_iff_integrable_sq hC.aestronglyMeasurable).mpr hic
  have hf2 : MemLp (fun ω => Real.log (familyLeafTotal ms u x ω).toReal) 2 μ := by
    have hh := hc2.add (memLp_const (familyRecursion ms ν u x))
    change MemLp (fun ω => (Real.log (familyLeafTotal ms u x ω).toReal-familyRecursion ms ν u x)+familyRecursion ms ν u x) 2 μ at hh
    simpa only [Pi.add_apply, sub_add_cancel] using hh
  have hiS := integrable_log_of_square μ hS hp.2.2
  have hiC := hc.integrable_iff.mpr hiS
  have hiF : Integrable (fun ω => Real.log (familyLeafTotal ms u x ω).toReal) μ := by
    have hh := hiC.add (integrable_const (familyRecursion ms ν u x))
    change Integrable (fun ω => (Real.log (familyLeafTotal ms u x ω).toReal-familyRecursion ms ν u x)+familyRecursion ms ν u x) μ at hh
    simpa only [Pi.add_apply, sub_add_cancel] using hh
  have he : familyLogPartition ms u x =ᵐ[μ]
      (fun ω => Real.log (familyLeafTotal ms u x ω).toReal-Real.log (familyUnmarkedTotal ms ω).toReal) := by
    filter_upwards [hpos,hp.1] with ω hω hs
    unfold familyLogPartition
    rw [familyLeafTotal_zero]
    exact Real.log_div (ENNReal.toReal_pos hω.1.ne' hω.2.ne).ne'
      (ENNReal.toReal_pos hs.1.ne' hs.2.ne).ne'
  refine ⟨hpos, ?_, (hiF.sub hiS).congr he.symm, ?_⟩
  · simpa only [sq_abs] using hf2.integrable_sq
  · rw [integral_congr_ae he, integral_sub hiF hiS]
    have hv := hc.integral_eq
    change (∫ ω, Real.log (familyLeafTotal ms u x ω).toReal-familyRecursion ms ν u x ∂μ) =
      ∫ ω, Real.log (familyUnmarkedTotal ms ω).toReal ∂μ at hv
    rw [integral_sub hiF (integrable_const _), integral_const, probReal_univ, one_smul] at hv
    linarith
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma measurable_measure_withDensity {X : Type*} [MeasurableSpace X]
    {w : X → ℝ≥0∞} (hw : Measurable w) :
    Measurable (fun μ : Measure X => μ.withDensity w) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [withDensity_apply _ hs, ← lintegral_indicator hs]
  exact Measure.measurable_lintegral (hw.indicator hs)

def weightedMass {X : Type*} [MeasurableSpace X] (w : X → ℝ≥0∞) (μ : Measure X) : ℝ≥0∞ :=
  ∫⁻ x, w x ∂μ

def weightedFiniteKernel {X : Type*} [MeasurableSpace X] (w : X → ℝ≥0∞) (hw : Measurable w) :
    Kernel (Measure X) X :=
  ⟨fun μ => (1 + weightedMass w μ)⁻¹ • μ.withDensity w, by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact (measurable_const.add (Measure.measurable_lintegral hw)).inv.mul
      ((Measure.measurable_coe hs).comp (measurable_measure_withDensity hw))⟩

instance weightedFiniteKernel_finite {X : Type*} [MeasurableSpace X]
    (w : X → ℝ≥0∞) (hw : Measurable w) : IsFiniteKernel (weightedFiniteKernel w hw) := by
  refine ⟨⟨1, by simp, fun μ => ?_⟩⟩
  change ((1 + weightedMass w μ)⁻¹ • μ.withDensity w) univ ≤ 1
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  calc
    _ ≤ (1 + weightedMass w μ)⁻¹ * (1 + weightedMass w μ) := by
      gcongr
      exact le_add_left le_rfl
    _ ≤ 1 := ENNReal.inv_mul_le_one _

def weightedHullDensity {X : Type*} [MeasurableSpace X] (w : X → ℝ≥0∞)
    (μ : Measure X) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + (weightedMass w μ).toReal) / w x

lemma measurable_weightedHullDensity {X : Type*} [MeasurableSpace X]
    {w : X → ℝ≥0∞} (hw : Measurable w) :
    Measurable (Function.uncurry (weightedHullDensity w)) := by
  exact (measurable_const.add ((Measure.measurable_lintegral hw).comp measurable_fst).ennreal_toReal).ennreal_ofReal.div
    (hw.comp measurable_snd)

def weightedHull {X : Type*} [MeasurableSpace X] (w : X → ℝ≥0∞) (hw : Measurable w) :
    Kernel (Measure X) X :=
  (weightedFiniteKernel w hw).withDensity (weightedHullDensity w)

lemma weightedHull_sfinite {X : Type*} [MeasurableSpace X]
    (w : X → ℝ≥0∞) (hw : Measurable w) (hpos : ∀ x, w x ≠ 0) :
    IsSFiniteKernel (weightedHull w hw) := by
  apply Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
  intro μ x
  exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (hpos x)

lemma weightedHull_eq {X : Type*} [MeasurableSpace X]
    {w : X → ℝ≥0∞} (hw : Measurable w) (hpos : ∀ x, w x ≠ 0)
    (hfin : ∀ x, w x ≠ ∞) (μ : Measure X) (hμ : weightedMass w μ ≠ ∞) :
    weightedHull w hw μ = μ := by
  rw [weightedHull, Kernel.withDensity_apply _ (measurable_weightedHullDensity hw)]
  change (((1 + weightedMass w μ)⁻¹ • μ.withDensity w).withDensity (weightedHullDensity w μ)) = μ
  have hd : Measurable (weightedHullDensity w μ) := by
    exact measurable_const.div hw
  rw [withDensity_smul_measure, ← withDensity_mul μ hw hd]
  have hg : w * weightedHullDensity w μ = fun _ => 1 + weightedMass w μ := by
    funext x
    simp only [Pi.mul_apply, weightedHullDensity]
    rw [ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal hμ]
    exact ENNReal.mul_div_cancel (hpos x) (hfin x)
  rw [hg, withDensity_const, smul_smul, ENNReal.inv_mul_cancel]
  · simp
  · exact (add_pos_of_pos_of_nonneg zero_lt_one (zero_le)).ne'
  · exact ENNReal.add_ne_top.mpr ⟨by simp, hμ⟩

end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma measurableSet_mem_evaluated_list {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    [MeasurableEq X] (xs : List (B → X)) (hxs : ∀ f ∈ xs, Measurable f)
    {x : B → X} (hx : Measurable x) :
    MeasurableSet {b | x b ∈ xs.map (fun f => f b)} := by
  induction xs with
  | nil => simp
  | cons f fs ih =>
    have hf := hxs f (by simp)
    have hfs : ∀ g ∈ fs, Measurable g := fun g hg => hxs g (by simp [hg])
    simpa only [List.map_cons, List.mem_cons, Set.union_def, Set.mem_ofPred_eq] using
      (measurableSet_eq_fun hx hf).union (ih hfs)

lemma measurable_distinctCloudIntegral {X : Type} [MeasurableSpace X] [MeasurableEq X]
    (fs : List (X → ℝ≥0∞)) (hfs : ∀ f ∈ fs, Measurable f) :
    ∀ {B : Type*} [MeasurableSpace B] (κ : Kernel B X) [IsSFiniteKernel κ]
      (xs : List (B → X)), (∀ x ∈ xs, Measurable x) →
      Measurable (fun b => distinctCloudIntegral fs (κ b) (xs.map (fun x => x b))) := by
  classical
  induction fs with
  | nil => intros; exact measurable_const
  | cons f fs ih =>
    intro B mB κ hκ xs hxs
    have hf : Measurable f := hfs f (by simp)
    have htail : ∀ g ∈ fs, Measurable g := fun g hg => hfs g (by simp [hg])
    let ys : List (B × X → X) := Prod.snd :: xs.map (fun x => x ∘ Prod.fst)
    have hys : ∀ y ∈ ys, Measurable y := by
      intro y hy
      simp only [ys, List.mem_cons, List.mem_map] at hy
      rcases hy with rfl | ⟨z,hz,rfl⟩
      · exact measurable_snd
      · exact (hxs z hz).comp measurable_fst
    have hi := ih htail (κ.comap Prod.fst measurable_fst) ys hys
    have hc := measurableSet_mem_evaluated_list
      (xs.map (fun x => x ∘ Prod.fst)) (by
        intro y hy
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
        exact (hxs z hz).comp measurable_fst) (measurable_snd : Measurable (Prod.snd : B × X → X))
    have hm : Measurable (fun z : B × X => if z.2 ∈ xs.map (fun x => x z.1) then 0 else
        f z.2 * distinctCloudIntegral fs (κ z.1) (z.2 :: xs.map (fun x => x z.1))) := by
      apply Measurable.ite
      · simpa only [List.map_map, Function.comp_def] using hc
      · exact measurable_const
      · exact (hf.comp measurable_snd).mul (by
          simpa only [ys, List.map_cons, List.map_map, Function.comp_def, Kernel.comap_apply] using hi)
    exact hm.lintegral_kernel_prod_right'

lemma distinctCloudIntegral_add_dirac {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (fs : List (X → ℝ≥0∞)) (μ : Measure X)
    (xs : List X) {a : X} (ha : a ∈ xs) :
    distinctCloudIntegral fs (Measure.dirac a + μ) xs = distinctCloudIntegral fs μ xs := by
  classical
  induction fs generalizing xs with
  | nil => rfl
  | cons f fs ih =>
    simp only [distinctCloudIntegral, lintegral_add_measure, lintegral_dirac, ite_eq_left ha, zero_add]
    apply lintegral_congr
    intro x
    split_ifs
    · rfl
    · rw [ih (x::xs) (by simp [ha])]

end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def finiteCounting {X : Type*} [MeasurableSpace X] {k : ℕ} (y : Fin k → X) : Measure X :=
  ∑ i, Measure.dirac (y i)

lemma measurable_finiteCounting {X : Type*} [MeasurableSpace X] (k : ℕ) :
    Measurable (@finiteCounting X _ k) := by
  exact Finset.measurable_fun_sum _ (fun i _ => Measure.measurable_dirac.comp (measurable_pi_apply i))

lemma finiteCounting_insert {X : Type*} [MeasurableSpace X] {k : ℕ}
    (i : Fin (k+1)) (x : X) (y : Fin k → X) :
    finiteCounting (i.insertNth x y) = Measure.dirac x + finiteCounting y := by
  unfold finiteCounting
  rw [Fin.sum_univ_succAbove _ i]
  simp

lemma finite_counting_campbell {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (k : ℕ) {F : X × Measure X → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y : Fin (k+1) → X, ∑ i, F (y i, finiteCounting y) ∂Measure.pi (fun _ => μ)) =
      (k+1) * ∫⁻ x, ∫⁻ y : Fin k → X,
        F (x, Measure.dirac x + finiteCounting y) ∂Measure.pi (fun _ => μ) ∂μ := by
  rw [lintegral_finsetSum _ (fun i _ =>
    show Measurable (fun y : Fin (k+1) → X => F (y i, finiteCounting y)) from
      hF.comp ((measurable_pi_apply i).prodMk (measurable_finiteCounting _)))]
  have h (i : Fin (k+1)) :
      (∫⁻ y : Fin (k+1) → X, F (y i, finiteCounting y) ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x, ∫⁻ y : Fin k → X, F (x, Measure.dirac x + finiteCounting y)
        ∂Measure.pi (fun _ => μ) ∂μ := by
    have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) i).symm
    have h := hm.lintegral_comp (hF.comp ((measurable_pi_apply i).prodMk (measurable_finiteCounting _)))
    simp only [Function.comp_def] at h
    rw [← h]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_apply_same, finiteCounting_insert]
    exact lintegral_prod _ (hF.comp (measurable_fst.prodMk
      ((Measure.measurable_dirac.comp measurable_fst).add ((measurable_finiteCounting _).comp measurable_snd)))).aemeasurable
  simp_rw [h]
  simp

end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def poissonBinMeasure {X : Type*} [MeasurableSpace X] (b : PoissonBin X) : Measure X :=
  finiteCounting (fun i : Fin b.1 => b.2 i)

lemma measurable_poissonBinMeasure {X : Type*} [MeasurableSpace X] :
    Measurable (@poissonBinMeasure X _) := by
  apply measurable_from_prod_countable_right
  intro k
  exact (measurable_finiteCounting k).comp (by fun_prop)

lemma lintegral_poissonBinMeasure {X : Type*} [MeasurableSpace X]
    (b : PoissonBin X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂poissonBinMeasure b) = ∑ i : Fin b.1, f (b.2 i) := by
  simp only [poissonBinMeasure, finiteCounting, lintegral_finsetSum_measure,
    lintegral_dirac' _ hf]

lemma measurable_bin_functional {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    {b : B → PoissonBin X} (hb : Measurable b) {f : B × X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ x, f (a,x) ∂poissonBinMeasure (b a)) := by
  have he (a : B) : (∫⁻ x, f (a,x) ∂poissonBinMeasure (b a)) =
      ∑ i ∈ Finset.range (b a).1, f (a,(b a).2 i) := by
    rw [lintegral_poissonBinMeasure (b a) (f := fun x => f (a,x))
      (hf.comp (measurable_const.prodMk measurable_id))]
    exact Fin.sum_univ_eq_sum_range (fun j => f (a,(b a).2 j)) (b a).1
  simp_rw [he]
  have h : Measurable (fun z : ℕ × B => ∑ i ∈ Finset.range z.1, f (z.2,(b z.2).2 i)) :=
    measurable_from_prod_countable_right (fun k =>
      Finset.measurable_fun_sum (Finset.range k) (fun i _ =>
        show Measurable (fun a => f (a,(b a).2 i)) from hf.comp
          (measurable_id.prodMk ((measurable_pi_apply i).comp hb.snd))))
  exact h.comp (hb.fst.prodMk measurable_id)

lemma poisson_one_shift (k : ℕ) :
    (k+1 : ℝ≥0∞) * (poissonMeasure 1) {k+1} = (poissonMeasure 1) {k} := by
  simp only [poissonMeasure_singleton, NNReal.coe_one, one_pow, mul_one]
  rw [show (k+1:ℝ≥0∞) = ENNReal.ofReal (k+1:ℝ) by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one],
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

lemma iid_prefix_counting {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (k : ℕ) {H : (Fin k → X) → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y : ℕ → X, H (fun i : Fin k => y i) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ y, H y ∂Measure.pi (fun _ : Fin k => μ) := by
  rw [← iid_prefix_map μ k]
  exact (lintegral_map hH (by fun_prop)).symm

lemma poisson_bin_campbell {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {F : X × Measure X → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ b, ∫⁻ x, F (x, poissonBinMeasure b) ∂poissonBinMeasure b ∂poissonBinLaw μ) =
      ∫⁻ x, ∫⁻ b, F (x, Measure.dirac x + poissonBinMeasure b) ∂poissonBinLaw μ ∂μ := by
  have h1 : Measurable (fun b : PoissonBin X => ∫⁻ x, F (x, poissonBinMeasure b) ∂poissonBinMeasure b) :=
    measurable_bin_functional measurable_id
      (hF.comp (measurable_snd.prodMk (measurable_poissonBinMeasure.comp measurable_fst)))
  rw [show poissonBinLaw μ = (poissonMeasure 1).prod (Measure.infinitePi (fun _ : ℕ => μ)) from rfl,
    lintegral_prod _ h1.aemeasurable]
  have h2 (k : ℕ) : (∫⁻ y : ℕ → X, ∫⁻ x, F (x, poissonBinMeasure (k,y))
      ∂poissonBinMeasure (k,y) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ y : Fin k → X, ∑ i, F (y i, finiteCounting y) ∂Measure.pi (fun _ => μ) := by
    have hbb (y : ℕ → X) := lintegral_poissonBinMeasure (k,y)
      (f := fun x => F (x,poissonBinMeasure (k,y)))
      (hF.comp (measurable_id.prodMk measurable_const))
    simp_rw [hbb]
    exact iid_prefix_counting μ k (H := fun y => ∑ i, F (y i,finiteCounting y)) (by
      exact Finset.measurable_fun_sum Finset.univ (fun i _ =>
        hF.comp ((measurable_pi_apply i).prodMk (measurable_finiteCounting _))))
  simp_rw [h2]
  rw [lintegral_countable', tsum_eq_zero_add' ENNReal.summable]
  simp only [Fin.sum_univ_zero, lintegral_zero, zero_mul, zero_add]
  simp_rw [finite_counting_campbell μ _ hF]
  have he (k : ℕ) (v : ℝ≥0∞) : ((k+1 : ℝ≥0∞)*v)*(poissonMeasure 1) {k+1} =
      v*(poissonMeasure 1) {k} := by rw [mul_comm (k+1 : ℝ≥0∞), mul_assoc, poisson_one_shift]
  simp_rw [he]
  rw [← lintegral_countable']
  have hm : Measurable (fun z : ℕ × X => ∫⁻ y : ℕ → X,
      F (z.2, Measure.dirac z.2 + poissonBinMeasure (z.1,y))
        ∂Measure.infinitePi (fun _ : ℕ => μ)) := by
    exact (show Measurable (fun w : (ℕ × X) × (ℕ → X) =>
      F (w.1.2, Measure.dirac w.1.2 + poissonBinMeasure (w.1.1,w.2))) from
      hF.comp (measurable_fst.snd.prodMk
        ((Measure.measurable_dirac.comp measurable_fst.snd).add
          (measurable_poissonBinMeasure.comp (measurable_fst.fst.prodMk measurable_snd))))).lintegral_prod_right' 
  have hp (k : ℕ) (x : X) : (∫⁻ y : Fin k → X,
      F (x, Measure.dirac x + finiteCounting y) ∂Measure.pi (fun _ => μ)) =
      ∫⁻ y : ℕ → X, F (x, Measure.dirac x + poissonBinMeasure (k,y))
        ∂Measure.infinitePi (fun _ : ℕ => μ) := by
    exact (iid_prefix_counting μ k (hF.comp (measurable_const.prodMk
      (measurable_const.add (measurable_finiteCounting _))))).symm
  simp_rw [hp]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro x
  exact (lintegral_prod _ (hF.comp (measurable_const.prodMk
    (measurable_const.add measurable_poissonBinMeasure))).aemeasurable).symm

end MicroscopicJamming

end

end OAI
