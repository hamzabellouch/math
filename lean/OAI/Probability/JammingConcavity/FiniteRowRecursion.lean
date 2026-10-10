import Mathlib
import OAI.Probability.JammingConcavity.CascadeNormalization

namespace OAI

/-! Finite Row Recursion. -/

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
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def MarkedCascadeTree : ℕ → Type
  | 0 => Unit
  | k+1 => PointCloud (ℝ × MarkedCascadeTree k)

instance markedCascadeTreeMeasurable : (k : ℕ) → MeasurableSpace (MarkedCascadeTree k)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | k+1 => by
    letI := markedCascadeTreeMeasurable k
    exact inferInstanceAs (MeasurableSpace (PointCloud (ℝ × MarkedCascadeTree k)))

def forgetCascadeMarks : (k : ℕ) → MarkedCascadeTree k → CascadeTree k
  | 0, _ => ()
  | k+1, ω => mapPointCloud (fun z : ℝ × MarkedCascadeTree k => forgetCascadeMarks k z.2) ω

def incrementCascadeLaw : (k : ℕ) → (ℕ → Measure ℝ) → Measure (MarkedCascadeTree k)
  | 0, _ => Measure.dirac ()
  | k+1, ν => pointCloudLaw ((ν 0).prod (incrementCascadeLaw k (fun j => ν (j+1))))

def incrementCascadeTotal : (ms : List ℝ) → (ℝ → ℝ) → ℝ → MarkedCascadeTree ms.length → ℝ≥0∞
  | [], u, x, _ => ENNReal.ofReal (Real.exp (u x))
  | m::ms, u, x, ω => pointCloudFunctional (fun z : ℝ × (ℝ × MarkedCascadeTree ms.length) =>
      ENNReal.ofReal (z.1^(-1/m))*incrementCascadeTotal ms u (x+z.2.1) z.2.2) ω

def incrementUnmarkedTotal (ms : List ℝ) (ω : MarkedCascadeTree ms.length) : ℝ≥0∞ :=
  cascadeTotal ms (forgetCascadeMarks ms.length ω)

def finiteRowRecursion : List ℝ → (ℕ → Measure ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], _, u, x => u x
  | m::ms, ν, u, x => (1/m)*Real.log (∫ a, Real.exp
      (m*finiteRowRecursion ms (fun j => ν (j+1)) u (x+a)) ∂ν 0)

def RecursionMomentsFinite : List ℝ → (ℕ → Measure ℝ) → (ℝ → ℝ) → Prop
  | [], _, _ => True
  | m::ms, ν, u =>
      (∀ x, Integrable (fun a => Real.exp
        (m*finiteRowRecursion ms (fun j => ν (j+1)) u (x+a))) (ν 0)) ∧
      RecursionMomentsFinite ms (fun j => ν (j+1)) u

def incrementLogPartition (ms : List ℝ) (u : ℝ → ℝ)
    (z : ℝ × MarkedCascadeTree ms.length) : ℝ :=
  Real.log ((incrementCascadeTotal ms u z.1 z.2).toReal / (incrementUnmarkedTotal ms z.2).toReal)

def FiniteRowRecursionStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ ν : ℕ → Measure ℝ, (∀ j, IsProbabilityMeasure (ν j)) →
  ∀ u : ℝ → ℝ, Measurable u → RecursionMomentsFinite ms ν u →
  ∀ ν₀ : Measure ℝ, IsProbabilityMeasure ν₀ → Integrable (finiteRowRecursion ms ν u) ν₀ →
    Integrable (incrementLogPartition ms u) (ν₀.prod (incrementCascadeLaw ms.length ν)) ∧
    (∫ z, incrementLogPartition ms u z ∂ν₀.prod (incrementCascadeLaw ms.length ν)) =
      ∫ x, finiteRowRecursion ms ν u x ∂ν₀
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MicroscopicJamming

def rowVarianceSum : List ℝ → (ℕ → ℝ≥0) → ℝ
  | [], _ => 0
  | _::ms, d => (d 0:ℝ)+rowVarianceSum ms (fun j => d (j+1))

def GaussianRowEnvelopeStatement : Prop :=
  ∀ (ms : List ℝ), (∀ m ∈ ms, 0 < m ∧ m ≤ 1) →
  ∀ (d : ℕ → ℝ≥0) (u : ℝ → ℝ), Measurable u →
  ∀ (A B : ℝ), 0 ≤ A → (∀ x, -A*(1+x^2) ≤ u x ∧ u x ≤ B) →
    RecursionMomentsFinite ms (fun j => gaussianReal 0 (d j)) u ∧
    (∀ x, -A*(1+x^2+rowVarianceSum ms d) ≤
      finiteRowRecursion ms (fun j => gaussianReal 0 (d j)) u x ∧
      finiteRowRecursion ms (fun j => gaussianReal 0 (d j)) u x ≤ B) ∧
    ∀ p₀ : ℝ≥0, Integrable
      (finiteRowRecursion ms (fun j => gaussianReal 0 (d j)) u) (gaussianReal 0 p₀)
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma measurable_forgetCascadeMarks (k : ℕ) : Measurable (forgetCascadeMarks k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact measurable_mapPointCloud (ih.comp measurable_snd)

lemma incrementCascadeLaw_probability (k : ℕ) (ν : ℕ → Measure ℝ)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) : IsProbabilityMeasure (incrementCascadeLaw k ν) := by
  induction k generalizing ν with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ k ih =>
    have := hν 0
    have := ih (fun j => ν (j+1)) (fun j => hν (j+1))
    exact inferInstanceAs (IsProbabilityMeasure (pointCloudLaw ((ν 0).prod
      (incrementCascadeLaw k (fun j => ν (j+1))))))

lemma incrementCascadeLaw_forget (ms : List ℝ) (ν : ℕ → Measure ℝ)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) :
    (incrementCascadeLaw ms.length ν).map (forgetCascadeMarks ms.length) = cascadeLaw ms := by
  induction ms generalizing ν with
  | nil => exact Measure.map_dirac' measurable_const ()
  | cons m ms ih =>
    have := hν 0
    have := incrementCascadeLaw_probability ms.length (fun j => ν (j+1)) (fun j => hν (j+1))
    change (pointCloudLaw ((ν 0).prod (incrementCascadeLaw ms.length (fun j => ν (j+1))))).map
      (mapPointCloud (fun z => forgetCascadeMarks ms.length z.2)) = pointCloudLaw (cascadeLaw ms)
    rw [pointCloudLaw_map _ (f := fun z : ℝ × MarkedCascadeTree ms.length =>
      forgetCascadeMarks ms.length z.2) ((measurable_forgetCascadeMarks ms.length).comp measurable_snd)]
    congr 1
    erw [← Measure.map_map (measurable_forgetCascadeMarks ms.length) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, ih]
    exact fun j => hν (j+1)

lemma measurable_pointCloudFunctional_param {P A : Type*} [MeasurableSpace P] [MeasurableSpace A]
    {f : P × (ℝ × A) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : P × PointCloud A => pointCloudFunctional (fun v => f (z.1,v)) z.2) := by
  have hm : Measurable (fun z : P × PointCloud A =>
      mapPointCloud (fun a => (z.1,a)) z.2) := by
    unfold mapPointCloud mapPoissonBin Prod.map id
    fun_prop
  exact (measurable_pointCloudFunctional (hf.comp (by fun_prop : Measurable
    (fun z : ℝ × (P × A) => (z.2.1,(z.1,z.2.2)))))).comp hm

lemma measurable_incrementCascadeTotal (ms : List ℝ) {u : ℝ → ℝ} (hu : Measurable u) :
    Measurable (fun z : ℝ × MarkedCascadeTree ms.length => incrementCascadeTotal ms u z.1 z.2) := by
  induction ms with
  | nil => exact (Real.measurable_exp.comp (hu.comp measurable_fst)).ennreal_ofReal
  | cons m ms ih =>
    exact measurable_pointCloudFunctional_param (f := fun z : ℝ × (ℝ × (ℝ × MarkedCascadeTree ms.length)) =>
      ENNReal.ofReal (z.2.1^(-1/m))*incrementCascadeTotal ms u (z.1+z.2.2.1) z.2.2.2) ( (by fun_prop : Measurable (fun z : ℝ × (ℝ × (ℝ × MarkedCascadeTree ms.length)) =>
      ENNReal.ofReal (z.2.1^(-1/m)))).mul
      (ih.comp (by fun_prop : Measurable (fun z : ℝ × (ℝ × (ℝ × MarkedCascadeTree ms.length)) =>
        (z.1+z.2.2.1,z.2.2.2)))))

lemma measurable_incrementUnmarkedTotal (ms : List ℝ) : Measurable (incrementUnmarkedTotal ms) :=
  (measurable_cascadeTotal ms).comp (measurable_forgetCascadeMarks ms.length)

lemma measurable_finiteRowRecursion (ms : List ℝ) (ν : ℕ → Measure ℝ)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) {u : ℝ → ℝ} (hu : Measurable u) :
    Measurable (finiteRowRecursion ms ν u) := by
  induction ms generalizing ν with
  | nil => exact hu
  | cons m ms ih =>
    have := hν 0
    have ht := ih (fun j => ν (j+1)) (fun j => hν (j+1))
    have he : Measurable (fun z : ℝ × ℝ => Real.exp
        (m*finiteRowRecursion ms (fun j => ν (j+1)) u (z.1+z.2))) := by fun_prop
    exact (Real.measurable_log.comp he.stronglyMeasurable.integral_prod_right'.measurable).const_mul _

lemma incrementUnmarkedTotal_cons (m : ℝ) (ms : List ℝ) (ω : MarkedCascadeTree (m::ms).length) :
    incrementUnmarkedTotal (m::ms) ω = pointCloudFunctional
      (fun z : ℝ × (ℝ × MarkedCascadeTree ms.length) =>
        ENNReal.ofReal (z.1^(-1/m))*incrementUnmarkedTotal ms z.2.2) ω := rfl

lemma incrementUnmarkedTotal_properties (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (ν : ℕ → Measure ℝ)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) :
    (∀ᵐ ω ∂incrementCascadeLaw ms.length ν,
      0 < incrementUnmarkedTotal ms ω ∧ incrementUnmarkedTotal ms ω < ∞) ∧
    (∀ a : ℝ, 0 < a → (∀ m ∈ ms, a < m) → Integrable
      (fun ω => (incrementUnmarkedTotal ms ω).toReal^a) (incrementCascadeLaw ms.length ν)) ∧
    Integrable (fun ω => |Real.log (incrementUnmarkedTotal ms ω).toReal|^2)
      (incrementCascadeLaw ms.length ν) := by
  have hp : MeasurePreserving (forgetCascadeMarks ms.length) (incrementCascadeLaw ms.length ν)
      (cascadeLaw ms) := ⟨measurable_forgetCascadeMarks _, incrementCascadeLaw_forget ms ν hν⟩
  have h := cascadeTotal_properties ms hms h01
  exact ⟨hp.quasiMeasurePreserving.ae h.1, fun a ha ham => hp.integrable_comp_of_integrable (h.2.1 a ha ham),
    hp.integrable_comp_of_integrable h.2.2⟩
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace MicroscopicJamming

lemma gaussian_shift_square (x : ℝ) (d : ℝ≥0) :
    Integrable (fun a : ℝ => (x+a)^2) (gaussianReal 0 d) ∧
    (∫ a : ℝ, (x+a)^2 ∂gaussianReal 0 d) = x^2+(d:ℝ) := by
  have h2 : MemLp (fun a : ℝ => a) 2 (gaussianReal 0 d) := memLp_id_gaussianReal 2
  have hi : Integrable (fun a : ℝ => a) (gaussianReal 0 d) := h2.integrable (by norm_num)
  have hs : (∫ a : ℝ, a^2 ∂gaussianReal 0 d) = (d:ℝ) := by
    have hv := variance_fun_id_gaussianReal (μ := 0) (v := d)
    rw [variance_eq_integral (by fun_prop)] at hv
    simpa using hv
  have he : (fun a : ℝ => (x+a)^2) = fun a => x^2+2*x*a+a^2 := by funext a; ring
  rw [he]
  have ht : Integrable (fun a : ℝ => 2*x*a) (gaussianReal 0 d) := hi.const_mul (2*x)
  have hc : Integrable (fun a : ℝ => x^2+2*x*a) (gaussianReal 0 d) := (integrable_const (x^2)).add ht
  refine ⟨hc.add h2.integrable_sq, ?_⟩
  rw [integral_add hc h2.integrable_sq, integral_add (integrable_const (x^2)) ht, integral_const_mul]
  simp [hs]

lemma gaussian_envelope_integrable {u : ℝ → ℝ} (hu : Measurable u)
    {A B R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hb : ∀ z, -A*(1+z^2+R) ≤ u z ∧ u z ≤ B) (x : ℝ) (d : ℝ≥0) :
    Integrable (fun a => u (x+a)) (gaussianReal 0 d) := by
  have hg : Integrable (fun a : ℝ => |B|+A*(1+(x+a)^2+R)) (gaussianReal 0 d) :=
    (integrable_const _).add ((((integrable_const _).add (gaussian_shift_square x d).1).add
      (integrable_const _)).const_mul _)
  apply hg.mono' (hu.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards [] with a
  rw [Real.norm_eq_abs, abs_le]
  have hn : 0 ≤ A*(1+(x+a)^2+R) := mul_nonneg hA (by positivity)
  constructor
  · change -(|B|+A*(1+(x+a)^2+R)) ≤ u (x+a)
    have h := (hb (x+a)).1
    nlinarith [abs_nonneg B]
  · exact (hb (x+a)).2.trans ((le_abs_self B).trans (by linarith))

lemma gaussian_envelope_integral_lower {u : ℝ → ℝ} (hu : Measurable u)
    {A B R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hb : ∀ z, -A*(1+z^2+R) ≤ u z ∧ u z ≤ B) (x : ℝ) (d : ℝ≥0) :
    -A*(1+x^2+R+(d:ℝ)) ≤ ∫ a, u (x+a) ∂gaussianReal 0 d := by
  have hil : Integrable (fun a : ℝ => -A*(1+(x+a)^2+R)) (gaussianReal 0 d) :=
    (((integrable_const _).add (gaussian_shift_square x d).1).add (integrable_const _)).const_mul _
  have h := integral_mono hil (gaussian_envelope_integrable hu hA hR hb x d)
    (fun a => (hb (x+a)).1)
  have hi1 : Integrable (fun a : ℝ => 1+(x+a)^2) (gaussianReal 0 d) :=
    (integrable_const (1:ℝ)).add (gaussian_shift_square x d).1
  rw [integral_const_mul, integral_add hi1 (integrable_const R),
    integral_add (integrable_const (1:ℝ)) (gaussian_shift_square x d).1,
    (gaussian_shift_square x d).2] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  nlinarith only [h]

lemma gaussian_log_operator_barrier {u : ℝ → ℝ} (hu : Measurable u)
    {A B R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hb : ∀ z, -A*(1+z^2+R) ≤ u z ∧ u z ≤ B)
    {m : ℝ} (hm : 0 < m) (x : ℝ) (d : ℝ≥0) :
    Integrable (fun a => Real.exp (m*u (x+a))) (gaussianReal 0 d) ∧
    -A*(1+x^2+R+(d:ℝ)) ≤ (1/m)*Real.log (∫ a, Real.exp (m*u (x+a)) ∂gaussianReal 0 d) ∧
    (1/m)*Real.log (∫ a, Real.exp (m*u (x+a)) ∂gaussianReal 0 d) ≤ B := by
  have hi := gaussian_envelope_integrable hu hA hR hb x d
  have he : Integrable (fun a => Real.exp (m*u (x+a))) (gaussianReal 0 d) := by
    apply (integrable_const (Real.exp (m*B))).mono'
      (((hu.comp (measurable_const.add measurable_id)).const_mul m).exp.aestronglyMeasurable)
    filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb (x+a)).2 hm.le)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (by filter_upwards [] with a; exact mem_univ _) (hi.const_mul m) he
  rw [integral_const_mul] at hj
  have hp : 0 < ∫ a, Real.exp (m*u (x+a)) ∂gaussianReal 0 d :=
    (Real.exp_pos _).trans_le hj
  refine ⟨he, ?_, ?_⟩
  · apply (gaussian_envelope_integral_lower hu hA hR hb x d).trans
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hm).mpr
    simpa only [mul_comm] using (Real.le_log_iff_exp_le hp).mpr hj
  · rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hm).mpr
    rw [mul_comm B m]
    apply (Real.log_le_iff_le_exp hp).mpr
    calc
      (∫ a, Real.exp (m*u (x+a)) ∂gaussianReal 0 d) ≤ ∫ _ : ℝ, Real.exp (m*B) ∂gaussianReal 0 d :=
        integral_mono he (integrable_const _) (fun a =>
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb (x+a)).2 hm.le))
      _ = Real.exp (m*B) := by simp
end MicroscopicJamming

 

 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MicroscopicJamming

lemma hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hh := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert hh using 1
  · funext y
    simp [gaussianPDFReal]
  · simp [gaussianPDFReal]
    ring

lemma integrable_gaussianPDF_mul {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) volume := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0)≠0)] at hf
  have hh := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp hf
  simpa only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _),smul_eq_mul] using hh

 
theorem standardGaussian_integration_by_parts {f f' : ℝ → ℝ}
    (hd : ∀ x,HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1) = ∫ x,f' x ∂gaussianReal 0 1 := by
  have h1 : Integrable ((gaussianPDFReal 0 1)*f') := integrable_gaussianPDF_mul hf'
  have h2 : Integrable ((fun x => -x*gaussianPDFReal 0 1 x)*f) := by
    convert (integrable_gaussianPDF_mul hxf).neg using 1
    funext x
    dsimp
    ring
  have h3 : Integrable ((gaussianPDFReal 0 1)*f) := integrable_gaussianPDF_mul hf
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := gaussianPDFReal 0 1) (u' := fun x => -x*gaussianPDFReal 0 1 x)
    (v := f) (v' := f') (fun x _ => hasDerivAt_standardGaussianPDF x)
    (fun x _ => hd x) h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0)≠0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0)≠0)]
  simp only [smul_eq_mul]
  rw [hh]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

 
theorem standardGaussian_product_integration_by_parts {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {f f' : ℝ × Ω → ℝ}
    (hd : ∀ y x, HasDerivAt (fun z => f (z,y)) (f' (x,y)) x)
    (hf : Integrable f ((gaussianReal 0 1).prod μ))
    (hf' : Integrable f' ((gaussianReal 0 1).prod μ))
    (hxf : Integrable (fun x => x.1*f x) ((gaussianReal 0 1).prod μ)) :
    (∫ x, x.1*f x ∂(gaussianReal 0 1).prod μ) =
      ∫ x,f' x ∂(gaussianReal 0 1).prod μ := by
  rw [integral_prod_symm _ hxf,integral_prod_symm _ hf']
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae,hf'.prod_left_ae,hxf.prod_left_ae] with y h0 h1 h2
  exact standardGaussian_integration_by_parts (hd y) h0 h1 h2

 

theorem standardGaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n+1))
    {f f' : (Fin (n+1) → ℝ) → ℝ}
    (hd : ∀ (y : Fin n → ℝ) x,
      HasDerivAt (fun z => f (i.insertNth z y)) (f' (i.insertNth x y)) x)
    (hf : Integrable f (Measure.pi fun _ => gaussianReal 0 1))
    (hf' : Integrable f' (Measure.pi fun _ => gaussianReal 0 1))
    (hxf : Integrable (fun x => x i*f x) (Measure.pi fun _ => gaussianReal 0 1)) :
    (∫ x, x i*f x ∂Measure.pi fun _ => gaussianReal 0 1) =
      ∫ x,f' x ∂Measure.pi fun _ => gaussianReal 0 1 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have h0 := he.integrable_comp_emb e.symm.measurableEmbedding |>.mpr hf
  have h1 := he.integrable_comp_emb e.symm.measurableEmbedding |>.mpr hf'
  have h2 := he.integrable_comp_emb e.symm.measurableEmbedding |>.mpr hxf
  rw [← he.integral_comp' (fun x => x i*f x),← he.integral_comp' f']
  simp only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv, Equiv.coe_fn_mk,
    Fin.insertNth_apply_same] at h0 h1 h2 ⊢
  exact standardGaussian_product_integration_by_parts _ hd h0 h1 h2

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

def HeatQuadraticGrowth (v : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |v x| ≤ C*(1+|x|)^2

lemma gaussian_abs_one_pow_integrable (n : ℕ) :
    Integrable (fun z : ℝ => (1+|z|)^n) (gaussianReal 0 1) := by
  by_cases hn : n=0
  · subst n
    simp only [pow_zero]
    exact integrable_const 1
  have hi : Integrable (fun z : ℝ => |z|^n) (gaussianReal 0 1) := by
    have hp := (memLp_id_gaussianReal' (n:ℝ≥0∞) (by simp) :
      MemLp id (n:ℝ≥0∞) (gaussianReal 0 1)).integrable_norm_rpow (by exact_mod_cast hn) (by simp)
    simpa only [id_eq, Real.norm_eq_abs, ENNReal.toReal_natCast, Real.rpow_natCast] using hp
  have hh : Integrable (fun z : ℝ => (2:ℝ)^(n-1)*(1+|z|^n)) (gaussianReal 0 1) :=
    ((integrable_const (1:ℝ)).add hi).const_mul _
  apply hh.mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (1+|z|)^n by positivity)]
  simpa only [one_pow] using add_pow_le (show (0:ℝ) ≤ 1 by norm_num) (abs_nonneg z) n

lemma heat_affine_bound (a b z : ℝ) :
    1+|a+b*z| ≤ (1+|a|+|b|)*(1+|z|) := by
  have ht : |a+b*z| ≤ |a|+|b| *|z| := by simpa [abs_mul] using abs_add_le a (b*z)
  nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg z, mul_nonneg (abs_nonneg a) (abs_nonneg z)]

lemma heat_affine_quadratic_integrable {v : ℝ → ℝ} (hv : Measurable v)
    (hg : HeatQuadraticGrowth v) (a b : ℝ) :
    Integrable (fun z : ℝ => v (a+b*z)) (gaussianReal 0 1) := by
  obtain ⟨C,hC,hg⟩ := hg
  have hdom := (gaussian_abs_one_pow_integrable 2).const_mul (C*(1+|a|+|b|)^2)
  apply hdom.mono' (hv.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  calc
    |v (a+b*z)| ≤ C*(1+|a+b*z|)^2 := hg _
    _ ≤ C*((1+|a|+|b|)*(1+|z|))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (heat_affine_bound a b z) 2) hC
    _ = C*(1+|a|+|b|)^2*(1+|z|)^2 := by ring

lemma heat_affine_mul_integrable {v : ℝ → ℝ} (hv : Measurable v)
    (hg : HeatQuadraticGrowth v) (a b : ℝ) :
    Integrable (fun z : ℝ => z*v (a+b*z)) (gaussianReal 0 1) := by
  obtain ⟨C,hC,hg⟩ := hg
  apply ((gaussian_abs_one_pow_integrable 3).const_mul (C*(1+|a|+|b|)^2)).mono'
    (measurable_id.mul (hv.comp (by fun_prop))).aestronglyMeasurable
  filter_upwards [] with z
  change |z*v (a+b*z)| ≤ _
  rw [abs_mul]
  have ht := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|a+b*z|) (heat_affine_bound a b z) 2
  calc
    |z| *|v (a+b*z)| ≤ (1+|z|)*(C*((1+|a|+|b|)*(1+|z|))^2) :=
      mul_le_mul (by linarith) ((hg _).trans (mul_le_mul_of_nonneg_left ht hC)) (abs_nonneg _) (by positivity)
    _ = C*(1+|a|+|b|)^2*(1+|z|)^3 := by ring

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma row_terminal_deriv_linear {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |deriv u x| ≤ L*(1+|x|) := by
  obtain ⟨hdu,hcu'⟩ := contDiff_infty_iff_deriv.mp hu.1
  have hdu' := (contDiff_infty_iff_deriv.mp hcu').1
  let L := |deriv u 0|+C+κ
  refine ⟨L, by dsimp [L]; linarith [abs_nonneg (deriv u 0),hu.2.2.1,hu.2.2.2.1], ?_⟩
  intro x
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := deriv u) (s := univ) (C := C+κ) (fun y _ => hdu' y)
    (fun y _ => by
      rw [Real.norm_eq_abs, abs_le]
      have hy := hu.2.2.2.2.2.2 y
      constructor <;> linarith [hy.2.2.1,hy.2.2.2,hu.2.2.1,hu.2.2.2.1])
    (convex_univ) (x := 0) (y := x) (mem_univ _) (mem_univ _)
  simp only [Real.norm_eq_abs, sub_zero] at hh
  have ha := abs_add_le (deriv u x-deriv u 0) (deriv u 0)
  rw [sub_add_cancel] at ha
  dsimp [L]
  nlinarith [hu.2.2.1, hu.2.2.2.1, abs_nonneg (deriv u 0), abs_nonneg x, mul_nonneg (abs_nonneg (deriv u 0)) (abs_nonneg x)]

lemma row_terminal_quadratic_growth {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) : HeatQuadraticGrowth u := by
  refine ⟨A+|B|, by linarith [hu.2.1,abs_nonneg B], ?_⟩
  intro x
  have hb := hu.2.2.2.2.2.2 x
  have hsq : x^2 ≤ (1+|x|)^2 := by nlinarith [sq_abs x, abs_nonneg x]
  rw [abs_le]
  constructor
  · nlinarith [hu.2.1,abs_nonneg B, mul_nonneg (abs_nonneg B) (sq_nonneg (1+|x|)),sq_abs x,abs_nonneg x]
  · have hp : 1 ≤ (1+|x|)^2 := by nlinarith [abs_nonneg x,sq_nonneg x,sq_abs x]
    have h := mul_le_mul_of_nonneg_left hp (abs_nonneg B)
    nlinarith [le_abs_self B,hu.2.1,mul_nonneg hu.2.1 (sq_nonneg (1+|x|))]

lemma row_terminal_deriv_growth {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) : HeatQuadraticGrowth (deriv u) := by
  obtain ⟨L,hL,h⟩ := row_terminal_deriv_linear hu
  refine ⟨L,hL,fun x => (h x).trans (mul_le_mul_of_nonneg_left ?_ hL)⟩
  nlinarith [abs_nonneg x, sq_nonneg x,sq_abs x]

lemma row_terminal_second_growth {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) : HeatQuadraticGrowth (deriv (deriv u)) := by
  have hK : 0 ≤ C+κ := add_nonneg hu.2.2.1 hu.2.2.2.1
  refine ⟨C+κ,hK,fun x => ?_⟩
  have h : |deriv (deriv u) x| ≤ C+κ := by
    rw [abs_le]; have hx := hu.2.2.2.2.2.2 x
    constructor <;> linarith [hx.2.2.1,hx.2.2.2,hu.2.2.1,hu.2.2.2.1]
  exact h.trans (le_mul_of_one_le_right hK (by nlinarith [abs_nonneg x,sq_nonneg x,sq_abs x]))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

def rowExpFirst (a : ℝ) (u : ℝ → ℝ) (x : ℝ) := a*deriv u x*Real.exp (a*u x)
def rowExpSecond (a : ℝ) (u : ℝ → ℝ) (x : ℝ) :=
  (a*deriv (deriv u) x+a^2*(deriv u x)^2)*Real.exp (a*u x)

lemma row_exp_derivatives {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (a : ℝ) :
    (∀ x, HasDerivAt (fun y => Real.exp (a*u y)) (rowExpFirst a u x) x) ∧
    (∀ x, HasDerivAt (rowExpFirst a u) (rowExpSecond a u x) x) := by
  obtain ⟨hdu,hcu'⟩ := contDiff_infty_iff_deriv.mp hu.1
  have hdu' := (contDiff_infty_iff_deriv.mp hcu').1
  constructor
  · intro x
    convert ((hdu x).hasDerivAt.const_mul a).exp using 1
    first | rfl | (simp only [rowExpFirst]; ring)
  · intro x
    convert (((hdu' x).hasDerivAt.const_mul a).mul
      ((hdu x).hasDerivAt.const_mul a).exp) using 1 <;> first | rfl | (dsimp only [rowExpFirst,rowExpSecond]; ring)

lemma row_exp_measurable {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (a : ℝ) :
    Measurable (fun x => Real.exp (a*u x)) ∧ Measurable (rowExpFirst a u) ∧
      Measurable (rowExpSecond a u) := by
  have h0 := hu.1.continuous.measurable
  have h1 := (contDiff_infty_iff_deriv.mp hu.1).2.continuous.measurable
  have h2 := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hu.1).2).2.continuous.measurable
  refine ⟨?_, ?_, ?_⟩
  · fun_prop
  · unfold rowExpFirst; fun_prop
  · unfold rowExpSecond; fun_prop

lemma row_exp_growth {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (ha : 0 ≤ a) :
    HeatQuadraticGrowth (fun x => Real.exp (a*u x)) ∧
    HeatQuadraticGrowth (rowExpFirst a u) ∧ HeatQuadraticGrowth (rowExpSecond a u) := by
  obtain ⟨L,hL,hlin⟩ := row_terminal_deriv_linear hu
  have hD : 0 ≤ C+κ := add_nonneg hu.2.2.1 hu.2.2.2.1
  have he (x : ℝ) : Real.exp (a*u x) ≤ Real.exp (a*B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hu.2.2.2.2.2.2 x).2.1 ha)
  have hs (x : ℝ) : 1 ≤ (1+|x|)^2 := by nlinarith [abs_nonneg x,sq_nonneg x,sq_abs x]
  have hd (x : ℝ) : |deriv (deriv u) x| ≤ C+κ := by
    rw [abs_le]
    have hh := hu.2.2.2.2.2.2 x
    constructor <;> linarith [hh.2.2.1,hh.2.2.2,hu.2.2.1,hu.2.2.2.1]
  constructor
  · refine ⟨Real.exp (a*B),(Real.exp_pos _).le,fun x => ?_⟩
    rw [abs_of_pos (Real.exp_pos _)]
    exact (he x).trans (le_mul_of_one_le_right (Real.exp_pos _).le (hs x))
  constructor
  · refine ⟨a*L*Real.exp (a*B),by positivity,fun x => ?_⟩
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left (hlin x) ha) (he x)
      (Real.exp_pos _).le (by positivity : 0 ≤ a*(L*(1+|x|)))
    dsimp [rowExpFirst]
    rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (a*(L*(1+|x|)))*Real.exp (a*B) := hh
      _ ≤ a*L*Real.exp (a*B)*(1+|x|)^2 := by
        have hh := mul_le_mul_of_nonneg_left
          (show 1+|x| ≤ (1+|x|)^2 by nlinarith [abs_nonneg x,sq_nonneg x,sq_abs x])
          (show 0 ≤ a*L*Real.exp (a*B) by positivity)
        nlinarith
  · refine ⟨(a*(C+κ)+a^2*L^2)*Real.exp (a*B),by positivity,fun x => ?_⟩
    have hp : (deriv u x)^2 ≤ (L*(1+|x|))^2 := by
      nlinarith [sq_le_sq₀ (abs_nonneg (deriv u x)) (show 0 ≤ L*(1+|x|) by positivity) |>.mpr (hlin x), sq_abs (deriv u x)]
    have hq : |a*deriv (deriv u) x+a^2*(deriv u x)^2| ≤
        (a*(C+κ)+a^2*L^2)*(1+|x|)^2 := by
      calc
        _ ≤ |a*deriv (deriv u) x|+|a^2*(deriv u x)^2| := abs_add_le _ _
        _ = a*|deriv (deriv u) x|+a^2*(deriv u x)^2 := by
          rw [abs_mul, abs_of_nonneg ha, abs_of_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg _))]
        _ ≤ a*(C+κ)+a^2*(L*(1+|x|))^2 := add_le_add
          (mul_le_mul_of_nonneg_left (hd x) ha) (mul_le_mul_of_nonneg_left hp (sq_nonneg a))
        _ ≤ (a*(C+κ)+a^2*L^2)*(1+|x|)^2 := by
          have hh := mul_le_mul_of_nonneg_left (hs x) (show 0 ≤ a*(C+κ) by positivity)
          nlinarith
    dsimp [rowExpSecond]
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ ((a*(C+κ)+a^2*L^2)*(1+|x|)^2)*Real.exp (a*B) :=
        mul_le_mul hq (he x) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma heat_curve_derivative {v v' : ℝ → ℝ} (hv : Measurable v) (hv' : Measurable v')
    (hg : HeatQuadraticGrowth v) (hg' : HeatQuadraticGrowth v')
    (hdv : ∀ x, HasDerivAt v (v' x) x)
    {a b a' b' : ℝ → ℝ} {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (hda : ∀ t ∈ s, HasDerivAt a (a' t) t)
    (hdb : ∀ t ∈ s, HasDerivAt b (b' t) t)
    (hca' : ContinuousAt a' t₀) (hcb' : ContinuousAt b' t₀) :
    HasDerivAt (fun t => ∫ z : ℝ, v (a t+b t*z) ∂gaussianReal 0 1)
      (∫ z : ℝ, v' (a t₀+b t₀*z)*(a' t₀+b' t₀*z) ∂gaussianReal 0 1) t₀ := by
  let K := 1+|a t₀|+|b t₀|+|a' t₀|+|b' t₀|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have h0 := mem_of_mem_nhds hs
  have hAb : |a t₀| < K := by dsimp [K]; linarith [abs_nonneg (b t₀), abs_nonneg (a' t₀), abs_nonneg (b' t₀)]
  have hBb : |b t₀| < K := by dsimp [K]; linarith [abs_nonneg (a t₀), abs_nonneg (a' t₀), abs_nonneg (b' t₀)]
  have hAd : |a' t₀| < K := by dsimp [K]; linarith [abs_nonneg (a t₀), abs_nonneg (b t₀), abs_nonneg (b' t₀)]
  have hBd : |b' t₀| < K := by dsimp [K]; linarith [abs_nonneg (a t₀), abs_nonneg (b t₀), abs_nonneg (a' t₀)]
  have hea : ∀ᶠ t in 𝓝 t₀, |a t| ≤ K :=
    (((hda t₀ h0).continuousAt.abs.tendsto).eventually (eventually_lt_nhds hAb)).mono fun _ h => h.le
  have heb : ∀ᶠ t in 𝓝 t₀, |b t| ≤ K :=
    (((hdb t₀ h0).continuousAt.abs.tendsto).eventually (eventually_lt_nhds hBb)).mono fun _ h => h.le
  have hea' : ∀ᶠ t in 𝓝 t₀, |a' t| ≤ K :=
    (hca'.abs.tendsto.eventually (eventually_lt_nhds hAd)).mono fun _ h => h.le
  have heb' : ∀ᶠ t in 𝓝 t₀, |b' t| ≤ K :=
    (hcb'.abs.tendsto.eventually (eventually_lt_nhds hBd)).mono fun _ h => h.le
  obtain ⟨C,hC,hgrow⟩ := hg'
  let U := {t | t ∈ s ∧ |a t| ≤ K ∧ |b t| ≤ K ∧ |a' t| ≤ K ∧ |b' t| ≤ K}
  have hU : U ∈ 𝓝 t₀ := inter_mem hs (hea.and (heb.and (hea'.and heb')))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := U) (F := fun t z => v (a t+b t*z))
    (F' := fun t z => v' (a t+b t*z)*(a' t+b' t*z))
    (bound := fun z => C*(1+2*K)^2*K*(1+|z|)^3) hU
    (Eventually.of_forall fun t => (hv.comp (by fun_prop)).aestronglyMeasurable)
    (heat_affine_quadratic_integrable hv hg (a t₀) (b t₀))
    (((hv'.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable)
    ?_ ((gaussian_abs_one_pow_integrable 3).const_mul _) ?_).2
  · filter_upwards [] with z
    intro t ht
    have hab : 1+|a t+b t*z| ≤ (1+2*K)*(1+|z|) := by
      have h := heat_affine_bound (a t) (b t) z
      have hp := mul_le_mul_of_nonneg_right (show 1+|a t|+|b t| ≤ 1+2*K by linarith [ht.2.1,ht.2.2.1])
        (show 0 ≤ 1+|z| by positivity)
      exact h.trans hp
    have hd : |a' t+b' t*z| ≤ K*(1+|z|) := by
      have h := abs_add_le (a' t) (b' t*z)
      rw [abs_mul] at h
      have hp := mul_le_mul_of_nonneg_right ht.2.2.2.2 (abs_nonneg z)
      nlinarith [ht.2.2.2.1]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |v' (a t+b t*z)| * |a' t+b' t*z| ≤
          (C*((1+2*K)*(1+|z|))^2)*(K*(1+|z|)) :=
        mul_le_mul ((hgrow _).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hab 2) hC)) hd (abs_nonneg _) (by positivity)
      _ = C*(1+2*K)^2*K*(1+|z|)^3 := by ring
  · filter_upwards [] with z
    intro t ht
    exact (hdv _).comp t ((hda t ht.1).add ((hdb t ht.1).mul_const z))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma gaussianHeat_space_derivative {v v' : ℝ → ℝ}
    (hv : Measurable v) (hv' : Measurable v')
    (hg : HeatQuadraticGrowth v) (hg' : HeatQuadraticGrowth v')
    (hdv : ∀ x, HasDerivAt v (v' x) x) (T x : ℝ) :
    HasDerivAt (gaussianHeat v T) (gaussianHeat v' T x) x := by
  have hh := heat_curve_derivative hv hv' hg hg' hdv
    (a := id) (b := fun _ => Real.sqrt T) (a' := fun _ => 1) (b' := fun _ => 0)
    (t₀ := x) (s := univ) univ_mem
    (fun t _ => hasDerivAt_id t) (fun t _ => hasDerivAt_const t _)
    continuousAt_const continuousAt_const
  convert hh using 1 <;> first | rfl | simp only [gaussianHeat, id_eq, zero_mul, add_zero, mul_one]

lemma gaussianHeat_time_derivative {v v' v'' : ℝ → ℝ}
    (hv : Measurable v) (hv' : Measurable v') (hv'' : Measurable v'')
    (hg : HeatQuadraticGrowth v) (hg' : HeatQuadraticGrowth v') (hg'' : HeatQuadraticGrowth v'')
    (hdv : ∀ x, HasDerivAt v (v' x) x) (hdv' : ∀ x, HasDerivAt v' (v'' x) x)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    HasDerivAt (fun r => gaussianHeat v r x) ((1/2:ℝ)*gaussianHeat v'' T x) T := by
  have hs : Ioi (0:ℝ) ∈ 𝓝 T := Ioi_mem_nhds hT
  have hc : ContinuousAt (fun t : ℝ => (2*Real.sqrt t)⁻¹) T :=
    (continuousAt_const.mul (Real.continuous_sqrt.continuousAt)).inv₀ (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hT))
  have hh := heat_curve_derivative hv hv' hg hg' hdv
    (a := fun _ => x) (b := Real.sqrt) (a' := fun _ => 0) (b' := fun t => (2*Real.sqrt t)⁻¹)
    hs (fun t _ => hasDerivAt_const t _) (fun t ht => by simpa only [one_div] using Real.hasDerivAt_sqrt (show t ≠ 0 from ht.ne'))
    continuousAt_const hc
  have hi := standardGaussian_integration_by_parts
    (f := fun z => v' (x+Real.sqrt T*z))
    (f' := fun z => v'' (x+Real.sqrt T*z)*Real.sqrt T)
    (fun z => by
      convert (hdv' _).comp z ((hasDerivAt_const z x).add
        ((hasDerivAt_id z).const_mul (Real.sqrt T))) using 1 <;> first | rfl | simp)
    (heat_affine_quadratic_integrable hv' hg' x (Real.sqrt T))
    ((heat_affine_quadratic_integrable hv'' hg'' x (Real.sqrt T)).mul_const _)
    (heat_affine_mul_integrable hv' hg' x (Real.sqrt T))
  have he : (∫ z : ℝ, v' (x+Real.sqrt T*z)*(0+(2*Real.sqrt T)⁻¹*z) ∂gaussianReal 0 1) =
      (1/2:ℝ)*gaussianHeat v'' T x := by
    calc
      _ = (2*Real.sqrt T)⁻¹*(∫ z : ℝ, z*v' (x+Real.sqrt T*z) ∂gaussianReal 0 1) := by
        rw [← integral_const_mul]; congr 1; funext z; ring
      _ = (2*Real.sqrt T)⁻¹*((∫ z : ℝ, v'' (x+Real.sqrt T*z) ∂gaussianReal 0 1)*Real.sqrt T) := by
        rw [hi, integral_mul_const]
      _ = (1/2:ℝ)*gaussianHeat v'' T x := by
        dsimp [gaussianHeat]; field_simp [Real.sqrt_ne_zero'.mpr hT]
  rw [he] at hh
  exact hh

end MicroscopicJamming

end

end OAI
