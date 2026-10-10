import Mathlib

namespace OAI

/-! Cumulative. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology

namespace SKFluctuations.PreKopa

def cumulative (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Iic x, f t

theorem hasDerivAt_cumulative {f : ℝ → ℝ} (hi : Integrable f)
    (hc : Continuous f) (x : ℝ) : HasDerivAt (cumulative f) (f x) x := by
  have heq : cumulative f = fun y => cumulative f 0 + ∫ t in (0 : ℝ)..y, f t := by
    funext y
    have h := intervalIntegral.integral_Iic_sub_Iic
      (a := (0 : ℝ)) (b := y) hi.integrableOn hi.integrableOn
    dsimp [cumulative]
    linarith
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

theorem continuous_cumulative {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f) :
    Continuous (cumulative f) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_cumulative hi hc x).continuousAt

theorem strictMono_cumulative {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (hp : ∀ x, 0 < f x) : StrictMono (cumulative f) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_cumulative hi hc x).deriv]
  exact hp x

theorem tendsto_cumulative_atBot (f : ℝ → ℝ) :
    Tendsto (cumulative f) atBot (𝓝 0) := tendsto_integral_Iic_zero tendsto_id

theorem tendsto_cumulative_atTop {f : ℝ → ℝ} (hi : Integrable f) :
    Tendsto (cumulative f) atTop (𝓝 (∫ t, f t)) := by
  exact (aecover_Iic (μ := volume) (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)).integral_tendsto_of_countably_generated hi

theorem cumulative_mem_unitInterval {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (hp : ∀ x, 0 < f x) (h1 : ∫ t, f t = 1) (x : ℝ) :
    cumulative f x ∈ Ioo (0 : ℝ) 1 := by
  have hm := strictMono_cumulative hi hc hp
  have hn (y : ℝ) : 0 ≤ cumulative f y := integral_nonneg fun z => (hp z).le
  have hb (y : ℝ) : cumulative f y ≤ 1 := by
    rw [← h1]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun z => (hp z).le)
  exact ⟨lt_of_le_of_lt (hn (x - 1)) (hm (by linarith)),
    lt_of_lt_of_le (hm (show x < x + 1 by linarith)) (hb (x + 1))⟩

theorem cumulative_surj_unitInterval {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (h1 : ∫ t, f t = 1) : SurjOn (cumulative f) univ (Ioo (0 : ℝ) 1) := by
  have htop := tendsto_cumulative_atTop hi
  rw [h1] at htop
  exact isPreconnected_univ.intermediate_value_Ioo (by simp) (by simp)
    (continuous_cumulative hi hc).continuousOn (tendsto_cumulative_atBot f) htop

 
def cumulativeIso {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (hp : ∀ x, 0 < f x) (h1 : ∫ t, f t = 1) : ℝ ≃o Ioo (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective
    (f := fun x => (⟨cumulative f x, cumulative_mem_unitInterval hi hc hp h1 x⟩ : Ioo (0 : ℝ) 1))
    (fun _ _ h => strictMono_cumulative hi hc hp h)
    (fun y => by
      obtain ⟨x, _, hx⟩ := cumulative_surj_unitInterval hi hc h1 y.property
      exact ⟨x, Subtype.ext hx⟩)

@[simp] theorem cumulativeIso_apply {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (hp : ∀ x, 0 < f x) (h1 : ∫ t, f t = 1) (x : ℝ) :
    (cumulativeIso hi hc hp h1 x : ℝ) = cumulative f x := rfl

 
def transportIso {f g : ℝ → ℝ} (hfi : Integrable f) (hfc : Continuous f)
    (hfp : ∀ x, 0 < f x) (hf1 : ∫ x, f x = 1)
    (hgi : Integrable g) (hgc : Continuous g) (hgp : ∀ x, 0 < g x)
    (hg1 : ∫ x, g x = 1) : ℝ ≃o ℝ :=
  (cumulativeIso hfi hfc hfp hf1).trans (cumulativeIso hgi hgc hgp hg1).symm

theorem cumulative_transport {f g : ℝ → ℝ} (hfi : Integrable f) (hfc : Continuous f)
    (hfp : ∀ x, 0 < f x) (hf1 : ∫ x, f x = 1)
    (hgi : Integrable g) (hgc : Continuous g) (hgp : ∀ x, 0 < g x)
    (hg1 : ∫ x, g x = 1) (x : ℝ) :
    cumulative g (transportIso hfi hfc hfp hf1 hgi hgc hgp hg1 x) = cumulative f x := by
  exact congrArg Subtype.val ((cumulativeIso hgi hgc hgp hg1).apply_symm_apply
    (cumulativeIso hfi hfc hfp hf1 x))

theorem hasDerivAt_transport {f g : ℝ → ℝ} (hfi : Integrable f) (hfc : Continuous f)
    (hfp : ∀ x, 0 < f x) (hf1 : ∫ x, f x = 1)
    (hgi : Integrable g) (hgc : Continuous g) (hgp : ∀ x, 0 < g x)
    (hg1 : ∫ x, g x = 1) (x : ℝ) :
    HasDerivAt (transportIso hfi hfc hfp hf1 hgi hgc hgp hg1)
      (f x / g (transportIso hfi hfc hfp hf1 hgi hgc hgp hg1 x)) x := by
  apply HasDerivAt.of_comp_left (transportIso hfi hfc hfp hf1 hgi hgc hgp hg1).continuous.continuousAt
    (hasDerivAt_cumulative hgi hgc _) (hasDerivAt_cumulative hfi hfc _) (ne_of_gt (hgp _))
  exact Filter.Eventually.of_forall (cumulative_transport hfi hfc hfp hf1 hgi hgc hgp hg1)

 
theorem transport_jacobian_bound {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hp : 0 < p) (hq : 0 < q) :
    p ≤ (a + b * (p / q)) * (p ^ a * q ^ b) := by
  have hg := Real.geom_mean_le_arith_mean2_weighted ha hb
    (show (0 : ℝ) ≤ 1 by norm_num) (show 0 ≤ p / q by positivity) hab
  simp only [Real.one_rpow, one_mul, mul_one] at hg
  have he : (p / q) ^ b * (p ^ a * q ^ b) = p := by
    rw [Real.div_rpow hp.le hq.le]
    calc
      p ^ b / q ^ b * (p ^ a * q ^ b) = p ^ a * p ^ b := by
        field_simp
      _ = p ^ (a + b) := (Real.rpow_add hp a b).symm
      _ = p := by rw [hab, Real.rpow_one]
  calc
    p = (p / q) ^ b * (p ^ a * q ^ b) := he.symm
    _ ≤ (a + b * (p / q)) * (p ^ a * q ^ b) :=
      mul_le_mul_of_nonneg_right hg (by positivity)

 

theorem prekopaLeindler_normalized {f g h : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hfi : Integrable f) (hfc : Continuous f) (hfp : ∀ x, 0 < f x) (hf1 : ∫ x, f x = 1)
    (hgi : Integrable g) (hgc : Continuous g) (hgp : ∀ x, 0 < g x) (hg1 : ∫ x, g x = 1)
    (hhi : Integrable h) (hhp : ∀ x, 0 ≤ h x)
    (hpoint : ∀ x y, f x ^ a * g y ^ b ≤ h (a * x + b * y)) :
    1 ≤ ∫ x, h x := by
  let T := transportIso hfi hfc hfp hf1 hgi hgc hgp hg1
  let S : ℝ → ℝ := fun x => a * x + b * T x
  let S' : ℝ → ℝ := fun x => a + b * (f x / g (T x))
  have hd (x : ℝ) : HasDerivAt S (S' x) x := by
    convert! ((hasDerivAt_id x).const_mul a).add
      ((hasDerivAt_transport hfi hfc hfp hf1 hgi hgc hgp hg1 x).const_mul b) using 1
    simp [S', T]
  have hpos (x : ℝ) : 0 < S' x := by
    dsimp [S']
    exact add_pos ha (mul_pos hb (div_pos (hfp x) (hgp (T x))))
  have hm : StrictMono S := by
    apply strictMono_of_deriv_pos
    intro x
    rw [(hd x).deriv]
    exact hpos x
  have hi : Integrable (fun x => |S' x| • h (S x)) := by
    simpa only [integrableOn_univ] using
      (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
        (fun x _ => (hd x).hasDerivWithinAt) hm.injective.injOn h).mp hhi.integrableOn
  calc
    1 = ∫ x, f x := hf1.symm
    _ ≤ ∫ x, |S' x| • h (S x) := by
      apply integral_mono hfi hi
      intro x
      change f x ≤ |S' x| * h (S x)
      rw [abs_of_pos (hpos x)]
      exact (transport_jacobian_bound ha.le hb.le hab (hfp x) (hgp (T x))).trans
        (mul_le_mul_of_nonneg_left (hpoint x (T x)) (hpos x).le)
    _ = ∫ x in S '' univ, h x := by
      symm
      simpa only [Measure.restrict_univ] using
        integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
          (fun x _ => (hd x).hasDerivWithinAt) hm.injective.injOn h
    _ ≤ ∫ x, h x := setIntegral_le_integral hhi (Filter.Eventually.of_forall hhp)

 
theorem integral_strictlyPositive {α : Type*} [MeasureSpace α]
    [NeZero (volume : Measure α)] {f : α → ℝ} (hi : Integrable f)
    (hp : ∀ x, 0 < f x) : 0 < ∫ x, f x := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hi]
  have he : Function.support f = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact ne_of_gt (hp x)
  simp [he, NeZero.ne (volume : Measure α)]

 

theorem prekopaLeindler {f g h : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hfi : Integrable f) (hfc : Continuous f) (hfp : ∀ x, 0 < f x)
    (hgi : Integrable g) (hgc : Continuous g) (hgp : ∀ x, 0 < g x)
    (hhi : Integrable h) (hhp : ∀ x, 0 ≤ h x)
    (hpoint : ∀ x y, f x ^ a * g y ^ b ≤ h (a * x + b * y)) :
    (∫ x, f x) ^ a * (∫ x, g x) ^ b ≤ ∫ x, h x := by
  let A := ∫ x, f x
  let B := ∫ x, g x
  let C := A ^ a * B ^ b
  have hA : 0 < A := integral_strictlyPositive hfi hfp
  have hB : 0 < B := integral_strictlyPositive hgi hgp
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos hA a) (Real.rpow_pos_of_pos hB b)
  have hfn : ∫ x, f x / A = 1 := by rw [integral_div]; exact div_self (ne_of_gt hA)
  have hgn : ∫ x, g x / B = 1 := by rw [integral_div]; exact div_self (ne_of_gt hB)
  have hn := prekopaLeindler_normalized ha hb hab
    (hfi.div_const A) (hfc.div_const A) (fun x => div_pos (hfp x) hA) hfn
    (hgi.div_const B) (hgc.div_const B) (fun x => div_pos (hgp x) hB) hgn
    (hhi.div_const C) (fun x => div_nonneg (hhp x) hC.le) (fun x y => by
      rw [Real.div_rpow (hfp x).le hA.le, Real.div_rpow (hgp y).le hB.le]
      rw [div_mul_div_comm]
      exact div_le_div_of_nonneg_right (hpoint x y) hC.le)
  rw [integral_div] at hn
  simpa only [one_mul] using (le_div_iff₀ hC).mp hn

 
def gaussianEnvelope {n : ℕ} (c : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, Real.exp (-c * (x i) ^ 2)

@[simp] theorem gaussianEnvelope_cons {n : ℕ} (c t : ℝ) (x : Fin n → ℝ) :
    gaussianEnvelope c (Fin.cons t x) = Real.exp (-c * t ^ 2) * gaussianEnvelope c x := by
  simp [gaussianEnvelope, Fin.prod_univ_succ]

theorem gaussianEnvelope_pos {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    0 < gaussianEnvelope c x := Finset.prod_pos fun _ _ => Real.exp_pos _

theorem gaussianEnvelope_le_one {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (x : Fin n → ℝ) :
    gaussianEnvelope c x ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i _; exact (Real.exp_pos _).le
  · intro i _; apply Real.exp_le_one_iff.mpr; nlinarith [sq_nonneg (x i)]

theorem integrable_gaussianEnvelope {n : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (gaussianEnvelope (n := n) c) :=
  Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq hc

theorem continuous_cons {n : ℕ} :
    Continuous (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (continuous_fst : Continuous (Prod.fst : ℝ × (Fin n → ℝ) → ℝ))
  · simpa only [Fin.cons_succ, Function.comp_def] using (continuous_apply j).comp
      (continuous_snd : Continuous (Prod.snd : ℝ × (Fin n → ℝ) → (Fin n → ℝ)))

 

def GaussianDominated {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x, ‖f x‖ ≤ C * gaussianEnvelope c x

theorem GaussianDominated.integrable {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : GaussianDominated f) : Integrable f := by
  obtain ⟨hc, C, c, _, hcp, hb⟩ := hf
  exact ((integrable_gaussianEnvelope hcp).const_mul C).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem GaussianDominated.slice {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : GaussianDominated f) (t : ℝ) : GaussianDominated (fun x => f (Fin.cons t x)) := by
  obtain ⟨hc, C, c, hC, hcp, hb⟩ := hf
  refine ⟨hc.comp (continuous_cons.comp (continuous_const.prodMk continuous_id)),
    C * Real.exp (-c * t ^ 2), c, mul_pos hC (Real.exp_pos _), hcp, ?_⟩
  intro x
  simpa only [gaussianEnvelope_cons, mul_assoc] using hb (Fin.cons t x)

def firstMarginal {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, f (Fin.cons t x)

theorem GaussianDominated.continuous_firstMarginal {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : GaussianDominated f) :
    Continuous (firstMarginal f) := by
  obtain ⟨hc, C, c, hC, hcp, hb⟩ := hf
  apply continuous_of_dominated
    (bound := fun x : Fin n → ℝ => C * gaussianEnvelope c x)
  · intro t
    exact (hc.comp (continuous_cons.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · intro t
    apply Filter.Eventually.of_forall
    intro x
    apply (hb (Fin.cons t x)).trans
    rw [gaussianEnvelope_cons]
    have ht : Real.exp (-c * t ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg t]
    calc
      C * (Real.exp (-c * t ^ 2) * gaussianEnvelope c x) ≤
          C * (1 * gaussianEnvelope c x) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right ht (gaussianEnvelope_pos c x).le) hC.le
      _ = C * gaussianEnvelope c x := by ring
  · exact (integrable_gaussianEnvelope hcp).const_mul C
  · apply Filter.Eventually.of_forall
    intro x
    exact hc.comp (continuous_cons.comp (continuous_id.prodMk continuous_const))

theorem GaussianDominated.integral_firstMarginal {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : GaussianDominated f) :
    ∫ t, firstMarginal f t = ∫ x, f x := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hi := (hp.integrable_comp_emb e.symm.measurableEmbedding).mpr hf.integrable
  have he (p : ℝ × (Fin n → ℝ)) : e.symm p = Fin.cons p.1 p.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  change Integrable (fun p => f (e.symm p)) at hi
  have hi' : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2)) := by
    simpa only [he] using hi
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) := integral_integral hi'
    _ = ∫ x, f x := by
      have hai : (∫ p, f (e.symm p)) = ∫ x, f x := hp.integral_comp' f
      simpa only [he] using hai

theorem GaussianDominated.firstMarginal_bound {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : GaussianDominated f)
    {C c : ℝ} (hcp : 0 < c) (hb : ∀ x, ‖f x‖ ≤ C * gaussianEnvelope c x) (t : ℝ) :
    ‖firstMarginal f t‖ ≤ (C * ∫ x : Fin n → ℝ, gaussianEnvelope c x) *
      Real.exp (-c * t ^ 2) := by
  calc
    _ ≤ ∫ x : Fin n → ℝ, ‖f (Fin.cons t x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : Fin n → ℝ, (C * Real.exp (-c * t ^ 2)) * gaussianEnvelope c x := by
      apply integral_mono (hf.slice t).integrable.norm
        ((integrable_gaussianEnvelope hcp).const_mul _)
      intro x
      simpa only [gaussianEnvelope_cons, mul_assoc] using hb (Fin.cons t x)
    _ = _ := by rw [integral_const_mul]; ring

theorem GaussianDominated.integrable_firstMarginal {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : GaussianDominated f) :
    Integrable (firstMarginal f) := by
  obtain ⟨C, c, _, hcp, hb⟩ := hf.2
  exact ((integrable_exp_neg_mul_sq hcp).const_mul
    (C * ∫ x : Fin n → ℝ, gaussianEnvelope c x)).mono'
    hf.continuous_firstMarginal.aestronglyMeasurable
    (Filter.Eventually.of_forall (hf.firstMarginal_bound hcp hb))

theorem integral_finZero (f : (Fin 0 → ℝ) → ℝ) : ∫ x, f x = f 0 := by
  rw [integral_unique]
  have hv : volume (univ : Set (Fin 0 → ℝ)) = 1 :=
    Measure.pi_empty_univ (fun _ : Fin 0 => (volume : Measure ℝ))
  simp only [Measure.real, hv, ENNReal.toReal_one, one_smul]
  exact congrArg f (Subsingleton.elim _ _)

 

theorem prekopaLeindler_fin (n : ℕ) {f g h : (Fin n → ℝ) → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hf : GaussianDominated f) (hg : GaussianDominated g) (hh : GaussianDominated h)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (hhp : ∀ x, 0 ≤ h x)
    (hpoint : ∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y)) :
    (∫ x, f x) ^ a * (∫ x, g x) ^ b ≤ ∫ x, h x := by
  induction n with
  | zero =>
    simpa only [integral_finZero, smul_zero, add_zero] using hpoint 0 0
  | succ n ih =>
    rw [← hf.integral_firstMarginal, ← hg.integral_firstMarginal,
      ← hh.integral_firstMarginal]
    apply prekopaLeindler ha hb hab
      hf.integrable_firstMarginal hf.continuous_firstMarginal
      (fun t => integral_strictlyPositive (hf.slice t).integrable (fun x => hfp _))
      hg.integrable_firstMarginal hg.continuous_firstMarginal
      (fun t => integral_strictlyPositive (hg.slice t).integrable (fun x => hgp _))
      hh.integrable_firstMarginal
      (fun t => integral_nonneg fun x => hhp _)
    intro t u
    apply ih (hf.slice t) (hg.slice u) (hh.slice (a * t + b * u))
      (fun x => hfp _) (fun x => hgp _) (fun x => hhp _)
    intro x y
    have he : a • (Fin.cons t x : Fin (n + 1) → ℝ) + b • Fin.cons u y =
        Fin.cons (a * t + b * u) (a • x + b • y) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    simpa only [he] using hpoint (Fin.cons t x) (Fin.cons u y)

 
def LogConcave {E : Type*} [Add E] [SMul ℝ E] (f : E → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∀ (x y : E) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    f x ^ a * f y ^ b ≤ f (a • x + b • y)

theorem logConcave_exp_neg {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {V : E → ℝ} (hV : ConvexOn ℝ univ V) : LogConcave (fun x => Real.exp (-V x)) := by
  refine ⟨fun x => (Real.exp_pos _).le, ?_⟩
  intro x y a b ha hb hab
  have hc := hV.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hc
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem logConcave_marginal {n : ℕ} {F : ℝ × (Fin n → ℝ) → ℝ}
    (hF : LogConcave F) (hp : ∀ z x, 0 < F (z, x))
    (hG : ∀ z, GaussianDominated (fun x => F (z, x))) :
    LogConcave (fun z => ∫ x, F (z, x)) := by
  refine ⟨fun z => integral_nonneg fun x => hF.1 (z, x), ?_⟩
  intro z w a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · simp_all
  obtain rfl | hb' := hb.eq_or_lt
  · simp_all
  apply prekopaLeindler_fin n ha' hb' hab (hG z) (hG w) (hG (a * z + b * w))
    (hp z) (hp w) (fun x => hF.1 _) (fun x y => ?_)
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using
    hF.2 (z, x) (w, y) a b ha hb hab

theorem logConcave_integral_exp_neg {n : ℕ} {V : ℝ × (Fin n → ℝ) → ℝ}
    (hV : ConvexOn ℝ univ V)
    (hG : ∀ z, GaussianDominated (fun x => Real.exp (-V (z, x)))) :
    LogConcave (fun z => ∫ x, Real.exp (-V (z, x))) :=
  logConcave_marginal (logConcave_exp_neg hV) (fun _ _ => Real.exp_pos _) hG

 
theorem LogConcave.of_tendsto {E : Type*} [Add E] [SMul ℝ E]
    {F : ℕ → E → ℝ} {f : E → ℝ} (hF : ∀ n, LogConcave (F n))
    (hf : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) : LogConcave f := by
  refine ⟨fun x => ge_of_tendsto (hf x) (Filter.Eventually.of_forall fun n => (hF n).1 x), ?_⟩
  intro x y a b ha hb hab
  exact le_of_tendsto_of_tendsto
    (((hf x).rpow_const (Or.inr ha)).mul ((hf y).rpow_const (Or.inr hb)))
    (hf (a • x + b • y)) (Filter.Eventually.of_forall fun n => (hF n).2 x y a b ha hb hab)

end SKFluctuations.PreKopa

namespace SKFluctuations.PreKopa

 
def epigraphPotential {n : ℕ} (F : (Fin n → ℝ) → ℝ) (c : ℝ)
    (v : Fin n → ℝ) (k : ℝ) (p : ℝ × (Fin n → ℝ)) : ℝ :=
  c * ∑ i, (p.2 i) ^ 2 - ∑ i, v i * p.2 i + p.1 + k * max (F p.2 - p.1) 0

 
theorem convexOn_epigraphPotential {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ConvexOn ℝ univ F) {c k : ℝ} (hc : 0 ≤ c) (hk : 0 ≤ k)
    (v : Fin n → ℝ) : ConvexOn ℝ univ (epigraphPotential F c v k) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hsq (i : Fin n) : (a * x.2 i + b * y.2 i) ^ 2 ≤
      a * (x.2 i) ^ 2 + b * (y.2 i) ^ 2 := by
    simpa only [smul_eq_mul] using
      ((show Even (2 : ℕ) by decide).convexOn_pow (𝕜 := ℝ)).2
        (mem_univ (x.2 i)) (mem_univ (y.2 i)) ha hb hab
  have hsum : (∑ i, (a * x.2 i + b * y.2 i) ^ 2) ≤
      a * (∑ i, (x.2 i) ^ 2) + b * (∑ i, (y.2 i) ^ 2) := by
    simpa only [Finset.sum_add_distrib, Finset.mul_sum] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsq i)
  have hlin : (∑ i, v i * (a * x.2 i + b * y.2 i)) =
      a * (∑ i, v i * x.2 i) + b * (∑ i, v i * y.2 i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hfc : F (a • x.2 + b • y.2) ≤ a * F x.2 + b * F y.2 :=
    hF.2 (mem_univ _) (mem_univ _) ha hb hab
  have hmax : max (F (a • x.2 + b • y.2) - (a * x.1 + b * y.1)) 0 ≤
      a * max (F x.2 - x.1) 0 + b * max (F y.2 - y.1) 0 := by
    apply max_le
    · have h1 := mul_le_mul_of_nonneg_left (le_max_left (F x.2 - x.1) 0) ha
      have h2 := mul_le_mul_of_nonneg_left (le_max_left (F y.2 - y.1) 0) hb
      linarith
    · positivity
  have hs := mul_le_mul_of_nonneg_left hsum hc
  have hm := mul_le_mul_of_nonneg_left hmax hk
  simp only [epigraphPotential, Prod.smul_fst, Prod.fst_add, Prod.smul_snd,
    Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hlin]
  change c * (∑ i, (a * x.2 i + b * y.2 i) ^ 2) -
      (a * (∑ i, v i * x.2 i) + b * (∑ i, v i * y.2 i)) +
      (a * x.1 + b * y.1) + k * max (F (a • x.2 + b • y.2) -
      (a * x.1 + b * y.1)) 0 ≤ _
  linarith

 
theorem epigraph_exponential_bound {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    {c k : ℝ} (hc : 0 < c) (hk : 0 ≤ k) (v : Fin n → ℝ)
    (z : ℝ) (x : Fin n → ℝ) :
    ‖Real.exp (-epigraphPotential F c v k (z, x))‖ ≤
      Real.exp ((∑ i, (v i) ^ 2 / (2 * c)) - z) * gaussianEnvelope (c / 2) x := by
  have hsq (i : Fin n) : -c * (x i) ^ 2 + v i * x i ≤
      (v i) ^ 2 / (2 * c) - c / 2 * (x i) ^ 2 := by
    have h := sq_nonneg (c * x i - v i)
    have hdiv : (v i) ^ 2 / (2 * c) * (2 * c) = (v i) ^ 2 :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsq i)
  have hp : 0 ≤ k * max (F x - z) 0 := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he : gaussianEnvelope (c / 2) x = Real.exp (∑ i, -(c / 2) * (x i) ^ 2) := by
    simp only [gaussianEnvelope, Real.exp_sum]
  rw [he, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [epigraphPotential]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, neg_mul,
    Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum ⊢
  linarith

theorem gaussianDominated_epigraphApprox {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : Continuous F) {c k : ℝ} (hc : 0 < c) (hk : 0 ≤ k)
    (v : Fin n → ℝ) (z : ℝ) :
    GaussianDominated (fun x => Real.exp (-epigraphPotential F c v k (z, x))) := by
  refine ⟨?_, Real.exp ((∑ i, (v i) ^ 2 / (2 * c)) - z), c / 2,
    Real.exp_pos _, half_pos hc, epigraph_exponential_bound F hc hk v z⟩
  unfold epigraphPotential
  fun_prop

def epigraphMarginal {n : ℕ} (F : (Fin n → ℝ) → ℝ) (c : ℝ)
    (v : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∫ x, if F x ≤ z then Real.exp (-(c * ∑ i, (x i) ^ 2 - ∑ i, v i * x i + z)) else 0

 
theorem tendsto_epigraphApprox {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : Continuous F) {c : ℝ} (hc : 0 < c) (v : Fin n → ℝ) (z : ℝ) :
    Tendsto (fun k : ℕ => ∫ x, Real.exp (-epigraphPotential F c v (k : ℝ) (z, x)))
      atTop (𝓝 (epigraphMarginal F c v z)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => Real.exp ((∑ i, (v i) ^ 2 / (2 * c)) - z) * gaussianEnvelope (c / 2) x)
  · intro k
    exact (gaussianDominated_epigraphApprox hF hc (Nat.cast_nonneg k) v z).1.aestronglyMeasurable
  · exact (integrable_gaussianEnvelope (half_pos hc)).const_mul _
  · intro k
    exact Filter.Eventually.of_forall (epigraph_exponential_bound F hc (Nat.cast_nonneg k) v z)
  · apply Filter.Eventually.of_forall
    intro x
    by_cases hx : F x ≤ z
    · have hm : max (F x - z) 0 = 0 := max_eq_right (sub_nonpos.mpr hx)
      simp only [hx, ite_true, epigraphPotential, hm, mul_zero, add_zero]
      exact tendsto_const_nhds
    · have hp : 0 < F x - z := sub_pos.mpr (lt_of_not_ge hx)
      have hm : max (F x - z) 0 = F x - z := max_eq_left hp.le
      have ht : Tendsto (fun k : ℕ => Real.exp (-((k : ℝ) * (F x - z))))
          atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hp)
      have he (k : ℕ) : Real.exp (-epigraphPotential F c v (k : ℝ) (z, x)) =
          Real.exp (-(c * ∑ i, (x i) ^ 2 - ∑ i, v i * x i + z)) *
            Real.exp (-((k : ℝ) * (F x - z))) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [epigraphPotential]
        rw [hm]
        ring
      simp only [hx, ite_false, he]
      simpa only [mul_zero] using tendsto_const_nhds.mul ht

 

theorem logConcave_epigraphMarginal {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hFc : Continuous F) (hFv : ConvexOn ℝ univ F) {c : ℝ} (hc : 0 < c)
    (v : Fin n → ℝ) : LogConcave (epigraphMarginal F c v) := by
  apply LogConcave.of_tendsto
    (F := fun k : ℕ => fun z => ∫ x, Real.exp (-epigraphPotential F c v (k : ℝ) (z, x)))
  · intro k
    exact logConcave_integral_exp_neg
      (convexOn_epigraphPotential hFv hc.le (Nat.cast_nonneg k) v)
      (gaussianDominated_epigraphApprox hFc hc (Nat.cast_nonneg k) v)
  · exact tendsto_epigraphApprox hFc hc v

end SKFluctuations.PreKopa

namespace SKFluctuations.PreKopa
open ProbabilityTheory

 
def standardGaussianPDF {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

theorem standardGaussianPDF_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ standardGaussianPDF x := Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

theorem integrable_standardGaussianPDF {ι : Type*} [Fintype ι] :
    Integrable (standardGaussianPDF (ι := ι)) :=
  Integrable.fintype_prod fun _ => integrable_gaussianPDFReal _ _

 
theorem standardGaussian_pi_withDensity {ι : Type*} [Fintype ι] :
    (Measure.pi fun _ : ι => gaussianReal 0 1) =
      volume.withDensity (fun x => ENNReal.ofReal (standardGaussianPDF x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_standardGaussianPDF.restrict
    (Filter.Eventually.of_forall standardGaussianPDF_nonneg)]
  change ENNReal.ofReal (∫ x, standardGaussianPDF x ∂
    (Measure.pi fun _ : ι => (volume : Measure ℝ)).restrict (univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  rw [show (∫ x, standardGaussianPDF x ∂Measure.pi (fun i => volume.restrict (s i))) =
      ∏ i, ∫ x in s i, gaussianPDFReal 0 1 x from integral_fintype_prod_eq_prod _]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg _ _))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0) (s i)).symm

theorem standardGaussianPDF_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    standardGaussianPDF x = (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
      Real.exp (-((1 : ℝ) / 2) * ∑ i, (x i) ^ 2) := by
  unfold standardGaussianPDF
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem LogConcave.const_mul {E : Type*} [Add E] [SMul ℝ E]
    {f : E → ℝ} (hf : LogConcave f) {C : ℝ} (hC : 0 < C) :
    LogConcave (fun x => C * f x) := by
  refine ⟨fun x => mul_nonneg hC.le (hf.1 x), ?_⟩
  intro x y a b ha hb hab
  rw [Real.mul_rpow hC.le (hf.1 x), Real.mul_rpow hC.le (hf.1 y)]
  calc
    C ^ a * f x ^ a * (C ^ b * f y ^ b) = (C ^ a * C ^ b) * (f x ^ a * f y ^ b) := by ring
    _ = C * (f x ^ a * f y ^ b) := by rw [← Real.rpow_add hC, hab, Real.rpow_one]
    _ ≤ C * f (a • x + b • y) := mul_le_mul_of_nonneg_left (hf.2 x y a b ha hb hab) hC.le

 
def finiteEpigraphMarginal {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℝ) (c : ℝ)
    (v : ι → ℝ) (z : ℝ) : ℝ :=
  ∫ x, if F x ≤ z then Real.exp (-(c * ∑ i, (x i) ^ 2 - ∑ i, v i * x i + z)) else 0

theorem logConcave_finiteEpigraphMarginal {ι : Type*} [Fintype ι]
    {F : (ι → ℝ) → ℝ} (hFc : Continuous F) (hFv : ConvexOn ℝ univ F)
    {c : ℝ} (hc : 0 < c) (v : ι → ℝ) : LogConcave (finiteEpigraphMarginal F c v) := by
  let e := Fintype.equivFin ι
  let A : (Fin (Fintype.card ι) → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun x i => x (e i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hAc : Continuous A := by
    change Continuous (fun (x : Fin (Fintype.card ι) → ℝ) (i : ι) => x (e i))
    fun_prop
  have hAv : ConvexOn ℝ univ (F ∘ A) := by
    simpa only [preimage_univ] using hFv.comp_linearMap A
  have h := logConcave_epigraphMarginal (hFc.comp hAc) hAv hc (fun i => v (e.symm i))
  have he (z : ℝ) : finiteEpigraphMarginal F c v z =
      epigraphMarginal (F ∘ A) c (fun i => v (e.symm i)) z := by
    have hp := volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e.symm
    rw [finiteEpigraphMarginal, ← hp.integral_comp']
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    have heA : MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm x = A x := by
      ext i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, A]
    dsimp only
    rw [heA]
    have hs : (∑ i : ι, (A x i) ^ 2) = ∑ i, (x i) ^ 2 :=
      e.sum_comp (fun i => (x i) ^ 2)
    have hv : (∑ i : ι, v i * A x i) = ∑ i, v (e.symm i) * x i := by
      simpa only [A, LinearMap.coe_mk, AddHom.coe_mk, e.symm_apply_apply] using e.sum_comp (fun i => v (e.symm i) * x i)
    simp only [hs, hv, Function.comp_apply]
  have he' : finiteEpigraphMarginal F c v = epigraphMarginal (F ∘ A) c (fun i => v (e.symm i)) :=
    funext he
  rw [he']
  exact h

 
def gaussianEpigraphTilt {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℝ)
    (v : ι → ℝ) (z : ℝ) : ℝ :=
  Real.exp (-z) * ∫ x, (if F x ≤ z then Real.exp (∑ i, v i * x i) else 0)
    ∂Measure.pi (fun _ : ι => gaussianReal 0 1)

theorem gaussianEpigraphTilt_eq {ι : Type*} [Fintype ι]
    (F : (ι → ℝ) → ℝ) (v : ι → ℝ) (z : ℝ) :
    gaussianEpigraphTilt F v z =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
        finiteEpigraphMarginal F ((1 : ℝ) / 2) v z := by
  rw [gaussianEpigraphTilt, standardGaussian_pi_withDensity]
  have hm : Measurable (fun x : ι → ℝ => ENNReal.ofReal (standardGaussianPDF x)) := by
    unfold standardGaussianPDF
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (standardGaussianPDF_nonneg _), smul_eq_mul]
  rw [← integral_const_mul]
  unfold finiteEpigraphMarginal
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [standardGaussianPDF_eq]
  by_cases hx : F x ≤ z
  · simp only [hx, ite_true]
    rw [mul_assoc, ← Real.exp_add]
    calc
      Real.exp (-z) * ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
          Real.exp (-((1 : ℝ) / 2) * ∑ i, (x i) ^ 2 + ∑ i, v i * x i)) =
          (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
            (Real.exp (-z) * Real.exp (-((1 : ℝ) / 2) * ∑ i, (x i) ^ 2 + ∑ i, v i * x i)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  · simp only [hx, ite_false, mul_zero]

 
theorem logConcave_gaussianEpigraphTilt {ι : Type*} [Fintype ι]
    {F : (ι → ℝ) → ℝ} (hFc : Continuous F) (hFv : ConvexOn ℝ univ F)
    (v : ι → ℝ) : LogConcave (gaussianEpigraphTilt F v) := by
  have he : gaussianEpigraphTilt F v = fun z =>
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
        finiteEpigraphMarginal F ((1 : ℝ) / 2) v z := funext (gaussianEpigraphTilt_eq F v)
  rw [he]
  exact (logConcave_finiteEpigraphMarginal hFc hFv (by norm_num : (0 : ℝ) < 1 / 2) v).const_mul
    (by positivity)

end SKFluctuations.PreKopa

end

end OAI
