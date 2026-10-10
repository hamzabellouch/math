import Mathlib
import OAI.Probability.IsingPerceptron.EnrichedFieldCap

namespace OAI

/-! Mem Lp Of Abs Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
lemma memLp_of_abs_bound {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasure μ] {F : A → ℝ} (hm : Measurable F) {K : ℝ}
    (hb : ∀ a, |F a| ≤ K) (p : ℝ≥0∞) : MemLp F p μ :=
  MemLp.of_bound hm.aestronglyMeasurable K
    (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a))

lemma integral_abs_le_bound {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsProbabilityMeasure μ] {F : A → ℝ} {K : ℝ}
    (hb : ∀ a, |F a| ≤ K) : |∫ a, F a ∂μ| ≤ K := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := K)
      (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a)))

lemma variance_le_of_oscillation {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsProbabilityMeasure μ] {F : A → ℝ} (hm : Measurable F) {K c : ℝ}
    (hb : ∀ a, |F a| ≤ K) (hc : 0 ≤ c) (ho : ∀ a b, |F a - F b| ≤ c) :
    variance F μ ≤ c ^ 2 := by
  have hLp := memLp_of_abs_bound hm hb 2 (μ := μ)
  have hi := hLp.integrable (by norm_num)
  have hcenter : ∀ a, |F a - ∫ b, F b ∂μ| ≤ c := by
    intro a
    have h := integral_abs_le_bound (μ := μ) (F := fun b => F a - F b) (ho a)
    simpa only [integral_sub (integrable_const _) hi, integral_const,
      probReal_univ, one_smul] using h
  rw [variance_eq_integral hm.aemeasurable]
  have hisq := (hLp.sub (memLp_const (∫ a, F a ∂μ))).integrable_sq
  have h := integral_mono hisq (integrable_const (c ^ 2)) (fun a =>
    sq_le_sq.mpr (by simpa only [abs_of_nonneg hc, Pi.sub_apply] using hcenter a))
  simpa using h

lemma variance_prod_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hm : Measurable F) {K c : ℝ} (hb : ∀ z, |F z| ≤ K)
    (hc : 0 ≤ c) (ho : ∀ b a a', |F (a, b) - F (a', b)| ≤ c) :
    variance F (μ.prod ν) ≤ c ^ 2 + variance (fun b => ∫ a, F (a, b) ∂μ) ν := by
  have hLp := memLp_of_abs_bound hm hb 2 (μ := μ.prod ν)
  have hGm : Measurable (fun b => ∫ a, F (a, b) ∂μ) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable
  have hGb : ∀ b, |∫ a, F (a, b) ∂μ| ≤ K := fun b =>
    integral_abs_le_bound (fun a => hb (a, b))
  have hGLp := memLp_of_abs_bound hGm hGb 2 (μ := ν)
  have hsec : ∀ b, (∫ a, F (a, b) ^ 2 ∂μ) ≤ c ^ 2 + (∫ a, F (a, b) ∂μ) ^ 2 := by
    intro b
    have hm' : Measurable (fun a => F (a, b)) := hm.comp (measurable_id.prodMk measurable_const)
    have h := variance_le_of_oscillation (μ := μ) hm' (fun a => hb (a, b)) hc (ho b)
    rw [variance_eq_sub (memLp_of_abs_bound hm' (fun a => hb (a, b)) 2)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hs := integral_mono hLp.integrable_sq.integral_prod_right
    ((integrable_const (c ^ 2)).add hGLp.integrable_sq) hsec
  simp only [Pi.add_apply] at hs
  rw [integral_add (integrable_const _) hGLp.integrable_sq, integral_const,
    probReal_univ, one_smul] at hs
  rw [variance_eq_sub hLp, variance_eq_sub hGLp]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hLp.integrable_sq,
    integral_prod_symm _ (hLp.integrable (by norm_num))]
  linarith

lemma variance_pi_boundedDifferences {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ)
    {F : (Fin n → A) → ℝ} (hm : Measurable F) {K c : ℝ}
    (hb : ∀ x, |F x| ≤ K) (hc : 0 ≤ c)
    (ho : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c) :
    variance F (Measure.pi (fun _ : Fin n => μ)) ≤ n * c ^ 2 := by
  induction n with
  | zero =>
    have hF : F = fun _ => F (fun i : Fin 0 => i.elim0) := by
      funext x
      congr 1
      funext i
      exact i.elim0
    rw [hF, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let ν := Measure.pi (fun _ : Fin n => μ)
    have hcons : Measurable (fun z : A × (Fin n → A) => (Fin.cons z.1 z.2 : Fin (n + 1) → A)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : A × (Fin n → A) → A))
      · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_snd : Measurable (Prod.snd : A × (Fin n → A) → (Fin n → A)))
    have hFm : Measurable (fun z : A × (Fin n → A) => F (Fin.cons z.1 z.2)) := hm.comp hcons
    have hGb : ∀ x, |∫ a, F (Fin.cons a x) ∂μ| ≤ K := fun x =>
      integral_abs_le_bound (fun a => hb (Fin.cons a x))
    have hGm : Measurable (fun x => ∫ a, F (Fin.cons a x) ∂μ) :=
      hFm.stronglyMeasurable.integral_prod_left'.measurable
    have hGosc : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) →
        |(∫ a, F (Fin.cons a x) ∂μ) - ∫ a, F (Fin.cons a y) ∂μ| ≤ c := by
      intro i x y hxy
      have hmsec : ∀ x : Fin n → A, Measurable (fun a => F (Fin.cons a x)) :=
        fun x => hFm.comp (measurable_id.prodMk measurable_const)
      have hisec : ∀ x : Fin n → A, Integrable (fun a => F (Fin.cons a x)) μ :=
        fun x => (memLp_of_abs_bound (hmsec x) (fun a => hb (Fin.cons a x)) 1).integrable le_rfl
      have h := integral_abs_le_bound (μ := μ) (F := fun a => F (Fin.cons a x) - F (Fin.cons a y))
        (fun a => ho i.succ (Fin.cons a x) (Fin.cons a y) (fun j => by
          refine Fin.cases ?_ (fun l => ?_) j
          · intro _; simp
          · intro hl
            simp only [Fin.cons_succ]
            exact hxy l (fun h => hl (congrArg Fin.succ h))))
      simpa only [integral_sub (hisec x) (hisec y)] using h
    have hsec : ∀ (x : Fin n → A) a a', |F (Fin.cons a x) - F (Fin.cons a' x)| ≤ c := by
      intro x a a'
      apply ho 0
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · intro h; exact (h rfl).elim
      · intro _; simp
    have hprod := variance_prod_le (μ := μ) (ν := ν) hFm
      (fun z => hb (Fin.cons z.1 z.2)) hc hsec
    have htail := ih hGm hGb hGosc
    have heq : variance (fun z : A × (Fin n → A) => F (Fin.cons z.1 z.2)) (μ.prod ν) =
        variance F (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
      have h := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).variance_fun_comp hm.aemeasurable
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using h
    rw [heq] at hprod
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp only [ν] at hprod
    nlinarith

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma finite_linear_vector_bound {m : ℕ} {a : I → Fin m → ℝ} {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) (g g' : Fin m → ℝ) :
    ‖(fun x => ∑ j, a x j * g j) - (fun x => ∑ j, a x j * g' j)‖ ≤
      ∑ j, c j * |g j-g' j| := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hc j) (abs_nonneg _)))).mpr
  intro x
  simp only [Pi.sub_apply,Real.norm_eq_abs,← Finset.sum_sub_distrib,← mul_sub]
  exact (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum (fun j _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (ha x j) (abs_nonneg _))

def rootEnergy (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (g : Fin m → ℝ) : ℝ :=
  energyRecursion n b μ ν (fun x => H x+∑ j, a x j*g j)

lemma measurable_rootEnergy (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) :
    Measurable (rootEnergy n b μ ν H a) := by
  apply (measurable_energyRecursion n b μ ν).comp
  fun_prop

lemma rootEnergy_gaussian_slope (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) (g g' : Fin m → ℝ) :
    |rootEnergy n b μ ν H a g-rootEnergy n b μ ν H a g'| ≤ ∑ j, c j*|g j-g' j| := by
  refine (energyRecursion_lipschitz n b μ ν hμ hb _ _).trans ?_
  have heq : (fun x => H x+∑ j, a x j*g j) - (fun x => H x+∑ j, a x j*g' j) =
      (fun x => ∑ j, a x j*g j) - (fun x => ∑ j, a x j*g' j) := by
    ext x
    simp only [Pi.sub_apply,add_sub_add_left_eq_sub]
  rw [heq]
  exact finite_linear_vector_bound hc ha g g'

theorem rootEnergy_gaussian_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) :
    Var[rootEnergy n b μ ν H a; Measure.pi (fun _ : Fin m => gaussianReal 0 1)] ≤ ∑ j, (c j)^2 :=
  gaussian_variance_coordinate_bound m (measurable_rootEnergy n b μ ν H a)
    (rootEnergy_gaussian_slope n b μ ν hμ hb H a c hc ha)

lemma rootEnergy_base_lipschitz (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H G : I → ℝ) (a : I → Fin m → ℝ) (g : Fin m → ℝ) :
    |rootEnergy n b μ ν H a g-rootEnergy n b μ ν G a g| ≤ ‖H-G‖ := by
  have he := energyRecursion_lipschitz n b μ ν hμ hb
    (fun x => H x+∑ j, a x j*g j) (fun x => G x+∑ j, a x j*g j)
  have heq : (fun x => H x+∑ j, a x j*g j) - (fun x => G x+∑ j, a x j*g j) = H-G := by
    ext x
    simp only [Pi.sub_apply,add_sub_add_right_eq_sub]
  rw [heq] at he
  exact he

variable {A : Type*} [MeasurableSpace A]

def patternBase {M : ℕ} (φ : A → I → ℝ) (y : Fin M → A) (x : I) : ℝ := ∑ r, φ (y r) x

omit [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A] in
lemma patternBase_bound {M : ℕ} {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (y : Fin M → A) : ‖patternBase φ y‖ ≤ M*K := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hK)).mpr
  intro x
  simp only [patternBase,Real.norm_eq_abs]
  calc
    _ ≤ ∑ r : Fin M, |φ (y r) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin M, K := Finset.sum_le_sum (fun r _ => hφ (y r) x)
    _ = _ := by simp

omit [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A] in
lemma patternBase_one_change {M : ℕ} {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (i : Fin M) (y y' : Fin M → A)
    (he : ∀ j, j ≠ i → y j=y' j) : ‖patternBase φ y-patternBase φ y'‖ ≤ 2*K := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hK)).mpr
  intro x
  have hsum : (∑ r : Fin M, (φ (y r) x-φ (y' r) x)) = φ (y i) x-φ (y' i) x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [he j hji,sub_self]
    · simp
  simp only [Pi.sub_apply,patternBase,Real.norm_eq_abs,← Finset.sum_sub_distrib,hsum]
  linarith [abs_sub (φ (y i) x) (φ (y' i) x),hφ (y i) x,hφ (y' i) x]

theorem pattern_root_energy_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m M : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j)
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → I → ℝ}
    (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K) :
    Var[(fun p : (Fin m → ℝ) × (Fin M → A) => rootEnergy n b μ ν (patternBase φ p.2) a p.1);
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))]
      ≤ (∑ j, (c j)^2)+M*(2*K)^2 := by
  let γ := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let ρ := Measure.pi (fun _ : Fin M => P)
  let F : (Fin m → ℝ) × (Fin M → A) → ℝ :=
    fun p => rootEnergy n b μ ν (patternBase φ p.2) a p.1
  let F₀ : (Fin m → ℝ) → ℝ := rootEnergy n b μ ν 0 a
  have hFm : Measurable F := by
    apply (measurable_energyRecursion n b μ ν).comp
    apply Measurable.of_eval
    intro x
    apply Measurable.add
    · exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hm).comp
        ((measurable_pi_apply r).comp measurable_snd)))
    · fun_prop
  have hfl (y : Fin M → A) : MemLp (fun g => F (g,y)) 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν (patternBase φ y) a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb (patternBase φ y) a c hc ha) 2
  have h0l : MemLp F₀ 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν 0 a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb 0 a c hc ha) 2
  have hdiff (g : Fin m → ℝ) (y : Fin M → A) : |F (g,y)-F₀ g| ≤ M*K := by
    exact (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) 0 a g).trans
      (by simpa only [sub_zero] using patternBase_bound hK hφ y)
  have hLp : MemLp F 2 (γ.prod ρ) := by
    have hz : MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => F₀ p.1) 2 (γ.prod ρ) :=
      h0l.comp_measurePreserving (measurePreserving_fst (μ := γ) (ν := ρ))
    apply (hz.abs.add (memLp_const (M*K))).mono' hFm.aestronglyMeasurable
    apply ae_of_all
    intro p
    simp only [Pi.add_apply,Pi.abs_apply,Real.norm_eq_abs]
    linarith [hdiff p.1 p.2,abs_sub_abs_le_abs_sub (F p) (F₀ p.1)]
  let G : (Fin M → A) → ℝ := fun y => ∫ g, F (g,y) ∂γ
  have hGm : Measurable G := hFm.stronglyMeasurable.integral_prod_left'.measurable
  have hGb (y : Fin M → A) : |G y| ≤ |∫ g, F₀ g ∂γ|+M*K := by
    have hh := integral_abs_le_bound (μ := γ) (fun g => hdiff g y)
    rw [integral_sub ((hfl y).integrable (by norm_num)) (h0l.integrable (by norm_num))] at hh
    dsimp only [G]
    linarith [abs_sub_abs_le_abs_sub (∫ g, F (g,y) ∂γ) (∫ g, F₀ g ∂γ)]
  have hGLp : MemLp G 2 ρ := memLp_of_abs_bound hGm hGb 2
  have hosc (i : Fin M) (y y' : Fin M → A) (he : ∀ j, j ≠ i → y j=y' j) :
      |G y-G y'| ≤ 2*K := by
    have hd (g : Fin m → ℝ) : |F (g,y)-F (g,y')| ≤ 2*K :=
      (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) (patternBase φ y') a g).trans
        (patternBase_one_change hK hφ i y y' he)
    have hh := integral_abs_le_bound (μ := γ) hd
    simpa only [integral_sub ((hfl y).integrable (by norm_num))
      ((hfl y').integrable (by norm_num)),G] using hh
  have hv := variance_prod_le_fiber hLp hfl hGLp
    (fun y => rootEnergy_gaussian_variance n b μ ν hμ hb (patternBase φ y) a c hc ha)
  have hbvar := variance_pi_boundedDifferences P M hGm hGb (by positivity : 0 ≤ 2*K) hosc
  change Var[F; γ.prod ρ] ≤ _
  change Var[G; ρ] ≤ _ at hbvar
  linarith

end IsingPerceptron

namespace IsingPerceptron

def enrichedCoefficientsFin (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ)
    (x : Spin N) (j : Fin (Fintype.card (EnrichedBlock N))) : ℝ :=
  enrichedLevelCoefficient n h u i x ((Fintype.equivFin (EnrichedBlock N)).symm j)

def enrichedIncrement (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ)
    (g : Fin (Fintype.card (EnrichedBlock N)) → ℝ) (x : Spin N) : ℝ :=
  ∑ j, enrichedCoefficientsFin N n h u i x j*g j

lemma measurable_enrichedIncrement (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ) :
    Measurable (enrichedIncrement N n h u i) := by
  unfold enrichedIncrement
  fun_prop

def enrichedIncrementLaw (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ) :
    ProbabilityMeasure (Spin N → ℝ) :=
  ⟨(Measure.pi (fun _ : Fin (Fintype.card (EnrichedBlock N)) => gaussianReal 0 1)).map
    (enrichedIncrement N n h u i), by infer_instance⟩

lemma enrichedIncrementLaw_moments (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ) :
    ExponentialNormMoments (enrichedIncrementLaw N n h u i : Measure (Spin N → ℝ)) := by
  apply finite_gaussian_exponentialNormMoments (measurable_enrichedIncrement N n h u i)
    (fun _ => 0) (fun x => (∑ j, (enrichedCoefficientsFin N n h u i x j)^2).toNNReal)
  intro x
  exact (gaussian_weighted_sum_law (enrichedCoefficientsFin N n h u i x)).map_eq

theorem enriched_root_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : ∀ i < n, 0 < b i) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (M : ℕ) :
    Var[(fun p : (Fin (Fintype.card (EnrichedBlock N)) → ℝ) × (Fin M → A) =>
      rootEnergy n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
        (patternBase φ p.2) (enrichedCoefficientsFin N n h u 0) p.1);
      (Measure.pi (fun _ : Fin (Fintype.card (EnrichedBlock N)) => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin M => P))] ≤ N*h 0+4*N*(perturbationScale N)^2+M*(2*K)^2 := by
  let x₀ : Spin N := fun _ => 0
  let c := fun j => |enrichedCoefficientsFin N n h u 0 x₀ j|
  have H := pattern_root_energy_variance n b
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1)) hb
    (enrichedCoefficientsFin N n h u 0) c (fun _ => abs_nonneg _)
    (fun x j => (enrichedLevelCoefficient_abs n h u 0 x x₀ _).le)
    P hm hK hφ (M := M)
  have hc : (∑ j, (c j)^2) ≤ N*h 0+4*N*(perturbationScale N)^2 := by
    have he := (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
      (fun j => |enrichedLevelCoefficient n h u 0 x₀ j|^2)
    change (∑ j, |enrichedLevelCoefficient n h u 0 x₀ ((Fintype.equivFin _).symm j)|^2) ≤ _
    rw [he]
    exact enrichedRoot_envelope_sq hN n hh h0 u hu x₀
  linarith

variable {I A : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A]

lemma pattern_root_energy_memLp (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m M : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j)
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → I → ℝ}
    (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K) :
    MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => rootEnergy n b μ ν (patternBase φ p.2) a p.1) 2
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))) := by
  let γ := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let ρ := Measure.pi (fun _ : Fin M => P)
  let F : (Fin m → ℝ) × (Fin M → A) → ℝ :=
    fun p => rootEnergy n b μ ν (patternBase φ p.2) a p.1
  let F₀ : (Fin m → ℝ) → ℝ := rootEnergy n b μ ν 0 a
  have hFm : Measurable F := by
    apply (measurable_energyRecursion n b μ ν).comp
    apply Measurable.of_eval
    intro x
    apply Measurable.add
    · exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hm).comp
        ((measurable_pi_apply r).comp measurable_snd)))
    · fun_prop
  have h0l : MemLp F₀ 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν 0 a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb 0 a c hc ha) 2
  have hdiff (g : Fin m → ℝ) (y : Fin M → A) : |F (g,y)-F₀ g| ≤ M*K := by
    exact (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) 0 a g).trans
      (by simpa only [sub_zero] using patternBase_bound hK hφ y)
  have hLp : MemLp F 2 (γ.prod ρ) := by
    have hz : MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => F₀ p.1) 2 (γ.prod ρ) :=
      h0l.comp_measurePreserving (measurePreserving_fst (μ := γ) (ν := ρ))
    apply (hz.abs.add (memLp_const (M*K))).mono' hFm.aestronglyMeasurable
    apply ae_of_all
    intro p
    simp only [Pi.add_apply,Pi.abs_apply,Real.norm_eq_abs]
    linarith [hdiff p.1 p.2,abs_sub_abs_le_abs_sub (F p) (F₀ p.1)]
  exact hLp

end IsingPerceptron

namespace IsingPerceptron

abbrev EnrichedRootSize (N : ℕ) := Fintype.card (EnrichedBlock N)
abbrev EnrichedRootData (N M : ℕ) (A : Type*) := (Fin (EnrichedRootSize N) → ℝ) × (Fin M → A)

def enrichedBaseEnergy {N M : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (φ : A → Spin N → ℝ) (p : EnrichedRootData N M A) (x : Spin N) : ℝ :=
  patternBase φ p.2 x + enrichedIncrement N n h u 0 p.1 x

lemma measurable_enrichedBaseEnergy {N M : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ} (hφ : Measurable φ) :
    Measurable (enrichedBaseEnergy (M := M) n h u φ) := by
  apply Measurable.of_eval
  intro x
  exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hφ).comp
    ((measurable_pi_apply r).comp measurable_snd))).add
    (((measurable_pi_apply x).comp (measurable_enrichedIncrement N n h u 0)).comp measurable_fst)

def enrichedFixedCountLog {N M : ℕ} {A : Type*} (n : ℕ) (b h : ℕ → ℝ) (u : Fin N → ℝ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedRootData N M A × NoiseTree (Spin N → ℝ) n) : ℝ :=
  cascadeEnergyLog n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (enrichedBaseEnergy n h u φ p.1) p.2 - N*h n/2

lemma enrichedBaseEnergy_memLp {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : ∀ i < n, 0 < b i) (h : ℕ → ℝ)
    (u : Fin N → ℝ)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (M : ℕ) :
    MemLp (fun p : EnrichedRootData N M A => energyRecursion n b
      (fun i => enrichedIncrementLaw N n h u (i+1)) ν (enrichedBaseEnergy n h u φ p)) 2
      ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin M => P))) := by
  let x₀ : Spin N := fun _ => 0
  let c := fun j => |enrichedCoefficientsFin N n h u 0 x₀ j|
  exact pattern_root_energy_memLp n b
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1)) hb
    (enrichedCoefficientsFin N n h u 0) c (fun _ => abs_nonneg _)
    (fun x j => (enrichedLevelCoefficient_abs n h u 0 x x₀ _).le) P hm hK hφ (M := M)

lemma enriched_fixed_count_unshifted {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (M : ℕ) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin M => P))).prod
          (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    MemLp (fun p : EnrichedRootData N M A × NoiseTree (Spin N → ℝ) n => cascadeEnergyLog n b μ ν (enrichedBaseEnergy n h u φ p.1) p.2) 2 Q ∧
    Var[(fun p : EnrichedRootData N M A × NoiseTree (Spin N → ℝ) n => cascadeEnergyLog n b μ ν (enrichedBaseEnergy n h u φ p.1) p.2); Q] ≤
      4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
        +N*h 0+4*N*(perturbationScale N)^2+M*(2*K)^2 := by
  dsimp only
  have hL := enrichedBaseEnergy_memLp n b (fun i hi => (hb.1 i hi).1) h u ν P hm hK hφ M
  have hv := cascadeEnergyLog_variance _ n b hb
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1))
    (measurable_enrichedBaseEnergy n h u hm) hL
  have hr := enriched_root_variance hN n b (fun i hi => (hb.1 i hi).1) hh h0 u hu ν P hm hK hφ M
  refine ⟨hv.1, ?_⟩
  change Var[(fun p => energyRecursion n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (enrichedBaseEnergy n h u φ p)) ; _] ≤ _ at hr
  linarith [hv.2]

lemma memLp_variance_shift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} {C : ℝ}
    (h : MemLp X 2 P ∧ Var[X;P] ≤ C) (c : ℝ) :
    MemLp (fun ω => X ω-c) 2 P ∧ Var[(fun ω => X ω-c);P] ≤ C := by
  refine ⟨h.1.sub (memLp_const _), ?_⟩
  rw [variance_sub_const h.1.aestronglyMeasurable]
  exact h.2

theorem enriched_fixed_count_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (M : ℕ) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin M => P))).prod
          (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    MemLp (enrichedFixedCountLog (M := M) n b h u ν φ) 2 Q ∧
    Var[enrichedFixedCountLog (M := M) n b h u ν φ; Q] ≤
      4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
        +N*h 0+4*N*(perturbationScale N)^2+M*(2*K)^2 := by
  exact memLp_variance_shift _
    (enriched_fixed_count_unshifted hN n b hb hh h0 u hu ν P hm hK hφ M) (N*h n/2)

def poissonMass (r : ℝ≥0) (n : ℕ) : ℝ := Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial

lemma poissonMass_succ (r : ℝ≥0) (n : ℕ) :
    poissonMass r (n+1) * (n+1) = r * poissonMass r n := by
  unfold poissonMass
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma poisson_first_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonMass r n * n) (r : ℝ) := by
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have he : (fun n : ℕ => poissonMass r (n+1) * (n+1)) =
      fun n => (r : ℝ) * poissonMass r n := funext (poissonMass_succ r)
  have hs' : HasSum (fun n : ℕ => poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)) (r : ℝ) := by
    simp only [Nat.cast_add,Nat.cast_one]
    rw [he]
    simpa only [mul_one,poissonMass] using hs
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => poissonMass r n * n) 1).mp hs'
  simpa [poissonMass] using h

lemma poisson_second_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonMass r n * (n : ℝ)^2) ((r : ℝ)^2+r) := by
  have hs := ((poisson_first_hasSum r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  have he (n : ℕ) : poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)^2 =
      (r : ℝ) * (poissonMass r n * n + poissonMass r n) := by
    push_cast
    calc
      _ = (poissonMass r (n+1) * (n+1)) * (n+1) := by ring
      _ = _ := by rw [poissonMass_succ]; ring
  have hs' : HasSum (fun n : ℕ => poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)^2)
      ((r : ℝ) * (r+1)) := by
    simp_rw [he]
    exact hs
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => poissonMass r n * (n : ℝ)^2) 1).mp hs'
  simpa [poissonMass, pow_two, mul_add] using h

lemma poisson_cast_memLp (r : ℝ≥0) : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq (Measurable.of_discrete.aestronglyMeasurable)).mpr
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_eq_abs, abs_sq, poissonMass] using
    (poisson_second_hasSum r).summable

lemma poisson_cast_mean (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  exact (poisson_first_hasSum r).tsum_eq

lemma poisson_cast_second (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2+r := by
  rw [integral_poissonMeasure]
  exact (poisson_second_hasSum r).tsum_eq

lemma poisson_cast_variance (r : ℝ≥0) : Var[(fun n : ℕ => (n : ℝ)); poissonMeasure r] = r := by
  rw [variance_eq_sub (poisson_cast_memLp r)]
  simp only [Pi.pow_apply, poisson_cast_second, poisson_cast_mean]
  ring

lemma integral_prod_sub_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ p : Ω × Ω, (X p.1-X p.2)^2 ∂P.prod P) = 2*Var[X;P] := by
  have hi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hLp : MemLp (fun p : Ω × Ω => X p.1-X p.2) 2 (P.prod P) :=
    (hX.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hX.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  rw [integral_prod _ hLp.integrable_sq]
  have he (x : Ω) : (∫ y, (X x-X y)^2 ∂P) =
      (X x)^2-2*X x*(∫ y, X y ∂P)+(∫ y, (X y)^2 ∂P) := by
    simp_rw [sub_sq]
    rw [integral_add (f := fun y => (X x)^2-2*X x*X y) (g := fun y => (X y)^2)
      ((integrable_const _).sub (hi.const_mul _)) hX.integrable_sq,
      integral_sub (f := fun _ => (X x)^2) (g := fun y => 2*X x*X y)
      (integrable_const _) (hi.const_mul _), integral_const,
      integral_const_mul, probReal_univ, one_smul]
  simp_rw [he]
  rw [integral_add (f := fun x => (X x)^2-2*X x*(∫ y, X y ∂P))
    (g := fun _ => ∫ y, (X y)^2 ∂P)
    (hX.integrable_sq.sub ((hi.const_mul 2).mul_const _)) (integrable_const _),
    integral_sub (f := fun x => (X x)^2) (g := fun x => 2*X x*(∫ y, X y ∂P))
      hX.integrable_sq ((hi.const_mul 2).mul_const _),integral_const,
    integral_mul_const,integral_const_mul,probReal_univ,one_smul,
    variance_eq_sub hX]
  simp only [Pi.pow_apply]
  ring

lemma variance_of_distance_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    {K : ℝ} (_hK : 0 ≤ K) (h : ∀ x y, |X x-X y| ≤ K*|Y x-Y y|) :
    Var[X;P] ≤ K^2 * Var[Y;P] := by
  have hDX := (hX.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hX.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  have hDY := (hY.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hY.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  have he := integral_mono hDX.integrable_sq (hDY.integrable_sq.const_mul (K^2))
    (show ∀ p : Ω × Ω, (X p.1-X p.2)^2 ≤ K^2*(Y p.1-Y p.2)^2 from fun p => by
      simpa only [mul_pow,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h p.1 p.2) 2)
  simp only [Pi.sub_apply,Function.comp_apply] at he
  rw [integral_const_mul,integral_prod_sub_sq P hX,integral_prod_sub_sq P hY] at he
  linarith

lemma nat_abs_step_bound {F : ℕ → ℝ} {K : ℝ} (h : ∀ m, |F (m+1)-F m| ≤ K) :
    ∀ m n, |F m-F n| ≤ K*|(m : ℝ)-n| := by
  have hle (n d : ℕ) : |F (n+d)-F n| ≤ K*d := by
    induction d with
    | zero => simp
    | succ d ih =>
      calc
        _ ≤ |F (n+d+1)-F (n+d)|+|F (n+d)-F n| := by
          simpa only [Nat.add_assoc] using abs_sub_le (F (n+d+1)) (F (n+d)) (F n)
        _ ≤ K+K*d := add_le_add (h (n+d)) ih
        _ = K*(d+1 : ℕ) := by push_cast; ring
  intro m n
  rcases le_total n m with hnm | hmn
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hnm
    simpa only [Nat.cast_add,add_sub_cancel_left,abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)] using hle n d
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [abs_sub_comm (F m) (F (m+d)),show (m : ℝ)-(m+d : ℕ) = -(d : ℝ) by push_cast; ring]
    simp only [abs_neg,abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    exact hle m d

lemma nat_step_memLp {P : Measure ℕ} [IsProbabilityMeasure P]
    (hP : MemLp (fun n : ℕ => (n : ℝ)) 2 P) {F : ℕ → ℝ} {K : ℝ}
    (h : ∀ m, |F (m+1)-F m| ≤ K) : MemLp F 2 P := by
  apply ((hP.const_mul K).add (memLp_const |F 0|)).mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro m
  have hh := nat_abs_step_bound h m 0
  simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)] at hh
  simp only [Pi.add_apply,Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (F m) (F 0)]

end IsingPerceptron

end

end OAI
