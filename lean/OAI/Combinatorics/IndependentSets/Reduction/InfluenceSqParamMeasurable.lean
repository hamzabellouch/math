import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.ArbitraryRealJunta

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped Classical
lemma influenceSq_param_measurable {X ι α : Type*} [MeasurableSpace X]
    [Fintype ι] [DecidableEq ι] [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (i : ι) {f : X × (ι → α) → ℝ} (hf : Measurable f) :
    Measurable (fun x => influenceSq μ i (fun z => f (x,z))) := by
  have hm : Measurable (fun p : (X × (ι → α)) × α => f (p.1.1, Function.update p.1.2 i p.2)) := by
    apply hf.comp
    exact (measurable_fst.comp measurable_fst).prodMk
      ((update_measurable i).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have ha : Measurable (fun p : X × (ι → α) => coordinateMean μ i (fun z => f (p.1,z)) p.2) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  exact ((hf.sub ha).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

lemma influenceSq_le_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) : influenceSq μ i f ≤ B^2 := by
  calc
    _ ≤ ∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ) := influenceSq_le μ i hf hb
    _ ≤ ∫ _ : ι → α, B^2 ∂Measure.pi (fun _ : ι => μ) := by
      apply integral_mono (bounded_sq_integrable hf hb) (integrable_const _)
      intro x
      nlinarith [hb x, abs_nonneg (f x), sq_abs (f x)]
    _ = B^2 := by simp
end LargeIndependentSets.ProductAveraging

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ j, Fintype (M j)] {τ : Type*}

omit [Fintype ι] [∀ index, Fintype (M index)] in
lemma blockShift_joint_measurable (q : ∀ j, M j → τ) (a : τ → ι) (j : ι) :
    Measurable (fun p : (Sigma M → ℝ) × (ι → Circle) => blockShift q a j p.2 p.1) := by
  apply Measurable.of_eval
  intro c
  by_cases hc : c.1 = j
  · simp only [blockShift, hc, ↓reduceIte, rotate]
    exact representative_measurable.comp
      ((quotient_preserving.measurable.comp ((measurable_pi_apply c).comp measurable_fst)).add
        ((measurable_pi_apply (a (q c.1 c.2))).comp measurable_snd))
  · simpa only [blockShift, hc, ↓reduceIte, Function.comp_def] using (measurable_pi_apply c).comp measurable_fst

omit [Fintype ι] [∀ index, Fintype (M index)] in
lemma shift_junta_independent (q : ∀ j, M j → τ) (a : τ → ι) (j i : ι)
    (S : Finset (Sigma M)) (g : (Sigma M → ℝ) → ℝ)
    (hdep : ∀ x y, (∀ c ∈ S, x c = y c) → g x = g y)
    (halign : ∀ c ∈ S, c.1 = j → a (q c.1 c.2) ≠ i)
    (θ : Sigma M → ℝ) (z : ι → Circle) (w : Circle) :
    g (blockShift q a j (Function.update z i w) θ) = g (blockShift q a j z θ) := by
  apply hdep
  intro c hc
  by_cases hj : c.1 = j
  · simp only [blockShift, hj, ↓reduceIte, Function.update_of_ne (halign c hc hj)]
  · simp only [blockShift, hj, ↓reduceIte]

lemma zero_influence_bound (q : ∀ j, M j → τ) (a : τ → ι) (j i : ι)
    (S : Finset (Sigma M)) (h g : (Sigma M → ℝ) → ℝ)
    (H : (Sigma M → ℝ) × (ι → Circle) → ℝ)
    (hh : Measurable h) (hg : Measurable g) (hH : Measurable H)
    (hb : ∀ θ, |h θ| ≤ 1) (hgb : ∀ θ, |g θ| ≤ 1) (hHb : ∀ p, |H p| ≤ 1)
    (hdep : ∀ x y, (∀ c ∈ S, x c = y c) → g x = g y)
    (halign : ∀ c ∈ S, c.1 = j → a (q c.1 c.2) ≠ i)
    {c γ : ℝ} (hc : 0 ≤ c) (hγ : c < γ)
    (hcomp : ∀ θ z, |H (θ,z)-h (blockShift q a j z θ)| ≤ c)
    (herr : (∫ θ, (h θ-g θ)^2 ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < γ^2) :
    (∫ θ, influenceSq volume i (fun z => H (θ,z))
      ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < (2*γ)^2 := by
  let ν := Measure.pi (fun _ : Sigma M => rotationLaw)
  let μ := Measure.pi (fun _ : ι => (volume : Measure Circle))
  let T : (Sigma M → ℝ) × (ι → Circle) → Sigma M → ℝ := fun p => blockShift q a j p.2 p.1
  have hTm : Measurable T := blockShift_joint_measurable q a j
  have hgi : Integrable (fun p => (H p-g (T p))^2) (ν.prod μ) :=
    bounded_sq_integrable (hH.sub (hg.comp hTm))
      (fun p => (abs_sub _ _).trans (add_le_add (hHb p) (hgb _)))
  have hhi : Integrable (fun p => (H p-h (T p))^2) (ν.prod μ) :=
    bounded_sq_integrable (hH.sub (hh.comp hTm))
      (fun p => (abs_sub _ _).trans (add_le_add (hHb p) (hb _)))
  have hji : Integrable (fun p => (h (T p)-g (T p))^2) (ν.prod μ) :=
    bounded_sq_integrable ((hh.comp hTm).sub (hg.comp hTm))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hgb _)))
  have hpi : Integrable (fun θ => influenceSq volume i (fun z => H (θ,z))) ν := by
    apply bounded_integrable (influenceSq_param_measurable volume i hH) (B:=1)
    intro θ
    rw [abs_of_nonneg (influenceSq_nonneg volume i _)]
    simpa only [one_pow, Function.comp_def, id_eq] using influenceSq_le_bound volume i
      (hH.comp (measurable_const.prodMk measurable_id)) (fun z => hHb (θ,z))
  have hprojection : (∫ θ, influenceSq volume i (fun z => H (θ,z)) ∂ν) ≤
      ∫ p, (H p-g (T p))^2 ∂ν.prod μ := by
    rw [integral_prod _ hgi]
    apply integral_mono hpi hgi.integral_prod_left
    intro θ
    exact influenceSq_of_independent volume i
      (hH.comp (measurable_const.prodMk measurable_id))
      (hg.comp (hTm.comp (measurable_const.prodMk measurable_id)))
      (fun z => hHb (θ,z)) (fun z => hgb _)
      (fun z w => shift_junta_independent q a j i S g hdep halign θ z w)
  have hcompat : (∫ p, (H p-h (T p))^2 ∂ν.prod μ) ≤ c^2 := by
    calc
      _ ≤ ∫ _ : (Sigma M → ℝ) × (ι → Circle), c^2 ∂ν.prod μ := by
        apply integral_mono hhi (integrable_const _)
        intro p
        have hp := hcomp p.1 p.2
        change |H p-h (T p)| ≤ c at hp
        nlinarith [sq_abs (H p-h (T p)), abs_nonneg (H p-h (T p))]
      _ = _ := by simp
  have hjunta : (∫ p, (h (T p)-g (T p))^2 ∂ν.prod μ) < γ^2 := by
    rw [integral_prod_symm _ hji]
    have he (z : ι → Circle) : (∫ θ, (h (T (θ,z))-g (T (θ,z)))^2 ∂ν) =
        ∫ θ, (h θ-g θ)^2 ∂ν :=
      integral_preserving (blockShift_preserving q a j z) ((hh.sub hg).pow_const 2).aestronglyMeasurable
    simp_rw [he]
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul] using herr
  have he : (∫ p, (H p-g (T p))^2 ∂ν.prod μ) ≤
      2*((∫ p, (H p-h (T p))^2 ∂ν.prod μ)+(∫ p, (h (T p)-g (T p))^2 ∂ν.prod μ)) := by
    rw [← integral_add hhi hji, ← integral_const_mul]
    apply integral_mono hgi ((hhi.add hji).const_mul 2)
    intro p
    change (H p-g (T p))^2 ≤ 2*((H p-h (T p))^2+(h (T p)-g (T p))^2)
    nlinarith [sq_nonneg ((H p-h (T p))-(h (T p)-g (T p)))]
  nlinarith
end LargeIndependentSets.PhaseTest

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory ProbabilityTheory
open scoped Classical

lemma restriction_preserving {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (e : κ → ι) (he : Function.Injective e) :
    MeasurePreserving (fun x : ι → α => x ∘ e)
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : κ => μ)) := by
  have hi := iIndepFun_pi (μ:=fun _ : ι => μ) (X:=fun _ => id) (fun _ => aemeasurable_id)
  have hs := hi.precomp he
  refine ⟨Measurable.of_eval (fun index => measurable_pi_apply (e index)), ?_⟩
  have h := hs.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  simpa only [Function.comp_def, id_eq, Measure.pi_map_eval, measure_univ, Finset.prod_const_one, one_smul] using h
end LargeIndependentSets.ProductAveraging

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ j, Fintype (M j)]
variable {κ κ' τ : Type*}

def eraseCoord (i : ι) : (Sigma fun j : {j : ι // j ≠ i} => M j.val) → Sigma M :=
  fun c => ⟨c.1.val,c.2⟩
omit [Fintype ι] [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma eraseCoord_injective (i : ι) : Function.Injective (eraseCoord (M:=M) i) := by
  intro x y h
  cases x with | mk a x =>
    cases y with | mk b y =>
      have hab : a = b := Subtype.ext (congrArg Sigma.fst h)
      subst b
      have hxy : x = y := by simpa only [eraseCoord, Sigma.mk.inj_iff, true_and, heq_eq_eq] using h
      subst y
      rfl

def restrictRotations (i : ι) (θ : Sigma M → ℝ) :
    (Sigma fun j : {j : ι // j ≠ i} => M j.val) → ℝ := θ ∘ eraseCoord i

omit [∀ index, Fintype (M index)] in
lemma deleted_phase (i : ι) (p : ∀ j, κ → M j)
    (p' : ∀ j : {j : ι // j ≠ i}, κ' → M j.val) (e : κ → κ')
    (hcomp : ∀ j k, p j.val k = p' j (e k))
    (t : ι → ℝ) (ht : t i = 0) (θ : Sigma M → ℝ) :
    phase p t θ = (phase p' (fun j => t j.val) (restrictRotations i θ)) ∘ e := by
  funext k
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun j => j ≠ i)
    (fun j => ((t j * θ ⟨j,p j k⟩ : ℝ) : Circle))
  have hzero : (∑ j : {j : ι // ¬ j ≠ i}, ((t j.val * θ ⟨j.val,p j.val k⟩ : ℝ) : Circle)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.val=i := by simpa only [not_not] using j.property
    simp only [hj, ht, zero_mul, AddCircle.coe_zero]
  rw [hzero, add_zero] at hsum
  rw [phase, ← hsum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [restrictRotations, eraseCoord, Function.comp_def, hcomp j k]

omit [∀ index, Fintype (M index)] in
lemma deleted_auxiliary (i j : ι) (p : ∀ j, κ → M j)
    (p' : ∀ j : {j : ι // j ≠ i}, κ' → M j.val) (e : κ → κ')
    (hp : ∀ j k, p j.val k = p' j (e k))
    (q : ∀ j, M j → τ) (r : κ → τ) (hq : ∀ j k, q j (p j k) = r k)
    (a : τ → ι) (t : ι → ℝ) (hi : t i = 0) (hj : t j = 1)
    (θ : Sigma M → ℝ) (z : ι → Circle) :
    auxiliary p r a t θ z =
      (phase p' (fun k => t k.val) (restrictRotations i (blockShift q a j z θ))) ∘ e := by
  rw [← full_block_absorption p q r hq a j t hj θ z]
  exact deleted_phase i p p' e hp t hi _
end LargeIndependentSets.PhaseTest

end OAI
