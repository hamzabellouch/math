import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.CellLaw
import OAI.Combinatorics.IndependentSets.Reduction.Bits

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

def rowBitsEquiv (n m : ℕ) : (Fin n → Cube m) ≃ ((Fin n × Fin m) → Bool) where
  toFun q ik := bit (q ik.1) ik.2
  invFun b i := ofBits (fun k => b (i,k))
  left_inv q := by funext i; exact ofBits_bit (q i)
  right_inv b := by funext ik; simp

lemma rowBits_flip {n m : ℕ} (i : Fin n) (k : Fin m) (q : Fin n → Cube m) :
    rowBitsEquiv n m (rowFlip i k q) = Function.update (rowBitsEquiv n m q) (i,k)
      (!(rowBitsEquiv n m q (i,k))) := by
  funext jk
  obtain ⟨j,l⟩ := jk
  by_cases hj : j = i
  · subst j
    by_cases hl : l = k
    · subst l; simp [rowBitsEquiv, rowFlip, bit_flip]
    · simp [rowBitsEquiv, rowFlip, bit_flip, hl, Prod.mk.injEq]
  · simp [rowBitsEquiv, rowFlip, hj, Prod.mk.injEq]

lemma bitInfluence_rows {n m : ℕ} (h : (Fin n → Cube m) → ℝ) (ik : Fin n × Fin m) :
    bitInfluence (h ∘ (rowBitsEquiv n m).symm) ik = rowInfluence h ik.1 ik.2 := by
  rcases ik with ⟨i,k⟩
  rw [bitInfluence, ← expect_equiv (rowBitsEquiv n m)]
  unfold rowInfluence
  apply Finset.expect_congr rfl
  intro q hq
  simp only [Function.comp_def, Equiv.symm_apply_apply, ← rowBits_flip]

theorem rows_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n m : ℕ, ∀ h : (Fin n → Cube m) → ℝ,
      (∀ x, |h x| ≤ 1) → (∑ i, ∑ k, rowInfluence h i k) ≤ L →
      ∃ S : Finset (Fin n), S.card ≤ J ∧ ∃ g : (Fin n → Cube m) → ℝ,
        (∀ x, |g x| ≤ 1) ∧
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (𝔼 x, (h x-g x)^2) < u := by
  obtain ⟨J,hJ,H⟩ := arbitrary_bits_junta_uniform hL hu
  refine ⟨J,hJ,?_⟩
  intro n m h hb hI
  let e := rowBitsEquiv n m
  have hI' : (∑ ik : Fin n × Fin m, bitInfluence (h ∘ e.symm) ik) ≤ L := by
    simp only [e, bitInfluence_rows, Fintype.sum_prod_type]
    exact hI
  obtain ⟨T,hT,g,hg,hdep,he⟩ := H (Fin n × Fin m) (h ∘ e.symm) (fun x => hb _) hI'
  refine ⟨T.image Prod.fst, (Finset.card_image_le).trans hT, g ∘ e, (fun x => hg _), ?_, ?_⟩
  · intro x y hxy
    apply hdep
    intro ik hik
    change bit (x ik.1) ik.2 = bit (y ik.1) ik.2
    rw [hxy ik.1 (Finset.mem_image.mpr ⟨ik,hik,rfl⟩)]
  · have heq : (𝔼 x, (h x-(g ∘ e) x)^2) = 𝔼 b, ((h ∘ e.symm) b-g b)^2 := by
      rw [← expect_equiv e]
      simp only [Function.comp_def, Equiv.symm_apply_apply]
    rwa [heq]

end LargeIndependentSets.BooleanJunta

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

lemma bounded_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {B : ℝ} (hm : Measurable f)
    (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall hb)

lemma bounded_sq_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {B : ℝ} (hm : Measurable f)
    (hb : ∀ x, |f x| ≤ B) : Integrable (fun x => (f x)^2) μ := by
  apply bounded_integrable (hm.pow_const 2) (B:=B^2)
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hb x))).mpr (hb x)

lemma square_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hi : Integrable f μ)
    (hi2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  let c := ∫ x, f x ∂μ
  have hp : (fun x => (f x-c)^2) = (fun x => (f x)^2 - 2*c*f x + c^2) := by
    funext x; ring
  have hn : 0 ≤ ∫ x, (f x-c)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hprod : Integrable (fun x => 2*c*f x) μ := hi.const_mul (2*c)
  have hsub : Integrable (fun x => (f x)^2-2*c*f x) μ := hi2.sub hprod
  rw [hp, integral_add hsub (integrable_const (c^2)),
    integral_sub hi2 hprod, integral_const_mul, integral_const] at hn
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hn
  dsimp [c] at hn
  nlinarith

noncomputable def average {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (f : (ι → α) → ℝ) (x : ι → α) : ℝ :=
  ∫ y, f (mix S (x,y)) ∂Measure.pi (fun _ : ι => μ)

lemma average_measurable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f : (ι → α) → ℝ} (hf : Measurable f) : Measurable (average μ S f) :=
  (hf.comp (mix_measurable S)).stronglyMeasurable.integral_prod_right'.measurable

lemma average_bound {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f : (ι → α) → ℝ} {B : ℝ} (hb : ∀ x, |f x| ≤ B) (x : ι → α) :
    |average μ S f x| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : ι => μ))
    (f:= fun y => f (mix S (x,y))) (C:=B)
    (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hb (mix S (x,y))))
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, average] using h

theorem junta_average_error {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f g : (ι → α) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1)
    (hdep : ∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) :
    (∫ x, (f x - average μ S f x)^2 ∂Measure.pi (fun _ : ι => μ)) ≤
      4 * ∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  let ν := Measure.pi (fun _ : ι => μ)
  have hm := mix_measurable (α:=α) S
  have hm' (x : ι → α) : Measurable (fun y => mix S (x,y)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  have hdiff (x y : ι → α) : |f x - f y| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [hfb x, hfb y])
  have herr (x : ι → α) : |f x-g x| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [hfb x, hgb x])
  have ham := average_measurable μ S hf
  have hab := average_bound μ S hfb
  have hi : Integrable (fun x => (f x-average μ S f x)^2) ν :=
    bounded_sq_integrable (B:=2) (hf.sub ham) (fun x => (abs_sub _ _).trans (by linarith [hfb x, hab x]))
  have he : Integrable (fun x => (f x-g x)^2) ν := bounded_sq_integrable (hf.sub hg) herr
  have hp : Integrable (fun p : (ι→α)×(ι→α) => (f p.1-f (mix S p))^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp hm)) (fun p => hdiff _ _)
  have hp2 : Integrable (fun p : (ι→α)×(ι→α) =>
      2*((f p.1-g p.1)^2 + (f (mix S p)-g (mix S p))^2)) (ν.prod ν) :=
    ((he.comp_fst ν).add ((mix_preserving μ S).integrable_comp_of_integrable he)).const_mul 2
  calc
    _ ≤ ∫ x, ∫ y, (f x-f (mix S (x,y)))^2 ∂ν ∂ν := by
      apply integral_mono hi hp.integral_prod_left
      intro x
      have hid : Integrable (fun y => f x-f (mix S (x,y))) ν :=
        bounded_integrable (measurable_const.sub (hf.comp (hm' x))) (fun y => hdiff _ _)
      have hid2 := bounded_sq_integrable (μ:=ν) (measurable_const.sub (hf.comp (hm' x)))
        (fun y => hdiff x (mix S (x,y)))
      have hsq := square_integral_le hid hid2
      have hsub : (∫ y, f x-f (mix S (x,y)) ∂ν) = f x-average μ S f x := by
        have hmxi : Integrable (fun y => f (mix S (x,y))) ν :=
          bounded_integrable (hf.comp (hm' x)) (fun y => hfb _)
        rw [integral_sub (integrable_const (f x)) hmxi]
        simp [average, ν]
      rwa [hsub] at hsq

    _ = ∫ p, (f p.1-f (mix S p))^2 ∂ν.prod ν := (integral_prod _ hp).symm
    _ ≤ ∫ p, 2*((f p.1-g p.1)^2 + (f (mix S p)-g (mix S p))^2) ∂ν.prod ν := by
      apply integral_mono hp hp2
      intro p
      have hge : g p.1 = g (mix S p) := hdep _ _ (fun i hi => by simp [mix, hi])
      dsimp only
      rw [← hge]
      nlinarith [sq_nonneg ((f p.1-g p.1)+(f (mix S p)-g p.1))]
    _ = _ := by
      have he1 : Integrable (fun p : (ι→α)×(ι→α) => (f p.1-g p.1)^2) (ν.prod ν) := he.comp_fst ν
      have he2 : Integrable (fun p : (ι→α)×(ι→α) => (f (mix S p)-g (mix S p))^2) (ν.prod ν) :=
        (mix_preserving μ S).integrable_comp_of_integrable he
      rw [integral_const_mul, integral_add he1 he2]
      rw [ProductAveraging.integral_preserving (mix_preserving μ S) he.aestronglyMeasurable]
      have hfst : (∫ p : (ι→α)×(ι→α), (f p.1-g p.1)^2 ∂ν.prod ν) =
          ∫ x, (f x-g x)^2 ∂ν :=
        integral_preserving (measurePreserving_fst (μ:=ν) (ν:=ν)) he.aestronglyMeasurable
      rw [hfst]
      ring

end LargeIndependentSets.ProductAveraging

end OAI
