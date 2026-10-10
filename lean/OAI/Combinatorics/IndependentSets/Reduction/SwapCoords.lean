import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.CoordinateMean

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def swapCoords {ι α : Type*} (S : Finset ι) (p : (ι → α) × (ι → α)) :=
  (mix S p, mix S p.swap)

lemma swapCoords_preserving {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι) :
    MeasurePreserving (swapCoords (α:=α) S)
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)))
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  have he := measurePreserving_arrowProdEquivProdArrow α α ι (fun _ => μ) (fun _ => μ)
  have hc (i : ι) : MeasurePreserving (fun p : α × α => if i ∈ S then p else p.swap)
      (μ.prod μ) (μ.prod μ) := by
    by_cases hi : i ∈ S
    · convert (MeasurePreserving.id (μ.prod μ)) using 1
      funext p
      simp [hi]
    · simpa only [hi, ↓reduceIte] using (Measure.measurePreserving_swap (μ:=μ) (ν:=μ))
  have hp := measurePreserving_pi (fun _ : ι => μ.prod μ) (fun _ => μ.prod μ) hc
  convert he.comp (hp.comp he.symm) using 1
  funext p
  apply Prod.ext <;> funext i <;> by_cases hi : i ∈ S <;>
    simp [swapCoords, mix, hi, Function.comp_def, MeasurableEquiv.arrowProdEquivProdArrow,
      Equiv.arrowProdEquivProdArrow]

lemma refresh_energy {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    (∫ x, ∫ t, (f x-f (Function.update x i t))^2 ∂μ ∂Measure.pi (fun _ : ι => μ)) =
      2*influenceSq μ i f := by
  let ν := Measure.pi (fun _ : ι => μ)
  have hb' (x : ι → α) : Measurable (fun t => f (Function.update x i t)) := hf.comp (by fun_prop)
  have hi' (x : ι → α) : Integrable (fun t => f (Function.update x i t)) μ :=
    bounded_integrable (hb' x) (fun t => hb _)
  have hi2' (x : ι → α) : Integrable (fun t => (f (Function.update x i t))^2) μ :=
    bounded_sq_integrable (hb' x) (fun t => hb _)
  have hpt (x : ι → α) : (∫ t, (f x-f (Function.update x i t))^2 ∂μ) =
      (f x)^2 - 2*(f x*coordinateMean μ i f x) + ∫ t, (f (Function.update x i t))^2 ∂μ := by
    have he (t : α) : (f x-f (Function.update x i t))^2 =
        (f x)^2 - 2*f x*f (Function.update x i t) + (f (Function.update x i t))^2 := by ring
    simp_rw [he]
    have hi0 : Integrable (fun t => (f x)^2 - 2*f x*f (Function.update x i t)) μ :=
      (integrable_const _).sub ((hi' x).const_mul _)
    rw [integral_add hi0 (hi2' x), integral_sub (integrable_const _) ((hi' x).const_mul _)]
    simp [integral_const_mul, coordinateMean, mul_assoc]
  simp_rw [hpt]
  have hf2 : Integrable (fun x => (f x)^2) ν := bounded_sq_integrable hf hb
  have hm := coordinateMean_measurable μ i hf
  have hp : Integrable (fun x => f x*coordinateMean μ i f x) ν :=
    bounded_integrable (hf.mul hm) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hb x) (coordinateMean_bound μ i hb x) (abs_nonneg _) ((abs_nonneg _).trans (hb x)))
  have hav : Integrable (fun x => ∫ t, (f (Function.update x i t))^2 ∂μ) ν :=
    ((update_preserving μ i).integrable_comp_of_integrable hf2).integral_prod_left
  have hsub : Integrable (fun x => (f x)^2-2*(f x*coordinateMean μ i f x)) ν := hf2.sub (hp.const_mul 2)
  rw [integral_add hsub hav, integral_sub hf2 (hp.const_mul 2), integral_const_mul,
    integral_mul_coordinateMean μ i hf hb, integral_update μ i hf2,
    influenceSq_identity μ i hf hb]
  ring

lemma refresh_energy_product {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    (∫ p : (ι → α) × (ι → α), (f p.1-f (Function.update p.1 i (p.2 i)))^2
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) =
      2*influenceSq μ i f := by
  let ν := Measure.pi (fun _ : ι => μ)
  have hT : MeasurePreserving (fun p : (ι→α)×(ι→α) => (p.1,p.2 i)) (ν.prod ν) (ν.prod μ) :=
    (MeasurePreserving.id ν).prod (measurePreserving_eval (fun _ : ι => μ) i)
  have hg : Measurable (fun p : (ι→α)×α => (f p.1-f (Function.update p.1 i p.2))^2) :=
    ((hf.comp measurable_fst).sub (hf.comp (update_measurable i))).pow_const 2
  have hi : Integrable (fun p : (ι→α)×α => (f p.1-f (Function.update p.1 i p.2))^2) (ν.prod μ) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp (update_measurable i)))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hb _)))
  rw [integral_preserving hT hi.aestronglyMeasurable, integral_prod _ hi]
  exact refresh_energy μ i hf hb

noncomputable def subsetEnergy {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (f : (ι → α) → ℝ) : ℝ :=
  ∫ p : (ι→α)×(ι→α), (f p.1-f (mix Sᶜ p))^2
    ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))

lemma mix_insert_compl {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (i : ι) (p : (ι→α)×(ι→α)) :
    mix (insert i S)ᶜ p = Function.update (mix Sᶜ p) i (p.2 i) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [mix]
  · simp [mix, hj]

lemma subsetEnergy_empty {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (f : (ι → α) → ℝ) : subsetEnergy μ ∅ f = 0 := by
  have hu (p : (ι→α)×(ι→α)) : mix (∅ : Finset ι)ᶜ p = p.1 := by
    funext i
    simp [mix]
  unfold subsetEnergy
  simp_rw [hu]
  simp

lemma subsetEnergy_insert {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι) (i : ι) (hi : i ∉ S)
    {f : (ι → α) → ℝ} {B : ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    subsetEnergy μ (insert i S) f ≤ 2*subsetEnergy μ S f + 4*influenceSq μ i f := by
  let ν := Measure.pi (fun _ : ι => μ)
  let A : (ι→α)×(ι→α) → ℝ := fun p => f p.1-f (mix Sᶜ p)
  let C : (ι→α)×(ι→α) → ℝ := fun p => f (mix Sᶜ p)-f (mix (insert i S)ᶜ p)
  have hd (x y : ι→α) : |f x-f y| ≤ B+B := (abs_sub _ _).trans (add_le_add (hb x) (hb y))
  have hAi : Integrable (fun p => (A p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp (mix_measurable _))) (fun p => hd _ _)
  have hCi : Integrable (fun p => (C p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp (mix_measurable _)).sub (hf.comp (mix_measurable _))) (fun p => hd _ _)
  have hEi : Integrable (fun p : (ι→α)×(ι→α) => (f p.1-f (mix (insert i S)ᶜ p))^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp (mix_measurable _))) (fun p => hd _ _)
  have hce : (∫ p, (C p)^2 ∂ν.prod ν) = 2*influenceSq μ i f := by
    let g : (ι→α)×(ι→α) → ℝ := fun p => (f p.1-f (Function.update p.1 i (p.2 i)))^2
    have hgm : Measurable g := by dsimp [g]; fun_prop
    have h := integral_preserving (swapCoords_preserving μ Sᶜ) hgm.aestronglyMeasurable
    have he (p : (ι→α)×(ι→α)) : g (swapCoords Sᶜ p) = (C p)^2 := by
      dsimp [g, swapCoords, C]
      rw [mix_insert_compl]
      simp [mix, hi]
    simp only [he] at h
    exact h.trans (refresh_energy_product μ i hf hb)
  have hdom : Integrable (fun p => 2*(A p)^2+2*(C p)^2) (ν.prod ν) :=
    (hAi.const_mul 2).add (hCi.const_mul 2)
  have hle := integral_mono hEi hdom (fun p => by
    dsimp [A, C]
    nlinarith [sq_nonneg ((f p.1-f (mix Sᶜ p))-(f (mix Sᶜ p)-f (mix (insert i S)ᶜ p)))])
  rw [integral_add (hAi.const_mul 2) (hCi.const_mul 2)] at hle
  simp only [integral_const_mul, hce] at hle
  change subsetEnergy μ (insert i S) f ≤ 2*subsetEnergy μ S f+2*(2*influenceSq μ i f) at hle
  linarith

lemma subsetEnergy_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    subsetEnergy μ S f ≤ (4:ℝ)^S.card * ∑ i ∈ S, influenceSq μ i f := by
  induction S using Finset.induction_on with
  | empty => simp [subsetEnergy_empty]
  | @insert i S hi ih =>
    have hn := influenceSq_nonneg μ i f
    have hs : 0 ≤ ∑ j ∈ S, influenceSq μ j f := Finset.sum_nonneg (fun j _ => influenceSq_nonneg μ j f)
    have hp : 1 ≤ (4:ℝ)^S.card := one_le_pow₀ (by norm_num)
    have h := subsetEnergy_insert μ S i hi hf hb
    rw [Finset.card_insert_of_notMem hi, Finset.sum_insert hi, pow_succ]
    have h₁ : 0 ≤ (4:ℝ)^S.card * ∑ j ∈ S, influenceSq μ j f := mul_nonneg (by positivity) hs
    have h₂ := mul_le_mul_of_nonneg_right hp hn
    nlinarith

end LargeIndependentSets.ProductAveraging

end OAI
