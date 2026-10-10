import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.SwapCoords

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

lemma pair_energy_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} {B : ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    (∫ p : α×α, (f p.1-f p.2)^2 ∂μ.prod μ) =
      2*((∫ x, (f x)^2 ∂μ)-(∫ x, f x ∂μ)^2) := by
  have hi := bounded_integrable (μ:=μ) hf hb
  have hi2 := bounded_sq_integrable (μ:=μ) hf hb
  have hpi : Integrable (fun p : α×α => (f p.1-f p.2)^2) (μ.prod μ) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp measurable_snd))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hb _)))
  rw [integral_prod _ hpi]
  have he (x : α) : (∫ y, (f x-f y)^2 ∂μ) =
      (f x)^2 - 2*f x*(∫ y, f y ∂μ) + ∫ y, (f y)^2 ∂μ := by
    have hpoly (y : α) : (f x-f y)^2 = (f x)^2-2*f x*f y+(f y)^2 := by ring
    simp_rw [hpoly]
    have hs : Integrable (fun y => (f x)^2-2*f x*f y) μ := (integrable_const _).sub (hi.const_mul _)
    rw [integral_add hs hi2, integral_sub (integrable_const _) (hi.const_mul _), integral_const_mul]
    simp
  simp_rw [he]
  have hmul : Integrable (fun x => 2*f x*(∫ y, f y ∂μ)) μ := (hi.const_mul 2).mul_const _
  have hs : Integrable (fun x => (f x)^2-2*f x*(∫ y, f y ∂μ)) μ := hi2.sub hmul
  rw [integral_add hs (integrable_const _), integral_sub hi2 hmul]
  simp only [integral_mul_const, integral_const_mul, integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_smul]
  ring

lemma average_depends {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (f : (ι → α) → ℝ) (x y : ι → α)
    (hxy : ∀ i ∈ S, x i = y i) : average μ S f x = average μ S f y := by
  unfold average
  congr 1
  funext z
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [mix, hi, hxy i hi]
  · simp [mix, hi]

lemma average_update_of_notMem {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (f : (ι → α) → ℝ) (i : ι) (hi : i ∉ S)
    (x : ι → α) (t : α) : average μ S f (Function.update x i t) = average μ S f x := by
  apply average_depends
  intro j hj
  exact Function.update_of_ne (by aesop) _ _

lemma junta_variance_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f g : (ι → α) → ℝ} {B C : ℝ} (hf : Measurable f) (hg : Measurable g)
    (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C)
    (hdep : ∀ x y, (∀ i ∈ S, x i = y i) → g x = g y)
    (hzero : (∫ x, f x ∂Measure.pi (fun _ : ι => μ)) = 0) :
    2*(∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ)) ≤
      3*subsetEnergy μ S f + 6*(∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ)) := by
  let ν := Measure.pi (fun _ : ι => μ)
  let R := mix (α:=α) Sᶜ
  let A : (ι→α)×(ι→α) → ℝ := fun p => f p.1-f (R p)
  let C : (ι→α)×(ι→α) → ℝ := fun p => f (R p)-g (R p)
  let D : (ι→α)×(ι→α) → ℝ := fun p => g p.2-f p.2
  have hR : MeasurePreserving R (ν.prod ν) ν := mix_preserving μ Sᶜ
  have hAi : Integrable (fun p => (A p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp hR.measurable))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hb _)))
  have hCi : Integrable (fun p => (C p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp hR.measurable).sub (hg.comp hR.measurable))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hc _)))
  have hDi : Integrable (fun p => (D p)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hg.comp measurable_snd).sub (hf.comp measurable_snd))
      (fun p => (abs_sub _ _).trans (add_le_add (hc _) (hb _)))
  have hi : Integrable (fun p : (ι→α)×(ι→α) => (f p.1-f p.2)^2) (ν.prod ν) :=
    bounded_sq_integrable ((hf.comp measurable_fst).sub (hf.comp measurable_snd))
      (fun p => (abs_sub _ _).trans (add_le_add (hb _) (hb _)))
  have hdom : Integrable (fun p => 3*((A p)^2+(C p)^2+(D p)^2)) (ν.prod ν) :=
    ((hAi.add hCi).add hDi).const_mul 3
  have hpt (p : (ι→α)×(ι→α)) : (f p.1-f p.2)^2 ≤ 3*((A p)^2+(C p)^2+(D p)^2) := by
    have hgR : g (R p) = g p.2 := hdep _ _ (fun i hi => by simp [R, mix, hi])
    dsimp [A, C, D]
    rw [hgR]
    nlinarith [sq_nonneg ((f p.1-f (R p))-(f (R p)-g p.2)),
      sq_nonneg ((f p.1-f (R p))-(g p.2-f p.2)),
      sq_nonneg ((f (R p)-g p.2)-(g p.2-f p.2))]
  have hle := integral_mono hi hdom hpt
  have hCE : (∫ p, (C p)^2 ∂ν.prod ν) = ∫ x, (f x-g x)^2 ∂ν :=
    integral_preserving hR ((hf.sub hg).pow_const 2).aestronglyMeasurable
  have hDE : (∫ p, (D p)^2 ∂ν.prod ν) = ∫ x, (f x-g x)^2 ∂ν := by
    have hs (x : ι→α) : (g x-f x)^2=(f x-g x)^2 := by ring
    simp only [D, hs]
    exact integral_preserving (measurePreserving_snd (μ:=ν) (ν:=ν))
      ((hf.sub hg).pow_const 2).aestronglyMeasurable
  rw [pair_energy_eq ν hf hb] at hle
  change (∫ x, f x ∂ν) = 0 at hzero
  rw [hzero] at hle
  have hACi : Integrable (fun p => (A p)^2+(C p)^2) (ν.prod ν) := hAi.add hCi
  rw [integral_const_mul, integral_add hACi hDi, integral_add hAi hCi, hCE, hDE] at hle
  change 2*((∫ x, (f x)^2 ∂ν)-0^2) ≤ 3*(subsetEnergy μ S f+
    (∫ x, (f x-g x)^2 ∂ν)+(∫ x, (f x-g x)^2 ∂ν)) at hle
  linarith

lemma exists_influence_of_junta {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {J : ℕ} (hJ : 1 ≤ J) (S : Finset ι) (hS : S.card ≤ J)
    {f g : (ι → α) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hb : ∀ x, |f x| ≤ 1) (hc : ∀ x, |g x| ≤ 1)
    (hdep : ∀ x y, (∀ i ∈ S, x i = y i) → g x = g y)
    {ε : ℝ} (hε : 0 < ε)
    (hzero : (∫ x, f x ∂Measure.pi (fun _ : ι => μ)) = 0)
    (hvar : ε < ∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ))
    (herr : (∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ)) < ε/12) :
    ∃ i, ε/(4*(4:ℝ)^J*J) ≤ influenceSq μ i f := by
  by_contra hn
  push Not at hn
  let b := ε/(4*(4:ℝ)^J*J)
  have hJp : (0:ℝ) < J := by exact_mod_cast (by omega : 0<J)
  have hbpos : 0 ≤ b := by dsimp [b]; positivity
  have hsum : (∑ i ∈ S, influenceSq μ i f) ≤ J*b := by
    calc
      _ ≤ ∑ i ∈ S, b := Finset.sum_le_sum (fun i _ => (hn i).le)
      _ = (S.card:ℝ)*b := by simp
      _ ≤ J*b := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hbpos
  have hen := subsetEnergy_le μ S hf hb
  have hpow : (4:ℝ)^S.card ≤ (4:ℝ)^J := pow_le_pow_right₀ (by norm_num) hS
  have hsumpos : 0 ≤ ∑ i ∈ S, influenceSq μ i f := Finset.sum_nonneg (fun i _ => influenceSq_nonneg μ i f)
  have he : subsetEnergy μ S f ≤ ε/4 := by
    calc
      _ ≤ (4:ℝ)^S.card * ∑ i ∈ S, influenceSq μ i f := hen
      _ ≤ (4:ℝ)^J*(J*b) := mul_le_mul hpow hsum hsumpos (by positivity)
      _ = ε/4 := by dsimp [b]; field_simp
  have hv := junta_variance_bound μ S hf hg hb hc hdep hzero
  linarith

lemma influential_card_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι)
    {f g : (ι → α) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hb : ∀ x, |f x| ≤ 1) (hc : ∀ x, |g x| ≤ 1)
    (hdep : ∀ x y, (∀ i ∈ S, x i = y i) → g x = g y)
    {a : ℝ} (herr : (∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ)) < a) :
    (Finset.univ.filter (fun i => a ≤ influenceSq μ i f)).card ≤ S.card := by
  apply Finset.card_le_card
  intro i hi
  by_contra hn
  have hgind (x : ι→α) (t : α) : g (Function.update x i t) = g x := by
    apply hdep
    intro j hj
    exact Function.update_of_ne (by aesop) _ _
  have hle := influenceSq_of_independent μ i hf hg hb hc hgind
  have hi' := (Finset.mem_filter.mp hi).2
  linarith

end LargeIndependentSets.ProductAveraging

end OAI
