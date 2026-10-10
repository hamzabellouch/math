import OAI.Combinatorics.Progressions.Lattices.JointAffineL1Parameter

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem jointAffineJetDensity_output_bounds {Q Z X K α : Type*} [Fintype Q]
    [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
    (hw : ∀ q j, 0 < w q j) (δ R : Q → ℝ≥0) (hδ : ∀ q, 0 < δ q)
    (hwidth : ∀ q j, (δ q : ℝ) ≤ w q (.inl j)) (hsupport : ∀ q j, |c q j|+w q j ≤ R q)
    (Cap Lip : ℝ≥0) (hCap : 1 ≤ Cap)
    (hcap : ∀ q, pivotKernelCap (UnselectedColumn (s q)) (A q) (R q) ((δ q)⁻¹^Fintype.card (J q)) ≤ Cap)
    (hlip : ∀ q, pivotKernelLip (UnselectedColumn (s q)) (A q) (R q) (affineProductProfileLip (J q) (δ q)) ≤ Lip)
    (x : X → ℝ) :
    (∀ v, |jointAffineJetDensity s A F e input z rows c w x v| ≤ (Cap : ℝ)^Fintype.card Q) ∧
      LipschitzWith (Fintype.card Q*Lip*Cap^Fintype.card Q)
        (jointAffineJetDensity s A F e input z rows c w x) := by
  let f := fun q (v : ∀ q, I q → ℝ) =>
    affineSelectedJetDensity (s q) (A q) (F q) (e q) input z (rows q) (c q) (w q) x (v q)
  have hb : ∀ q v, |f q v| ≤ Cap := by
    intro q v
    exact (affineSelectedJetDensity_output_cap (s q) (A q) (F q) (e q) input z (rows q)
      (c q) (w q) (hw q) (hδ q) (hwidth q) (R q) (hsupport q) x (v q)).trans (hcap q)
  have hLip : ∀ q, LipschitzWith Lip (f q) := by
    intro q
    have ht := affineSelectedJetDensity_output_lipschitz (s q) (A q) (F q) (e q) input z (rows q)
      (c q) (w q) (hw q) (hδ q) (hwidth q) (R q) (hsupport q) x
    apply LipschitzWith.of_dist_le_mul
    intro v u
    exact (ht.dist_le_mul (v q) (u q)).trans
      (mul_le_mul (show (_ : ℝ) ≤ Lip from hlip q) (dist_le_pi_dist v u q) dist_nonneg Lip.coe_nonneg)
  refine ⟨finiteProduct_cap f Cap.coe_nonneg hb, ?_⟩
  have hp := finiteProduct_lipschitzOn f Set.univ Cap Lip hCap
    (fun q => (hLip q).lipschitzOnWith) (fun q v _ => hb q v)
  apply LipschitzWith.of_dist_le_mul
  intro v u
  exact hp.dist_le_mul v (Set.mem_univ v) u (Set.mem_univ u)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem jointAffineJetDensity_output_support {Q Z X K α : Type*} [Fintype Q]
    [Fintype X] [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1) (rows : ∀ q, I q → Finset α)
    (degree : Q → ℕ) (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
    (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j)
    (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q)
    (Ro : ℝ≥0) (hRo : ∀ q, normalizedJetOutputRadius α (N q) (A q) (F q) (degree q) (R q) (R q) ≤ Ro)
    (x : X → ℝ) (hx : ‖x‖ ≤ 1) (v : ∀ q, I q → ℝ) (hv : (Ro : ℝ) < ‖v‖) :
    jointAffineJetDensity s A F e input z rows c w x v = 0 := by
  by_contra hne
  have hcoord (q) : ‖v q‖ ≤ (Ro : ℝ) := by
    apply le_of_not_gt
    intro hq
    apply hne
    exact Finset.prod_eq_zero (Finset.mem_univ q)
      (affineSelectedJetDensity_output_support (s q) (A q) (F q) (e q) input z hz (rows q)
        (hd q) (c q) (w q) (hw q) (R q) (hsupport q) x hx (v q)
        (lt_of_le_of_lt (show (_ : ℝ) ≤ Ro from hRo q) hq))
  exact hv.not_ge ((pi_norm_le_iff_of_nonneg Ro.coe_nonneg).mpr hcoord)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {T Q Z X K α : Type*} [MeasurableSpace T] [Fintype Q]
    [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
    (hw : ∀ q j, 0 < w q j) (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q)

include hw hsupport

theorem jointAffineJetDensity_mixture_spec
    (μ : Measure T) [IsProbabilityMeasure μ]
    (z : T → Z → ℝ) (hz : ∀ j, Measurable (fun t => z t j))
    (x : T → X → ℝ) (hx : ∀ j, Measurable (fun t => x t j))
    (δ : Q → ℝ≥0) (hδ : ∀ q, 0 < δ q) (hwidth : ∀ q j, (δ q : ℝ) ≤ w q (.inl j))
    (Cap Lip : ℝ≥0) (hCap : 1 ≤ Cap)
    (hcap : ∀ q, pivotKernelCap (UnselectedColumn (s q)) (A q) (R q) ((δ q)⁻¹^Fintype.card (J q)) ≤ Cap)
    (hlip : ∀ q, pivotKernelLip (UnselectedColumn (s q)) (A q) (R q) (affineProductProfileLip (J q) (δ q)) ≤ Lip) :
    let D := densityMixture μ (fun t => jointAffineJetDensity s A F e input (z t) rows c w (x t))
    (∀ v, D v ∈ Set.Icc (0 : ℝ) ((Cap : ℝ)^Fintype.card Q)) ∧
      LipschitzWith (Fintype.card Q*Lip*Cap^Fintype.card Q) D ∧
      Integrable D ∧ (∫ v, D v) = 1 := by
  let H := fun t => jointAffineJetDensity s A F e input (z t) rows c w (x t)
  have hm : Measurable (Function.uncurry H) :=
    jointAffineJetDensity_measurable_comp (Ω := T × (∀ q, I q → ℝ))
      s A F e input rows c w hw R hsupport
      (fun p => z p.1) (fun j => (hz j).comp measurable_fst)
      (fun p => x p.1) (fun j => (hx j).comp measurable_fst)
      (fun p => p.2) (fun q i => (measurable_pi_apply i).comp ((measurable_pi_apply q).comp measurable_snd))
  have hp (t) := jointAffineJetDensity_probability_data s A F e input (z t) rows c w hw R hsupport (x t)
  have hb (t) := jointAffineJetDensity_output_bounds s A F e input (z t) rows c w hw δ R hδ
    hwidth hsupport Cap Lip hCap hcap hlip (x t)
  have hreg := densityMixture_uniform_bound μ H (Cap^Fintype.card Q)
    (Fintype.card Q*Lip*Cap^Fintype.card Q)
    (fun v => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t => ⟨fun v => ⟨(hp t).2.1 v,
      (le_abs_self _).trans ((hb t).1 v)⟩, (hb t).2⟩))
  have hprob := densityMixture_probability_density μ volume H hm
    (Filter.Eventually.of_forall (fun t => ⟨(hp t).2.1, (hp t).1, (hp t).2.2⟩))
  exact ⟨hreg.1, hreg.2, hprob.2.1, hprob.2.2⟩

theorem jointAffineJetDensity_mixture_support [Fintype X]
    (μ : Measure T) (z : T → Z → ℝ) (x : T → X → ℝ)
    (hbox : ∀ᵐ t ∂μ, (∀ j, |z t j| ≤ 1) ∧ ‖x t‖ ≤ 1)
    (degree : Q → ℕ) (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
    (Ro : ℝ≥0) (hRo : ∀ q, normalizedJetOutputRadius α (N q) (A q) (F q) (degree q) (R q) (R q) ≤ Ro)
    (v : ∀ q, I q → ℝ) (hv : (Ro : ℝ) < ‖v‖) :
    densityMixture μ (fun t => jointAffineJetDensity s A F e input (z t) rows c w (x t)) v = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hbox] with t ht
  exact jointAffineJetDensity_output_support s A F e input (z t) ht.1 rows degree hd
    c w hw R hsupport Ro hRo (x t) ht.2 v hv

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem jointAffineJetDensity_mixture_law {T Q Z X K α : Type*}
    [MeasurableSpace T] [Fintype Q] [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
    (hw : ∀ q j, 0 < w q j) (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q)
    (μ : Measure T) [IsProbabilityMeasure μ]
    (z : T → Z → ℝ) (hz : ∀ j, Measurable (fun t => z t j))
    (x : T → X → ℝ) (hx : ∀ j, Measurable (fun t => x t j)) :
    (μ.prod (Measure.pi (fun q => realDensityMeasure volume (affineSelectedJetProfile (s q) (c q) (w q))))).map
      (fun p q => A q (p.2 q).2 +
        splitFreeColumns (F q)
          (polynomialColumns (fun o n => normalizedJetColumn (e q n) input (z p.1) (rows q o)) (x p.1))
          (p.2 q).1) =
      realDensityMeasure volume
        (densityMixture μ (fun t => jointAffineJetDensity s A F e input (z t) rows c w (x t))) := by
  let Ω := ∀ q, (UnselectedColumn (s q) ⊕ N q → ℝ) × (I q → ℝ)
  let U := fun (p : T × Ω) q => A q (p.2 q).2 +
    splitFreeColumns (F q)
      (polynomialColumns (fun o n => normalizedJetColumn (e q n) input (z p.1) (rows q o)) (x p.1))
      (p.2 q).1
  have hU : Measurable U := by
    apply Measurable.of_eval
    intro q
    have hc := normalizedJetColumns_measurable_comp (Ω := T × Ω) (e q) input (rows q)
      (fun p => z p.1) (fun j => (hz j).comp measurable_fst)
      (fun p => x p.1) (fun j => (hx j).comp measurable_fst)
      (fun p n => (p.2 q).1 (.inr n)) (fun _ => by fun_prop)
    have hk : Measurable (fun p : T × Ω => A q (p.2 q).2 + F q (fun j => (p.2 q).1 (.inl j))) := by
      fun_prop
    convert hk.add hc using 1
    ext p i
    simp only [U, Pi.add_apply, splitFreeColumns_apply, add_assoc]
  have hprofile (q) := affineSelectedJetProfile_probability_data (s q) (c q) (w q) (hw q) (R q) (hsupport q)
  let : ∀ q, IsProbabilityMeasure (realDensityMeasure volume (affineSelectedJetProfile (s q) (c q) (w q))) :=
    fun q => realDensityMeasure_probability volume _ (hprofile q).1 (hprofile q).2.1 (hprofile q).2.2
  have hm := jointAffineJetDensity_measurable_comp (Ω := T × (∀ q, I q → ℝ))
    s A F e input rows c w hw R hsupport
    (fun p => z p.1) (fun j => (hz j).comp measurable_fst)
    (fun p => x p.1) (fun j => (hx j).comp measurable_fst)
    (fun p => p.2) (fun q i => (measurable_pi_apply i).comp ((measurable_pi_apply q).comp measurable_snd))
  apply densityMixture_image_law μ _ volume U hU
    (fun t => jointAffineJetDensity s A F e input (z t) rows c w (x t)) hm
  · intro t
    have hp := jointAffineJetDensity_probability_data s A F e input (z t) rows c w hw R hsupport (x t)
    exact ⟨hp.2.1, hp.1, hp.2.2⟩
  · intro t
    exact jointAffineJetDensity_law s A F e input (z t) rows c w hw R hsupport (x t)

end Erdos3

end

end OAI
