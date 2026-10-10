import OAI.Probability.DilutedSpin.CompoundCoupling
import OAI.Probability.DilutedSpin.NormalizedCutoff

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Superposition with null marks permitted: equality of the centered mark
 characteristic exponents is enough, without equality of the raw intensities. -/
lemma compoundPoisson_superposition_centered (r s t : ℝ≥0)
    (μ ν τ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (h : ∀ L : StrongDual ℝ E, (r:ℂ)*(charFunDual μ L-1) =
      (s:ℂ)*(charFunDual ν L-1)+(t:ℂ)*(charFunDual τ L-1)) :
    compoundPoisson r μ = compoundPoisson s ν ∗ compoundPoisson t τ := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_conv,charFunDual_compoundPoisson,charFunDual_compoundPoisson,
    charFunDual_compoundPoisson,← Complex.exp_add,h]

omit [CompleteSpace E] in
lemma charFunDual_centered_map {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (V : X → E) (hV : Measurable V) (L : StrongDual ℝ E) :
    charFunDual (Measure.map V μ) L-1 = ∫ x, Complex.exp ((L (V x):ℂ)*Complex.I)-1 ∂μ := by
  have hi : Integrable (fun x => Complex.exp ((L (V x):ℂ)*Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul,
    charFunDual_apply,integral_map hV.aemeasurable (by fun_prop)]

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Coordinatewise zero cutoff, retaining iid f and independence from b. -/
noncomputable def factorCut (R : ℝ) (f : Spin → ℝ) : Spin → ℝ :=
  if ‖f‖≤R then f else 0

lemma measurable_factorCut (R : ℝ) : Measurable (factorCut R) :=
  measurable_id.ite (measurableSet_le measurable_norm measurable_const) measurable_const

lemma factorCut_bound {R : ℝ} (hR : 0≤R) (f : Spin → ℝ) (s : Spin) :
    |factorCut R f s|≤R := by
  by_cases h : ‖f‖≤R
  · simpa only [factorCut,ite_eq_left h,Real.norm_eq_abs] using (norm_le_pi_norm f s).trans h
  · simp [factorCut,h,hR]

lemma factorCut_product {p : ℕ} (R b : ℝ) (f : Fin p → Spin → ℝ) (s : Fin p → Spin) :
    b*(∏ l,factorCut R (f l) (s l)) =
      if ∀ l,‖f l‖≤R then b*∏ l,f l (s l) else 0 := by
  classical
  by_cases h : ∀ l,‖f l‖≤R
  · simp [factorCut,h]
  · obtain ⟨j,hj⟩ := not_forall.mp h
    have hz : ∏ l,factorCut R (f l) (s l) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [factorCut,hj])
    simp [h,hz]

lemma factorCut_product_lt_one {p : ℕ} (R b : ℝ) (f : Fin p → Spin → ℝ)
    (h : ∀ s : Fin p → Spin,|b*∏ l,f l (s l)|<1) :
    ∀ s : Fin p → Spin,|b*∏ l,factorCut R (f l) (s l)|<1 := by
  intro s
  rw [factorCut_product]
  split_ifs
  · exact h s
  · norm_num

noncomputable def patternFeature {n : ℕ} (R : ℝ) (P : FiniteLaw (Fin n → Spin))
    (f : Spin → ℝ) : ℝ := P.expect (fun s => ∏ a,factorCut R f (s a))

lemma measurable_patternFeature {n : ℕ} (R : ℝ) (P : FiniteLaw (Fin n → Spin)) :
    Measurable (patternFeature R P) := by
  unfold patternFeature FiniteLaw.expect
  apply Finset.measurable_sum
  intro s _
  apply Measurable.const_mul
  exact Finset.measurable_prod _ (fun a _ => (measurable_pi_apply (s a)).comp (measurable_factorCut R))

lemma patternFeature_bound {n : ℕ} {R : ℝ} (hR : 0≤R) (P : FiniteLaw (Fin n → Spin))
    (f : Spin → ℝ) : |patternFeature R P f|≤R^n := by
  apply FiniteLaw.abs_expect_le
  intro s
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _a : Fin n,R := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun a _ => factorCut_bound hR f (s a))
    _ = _ := by simp

/-- Independence of b and the iid factors, applied to actual measurable
coordinate tests rather than assuming a replica coefficient formula. -/
lemma integral_b_factors {p : ℕ} (M : Model p) (hM : Admissible M) (n : ℕ)
    (g : Fin p → (Spin → ℝ) → ℝ) (hg : ∀ l,Measurable (g l)) :
    (∫ z : InteractionSample p,(-z.2.2.1)^n*(∏ l,g l (z.2.2.2 l)) ∂M.disorder.toMeasure) =
      (∫ z : InteractionSample p,(-z.2.2.1)^n ∂M.disorder.toMeasure)*
      ∏ l,∫ z : InteractionSample p,g l (z.2.2.2 l) ∂M.disorder.toMeasure := by
  have hgm : Measurable (fun f : Fin p → Spin → ℝ => ∏ l,g l (f l)) :=
    Finset.measurable_prod _ (fun l _ => (hg l).comp (measurable_pi_apply l))
  have hb := hM.independent_b.comp (show Measurable (fun b : ℝ => (-b)^n) by fun_prop) hgm
  have he := hb.integral_fun_mul_eq_mul_integral
    (show AEStronglyMeasurable (fun z : InteractionSample p => (-z.2.2.1)^n) M.disorder.toMeasure by fun_prop)
    (show AEStronglyMeasurable (fun z : InteractionSample p => ∏ l,g l (z.2.2.2 l)) M.disorder.toMeasure from
      (hgm.comp (by fun_prop)).aestronglyMeasurable)
  simp only [Function.comp_def] at he
  rw [he,hM.independent_f.integral_fun_prod_comp (fun l => by fun_prop) (fun l => (hg l).aestronglyMeasurable)]

lemma integral_factor_coordinate {p : ℕ} (M : Model p) (hM : Admissible M)
    (j l : Fin p) (g : (Spin → ℝ) → ℝ) (hg : Measurable g) :
    (∫ z : InteractionSample p,g (z.2.2.2 l) ∂M.disorder.toMeasure) =
      ∫ z : InteractionSample p,g (z.2.2.2 j) ∂M.disorder.toMeasure :=
  ((hM.identically_distributed_f l j).comp hg).integral_eq

/-- All coordinates may use different replica-pattern laws. This includes the
old spin replicas and fresh message replicas on every prescribed topology. -/
lemma upper_pattern_moment {p n : ℕ} (M : Model p) (hM : Admissible M)
    (j : Fin p) (R : ℝ) (P : Fin p → FiniteLaw (Fin n → Spin)) :
    (∫ z : InteractionSample p,(-z.2.2.1)^n*
      (FiniteLaw.pi P).expect (fun s => ∏ a : Fin n,∏ l : Fin p,factorCut R (z.2.2.2 l) (s l a))
      ∂M.disorder.toMeasure) =
      (∫ z : InteractionSample p,(-z.2.2.1)^n ∂M.disorder.toMeasure)*
      ∏ l,∫ z : InteractionSample p,patternFeature R (P l) (z.2.2.2 j) ∂M.disorder.toMeasure := by
  have he (z : InteractionSample p) :
      (FiniteLaw.pi P).expect (fun s => ∏ a : Fin n,∏ l : Fin p,factorCut R (z.2.2.2 l) (s l a)) =
      ∏ l,patternFeature R (P l) (z.2.2.2 l) := by
    conv_lhs => arg 2; ext s; rw [Finset.prod_comm]
    exact FiniteLaw.expect_pi_product P (fun l s => ∏ a, factorCut R (z.2.2.2 l) (s a))
  simp_rw [he]
  rw [integral_b_factors M hM n (fun l => patternFeature R (P l)) (fun l => measurable_patternFeature R (P l))]
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  exact integral_factor_coordinate M hM j l _ (measurable_patternFeature R (P l))

lemma product_one_distinguished {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι) (P B : ℝ) :
    (∏ l : ι,if l=j then P else B)=P*B^(Fintype.card ι-1) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [↓reduceIte]
  congr 1
  have he : (∏ l ∈ Finset.univ.erase j,if l=j then P else B) = ∏ _l ∈ Finset.univ.erase j,B := by
    apply Finset.prod_congr rfl
    intro l hl
    simp only [(Finset.mem_erase.mp hl).1,↓reduceIte]
  rw [he,Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ]

end DilutedSpinGlass

end

end OAI
