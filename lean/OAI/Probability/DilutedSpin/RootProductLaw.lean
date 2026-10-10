import OAI.Probability.DilutedSpin.FinitePoissonSplit
import OAI.Probability.DilutedSpin.InsertionStability

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma finiteUniform_pi {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    Measure.pi (fun _ : ι => finiteUniform J) = finiteUniform (ι → J) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton,finiteUniform,PMF.uniformOfFintype_apply,ENNReal.inv_pow]

lemma integral_root_prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (n : ℕ) (F : (Fin n → X) × (Fin n → Y) → ℝ)
    (hF : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => ν)))) :
    (∫ z : RootPath (X×Y) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod ν)) =
      ∫ x : Fin n → X,∫ y : Fin n → Y,F (x,y)
        ∂Measure.pi (fun _ : Fin n => ν) ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_rootArray_eq_pi (μ.prod ν) n (fun z : Fin n → X×Y => F ((fun i => (z i).1),(fun i => (z i).2)))]
  have he := (measurePreserving_arrowProdEquivProdArrow X Y (Fin n)
    (fun _ => μ) (fun _ => ν)).integral_comp' F
  exact he.trans (integral_prod F hF)

lemma integral_root_prod_finite {X J : Type} [MeasurableSpace X]
    [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin n → X) × (Fin n → J) → ℝ) (hF : Measurable F)
    {B : ℝ} (hb : ∀ z,|F z|≤B) :
    (∫ z : RootPath (X×J) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod (PMF.uniformOfFintype J).toMeasure)) =
      ∫ x : Fin n → X,(FiniteLaw.uniform : FiniteLaw (Fin n → J)).expect (fun j => F (x,j))
        ∂Measure.pi (fun _ : Fin n => μ) := by
  have hi : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype J).toMeasure))) :=
    Integrable.of_bound hF.aestronglyMeasurable B (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hb z))
  rw [integral_root_prod μ (PMF.uniformOfFintype J).toMeasure n F hi]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ j,F (x,j) ∂Measure.pi (fun _ : Fin n => finiteUniform J)) = _
  rw [finiteUniform_pi,integral_finiteUniform,FiniteLaw.expect_uniform]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X E A B : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

lemma map_redundant_finite_mark (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X×(A×B) → E) (W : X×B → E) (hV : Measurable V) (hW : Measurable W)
    (h : ∀ a b,IdentDistrib (fun x => V (x,(a,b))) (fun x => W (x,b)) μ μ) :
    Measure.map V (μ.prod (finiteUniform (A×B))) = Measure.map W (μ.prod (finiteUniform B)) := by
  apply Measure.ext_of_charFunDual
  funext L
  suffices heq : charFunDual (Measure.map V (μ.prod (finiteUniform (A×B)))) L-1 =
      charFunDual (Measure.map W (μ.prod (finiteUniform B))) L-1 by exact sub_left_inj.mp heq
  rw [centered_finite_mark μ V hV,centered_finite_mark μ W hW]
  have he (a : A) (b : B) :
      (∫ x,Complex.exp ((L (V (x,(a,b))):ℂ)*Complex.I)-1 ∂μ)=
      (∫ x,Complex.exp ((L (W (x,b)):ℂ)*Complex.I)-1 ∂μ) := ((h a b).comp (show Measurable (fun v : E => Complex.exp ((L v:ℂ)*Complex.I)-1) by fun_prop)).integral_eq
  simp only [Fintype.sum_prod_type,he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_prod,Nat.cast_mul]
  have hA : (Fintype.card A:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  simp only [mul_comm Complex.I]

end DilutedSpinGlass

end

end OAI
