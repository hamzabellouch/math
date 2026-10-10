import Mathlib
import OAI.Probability.SKValue.GroundState.EmpiricalPower

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def branchMax (m : ℝ) (b : ℕ)
    (p : (Fin (b+1) → ℝ) × (Fin (b+1) → ℝ)) : ℝ :=
  finiteMaximum (fun i ↦ p.1 i+p.2 i/m)-Real.log (b+1 : ℝ)/m

lemma continuous_branchMax (m : ℝ) (b : ℕ) : Continuous (branchMax m b) := by
  apply Continuous.sub _ continuous_const
  exact continuous_finiteMaximum.comp (by fun_prop)

noncomputable def branchLaw (μ : Measure ℝ) (m : ℝ) (b : ℕ) : Measure ℝ :=
  Measure.map (branchMax m b)
    ((Measure.pi (fun _ : Fin (b+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw)))

instance branchLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) (b : ℕ) :
    IsProbabilityMeasure (branchLaw μ m b) := by
  unfold branchLaw
  infer_instance

lemma integrable_finiteMaximum_of_integrable {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] {μ : Measure Ω} {f : ι → Ω → ℝ}
    (hf : ∀ i,Integrable (f i) μ) : Integrable (fun ω ↦ finiteMaximum (fun i ↦ f i ω)) μ := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ (hf i).abs)).mono'
    (continuous_finiteMaximum.comp_aestronglyMeasurable ((integrable_pi_iff.mpr hf).aestronglyMeasurable))
  exact Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using abs_finiteMaximum_le (fun i ↦ f i ω))

lemma branchMax_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) (m : ℝ) (b : ℕ) :
    Integrable (branchMax m b)
      ((Measure.pi (fun _ : Fin (b+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))) := by
  apply Integrable.sub _ (integrable_const _)
  apply integrable_finiteMaximum_of_integrable
  intro i
  have hiX : Integrable (fun x : Fin (b+1) → ℝ ↦ x i) (Measure.pi (fun _ ↦ μ)) :=
    (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).integrable_comp (by fun_prop) |>.mpr hi
  have hiG : Integrable (fun z : Fin (b+1) → ℝ ↦ z i) (Measure.pi (fun _ ↦ gumbelLaw)) :=
    (measurePreserving_eval (fun _ : Fin (b+1) ↦ gumbelLaw) i).integrable_comp (by fun_prop) |>.mpr gumbel_integrable
  exact (hiX.comp_fst _).add ((hiG.div_const m).comp_snd _)

lemma branchLaw_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) (m : ℝ) (b : ℕ) :
    Integrable (fun x : ℝ ↦ x) (branchLaw μ m b) := by
  rw [branchLaw,integrable_map_measure (by fun_prop) (continuous_branchMax m b).measurable.aemeasurable]
  exact branchMax_integrable hi m b

lemma branchMax_exp_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a m : ℝ} (_ : 0≤a) (ham : a/m<1)
    (he : Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ) (b : ℕ) :
    Integrable (fun p ↦ Real.exp (a*branchMax m b p))
      ((Measure.pi (fun _ : Fin (b+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))) := by
  have hi (i : Fin (b+1)) : Integrable (fun p : (Fin (b+1) → ℝ) × (Fin (b+1) → ℝ) ↦
      Real.exp (a*p.1 i)*Real.exp ((a/m)*p.2 i))
      ((Measure.pi (fun _ : Fin (b+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))) := by
    apply Integrable.mul_prod (f := fun x : Fin (b+1) → ℝ ↦ Real.exp (a*x i))
      (g := fun z : Fin (b+1) → ℝ ↦ Real.exp ((a/m)*z i))
    · exact (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).integrable_comp (by fun_prop) |>.mpr he
    · exact (measurePreserving_eval (fun _ : Fin (b+1) ↦ gumbelLaw) i).integrable_comp (by fun_prop) |>.mpr (gumbel_exp_integrable ham)
  apply ((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).mul_const
    (Real.exp (-a*Real.log (b+1 : ℝ)/m))).mono'
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_branchMax m b))).aestronglyMeasurable)
  apply Eventually.of_forall
  intro p
  simp only [Function.comp_def,Pi.mul_apply]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  obtain ⟨i,hi⟩ := exists_finiteMaximum (fun i : Fin (b+1) ↦ p.1 i+p.2 i/m)
  calc
    _ = (Real.exp (a*p.1 i)*Real.exp ((a/m)*p.2 i))*Real.exp (-a*Real.log (b+1 : ℝ)/m) := by
      simp only [branchMax,←hi,←Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun j : Fin (b+1) ↦ Real.exp (a*p.1 j)*Real.exp ((a/m)*p.2 j))
      (fun j _ ↦ by positivity) (Finset.mem_univ i)) (Real.exp_pos _).le

lemma branchLaw_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) (m : ℝ) (b : ℕ) :
    (∫ x,x ∂branchLaw μ m b)=
      ∫ x,(∫ z,branchMax m b (x,z) ∂Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))
        ∂Measure.pi (fun _ : Fin (b+1) ↦ μ) := by
  rw [branchLaw,integral_map (continuous_branchMax m b).measurable.aemeasurable (by fun_prop)]
  exact integral_prod _ (branchMax_integrable hi m b)

lemma branchLaw_exp_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a m : ℝ} (ha : 0≤a) (ham : a/m<1)
    (he : Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ) (b : ℕ) :
    (∫ x,Real.exp (a*x) ∂branchLaw μ m b)=
      ∫ x,(∫ z,Real.exp (a*branchMax m b (x,z)) ∂Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))
        ∂Measure.pi (fun _ : Fin (b+1) ↦ μ) := by
  rw [branchLaw,integral_map (continuous_branchMax m b).measurable.aemeasurable (by fun_prop)]
  exact integral_prod _ (branchMax_exp_integrable ha ham he b)

lemma iid_sequence_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : ℕ) :
    HasLaw (fun x : ℕ → ℝ ↦ x i) μ (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i).hasLaw

lemma iid_finite_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℕ) :
    HasLaw (fun x : ℕ → ℝ ↦ fun i : Fin (b+1) ↦ x i) (Measure.pi (fun _ : Fin (b+1) ↦ μ))
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  apply iIndepFun.hasLaw_pi (fun i : Fin (b+1) ↦ iid_sequence_law μ i.val)
  exact (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ x ↦ x)
    (fun _ ↦ measurable_id)).precomp Fin.val_injective

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma integrable_exp_smaller {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a m : ℝ} (ha : 0≤a) (ham : a ≤ m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) :
    Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ := by
  apply (he.add (integrable_const 1)).mono' (by fun_prop)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  change Real.exp (a*x)≤Real.exp (m*x)+1
  by_cases hx : 0≤x
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ham hx)).trans (by linarith)
  · have h := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hx))
    linarith [Real.exp_pos (m*x)]

lemma iid_branchIntegral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (b : ℕ) (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    (∫ x,(∫ z,ψ (branchMax m b (x,z)) ∂Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))
      ∂Measure.pi (fun _ : Fin (b+1) ↦ μ))=
    ∫ x : ℕ → ℝ,(∫ z,ψ (branchMax m b ((fun i ↦ x i),z))
      ∂Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw)) ∂Measure.infinitePi (fun _ : ℕ ↦ μ) := by
  exact ((iid_finite_law μ b).integral_comp
    ((hψ.comp (continuous_branchMax m b)).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)).symm

lemma branchLaw_test {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) (m : ℝ) (b : ℕ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) :
    (∫ x,ψ x ∂branchLaw μ m b)=
      ∫ x,(∫ z,ψ (branchMax m b (x,z)) ∂Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))
        ∂Measure.pi (fun _ : Fin (b+1) ↦ μ) := by
  rw [branchLaw,integral_map (continuous_branchMax m b).measurable.aemeasurable
    hψ.continuous.aestronglyMeasurable]
  exact integral_prod _ (lipschitz_integrable_comp (branchMax_integrable hi m b) hψ)

lemma gumbelSmooth_id (m c : ℝ) : gumbelSmooth m id c=gumbelMean/m+c := by
  simp only [gumbelSmooth,id_eq]
  rw [integral_add (gumbel_integrable.div_const m) (integrable_const c),integral_div,integral_const]
  simp [gumbelMean]

theorem branchLaw_test_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) {m : ℝ} (hm : 0 < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) :
    Tendsto (fun b ↦ ∫ x,ψ x ∂branchLaw μ m b) atTop
      (𝓝 (gumbelSmooth m ψ (Real.log (∫ x,Real.exp (m*x) ∂μ)/m))) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let X := fun i (x : ℕ → ℝ) ↦ x i
  have hd : IdentDistrib (X 0) id P μ := (iid_sequence_law μ 0).identDistrib HasLaw.id
  have hex := (hd.comp (show Measurable (fun x : ℝ ↦ Real.exp (m*x)) by fun_prop))
  have hind : iIndepFun X P := iIndepFun_infinitePi (fun _ ↦ measurable_id)
  have h := marked_branching_limit X hm (hd.integrable_iff.mpr hi)
    (hex.integrable_iff.mpr he) (fun i j hij ↦ hind.indepFun hij)
    (fun i ↦ (iid_sequence_law μ i).identDistrib (iid_sequence_law μ 0)) hψ
  have heq := hex.integral_eq
  simp only [Function.comp_def,id_eq] at heq
  rw [heq] at h
  convert h using 1
  funext b
  exact (branchLaw_test hi m b hψ).trans (iid_branchIntegral μ m b ψ hψ.continuous)

theorem branchLaw_mean_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) {m : ℝ} (hm : 0 < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) :
    Tendsto (fun b ↦ ∫ x,x ∂branchLaw μ m b) atTop
      (𝓝 (gumbelMean/m+Real.log (∫ x,Real.exp (m*x) ∂μ)/m)) := by
  simpa only [gumbelSmooth_id,id_eq] using branchLaw_test_tendsto hi hm he LipschitzWith.id

theorem branchLaw_exp_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m) {a : ℝ} (ha : 0≤a) (ham : a < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) :
    Tendsto (fun b ↦ ∫ x,Real.exp (a*x) ∂branchLaw μ m b) atTop
      (𝓝 (gumbelExpMoment (a/m)*(∫ x,Real.exp (m*x) ∂μ)^(a/m))) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let X := fun i (x : ℕ → ℝ) ↦ x i
  have hd : IdentDistrib (X 0) id P μ := (iid_sequence_law μ 0).identDistrib HasLaw.id
  have hex := hd.comp (show Measurable (fun x : ℝ ↦ Real.exp (m*x)) by fun_prop)
  have hind : iIndepFun X P := iIndepFun_infinitePi (fun _ ↦ measurable_id)
  have h := marked_branching_exponential_limit X hm ha ham (hex.integrable_iff.mpr he)
    (fun i j hij ↦ hind.indepFun hij) (fun i ↦ (iid_sequence_law μ i).identDistrib (iid_sequence_law μ 0))
  have heq := hex.integral_eq
  simp only [Function.comp_def,id_eq] at heq
  rw [heq] at h
  convert h using 1
  funext b
  exact (branchLaw_exp_integral ha ((div_lt_one hm).mpr ham) (integrable_exp_smaller ha ham.le he) b).trans
    (iid_branchIntegral μ m b (fun x ↦ Real.exp (a*x)) (by fun_prop))

theorem branchLaw_exp_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m) {a : ℝ} (ha : 0≤a) (ham : a < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) (b : ℕ) :
    (∫ x,Real.exp (a*x) ∂branchLaw μ m b)≤
      gumbelExpMoment (a/m)*(∫ x,Real.exp (m*x) ∂μ)^(a/m) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let X := fun i (x : ℕ → ℝ) ↦ x i
  have hd : IdentDistrib (X 0) id P μ := (iid_sequence_law μ 0).identDistrib HasLaw.id
  have hex := hd.comp (show Measurable (fun x : ℝ ↦ Real.exp (m*x)) by fun_prop)
  have h := marked_branching_exponential_upper X hm ha ham (hex.integrable_iff.mpr he)
    (fun i ↦ (iid_sequence_law μ i).identDistrib (iid_sequence_law μ 0)) b
  have heq := hex.integral_eq
  simp only [Function.comp_def,id_eq] at heq
  rw [heq] at h
  have heqb := (branchLaw_exp_integral ha ((div_lt_one hm).mpr ham) (integrable_exp_smaller ha ham.le he) b).trans
    (iid_branchIntegral μ m b (fun x ↦ Real.exp (a*x)) (by fun_prop))
  rw [heqb]
  exact h

end SKValueG

end

end OAI
