import Mathlib
import OAI.Probability.IsingPerceptron.PoissonCloud

namespace OAI

/-! Labeled Sampling. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
open Function

lemma measurable_lintegral_pointwiseFinite {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel A B) (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : A × B → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a,b) ∂κ a) := by
  classical
  let F : ℕ → SimpleFunc (A × B) ℝ≥0∞ := SimpleFunc.eapprox f
  have h : ∀ a b, ⨆ n, F n (a,b) = f (a,b) :=
    fun a b => SimpleFunc.iSup_eapprox_apply hf (a,b)
  simp_rw [← h]
  have he (a : A) : (∫⁻ b, ⨆ n, F n (a,b) ∂κ a) =
      ⨆ n, ∫⁻ b, F n (a,b) ∂κ a := by
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox f hij _
  simp_rw [he]
  refine Measurable.iSup fun n => ?_
  refine SimpleFunc.induction (motive := fun g =>
    Measurable (fun a => ∫⁻ b, g (a,b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    have hi (a : A) : (∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a) =
        c * κ a (Prod.mk a ⁻¹' t) := by
      simp_rw [← indicator_comp_right (Prod.mk a)]
      rw [lintegral_indicator (ht.preimage measurable_prodMk_left)]
      simp only [Function.comp_apply, lintegral_const, Measure.restrict_apply_univ]
    change Measurable (fun a => ∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a)
    simp_rw [hi]
    exact measurable_const.mul (Kernel.measurable_kernel_prodMk_left_of_finite ht hκ)
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have ha (a : A) : (∫⁻ b, g₁ (a,b) + g₂ (a,b) ∂κ a) =
        (∫⁻ b, g₁ (a,b) ∂κ a) + ∫⁻ b, g₂ (a,b) ∂κ a :=
      lintegral_add_left (g₁.measurable.comp measurable_prodMk_left) _
    simp_rw [ha]
    exact hm₁.add hm₂

 
def finitePartKernel {E : Type*} [MeasurableSpace E] : Kernel (Measure E) E where
  toFun ν := if ν univ < ∞ then ν else 0
  measurable' := measurable_id.ite
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)
    measurable_const

lemma finitePartKernel_finite {E : Type*} [MeasurableSpace E] (ν : Measure E) :
    IsFiniteMeasure (finitePartKernel ν) := by
  by_cases h : ν univ < ∞
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_left h]
    exact ⟨h⟩
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_right h]
    infer_instance

lemma measurable_finitePart_lintegral {E : Type*} [MeasurableSpace E]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun ν : Measure E => ∫⁻ x, F (x,ν) ∂finitePartKernel ν) :=
  measurable_lintegral_pointwiseFinite finitePartKernel finitePartKernel_finite
    (hF.comp measurable_swap)

lemma infinitePi_indep_eval_rest {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    IndepFun (fun ω : ι → E => ω i)
      (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j) (Measure.infinitePi P) := by
  let m : ι → MeasurableSpace (ι → E) := fun j =>
    MeasurableSpace.comap (fun ω => ω j) inferInstance
  have hi : iIndep m (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have h := indep_iSup_of_disjoint (m := m) (fun j => (measurable_pi_apply j).comap_le) hi
    (S := {i}) (T := {j | j ≠ i}) (by simp)
  change Indep (MeasurableSpace.comap (fun ω : ι → E => ω i) inferInstance)
    (MeasurableSpace.comap (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j)
      inferInstance) (Measure.infinitePi P)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_ofPred_eq, m] using h

lemma infinitePi_eval_rest_map {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    (Measure.infinitePi P).map (fun ω : ι → E =>
      (ω i, fun j : {j : ι // j ≠ i} => ω j)) =
      (P i).prod (Measure.infinitePi (fun j : {j : ι // j ≠ i} => P j)) := by
  have hmap := IndepFun.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable
    (Measurable.of_eval fun j : {j : ι // j ≠ i} =>
      measurable_pi_apply (j : ι)).aemeasurable (infinitePi_indep_eval_rest P i)
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective] at hmap
  exact hmap

lemma measureSum_eq_eval_add_rest {E : Type*} [MeasurableSpace E]
    (ω : ℕ → Measure E) (i : ℕ) :
    Measure.sum ω = ω i + Measure.sum (fun j : {j : ℕ // j ≠ i} => ω j) := by
  classical
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.add_apply]
  rw [ENNReal.tsum_eq_add_tsum_ite i]
  congr 1
  trans ∑' j : ℕ, {j : ℕ | j ≠ i}.indicator (fun j => ω j s) j
  · apply tsum_congr
    intro j
    by_cases h : j = i <;> simp [h]
  · exact (tsum_subtype {j : ℕ | j ≠ i} (fun j => ω j s)).symm

variable {E : Type*} [MeasurableSpace E]
def atomCloud {n : ℕ} (ω : Fin n → E) : Measure E :=
  ∑ i, Measure.dirac (ω i)

lemma measurable_atomCloud (n : ℕ) : Measurable (atomCloud (E := E) (n := n)) := by
  exact Finset.measurable_sum _ (fun i _ => Measure.measurable_dirac.comp
    (measurable_pi_apply i))

lemma atomCloud_insertNth {n : ℕ} (i : Fin (n+1)) (x : E) (ω : Fin n → E) :
    atomCloud (i.insertNth x ω) = Measure.dirac x + atomCloud ω := by
  classical
  rw [atomCloud, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rfl

lemma atomCloud_lintegral {n : ℕ} (ω : Fin n → E) {f : E → ℝ≥0∞}
    (hf : Measurable f) : (∫⁻ x, f x ∂atomCloud ω) = ∑ i, f (ω i) := by
  simp [atomCloud, lintegral_finsetSum_measure, lintegral_dirac' _ hf]

lemma iid_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (i : Fin (n+1)) :
    (∫⁻ ω : Fin (n+1) → E, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  have hm : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
    |>.lintegral_comp (hF.comp ((measurable_pi_apply i).prodMk
      (measurable_atomCloud (n+1))))
  simp only [Function.comp_apply] at h
  have he (p : E × (Fin n → E)) :
      F (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p) i,
        atomCloud ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p)) =
      F (p.1, Measure.dirac p.1 + atomCloud p.2) := by
    change F ((i.insertNth (α := fun _ => E) p.1 p.2) i,
      atomCloud (i.insertNth (α := fun _ => E) p.1 p.2)) = _
    rw [Fin.insertNth_apply_same, atomCloud_insertNth]
  simp_rw [he] at h
  exact h.symm.trans (lintegral_prod _ hm.aemeasurable)

lemma iid_sum_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) :
    (∫⁻ ω : Fin (n+1) → E, ∑ i, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      (n+1 : ℝ≥0∞) * ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  rw [lintegral_finsetSum Finset.univ (f := fun i (ω : Fin (n+1) → E) => F (ω i, atomCloud ω)) (fun i _ =>
    (hF.comp ((measurable_pi_apply i).prodMk (measurable_atomCloud (n+1)))))]
  simp only [iid_point_insertion μ hF n, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

def poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ))

lemma poissonWeight_succ (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℝ≥0∞) = r * poissonWeight r n := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n+1 : ℝ) ≠ 0 := by positivity
  have he : (Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)) * (n+1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hh := congrArg ENNReal.ofReal he
  simpa only [poissonWeight, ENNReal.ofReal_mul (by positivity :
      0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)),
    ENNReal.ofReal_add (by positivity : 0 ≤ (n : ℝ)) (by positivity : 0 ≤ (1 : ℝ)),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_mul r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] using hh

lemma iid_restrict_lintegral (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ)
    {H : (Fin n → E) → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ ω : ℕ → E, H (fun i => ω i) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H ω ∂Measure.pi (fun _ => μ) := by
  have hp : MeasurePreserving (fun ω : ℕ → E => fun i : Fin n => ω i)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin n => μ)) := by
    refine ⟨Measurable.of_eval fun index => measurable_pi_apply (index : ℕ), ?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  exact hp.lintegral_comp hH

lemma lintegral_finitePoissonCloud (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {H : Measure E → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H (finiteCloudMeasure p) ∂finitePoissonCloud r μ) =
      ∑' n, poissonWeight r n * ∫⁻ ω : Fin n → E, H (atomCloud ω)
        ∂Measure.pi (fun _ => μ) := by
  rw [finitePoissonCloud, lintegral_prod (fun p => H (finiteCloudMeasure p)) (hH.comp measurable_finiteCloudMeasure).aemeasurable]
  have hi (n : ℕ) :
      (∫⁻ ω : ℕ → E, H (finiteCloudMeasure (n, ω))
        ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H (atomCloud ω) ∂Measure.pi (fun _ => μ) :=
    iid_restrict_lintegral μ n (hH.comp (measurable_atomCloud n))
  simp_rw [hi]
  rw [poissonMeasure, lintegral_sum_measure]
  simp [lintegral_smul_measure, poissonWeight, smul_eq_mul, lintegral_dirac]

 

theorem finitePoissonCloud_insertion (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F)
    :
    (∫⁻ p, ∫⁻ x, F (x, finiteCloudMeasure p) ∂finitePartKernel (finiteCloudMeasure p)
      ∂finitePoissonCloud r μ) =
      r * ∫⁻ x, ∫⁻ p, F (x, Measure.dirac x + finiteCloudMeasure p)
        ∂finitePoissonCloud r μ ∂μ := by
  rw [lintegral_finitePoissonCloud r μ (measurable_finitePart_lintegral hF)]
  have hm (x : E) : Measurable (fun ν : Measure E => F (x, Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  simp_rw [lintegral_finitePoissonCloud r μ (hm _)]
  have hi (n : ℕ) (ω : Fin n → E) : (∫⁻ x, F (x, atomCloud ω) ∂finitePartKernel (atomCloud ω)) =
      ∑ i, F (ω i, atomCloud ω) := by
    have hfin : IsFiniteMeasure (atomCloud ω) := by unfold atomCloud; infer_instance
    have he : finitePartKernel (atomCloud ω) = atomCloud ω :=
      ite_eq_left (measure_lt_top _ _)
    rw [he]
    exact atomCloud_lintegral ω (hF.comp (measurable_id.prodMk measurable_const))
  simp_rw [hi]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Fin.sum_univ_zero, lintegral_zero, mul_zero, zero_add]
  simp_rw [iid_sum_point_insertion μ hF, ← mul_assoc, poissonWeight_succ]
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hmj (n : ℕ) : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have hmi (n : ℕ) : Measurable (fun x => ∫⁻ ω : Fin n → E,
      F (x, Measure.dirac x + atomCloud ω) ∂Measure.pi (fun _ => μ)) :=
    (hmj n).lintegral_prod_right
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    rw [lintegral_const_mul _ (hmi n)]
  · intro n
    exact (measurable_const.mul (hmi n)).aemeasurable

lemma measurable_measureSum_countable {ι : Type*} [Countable ι] :
    Measurable (Measure.sum : (ι → Measure E) → Measure E) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun i => (Measure.measurable_coe hs).comp (measurable_pi_apply i)

lemma measurable_finitePart_param {A : Type*} [MeasurableSpace A]
    {N : A → Measure E} (hN : Measurable N) {F : A × E → ℝ≥0∞}
    (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂finitePartKernel (N a)) := by
  let κ : Kernel A E := ⟨fun a => finitePartKernel (N a),
    finitePartKernel.measurable.comp hN⟩
  exact measurable_lintegral_pointwiseFinite κ
    (fun a => finitePartKernel_finite (N a)) hF

variable [Nonempty E]

lemma finitePoissonLaw_finite (μ : FiniteMeasure E) :
    ∀ᵐ ν ∂finitePoissonLaw μ, ν univ < ∞ := by
  rw [finitePoissonLaw, ae_map_iff measurable_finiteCloudMeasure.aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)]
  exact ae_of_all _ fun p => by
    have : IsFiniteMeasure (finiteCloudMeasure p) := by
      unfold finiteCloudMeasure
      infer_instance
    exact measure_lt_top _ _

lemma finitePoissonLaw_insertion (μ : FiniteMeasure E)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ν, ∫⁻ x, F (x,ν) ∂finitePartKernel ν ∂finitePoissonLaw μ) =
      ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν) ∂finitePoissonLaw μ ∂(μ : Measure E) := by
  have hm (x : E) : Measurable (fun ν : Measure E => F (x,Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  rw [finitePoissonLaw, lintegral_map (measurable_finitePart_lintegral hF)
    measurable_finiteCloudMeasure]
  simp_rw [lintegral_map (hm _) measurable_finiteCloudMeasure]
  rw [finiteMeasure_mass_normalize μ, lintegral_smul_measure, smul_eq_mul]
  exact finitePoissonCloud_insertion μ.mass _ hF

 
lemma poissonComponent_insertion (μ : Measure E) [SFinite μ] (i : ℕ)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂finitePartKernel (ω i)
      ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂sfiniteSeq μ i := by
  let R := {j : ℕ // j ≠ i}
  let P := poissonComponentLaw μ
  let rest : (R → Measure E) → Measure E := Measure.sum
  have hrest : Measurable rest := measurable_measureSum_countable
  let joint := fun ω : ℕ → Measure E => (ω i, fun j : R => ω j)
  have hjoint : Measurable joint := (measurable_pi_apply i).prodMk
    (Measurable.of_eval fun index : R => measurable_pi_apply (index : ℕ))
  have hjlaw : (poissonProductLaw μ).map joint =
      (P i).prod (Measure.infinitePi (fun j : R => P j)) :=
    infinitePi_eval_rest_map P i
  have hI : Measurable (fun p : Measure E × (R → Measure E) =>
      ∫⁻ x, F (x,p.1 + rest p.2) ∂finitePartKernel p.1) := by
    apply measurable_finitePart_param measurable_fst (F := fun p => F (p.2,p.1.1 + rest p.1.2))
    exact hF.comp (measurable_snd.prodMk
      ((measurable_fst.comp measurable_fst).add
        (hrest.comp (measurable_snd.comp measurable_fst))))
  have hR (x : E) : Measurable (fun p : Measure E × (R → Measure E) =>
      F (x,Measure.dirac x + (p.1 + rest p.2))) :=
    hF.comp (measurable_const.prodMk (measurable_const.add
      (measurable_fst.add (hrest.comp measurable_snd))))
  have he (ω : ℕ → Measure E) : Measure.sum ω = (joint ω).1 + rest (joint ω).2 :=
    measureSum_eq_eval_add_rest ω i
  simp_rw [he]
  rw [← lintegral_map hI hjoint, hjlaw,
    lintegral_prod_symm _ hI.aemeasurable]
  simp_rw [← lintegral_map (hR _) hjoint, hjlaw]
  have hFp (ω : R → Measure E) : Measurable (fun p : E × Measure E =>
      F (p.1,p.2 + rest ω)) :=
    hF.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
  have hins (ω : R → Measure E) :
      (∫⁻ ν, ∫⁻ x, F (x,ν + rest ω) ∂finitePartKernel ν ∂P i) =
        ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν + rest ω) ∂P i ∂sfiniteSeq μ i :=
    finitePoissonLaw_insertion ⟨sfiniteSeq μ i, inferInstance⟩ (hFp ω)
  simp_rw [hins]
  have hJ : Measurable (fun p : (R → Measure E) × E =>
      ∫⁻ ν, F (p.2,Measure.dirac p.2 + ν + rest p.1) ∂P i) := by
    have hm : Measurable (fun p : ((R → Measure E) × E) × Measure E =>
        F (p.1.2,Measure.dirac p.1.2 + p.2 + rest p.1.1)) :=
      hF.comp ((measurable_snd.comp measurable_fst).prodMk
        (((Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst)).add
          measurable_snd).add (hrest.comp (measurable_fst.comp measurable_fst))))
    exact hm.lintegral_prod_right
  rw [lintegral_lintegral_swap hJ.aemeasurable]
  congr 1
  funext x
  rw [lintegral_prod_symm _ (hR x).aemeasurable]
  simp only [add_assoc]

lemma poissonProductLaw_finite (μ : Measure E) [SFinite μ] :
    ∀ᵐ ω ∂poissonProductLaw μ, ∀ i, ω i univ < ∞ := by
  rw [ae_all_iff]
  intro i
  have h := finitePoissonLaw_finite (⟨sfiniteSeq μ i, inferInstance⟩ : FiniteMeasure E)
  have he : (poissonProductLaw μ).map (fun ω => ω i) = poissonComponentLaw μ i :=
    Measure.infinitePi_map_eval _ i
  change ∀ᵐ ν ∂poissonComponentLaw μ i, ν univ < ∞ at h
  rw [← he] at h
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)).mp h

 
theorem poissonProductLaw_insertion (μ : Measure E) [SFinite μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂Measure.sum ω ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂μ := by
  have ha : (fun ω : ℕ → Measure E => ∫⁻ x, F (x,Measure.sum ω) ∂Measure.sum ω) =ᵐ[
      poissonProductLaw μ] (fun ω => ∑' i, ∫⁻ x, F (x,Measure.sum ω) ∂finitePartKernel (ω i)) := by
    filter_upwards [poissonProductLaw_finite μ] with ω hω
    rw [lintegral_sum_measure]
    apply tsum_congr
    intro i
    rw [show finitePartKernel (ω i) = ω i from ite_eq_left (hω i)]
  rw [lintegral_congr_ae ha, lintegral_tsum]
  · simp_rw [poissonComponent_insertion μ _ hF]
    rw [← lintegral_sum_measure, sum_sfiniteSeq]
  · intro i
    apply Measurable.aemeasurable
    apply measurable_finitePart_param (measurable_pi_apply i)
      (F := fun p => F (p.2,Measure.sum p.1))
    exact hF.comp (measurable_snd.prodMk (measurable_measureSum.comp measurable_fst))

lemma poissonProductLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ω, Measure.sum ω s ∂poissonProductLaw μ) = μ s := by
  have hF : Measurable (fun p : E × Measure E => s.indicator (fun _ => (1 : ℝ≥0∞)) p.1) :=
    (measurable_const.indicator hs).comp measurable_fst
  have h := poissonProductLaw_insertion μ hF
  simpa only [lintegral_indicator_const hs, one_mul, lintegral_const,
    measure_univ, mul_one] using h

lemma poissonLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ν, ν s ∂poissonLaw μ) = μ s := by
  rw [poissonLaw, lintegral_map (Measure.measurable_coe hs) measurable_measureSum]
  exact poissonProductLaw_mean_count μ hs

omit [Nonempty E] in
lemma measurable_measureRestrict {s : Set E} (hs : MeasurableSet s) :
    Measurable (fun ν : Measure E => ν.restrict s) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hs)

 

def sigmaPart (μ : Measure E) [SigmaFinite μ] (ν : Measure E) : Measure E :=
  Measure.sum (fun n => finitePartKernel (ν.restrict (disjointed (spanningSets μ) n)))

lemma sigmaPart_eq_ae (μ : Measure E) [SigmaFinite μ] :
    ∀ᵐ ν ∂poissonLaw μ, sigmaPart μ ν = ν := by
  have ha : ∀ n, ∀ᵐ ν ∂poissonLaw μ,
      ν (disjointed (spanningSets μ) n) < ∞ := by
    intro n
    have hm := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
    apply ae_lt_top (Measure.measurable_coe hm)
    rw [poissonLaw_mean_count μ hm]
    exact ((measure_mono (disjointed_subset _ _)).trans_lt
      (measure_spanningSets_lt_top μ n)).ne
  filter_upwards [ae_all_iff.mpr ha] with ν hν
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

omit [Nonempty E] in
lemma measurable_sigmaPart_param (μ : Measure E) [SigmaFinite μ]
    {A : Type*} [MeasurableSpace A] {N : A → Measure E} (hN : Measurable N)
    {F : A × E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂sigmaPart μ (N a)) := by
  simp only [sigmaPart, lintegral_sum_measure]
  apply Measurable.tsum
  intro n
  exact measurable_finitePart_param
    ((measurable_measureRestrict (MeasurableSet.disjointed (measurableSet_spanningSets μ) n)).comp hN) hF

lemma poissonLaw_campbell_aemeasurable (μ : Measure E) [SigmaFinite μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    AEMeasurable (fun ν => ∫⁻ x, F (x,ν) ∂ν) (poissonLaw μ) := by
  apply (measurable_sigmaPart_param μ measurable_id (hF.comp measurable_swap)).aemeasurable.congr
  filter_upwards [sigmaPart_eq_ae μ] with ν hν
  change (∫⁻ x, F (x,ν) ∂sigmaPart μ ν) = ∫⁻ x, F (x,ν) ∂ν
  rw [hν]

 

theorem poissonLaw_insertion (μ : Measure E) [SigmaFinite μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ν, ∫⁻ x, F (x,ν) ∂ν ∂poissonLaw μ) =
      ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν) ∂poissonLaw μ ∂μ := by
  have hI := poissonLaw_campbell_aemeasurable μ hF
  have hm (x : E) : Measurable (fun ν : Measure E => F (x,Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  rw [poissonLaw, lintegral_map' hI measurable_measureSum.aemeasurable]
  simp_rw [lintegral_map (hm _) measurable_measureSum]
  exact poissonProductLaw_insertion μ hF

end IsingPerceptron

 
namespace IsingPerceptron

 
def PoissonGood (μ : Measure ℝ) [SigmaFinite μ] (ν : Measure ℝ) : Prop :=
  ∀ n, ν (disjointed (spanningSets μ) n) < ∞

lemma poissonGood_ae (μ : Measure ℝ) [SigmaFinite μ] :
    ∀ᵐ ν ∂poissonLaw μ, PoissonGood μ ν := by
  rw [show (fun ν => PoissonGood μ ν) =
    (fun ν => ∀ n, ν (disjointed (spanningSets μ) n) < ∞) from rfl, ae_all_iff]
  intro n
  have hm := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
  apply ae_lt_top (Measure.measurable_coe hm)
  rw [poissonLaw_mean_count μ hm]
  exact ((measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)).ne

lemma sigmaPart_eq_of_good (μ : Measure ℝ) [SigmaFinite μ] {ν : Measure ℝ}
    (hν : PoissonGood μ ν) : sigmaPart μ ν = ν := by
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

lemma PoissonGood.dirac_add {μ : Measure ℝ} [SigmaFinite μ] {ν : Measure ℝ}
    (hν : PoissonGood μ ν) (x : ℝ) : PoissonGood μ (Measure.dirac x + ν) := by
  intro n
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, hν n⟩

 

def poissonFactorial (μ : Measure ℝ) [SigmaFinite μ] :
    (d : ℕ) → {m : ℕ} → (Fin d → ℝ → ℝ≥0∞) → (Fin m → ℝ) → Measure ℝ → ℝ≥0∞
  | 0, _, _, _, _ => 1
  | d+1, _, w, z, ν => ∫⁻ x,
      if ∀ j, x ≠ z j then
        w 0 x * poissonFactorial μ d (fun i => w i.succ) (Fin.cons x z) ν
      else 0 ∂sigmaPart μ ν

lemma measurable_fin_cons_param {A : Type*} [MeasurableSpace A] {m : ℕ}
    {x : A → ℝ} {z : A → Fin m → ℝ} (hx : Measurable x) (hz : Measurable z) :
    Measurable (fun a => (Fin.cons (x a) (z a) : Fin (m+1) → ℝ)) := by
  apply Measurable.of_eval
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [Fin.cons_zero] using hx
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply i).comp hz

lemma measurable_poissonFactorial_param (μ : Measure ℝ) [SigmaFinite μ] (d : ℕ) :
    ∀ {A : Type*} [MeasurableSpace A] {m : ℕ}
      {N : A → Measure ℝ} {z : A → Fin m → ℝ} {w : Fin d → ℝ → ℝ≥0∞},
      Measurable N → Measurable z → (∀ i, Measurable (w i)) →
      Measurable (fun a => poissonFactorial μ d w (z a) (N a)) := by
  induction d with
  | zero => intros; exact measurable_const
  | succ d ih =>
    intro A _ m N z w hN hz hw
    simp only [poissonFactorial]
    apply measurable_sigmaPart_param μ hN (F := fun p : A × ℝ =>
      if ∀ j, p.2 ≠ z p.1 j then
        w 0 p.2 * poissonFactorial μ d (fun i => w i.succ) (Fin.cons p.2 (z p.1)) (N p.1)
      else 0)
    have hz' : Measurable (fun p : A × ℝ => (Fin.cons p.2 (z p.1) : Fin (m+1) → ℝ)) :=
      measurable_fin_cons_param measurable_snd (hz.comp measurable_fst)
    have hf := ih (hN.comp measurable_fst) hz' (fun i => hw i.succ)
    apply ((hw 0).comp measurable_snd |>.mul hf).ite _ measurable_const
    simpa only [Set.ofPred_forall, Set.compl_ofPred, Function.comp_apply] using
      MeasurableSet.iInter fun j =>
        (measurableSet_eq_fun measurable_snd
          ((measurable_pi_apply j).comp (hz.comp measurable_fst))).compl

lemma poissonFactorial_dirac_add (μ : Measure ℝ) [SigmaFinite μ] (d : ℕ) :
    ∀ {m : ℕ} {w : Fin d → ℝ → ℝ≥0∞} {z : Fin m → ℝ} {ν : Measure ℝ} {x : ℝ},
      (∀ i, Measurable (w i)) → PoissonGood μ ν → (∃ j, z j = x) →
      poissonFactorial μ d w z (Measure.dirac x + ν) = poissonFactorial μ d w z ν := by
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro m w z ν x hw hν hx
    rw [poissonFactorial, poissonFactorial, sigmaPart_eq_of_good μ (hν.dirac_add x),
      sigmaPart_eq_of_good μ hν, lintegral_add_measure]
    have hzero : (∫⁻ y, if ∀ j, y ≠ z j then w 0 y *
        poissonFactorial μ d (fun i => w i.succ) (Fin.cons y z) (Measure.dirac x + ν)
        else 0 ∂Measure.dirac x) = 0 := by
      have hm : Measurable (fun y => if ∀ j, y ≠ z j then w 0 y *
          poissonFactorial μ d (fun i => w i.succ) (Fin.cons y z) (Measure.dirac x + ν)
          else 0) := by
        have hf : Measurable (fun y => poissonFactorial μ d (fun i => w i.succ)
            (Fin.cons y z) (Measure.dirac x + ν)) :=
          measurable_poissonFactorial_param μ d measurable_const
            (measurable_fin_cons_param measurable_id measurable_const) (fun i => hw i.succ)
        apply ((hw 0).mul hf).ite _ measurable_const
        simpa only [Set.ofPred_forall, Set.compl_ofPred, id_eq] using
          MeasurableSet.iInter fun j : Fin m =>
            (measurableSet_eq_fun measurable_id (measurable_const (a := z j))).compl
      rw [lintegral_dirac' _ hm]
      obtain ⟨j, hj⟩ := hx
      simp only [ite_eq_right (show ¬ ∀ j, x ≠ z j from fun h => h j hj.symm)]
    rw [hzero, zero_add]
    apply lintegral_congr
    intro y
    split_ifs with hy
    · congr 1
      apply ih (fun i => hw i.succ) hν
      obtain ⟨j, hj⟩ := hx
      exact ⟨j.succ, by simpa only [Fin.cons_succ] using hj⟩
    · rfl

def poissonLaplaceWeight (ψ : ℝ → ℝ≥0∞) (ν : Measure ℝ) : ℝ≥0∞ :=
  enegExp (∫⁻ x, ψ x ∂ν)

lemma measurable_poissonLaplaceWeight {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) :
    Measurable (poissonLaplaceWeight ψ) :=
  continuous_enegExp.measurable.comp (Measure.measurable_lintegral hψ)

lemma poissonLaplaceWeight_dirac_add {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ)
    (x : ℝ) (ν : Measure ℝ) :
    poissonLaplaceWeight ψ (Measure.dirac x + ν) =
      enegExp (ψ x) * poissonLaplaceWeight ψ ν := by
  simp only [poissonLaplaceWeight, lintegral_add_measure, lintegral_dirac' _ hψ, enegExp_add]

lemma measurable_poissonFactorial_body (μ : Measure ℝ) [SigmaFinite μ]
    {d m : ℕ} {w : Fin (d+1) → ℝ → ℝ≥0∞} (hw : ∀ i, Measurable (w i))
    (z : Fin m → ℝ) :
    Measurable (fun p : ℝ × Measure ℝ => if ∀ j, p.1 ≠ z j then
      w 0 p.1 * poissonFactorial μ d (fun i => w i.succ) (Fin.cons p.1 z) p.2 else 0) := by
  have hf : Measurable (fun p : ℝ × Measure ℝ => poissonFactorial μ d (fun i => w i.succ)
      (Fin.cons p.1 z) p.2) :=
    measurable_poissonFactorial_param μ d measurable_snd
      (measurable_fin_cons_param measurable_fst measurable_const) (fun i => hw i.succ)
  apply ((hw 0).comp measurable_fst |>.mul hf).ite _ measurable_const
  simpa only [Set.ofPred_forall, Set.compl_ofPred, id_eq] using
    MeasurableSet.iInter fun j : Fin m =>
      (measurableSet_eq_fun measurable_fst (measurable_const (a := z j))).compl

lemma poissonFactorial_laplace_step (μ : Measure ℝ) [SigmaFinite μ]
    {d m : ℕ} {w : Fin (d+1) → ℝ → ℝ≥0∞} (hw : ∀ i, Measurable (w i))
    {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) (z : Fin m → ℝ) :
    (∫⁻ ν, poissonLaplaceWeight ψ ν * poissonFactorial μ (d+1) w z ν ∂poissonLaw μ) =
      ∫⁻ x, if ∀ j, x ≠ z j then
        (w 0 x * enegExp (ψ x)) * ∫⁻ ν, poissonLaplaceWeight ψ ν *
          poissonFactorial μ d (fun i => w i.succ) (Fin.cons x z) ν ∂poissonLaw μ
      else 0 ∂μ := by
  let G : ℝ × Measure ℝ → ℝ≥0∞ := fun p => poissonLaplaceWeight ψ p.2 *
    (if ∀ j, p.1 ≠ z j then w 0 p.1 *
      poissonFactorial μ d (fun i => w i.succ) (Fin.cons p.1 z) p.2 else 0)
  have hG : Measurable G :=
    ((measurable_poissonLaplaceWeight hψ).comp measurable_snd).mul
      (measurable_poissonFactorial_body μ hw z)
  have he : (fun ν => poissonLaplaceWeight ψ ν * poissonFactorial μ (d+1) w z ν) =ᵐ[
      poissonLaw μ] (fun ν => ∫⁻ x, G (x,ν) ∂ν) := by
    filter_upwards [poissonGood_ae μ] with ν hν
    rw [poissonFactorial, sigmaPart_eq_of_good μ hν]
    exact (lintegral_const_mul' _ _ (enegExp_ne_top _)).symm
  rw [lintegral_congr_ae he, poissonLaw_insertion μ hG]
  apply lintegral_congr
  intro x
  by_cases hx : ∀ j, x ≠ z j
  · simp only [ite_eq_left hx]
    have hae : (fun ν => G (x,Measure.dirac x + ν)) =ᵐ[poissonLaw μ]
        (fun ν => (w 0 x * enegExp (ψ x)) * (poissonLaplaceWeight ψ ν *
          poissonFactorial μ d (fun i => w i.succ) (Fin.cons x z) ν)) := by
      filter_upwards [poissonGood_ae μ] with ν hν
      dsimp [G]
      rw [ite_eq_left hx, poissonLaplaceWeight_dirac_add hψ,
        poissonFactorial_dirac_add μ d (fun i => hw i.succ) hν ⟨0, Fin.cons_zero ..⟩]
      ring
    rw [lintegral_congr_ae hae, lintegral_const_mul]
    exact (measurable_poissonLaplaceWeight hψ).mul
      (measurable_poissonFactorial_param μ d measurable_id measurable_const (fun i => hw i.succ))
  · simp only [G, ite_eq_right hx, mul_zero, lintegral_zero]

 

theorem poissonFactorial_laplace (μ : Measure ℝ) [SigmaFinite μ] [NullSingletonClass μ]
    (d : ℕ) {w : Fin d → ℝ → ℝ≥0∞} (hw : ∀ i, Measurable (w i))
    {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ ν, poissonLaplaceWeight ψ ν * poissonFactorial μ d w z ν ∂poissonLaw μ) =
      (∏ i, ∫⁻ x, w i x * enegExp (ψ x) ∂μ) *
        ∫⁻ ν, poissonLaplaceWeight ψ ν ∂poissonLaw μ := by
  induction d generalizing m with
  | zero => simp [poissonFactorial]
  | succ d ih =>
    rw [poissonFactorial_laplace_step μ hw hψ]
    simp_rw [ih (fun i => hw i.succ)]
    have hae : ∀ᵐ x ∂μ, ∀ j, x ≠ z j := by
      rw [ae_all_iff]
      intro j
      exact ae_iff.mpr (by simp)
    rw [lintegral_congr_ae (hae.mono (fun x hx => ite_eq_left hx))]
    rw [lintegral_mul_const, Fin.prod_univ_succ]
    · ring
    · exact (hw 0).mul (continuous_enegExp.measurable.comp hψ)

end IsingPerceptron

end

end OAI
