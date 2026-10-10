import Mathlib

namespace OAI

/-! Gaussian Integration. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1 <;> try rfl
  · ext y
    simp [gaussianPDFReal]
  · norm_num [gaussianPDFReal]
    ring

lemma integrable_gaussian_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul']
  · simp [gaussianPDF, ENNReal.toReal_ofReal, gaussianPDFReal_nonneg]
  · exact measurable_gaussianPDF _ _
  · exact ae_of_all _ (fun x => by simp [gaussianPDF])

lemma gaussian_integration_by_parts {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := f') (v := gaussianPDFReal 0 1)
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x)
  have h1 : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert (integrable_gaussian_iff.mp hxf).neg using 1
    ext x; dsimp; ring
  have h2 : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) := by
    simpa [mul_comm] using integrable_gaussian_iff.mp hf'
  have h3 : Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
    simpa [mul_comm] using integrable_gaussian_iff.mp hf
  specialize hh h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul] at *
  have heq : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      fun x => -(gaussianPDFReal 0 1 x * (x * f x)) := by ext x; ring
  rw [heq, integral_neg] at hh
  simpa [mul_comm] using neg_injective hh

lemma gaussian_integration_by_parts_bounded {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hm' : Measurable f')
    {K K' : ℝ} (hb : ∀ x, |f x| ≤ K) (hb' : ∀ x, |f' x| ≤ K') :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hm : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hd x).continuousAt)).measurable
  have hif : Integrable f (gaussianReal 0 1) :=
    (MemLp.of_bound hm.aestronglyMeasurable K
      (ae_of_all _ (fun x => by simpa using hb x)) (p := 1)).integrable le_rfl
  have hif' : Integrable f' (gaussianReal 0 1) :=
    (MemLp.of_bound hm'.aestronglyMeasurable K'
      (ae_of_all _ (fun x => by simpa using hb' x)) (p := 1)).integrable le_rfl
  apply gaussian_integration_by_parts hd hif hif'
  exact ((memLp_id_gaussianReal 1).integrable le_rfl).mul_bdd
    hm.aestronglyMeasurable (ae_of_all _ (fun x => by simpa using hb x))

lemma gaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n + 1))
    {F F' : (Fin (n + 1) → ℝ) → ℝ} (hm : Measurable F) (hm' : Measurable F')
    (hd : ∀ (g : Fin n → ℝ) (x : ℝ),
      HasDerivAt (fun y => F (i.insertNth y g)) (F' (i.insertNth x g)) x)
    {K K' : ℝ} (hb : ∀ g, |F g| ≤ K) (hb' : ∀ g, |F' g| ≤ K') :
    (∫ g, g i * F g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ g, F' g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e.symm ((gaussianReal 0 1).prod ν) μ :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i).symm
  have hF' : Integrable F' μ :=
    (MemLp.of_bound hm'.aestronglyMeasurable K'
      (ae_of_all _ (fun g => by simpa using hb' g)) (p := 1)).integrable le_rfl
  have hFi : Integrable (fun g => g i * F g) μ := by
    have hc : Integrable (fun g : Fin (n + 1) → ℝ => g i) μ :=
      (measurePreserving_eval (fun _ : Fin (n + 1) => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)
    exact hc.mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa using hb g))
  change (∫ g, g i * F g ∂μ) = ∫ g, F' g ∂μ
  rw [← he.integral_comp' (fun g => g i * F g), ← he.integral_comp' F']
  have hi1 : Integrable (fun v => e.symm v i * F (e.symm v))
      ((gaussianReal 0 1).prod ν) := he.integrable_comp_of_integrable hFi
  have hi2 : Integrable (fun v => F' (e.symm v))
      ((gaussianReal 0 1).prod ν) := he.integrable_comp_of_integrable hF'
  rw [integral_prod_symm _ hi1, integral_prod_symm _ hi2]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_apply_same]
  apply gaussian_integration_by_parts_bounded (hd g)
  · exact hm'.comp (measurable_pi_iff.mpr (i.forall_iff_succAbove.mpr
      ⟨by simp only [Fin.insertNth_apply_same]; exact measurable_id,
        fun j => by simp⟩))
  · exact fun x => hb _
  · exact fun x => hb' _

section FiniteGibbs
variable {S : Type*} [Fintype S]

def finitePartition (w H : S → ℝ) : ℝ := ∑ x, w x * Real.exp (H x)
def finiteGibbs (w H : S → ℝ) (x : S) : ℝ :=
  w x * Real.exp (H x) / finitePartition w H

def GibbsReference (w : S → ℝ) : Prop := (∀ x, 0 ≤ w x) ∧ ∃ x, 0 < w x

lemma finitePartition_pos {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) :
    0 < finitePartition w H := by
  obtain ⟨x, hx⟩ := hw.2
  exact Finset.sum_pos' (fun y _ => mul_nonneg (hw.1 y) (Real.exp_pos _).le)
    ⟨x, Finset.mem_univ _, mul_pos hx (Real.exp_pos _)⟩

lemma finiteGibbs_nonneg {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) (x : S) :
    0 ≤ finiteGibbs w H x :=
  div_nonneg (mul_nonneg (hw.1 x) (Real.exp_pos _).le) (finitePartition_pos hw H).le

lemma finiteGibbs_sum {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) :
    ∑ x, finiteGibbs w H x = 1 := by
  simp only [finiteGibbs, ← Finset.sum_div]
  exact div_self (finitePartition_pos hw H).ne'

lemma finiteGibbs_le_one {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) (x : S) :
    finiteGibbs w H x ≤ 1 := by
  rw [← finiteGibbs_sum hw H]
  exact Finset.single_le_sum (fun y _ => finiteGibbs_nonneg hw H y) (Finset.mem_univ x)

lemma finiteGibbs_average_bound {w : S → ℝ} (hw : GibbsReference w)
    (H A : S → ℝ) {K : ℝ} (hA : ∀ x, |A x| ≤ K) :
    |∑ x, finiteGibbs w H x * A x| ≤ K := by
  calc
    _ ≤ ∑ x, |finiteGibbs w H x * A x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, finiteGibbs w H x * |A x| := by
      congr 1; ext x; rw [abs_mul, abs_of_nonneg (finiteGibbs_nonneg hw H x)]
    _ ≤ ∑ x, finiteGibbs w H x * K := Finset.sum_le_sum
      (fun x _ => mul_le_mul_of_nonneg_left (hA x) (finiteGibbs_nonneg hw H x))
    _ = K := by rw [← Finset.sum_mul, finiteGibbs_sum hw H, one_mul]

lemma hasDerivAt_finitePartition {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (w : S → ℝ) :
    HasDerivAt (fun s => finitePartition w (H s))
      (∑ x, w x * Real.exp (H t x) * dH x) t := by
  simpa only [finitePartition, mul_assoc] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => (hH x).exp.const_mul (w x)))

lemma hasDerivAt_finiteGibbs {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (x : S) :
    HasDerivAt (fun s => finiteGibbs w (H s) x)
      (finiteGibbs w (H t) x *
        (dH x - ∑ y, finiteGibbs w (H t) y * dH y)) t := by
  have hd := ((hH x).exp.const_mul (w x)).div
    (hasDerivAt_finitePartition hH w) (finitePartition_pos hw (H t)).ne'
  convert hd using 1 <;> try rfl
  simp only [finiteGibbs, div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp [(finitePartition_pos hw (H t)).ne']

lemma hasDerivAt_log_finitePartition {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) :
    HasDerivAt (fun s => Real.log (finitePartition w (H s)))
      (∑ x, finiteGibbs w (H t) x * dH x) t := by
  convert (hasDerivAt_finitePartition hH w).log (finitePartition_pos hw (H t)).ne' using 1
  simp only [finiteGibbs, div_mul_eq_mul_div, Finset.sum_div]

end FiniteGibbs

section GaussianGibbs
variable {S : Type*} [Fintype S]

def linearGaussian {n : ℕ} (C : S → Fin n → ℝ) (g : Fin n → ℝ) (x : S) : ℝ :=
  ∑ j, C x j * g j

def gaussianGibbs {n : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (g : Fin n → ℝ) (x : S) : ℝ :=
  finiteGibbs w (fun y => B y + linearGaussian C g y) x

lemma continuous_gaussianGibbs {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (x : S) :
    Continuous (fun g => gaussianGibbs w B C g x) := by
  unfold gaussianGibbs finiteGibbs
  apply Continuous.div
  · unfold linearGaussian; fun_prop
  · unfold finitePartition linearGaussian; fun_prop
  · exact fun g => (finitePartition_pos hw _).ne'

omit [Fintype S] in
lemma hasDerivAt_linearGaussian_insert {n : ℕ} (C : S → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (g : Fin n → ℝ) (x : S) (t : ℝ) :
    HasDerivAt (fun y => linearGaussian C (i.insertNth y g) x) (C x i) t := by
  have he : (fun y => linearGaussian C (i.insertNth y g) x) =
      fun y => C x i * y + ∑ j : Fin n, C x (i.succAbove j) * g j := by
    funext y
    simp only [linearGaussian, i.sum_univ_succAbove, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove]
  rw [he]
  simpa using ((hasDerivAt_id t).const_mul (C x i)).add_const
    (∑ j : Fin n, C x (i.succAbove j) * g j)

lemma hasDerivAt_gaussianGibbs_insert {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (g : Fin n → ℝ) (x : S) (t : ℝ) :
    HasDerivAt (fun y => gaussianGibbs w B C (i.insertNth y g) x)
      (gaussianGibbs w B C (i.insertNth t g) x *
        (C x i - ∑ z, gaussianGibbs w B C (i.insertNth t g) z * C z i)) t := by
  apply hasDerivAt_finiteGibbs hw
  intro z
  exact (hasDerivAt_linearGaussian_insert C i g z t).const_add (B z)

lemma gaussian_gibbs_coordinate_insertion {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1)) (x : S) :
    (∫ g, g i * gaussianGibbs w B C g x
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ g, gaussianGibbs w B C g x * (C x i - ∑ z, gaussianGibbs w B C g z * C z i)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  apply gaussian_pi_integration_by_parts i (K := 1) (K' := |C x i| + ∑ z, |C z i|)
    (continuous_gaussianGibbs hw B C x).measurable
  · exact ((continuous_gaussianGibbs hw B C x).mul
      (continuous_const.sub (continuous_finsetSum _
        (fun z _ => (continuous_gaussianGibbs hw B C z).mul continuous_const)))).measurable
  · exact fun g t => hasDerivAt_gaussianGibbs_insert hw B C i g x t
  · intro g
    change |finiteGibbs w (fun z => B z + linearGaussian C g z) x| ≤ 1
    rw [abs_of_nonneg (finiteGibbs_nonneg hw _ x)]
    exact finiteGibbs_le_one hw _ x
  · intro g
    let K := ∑ z, |C z i|
    have hK (z : S) : |C z i| ≤ K :=
      Finset.single_le_sum (fun y _ => abs_nonneg (C y i)) (Finset.mem_univ z)
    have ha := finiteGibbs_average_bound hw (fun z => B z + linearGaussian C g z)
      (fun z => C z i) hK
    change |gaussianGibbs w B C g x * _| ≤ |C x i| + K
    rw [abs_mul, abs_of_nonneg (show 0 ≤ gaussianGibbs w B C g x from finiteGibbs_nonneg hw _ x)]
    calc
      _ ≤ 1 * |C x i - ∑ z, gaussianGibbs w B C g z * C z i| :=
        mul_le_mul_of_nonneg_right (finiteGibbs_le_one hw _ x) (abs_nonneg _)
      _ ≤ |C x i| + K := by
        rw [one_mul]
        exact (abs_sub _ _).trans (add_le_add le_rfl ha)

end GaussianGibbs

section Replicas
variable {S : Type*} [Fintype S]

def replicaGibbs {n r : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (g : Fin n → ℝ) (σ : Fin r → S) : ℝ :=
  ∏ l, gaussianGibbs w B C g (σ l)

lemma replicaGibbs_nonneg {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) (σ : Fin r → S) :
    0 ≤ replicaGibbs w B C g σ :=
  Finset.prod_nonneg (fun l _ => finiteGibbs_nonneg hw _ (σ l))

lemma replicaGibbs_le_one {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) (σ : Fin r → S) :
    replicaGibbs w B C g σ ≤ 1 := by
  exact Finset.prod_le_one₀ (fun replica _ => finiteGibbs_nonneg hw _ (σ replica))
    (fun l _ => finiteGibbs_le_one hw _ (σ l))

lemma replicaGibbs_sum {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) :
    ∑ σ : Fin r → S, replicaGibbs w B C g σ = 1 := by
  classical
  unfold replicaGibbs
  rw [← Fintype.prod_sum]
  simp only [gaussianGibbs, finiteGibbs_sum hw, Finset.prod_const_one]

lemma continuous_replicaGibbs {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (σ : Fin r → S) :
    Continuous (fun g => replicaGibbs w B C g σ) := by
  exact continuous_finsetProd _ (fun l _ => continuous_gaussianGibbs hw B C (σ l))

lemma hasDerivAt_replicaGibbs_insert {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (g : Fin n → ℝ) (σ : Fin r → S) (t : ℝ) :
    HasDerivAt (fun y => replicaGibbs w B C (i.insertNth y g) σ)
      (replicaGibbs w B C (i.insertNth t g) σ *
        (∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C (i.insertNth t g) z * C z i))) t := by
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun l _ => hasDerivAt_gaussianGibbs_insert hw B C i g (σ l) t)
  convert hd using 1 <;> try rfl
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← mul_assoc, Finset.prod_erase_mul _ _ hl]
  rfl

lemma gaussian_replica_coordinate_insertion {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1)) (σ : Fin r → S) :
    (∫ g, g i * replicaGibbs w B C g σ
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ g, replicaGibbs w B C g σ *
      (∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let K := ∑ z, |C z i|
  have hK (z : S) : |C z i| ≤ K :=
    Finset.single_le_sum (fun y _ => abs_nonneg (C y i)) (Finset.mem_univ z)
  apply gaussian_pi_integration_by_parts i (K := 1) (K' := ∑ l, (|C (σ l) i| + K))
    (continuous_replicaGibbs hw B C σ).measurable
  · exact ((continuous_replicaGibbs hw B C σ).mul
      (continuous_finsetSum _ (fun l _ => continuous_const.sub
        (continuous_finsetSum _ (fun z _ =>
          (continuous_gaussianGibbs hw B C z).mul continuous_const))))).measurable
  · exact fun g t => hasDerivAt_replicaGibbs_insert hw B C i g σ t
  · intro g
    rw [abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
    exact replicaGibbs_le_one hw B C g σ
  · intro g
    rw [abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
    calc
      _ ≤ 1 * |∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i)| :=
        mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg _)
      _ ≤ ∑ l, (|C (σ l) i| + K) := by
        rw [one_mul]
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro l _
        exact (abs_sub _ _).trans (add_le_add le_rfl
          (finiteGibbs_average_bound hw (fun z => B z + linearGaussian C g z)
            (fun z => C z i) hK))

lemma integrable_gaussian_coordinate_mul {n : ℕ} (i : Fin n)
    {F : (Fin n → ℝ) → ℝ} (hm : Measurable F) {K : ℝ} (hK : ∀ g, |F g| ≤ K) :
    Integrable (fun g => g i * F g) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hc : Integrable (fun g : Fin n → ℝ => g i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
      ((memLp_id_gaussianReal 1).integrable le_rfl)
  exact hc.mul_bdd hm.aestronglyMeasurable (ae_of_all _ (fun g => by simpa using hK g))

omit [Fintype S] in
lemma gaussian_pi_linear_insertion {n : ℕ} (a : Fin (n + 1) → ℝ)
    {F : (Fin (n + 1) → ℝ) → ℝ} {F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ}
    (hm : Measurable F) (hm' : ∀ i, Measurable (F' i))
    (hd : ∀ i g x, HasDerivAt (fun y => F (i.insertNth y g)) (F' i (i.insertNth x g)) x)
    {K : ℝ} {K' : Fin (n + 1) → ℝ}
    (hb : ∀ g, |F g| ≤ K) (hb' : ∀ i g, |F' i g| ≤ K' i) :
    (∫ g, (∑ i, a i * g i) * F g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ g, ∑ i, a i * F' i g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hi i : Integrable (F' i) (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (MemLp.of_bound (hm' i).aestronglyMeasurable (K' i)
      (ae_of_all _ (fun g => by simpa using hb' i g)) (p := 1)).integrable le_rfl
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (integrable_gaussian_coordinate_mul i hm hb).const_mul _),
    integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_const_mul,
    gaussian_pi_integration_by_parts i hm (hm' i) (hd i) hb (hb' i)]

omit [Fintype S] in
def gaussianCross {n : ℕ} (A C : S → Fin n → ℝ) (x y : S) : ℝ :=
  ∑ i, A x i * C y i

lemma gaussian_replica_insertion {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n + 1) → ℝ) (x : S) (σ : Fin r → S) :
    (∫ g, linearGaussian A g x * replicaGibbs w B C g σ
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ g, replicaGibbs w B C g σ *
      (∑ l, (gaussianCross A C x (σ l) -
        ∑ z, gaussianGibbs w B C g z * gaussianCross A C x z))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hd := gaussian_pi_linear_insertion (A x) (continuous_replicaGibbs hw B C σ).measurable
    (F' := fun i g => replicaGibbs w B C g σ *
      ∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i))
    (fun i => ((continuous_replicaGibbs hw B C σ).mul
      (continuous_finsetSum _ (fun l _ => continuous_const.sub
        (continuous_finsetSum _ (fun z _ =>
          (continuous_gaussianGibbs hw B C z).mul continuous_const))))).measurable)
    (fun i g t => hasDerivAt_replicaGibbs_insert hw B C i g σ t)
    (K := 1) (K' := fun i => ∑ l, (|C (σ l) i| + ∑ z, |C z i|))
    (fun g => by rw [abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)];
                 exact replicaGibbs_le_one hw B C g σ)
  have hb i g : |replicaGibbs w B C g σ *
      ∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i)| ≤
      ∑ l, (|C (σ l) i| + ∑ z, |C z i|) := by
    rw [abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
    apply (mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg _)).trans
    rw [one_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro l _
    exact (abs_sub _ _).trans (add_le_add le_rfl
      (finiteGibbs_average_bound hw (fun z => B z + linearGaussian C g z)
        (fun z => C z i) (fun z => Finset.single_le_sum (fun y _ => abs_nonneg (C y i))
          (Finset.mem_univ z))))
  rw [show linearGaussian A = fun g x => ∑ i, A x i * g i from rfl, hd hb]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  simp only [gaussianCross, Finset.mul_sum, mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    ring

end Replicas

section Perturbation
variable {S : Type*} [Fintype S]

lemma log_finitePartition_le_add {w : S → ℝ} (hw : GibbsReference w)
    {H J : S → ℝ} {K : ℝ} (h : ∀ x, H x ≤ J x + K) :
    Real.log (finitePartition w H) ≤ Real.log (finitePartition w J) + K := by
  rw [← Real.log_exp K, ← Real.log_mul (finitePartition_pos hw J).ne' (Real.exp_pos K).ne']
  apply Real.log_le_log (finitePartition_pos hw H)
  unfold finitePartition
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h x)) (hw.1 x)

lemma log_finitePartition_lipschitz {w : S → ℝ} (hw : GibbsReference w)
    {H J : S → ℝ} {K : ℝ} (h : ∀ x, |H x - J x| ≤ K) :
    |Real.log (finitePartition w H) - Real.log (finitePartition w J)| ≤ K := by
  apply abs_le.mpr
  constructor
  · have hh := log_finitePartition_le_add hw (H := J) (J := H) (K := K)
      (fun x => by have := (abs_le.mp (h x)).1; linarith)
    linarith
  · have hh := log_finitePartition_le_add hw (H := H) (J := J) (K := K)
      (fun x => by have := (abs_le.mp (h x)).2; linarith)
    linarith

omit [Fintype S] in
lemma integrable_linearGaussian {n : ℕ} (A : S → Fin n → ℝ) (x : S) :
    Integrable (fun g => linearGaussian A g x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply integrable_finsetSum
  intro i _
  exact ((measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
    ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul _

lemma continuous_log_finitePartition {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) :
    Continuous (fun g => Real.log (finitePartition w (fun x => B x + t * linearGaussian A g x))) := by
  apply Continuous.log
  · unfold finitePartition linearGaussian; fun_prop
  · exact fun g => (finitePartition_pos hw _).ne'

lemma integrable_log_finitePartition {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) :
    Integrable (fun g => Real.log (finitePartition w (fun x => B x + t * linearGaussian A g x)))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hi : Integrable (fun g => |Real.log (finitePartition w B)| +
      |t| * ∑ x, |linearGaussian A g x|)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (integrable_const _).add ((integrable_finsetSum _
      (fun x _ => (integrable_linearGaussian A x).abs)).const_mul _)
  apply hi.mono' (continuous_log_finitePartition hw B A t).aestronglyMeasurable
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs]
  have hh := log_finitePartition_lipschitz hw (H := fun x => B x + t * linearGaussian A g x)
    (J := B) (K := |t| * ∑ x, |linearGaussian A g x|) (fun x => by
      simp only [add_sub_cancel_left, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian A g y)) (Finset.mem_univ x))
        (abs_nonneg t))
  have := abs_le.mp hh
  have hz := abs_le.mp (le_refl |Real.log (finitePartition w B)|)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma hasDerivAt_expected_log_finitePartition {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ g, Real.log (finitePartition w (fun x => B x + s * linearGaussian A g x))
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (∫ g, ∑ x, finiteGibbs w (fun z => B z + t * linearGaussian A g z) x * linearGaussian A g x
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) t := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  have hc (s : ℝ) (x : S) : Continuous (fun g =>
      finiteGibbs w (fun z => B z + s * linearGaussian A g z) x) := by
    unfold finiteGibbs
    apply Continuous.div
    · unfold linearGaussian; fun_prop
    · unfold finitePartition linearGaussian; fun_prop
    · exact fun g => (finitePartition_pos hw _).ne'
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := Set.univ)
    (F' := fun s g => ∑ x, finiteGibbs w (fun z => B z + s * linearGaussian A g z) x *
      linearGaussian A g x)
    (bound := fun g => ∑ x, |linearGaussian A g x|) (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun s => (continuous_log_finitePartition hw B A s).aestronglyMeasurable))
    (integrable_log_finitePartition hw B A t) ?_ ?_ ?_ ?_).2
  · apply Continuous.aestronglyMeasurable
    apply continuous_finsetSum
    intro x _
    exact (hc t x).mul (by unfold linearGaussian; fun_prop)
  · apply ae_of_all
    intro g s _
    rw [Real.norm_eq_abs]
    exact finiteGibbs_average_bound hw _ _ (fun x =>
      Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian A g y)) (Finset.mem_univ x))
  · exact integrable_finsetSum _ (fun x _ => (integrable_linearGaussian A x).abs)
  · apply ae_of_all
    intro g s _
    exact hasDerivAt_log_finitePartition hw (fun x => by simpa using
      ((hasDerivAt_id s).mul_const (linearGaussian A g x)).const_add (B x))

omit [Fintype S] in
lemma linearGaussian_scale {n : ℕ} (A : S → Fin n → ℝ) (t : ℝ) (g : Fin n → ℝ) (x : S) :
    linearGaussian (fun y i => t * A y i) g x = t * linearGaussian A g x := by
  simp only [linearGaussian, Finset.mul_sum, mul_assoc]

omit [Fintype S] in
lemma gaussianCross_scale {n : ℕ} (A : S → Fin n → ℝ) (t : ℝ) (x y : S) :
    gaussianCross A (fun z i => t * A z i) x y = t * gaussianCross A A x y := by
  simp only [gaussianCross, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gaussian_gibbs_insertion {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n + 1) → ℝ) (x : S) :
    (∫ g, linearGaussian A g x * gaussianGibbs w B C g x
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ g, gaussianGibbs w B C g x *
      (gaussianCross A C x x - ∑ z, gaussianGibbs w B C g z * gaussianCross A C x z)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  simpa [replicaGibbs, Fin.prod_univ_one, Fin.sum_univ_one] using
    gaussian_replica_insertion (r := 1) hw B A C x (fun _ => x)

lemma integrable_linearGaussian_mul_gibbs {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (x y : S) :
    Integrable (fun g => linearGaussian A g x * gaussianGibbs w B C g y)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply (integrable_linearGaussian A x).mul_bdd
    (continuous_gaussianGibbs hw B C y).aestronglyMeasurable (c := 1)
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ gaussianGibbs w B C g y from finiteGibbs_nonneg hw _ y)]
  exact finiteGibbs_le_one hw _ y

lemma hasDerivAt_expected_log_gaussian {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin (n + 1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ g, Real.log (finitePartition w (fun x => B x + s * linearGaussian A g x))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
      (∑ x, ∫ g, gaussianGibbs w B (fun y i => t * A y i) g x *
        (gaussianCross A (fun y i => t * A y i) x x -
          ∑ z, gaussianGibbs w B (fun y i => t * A y i) g z *
            gaussianCross A (fun y i => t * A y i) x z)
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) t := by
  convert hasDerivAt_expected_log_finitePartition hw B A t using 1
  have he : ∀ g x, finiteGibbs w (fun z => B z + t * linearGaussian A g z) x =
      gaussianGibbs w B (fun y i => t * A y i) g x := by
    intro g x
    simp only [gaussianGibbs, linearGaussian_scale]
  simp_rw [he, mul_comm (gaussianGibbs _ _ _ _ _) (linearGaussian _ _ _)]
  rw [integral_finsetSum _ (fun x _ => integrable_linearGaussian_mul_gibbs hw B A _ x x)]
  apply Finset.sum_congr rfl
  intro x _
  exact (gaussian_gibbs_insertion hw B A _ x).symm

lemma gaussian_covariance_difference_bound {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) {K : ℝ}
    (hK : ∀ x y, |gaussianCross A A x y| ≤ K) (g : Fin n → ℝ) (x : S) :
    |gaussianCross A (fun y i => t * A y i) x x -
      ∑ z, gaussianGibbs w B (fun y i => t * A y i) g z *
        gaussianCross A (fun y i => t * A y i) x z| ≤ 2 * |t| * K := by
  have hb : ∀ y, |gaussianCross A (fun z i => t * A z i) x y| ≤ |t| * K := by
    intro y
    rw [gaussianCross_scale, abs_mul]
    exact mul_le_mul_of_nonneg_left (hK x y) (abs_nonneg t)
  have hh := finiteGibbs_average_bound hw (fun y => B y + linearGaussian (fun z i => t * A z i) g y)
    (fun y => gaussianCross A (fun z i => t * A z i) x y) hb
  exact (abs_sub _ _).trans (by dsimp only [gaussianGibbs] at *; linarith [hb x])

lemma integrable_gaussian_covariance_insertion {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) {K : ℝ}
    (hK : ∀ x y, |gaussianCross A A x y| ≤ K) (x : S) :
    Integrable (fun g => gaussianGibbs w B (fun y i => t * A y i) g x *
      (gaussianCross A (fun y i => t * A y i) x x -
        ∑ z, gaussianGibbs w B (fun y i => t * A y i) g z *
          gaussianCross A (fun y i => t * A y i) x z))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply (MemLp.of_bound (p := 1) (C := 2 * |t| * K) ?_ ?_).integrable le_rfl
  · apply Continuous.aestronglyMeasurable
    apply (continuous_gaussianGibbs hw B _ x).mul
    exact continuous_const.sub (continuous_finsetSum _ (fun y _ =>
      (continuous_gaussianGibbs hw B _ y).mul continuous_const))
  · apply ae_of_all
    intro g
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ gaussianGibbs w B (fun y i => t * A y i) g x from finiteGibbs_nonneg hw _ x)]
    exact (mul_le_mul_of_nonneg_right (finiteGibbs_le_one hw _ x) (abs_nonneg _)).trans
      (by simpa only [one_mul] using gaussian_covariance_difference_bound hw B A t hK g x)

def expectedGaussianLog {n : ℕ} (w B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) : ℝ :=
  ∫ g, Real.log (finitePartition w (fun x => B x + t * linearGaussian A g x))
    ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)

def gaussianLogDerivative {n : ℕ} (w B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ x, ∫ g, gaussianGibbs w B (fun y i => t * A y i) g x *
    (gaussianCross A (fun y i => t * A y i) x x -
      ∑ z, gaussianGibbs w B (fun y i => t * A y i) g z *
        gaussianCross A (fun y i => t * A y i) x z)
    ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)

lemma gaussianLogDerivative_bound {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) {K : ℝ}
    (hK : ∀ x y, |gaussianCross A A x y| ≤ K) :
    |gaussianLogDerivative w B A t| ≤ 2 * |t| * K := by
  unfold gaussianLogDerivative
  rw [← integral_finsetSum _ (fun x _ => integrable_gaussian_covariance_insertion hw B A t hK x)]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (f := fun g => ∑ x, gaussianGibbs w B (fun y i => t * A y i) g x *
        (gaussianCross A (fun y i => t * A y i) x x -
          ∑ z, gaussianGibbs w B (fun y i => t * A y i) g z *
            gaussianCross A (fun y i => t * A y i) x z))
      (C := 2 * |t| * K) (ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs]
      exact finiteGibbs_average_bound hw (fun x => B x + linearGaussian (fun y i => t * A y i) g x) _
        (gaussian_covariance_difference_bound hw B A t hK g))))

theorem gaussian_perturbation_cost {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin (n+1) → ℝ) {K s : ℝ} (hs : 0 ≤ s)
    (hK : ∀ x y, |gaussianCross A A x y| ≤ K) :
    |expectedGaussianLog w B A s - Real.log (finitePartition w B)| ≤ K * s ^ 2 := by
  have hd (t : ℝ) : HasDerivAt (expectedGaussianLog w B A) (gaussianLogDerivative w B A t) t :=
    hasDerivAt_expected_log_gaussian hw B A t
  have hc : Continuous (expectedGaussianLog w B A) := continuous_iff_continuousAt.mpr
    (fun t => (hd t).continuousAt)
  have h0 : expectedGaussianLog w B A 0 = Real.log (finitePartition w B) := by
    simp [expectedGaussianLog]
  have hu : AntitoneOn (fun t => expectedGaussianLog w B A t - K * t ^ 2) (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
      ((hc.sub (continuous_const.mul (continuous_id.pow 2))).continuousOn)
      (fun t _ => ((hd t).sub (((hasDerivAt_id t).pow 2).const_mul K)).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht)
    have hb := (abs_le.mp (gaussianLogDerivative_bound hw B A t hK)).2
    rw [abs_of_nonneg ht0] at hb
    simp only [Nat.cast_ofNat, id_eq, Nat.add_one_sub_one, pow_one, mul_one]
    nlinarith
  have hl : MonotoneOn (fun t => expectedGaussianLog w B A t + K * t ^ 2) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      ((hc.add (continuous_const.mul (continuous_id.pow 2))).continuousOn)
      (fun t _ => ((hd t).add (((hasDerivAt_id t).pow 2).const_mul K)).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht)
    have hb := (abs_le.mp (gaussianLogDerivative_bound hw B A t hK)).1
    rw [abs_of_nonneg ht0] at hb
    simp only [Nat.cast_ofNat, id_eq, Nat.add_one_sub_one, pow_one, mul_one]
    nlinarith
  have huu := hu (Set.mem_Ici.mpr (le_refl (0 : ℝ))) hs hs
  have hll := hl (Set.mem_Ici.mpr (le_refl (0 : ℝ))) hs hs
  dsimp only at huu hll
  rw [h0] at huu hll
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, sub_zero] at huu hll
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Perturbation

section Thermal
variable {S : Type*} [Fintype S]

lemma hasDerivAt_finiteGibbs_mean {w : S → ℝ} (hw : GibbsReference w)
    (B Y : S → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∑ x, finiteGibbs w (fun y => B y+s*Y y) x * Y x)
      (∑ x, finiteGibbs w (fun y => B y+t*Y y) x *
        (Y x-∑ z, finiteGibbs w (fun y => B y+t*Y y) z*Y z)^2) t := by
  have hd x := (hasDerivAt_finiteGibbs hw
    (fun y => (hasDerivAt_const t (B y)).add ((hasDerivAt_id t).mul_const (Y y))) x).mul_const (Y x)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => hd x)
  convert hsum using 1 <;> try rfl
  let p := finiteGibbs w (fun y => B y+t*Y y)
  let m := ∑ z, p z*Y z
  have hp : ∑ x, p x = 1 := finiteGibbs_sum hw _
  change (∑ x, p x * (Y x-m)^2) = ∑ x, (p x * ((0+1*Y x)-∑ y, p y*(0+1*Y y)))*Y x
  simp only [zero_add, one_mul]
  change (∑ x, p x * (Y x-m)^2) = ∑ x, p x*(Y x-m)*Y x
  have he x : p x * (Y x-m)^2 = p x*(Y x-m)*Y x - m*(p x*Y x)+m^2*p x := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp]
  change (∑ x, p x*(Y x-m)*Y x) - m*m + m^2*1 = _
  ring

lemma convexOn_log_finitePartition {w : S → ℝ} (hw : GibbsReference w)
    (B Y : S → ℝ) :
    ConvexOn ℝ Set.univ (fun s => Real.log (finitePartition w (fun y => B y+s*Y y))) := by
  have h1 t := hasDerivAt_log_finitePartition hw
    (fun y => (hasDerivAt_const t (B y)).add ((hasDerivAt_id t).mul_const (Y y)))
  simp only [zero_add, one_mul] at h1
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (continuous_iff_continuousAt.mpr (fun t => (h1 t).continuousAt)).continuousOn
    (fun t _ => (h1 t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_finiteGibbs_mean hw B Y t).hasDerivWithinAt)
  intro t _
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (finiteGibbs_nonneg hw _ x) (sq_nonneg _))

end Thermal

abbrev Spin (N : ℕ) := Fin N → Fin 2
abbrev Patterns (M N : ℕ) := (Fin M × Fin N) → ℝ

def spinValue (x : Fin 2) : ℝ := if x = 0 then -1 else 1

def patternCount (α : ℝ) (N : ℕ) : ℕ := ⌊α * (N : ℝ)⌋₊

def projection {M N : ℕ} (g : Patterns M N) (a : Fin M) (x : Spin N) : ℝ :=
  (∑ i : Fin N, g (a, i) * spinValue (x i)) / Real.sqrt (N : ℝ)

def partitionFunction (α : ℝ) (f : ℝ → ℝ) (N : ℕ)
    (g : Patterns (patternCount α N) N) : ℝ :=
  (∑ x : Spin N, Real.exp (∑ a : Fin (patternCount α N), f (projection g a x))) /
    (2 : ℝ) ^ N

def pressure (α : ℝ) (f : ℝ → ℝ) (N : ℕ)
    (g : Patterns (patternCount α N) N) : ℝ :=
  Real.log (partitionFunction α f N g) / (N : ℝ)

def gaussianPatterns (M N : ℕ) : Measure (Patterns M N) :=
  Measure.pi (fun _ : Fin M × Fin N => gaussianReal 0 1)

def spinOverlap {N : ℕ} (x y : Spin N) : ℝ :=
  (∑ i, spinValue (x i)*spinValue (y i))/(N : ℝ)

def spinTensor {N : ℕ} (p : ℕ) (x : Spin N) (a : Fin p → Fin N) : ℝ :=
  ∏ l, spinValue (x (a l))/Real.sqrt (N : ℝ)

lemma abs_spinValue (x : Fin 2) : |spinValue x| = 1 := by
  unfold spinValue
  split <;> norm_num

lemma spinOverlap_diag {N : ℕ} (hN : 0 < N) (x : Spin N) : spinOverlap x x = 1 := by
  have hv (i : Fin N) : spinValue (x i)*spinValue (x i) = 1 := by
    have := abs_spinValue (x i)
    nlinarith [sq_abs (spinValue (x i))]
  simp [spinOverlap, hv, ne_of_gt hN]

lemma abs_spinOverlap_le {N : ℕ} (hN : 0 < N) (x y : Spin N) :
    |spinOverlap x y| ≤ 1 := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  rw [spinOverlap, abs_div, abs_of_pos hn, div_le_one hn]
  calc
    _ ≤ ∑ i, |spinValue (x i)*spinValue (y i)| := Finset.abs_sum_le_sum_abs _ _
    _ = N := by simp [abs_mul, abs_spinValue]

lemma spinTensor_covariance {N : ℕ} (p : ℕ) (x y : Spin N) :
    (∑ a : Fin p → Fin N, spinTensor p x a * spinTensor p y a) = (spinOverlap x y)^p := by
  have hs : Real.sqrt (N : ℝ)*Real.sqrt (N : ℝ) = N := by
    rw [← sq, Real.sq_sqrt (Nat.cast_nonneg N)]
  unfold spinTensor
  simp_rw [← Finset.prod_mul_distrib, div_mul_div_comm, hs]
  have he := Finset.sum_pow' (Finset.univ : Finset (Fin N))
    (fun i => spinValue (x i)*spinValue (y i)/(N : ℝ)) p
  simpa [spinOverlap, Finset.sum_div] using he.symm

abbrev BulkCoordinate (N : ℕ) := Σ j : Fin N, (Fin (j.val+1) → Fin N)

def bulkCoefficient {N : ℕ} (v : ℕ → ℝ) (x : Spin N) (a : BulkCoordinate N) : ℝ :=
  (v (a.1.val+1)/(2:ℝ)^(a.1.val+1))*spinTensor (a.1.val+1) x a.2

def bulkCovariance (N : ℕ) (v : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ j : Fin N, (v (j.val+1)/(2:ℝ)^(j.val+1))^2*r^(j.val+1)

lemma bulkCoefficient_covariance {N : ℕ} (v : ℕ → ℝ) (x y : Spin N) :
    (∑ a : BulkCoordinate N, bulkCoefficient v x a*bulkCoefficient v y a) =
      bulkCovariance N v (spinOverlap x y) := by
  rw [Fintype.sum_sigma]
  unfold bulkCovariance
  apply Finset.sum_congr rfl
  intro j _
  have he (a : Fin (j.val+1) → Fin N) :
      bulkCoefficient v x ⟨j,a⟩*bulkCoefficient v y ⟨j,a⟩ =
      (v (j.val+1)/(2:ℝ)^(j.val+1))^2*(spinTensor (j.val+1) x a*spinTensor (j.val+1) y a) := by
    unfold bulkCoefficient; ring
  simp_rw [he, ← Finset.mul_sum, spinTensor_covariance]

lemma bulkCovariance_abs_le (N : ℕ) (v : ℕ → ℝ) (hv : ∀ j, |v j| ≤ 2)
    {r : ℝ} (hr : |r| ≤ 1) : |bulkCovariance N v r| ≤ 4/3 := by
  have ha (j : ℕ) : (v j/(2:ℝ)^j)^2 ≤ 4*(1/4:ℝ)^j := by
    have hv2 : (v j)^2 ≤ 4 := by nlinarith [sq_abs (v j), hv j, abs_nonneg (v j)]
    have he : ((2:ℝ)^j)^2 = (4:ℝ)^j := by rw [← pow_mul, Nat.mul_comm j 2, pow_mul]; norm_num
    rw [div_pow, he, one_div_pow]
    simpa [div_eq_mul_inv] using div_le_div_of_nonneg_right hv2 (pow_nonneg (by norm_num : (0:ℝ) ≤ 4) j)
  calc
    _ ≤ ∑ j : Fin N, |(v (j.val+1)/(2:ℝ)^(j.val+1))^2*r^(j.val+1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, 4*(1/4:ℝ)^(j.val+1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_pow]
      calc
        _ ≤ (v (j.val+1)/(2:ℝ)^(j.val+1))^2*1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (abs_nonneg r) hr) (sq_nonneg _)
        _ ≤ _ := by simpa using ha (j.val+1)
    _ = ∑ j ∈ Finset.range N, (1/4:ℝ)^j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => 4*(1/4:ℝ)^(j+1))]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]; ring
    _ ≤ 4/3 := by
      have hh := geom_sum_Ico_le_of_lt_one (m := 0) (n := N)
        (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1)
      norm_num at hh ⊢
      simpa using hh

def indexedBulkCoefficient (N : ℕ) (v : ℕ → ℝ) (x : Spin N) :
    Fin (Fintype.card (BulkCoordinate N)+1) → ℝ :=
  Fin.cons 0 (fun i => bulkCoefficient v x ((Fintype.equivFin (BulkCoordinate N)).symm i))

lemma indexedBulkCoefficient_covariance (N : ℕ) (v : ℕ → ℝ) (x y : Spin N) :
    gaussianCross (indexedBulkCoefficient N v) (indexedBulkCoefficient N v) x y =
      bulkCovariance N v (spinOverlap x y) := by
  unfold gaussianCross indexedBulkCoefficient
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, mul_zero, zero_add, Fin.cons_succ]
  rw [Equiv.sum_comp (Fintype.equivFin (BulkCoordinate N)).symm
    (fun a => bulkCoefficient v x a*bulkCoefficient v y a)]
  exact bulkCoefficient_covariance v x y

lemma bulk_gaussian_perturbation_cost {N : ℕ} (hN : 0 < N)
    {w : Spin N → ℝ} (hw : GibbsReference w) (B : Spin N → ℝ)
    (v : ℕ → ℝ) (hv : ∀ j, |v j| ≤ 2) {s : ℝ} (hs : 0 ≤ s) :
    |expectedGaussianLog w B (indexedBulkCoefficient N v) s -
      Real.log (finitePartition w B)| ≤ (4/3)*s^2 := by
  apply gaussian_perturbation_cost hw B (indexedBulkCoefficient N v) hs
  intro x y
  rw [indexedBulkCoefficient_covariance]
  exact bulkCovariance_abs_le N v hv (abs_spinOverlap_le hN x y)

lemma coordinatewise_lipschitz_sum (n : ℕ) {F : (Fin n → ℝ) → ℝ} {L : Fin n → ℝ}
    (hL : ∀ i, 0 ≤ L i)
    (hF : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |F x-F y| ≤ L i*|x i-y i|)
    (x y : Fin n → ℝ) : |F x-F y| ≤ ∑ i, L i*|x i-y i| := by
  induction n with
  | zero =>
    have he : x = y := Subsingleton.elim _ _
    simp [he]
  | succ n ih =>
    let G := fun z : Fin n → ℝ => F (Fin.cons (y 0) z)
    have hG : ∀ i a b, (∀ j, j ≠ i → a j = b j) →
        |G a-G b| ≤ L i.succ*|a i-b i| := by
      intro i a b hab
      apply hF i.succ
      intro j
      refine Fin.cases (fun _ => rfl) (fun k hk => ?_) j
      simpa only [Fin.cons_succ] using hab k (fun h => hk (congrArg Fin.succ h))
    have hg := ih (fun i => hL i.succ) hG (Fin.tail x) (Fin.tail y)
    have hh := hF 0 x (Fin.cons (y 0) (Fin.tail x)) (fun j hj => by
      obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hj
      rw [← hk]; rfl)
    calc
      _ ≤ |F x-F (Fin.cons (y 0) (Fin.tail x))|+
          |F (Fin.cons (y 0) (Fin.tail x))-F y| := abs_sub_le _ _ _
      _ ≤ L 0*|x 0-y 0|+∑ i : Fin n, L i.succ*|x i.succ-y i.succ| := by
        apply add_le_add
        · simpa using hh
        · simpa [G, Fin.cons_self_tail, Fin.tail] using hg
      _ = _ := by rw [Fin.sum_univ_succ]

lemma memLp_gaussian_coordinatewise {n : ℕ} {F : (Fin n → ℝ) → ℝ} {L : Fin n → ℝ}
    (hm : Measurable F) (hL : ∀ i, 0 ≤ L i)
    (hF : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |F x-F y| ≤ L i*|x i-y i|)
    (p : ℝ≥0) :
    MemLp F p (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hg i : MemLp (fun g : Fin n → ℝ => |g i|) p
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    exact ((memLp_id_gaussianReal p).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)).norm
  have hsum := MemLp.add (memLp_const (|F 0|))
    (memLp_finsetSum' Finset.univ (fun i _ => (hg i).const_mul (L i)))
  apply hsum.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  have hh := coordinatewise_lipschitz_sum n hL hF x 0
  simp only [Pi.zero_apply, sub_zero] at hh
  simp only [Real.norm_eq_abs, Pi.add_apply, Finset.sum_apply]
  have ha := abs_add_le (F x-F 0) (F 0)
  calc
    |F x| ≤ |F x-F 0|+|F 0| := by simpa using ha
    _ ≤ |F 0|+∑ i, L i*|x i| := by linarith

lemma memLp_gaussian_lipschitz {F : ℝ → ℝ} {L : ℝ} (hm : Measurable F)
    (hF : ∀ x, |F x-F 0| ≤ L*|x|) (p : ℝ≥0) :
    MemLp F p (gaussianReal 0 1) := by
  have hg : MemLp (fun x : ℝ => |F 0|+L*|x|) p (gaussianReal 0 1) :=
    (memLp_const (|F 0|)).add ((memLp_id_gaussianReal p).norm.const_mul L)
  apply hg.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs]
  have := abs_add_le (F x-F 0) (F 0)
  have := hF x
  simp only [sub_add_cancel] at *
  linarith

lemma variance_gaussian_lipschitz {F : ℝ → ℝ} {L : ℝ} (hm : Measurable F)
    (hL : 0 ≤ L) (hF : ∀ x, |F x-F 0| ≤ L*|x|) :
    variance F (gaussianReal 0 1) ≤ L^2 := by
  have hLp := memLp_gaussian_lipschitz hm hF 2
  have hsq := (hLp.sub (memLp_const (F 0))).integrable_sq
  have hid : Integrable (fun x : ℝ => L^2*x^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq.const_mul _
  have hb := integral_mono hsq hid (fun x => by
    have := sq_le_sq.mpr (show |F x-F 0| ≤ |L*(|x|)| by
      rw [abs_of_nonneg (mul_nonneg hL (abs_nonneg x))]; exact hF x)
    simpa only [Pi.sub_apply, Pi.pow_apply, mul_pow, sq_abs] using this)
  have hz : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
    have hv := variance_eq_sub (memLp_id_gaussianReal 2 (μ := 0) (v := 1))
    simpa using hv.symm
  rw [integral_const_mul, hz, mul_one] at hb
  calc
    _ = variance (fun x => F x-F 0) (gaussianReal 0 1) :=
      (variance_sub_const hm.aestronglyMeasurable (F 0)).symm
    _ ≤ ∫ x, (F x-F 0)^2 ∂gaussianReal 0 1 :=
      variance_le_expectation_sq (hm.aestronglyMeasurable.sub aestronglyMeasurable_const)
    _ ≤ L^2 := hb

lemma variance_prod_section_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {c : ℝ} (hF : MemLp F 2 (μ.prod ν))
    (hG : MemLp (fun b => ∫ a, F (a,b) ∂μ) 2 ν)
    (hsec : ∀ b, MemLp (fun a => F (a,b)) 2 μ)
    (hv : ∀ b, variance (fun a => F (a,b)) μ ≤ c) :
    variance F (μ.prod ν) ≤ c+variance (fun b => ∫ a, F (a,b) ∂μ) ν := by
  have hpoint b : (∫ a, F (a,b)^2 ∂μ) ≤ c+(∫ a, F (a,b) ∂μ)^2 := by
    have h := hv b
    rw [variance_eq_sub (hsec b)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hs := integral_mono hF.integrable_sq.integral_prod_right
    ((integrable_const c).add hG.integrable_sq) hpoint
  simp only [Pi.add_apply] at hs
  rw [integral_add (integrable_const _) hG.integrable_sq, integral_const,
    probReal_univ, one_smul] at hs
  rw [variance_eq_sub hF, variance_eq_sub hG]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hF.integrable_sq,
    integral_prod_symm _ (hF.integrable (by norm_num))]
  linarith

lemma variance_gaussian_coordinatewise (n : ℕ) {F : (Fin n → ℝ) → ℝ} {L : Fin n → ℝ}
    (hm : Measurable F) (hL : ∀ i, 0 ≤ L i)
    (hF : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |F x-F y| ≤ L i*|x i-y i|) :
    variance F (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) ≤ ∑ i, (L i)^2 := by
  induction n with
  | zero =>
    have he : F = fun _ => F 0 := by ext x; congr 1; exact Subsingleton.elim _ _
    rw [he, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let μ := gaussianReal 0 1
    let ν := Measure.pi (fun _ : Fin n => μ)
    let C := fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)
    let G := fun x : Fin n → ℝ => ∫ a, C (a,x) ∂μ
    have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) => (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : ℝ × (Fin n → ℝ) → ℝ))
      · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_snd : Measurable (Prod.snd : ℝ × (Fin n → ℝ) → (Fin n → ℝ)))
    have hCm : Measurable C := hm.comp hcons
    have hGm : Measurable G := hCm.stronglyMeasurable.integral_prod_left'.measurable
    have hhead x a : |C (a,x)-C (0,x)| ≤ L 0*|a| := by
      have hh := hF 0 (Fin.cons a x) (Fin.cons 0 x) (fun j hj => by
        obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hj
        rw [← hk]; rfl)
      simpa [C] using hh
    have hsec x : MemLp (fun a => C (a,x)) 2 μ :=
      memLp_gaussian_lipschitz
        (hCm.comp (measurable_id.prodMk measurable_const)) (hhead x) 2
    have hGlip : ∀ i x y, (∀ j, j ≠ i → x j = y j) →
        |G x-G y| ≤ L i.succ*|x i-y i| := by
      intro i x y hxy
      have hb a : |C (a,x)-C (a,y)| ≤ L i.succ*|x i-y i| := by
        apply hF i.succ
        intro j
        refine Fin.cases (fun _ => rfl) (fun k hk => ?_) j
        simpa only [Fin.cons_succ] using hxy k (fun he => hk (congrArg Fin.succ he))
      have hh := norm_integral_le_of_norm_le_const (μ := μ) (f := fun a => C (a,x)-C (a,y))
        (ae_of_all μ (fun a => by simpa only [Real.norm_eq_abs] using hb a))
      rw [integral_sub ((hsec x).integrable (by norm_num)) ((hsec y).integrable (by norm_num))] at hh
      simpa [G] using hh
    have hG2 := memLp_gaussian_coordinatewise hGm (fun i => hL i.succ) hGlip 2
    have hF2 := memLp_gaussian_coordinatewise hm hL hF 2
    have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
    have hC2 : MemLp C 2 (μ.prod ν) := by
      have hh := hF2.comp_measurePreserving he
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq, Function.comp_def, C, ν, ENNReal.coe_ofNat] using hh
    have hp := variance_prod_section_bound hC2 hG2 hsec
      (fun x => variance_gaussian_lipschitz
        (hCm.comp (measurable_id.prodMk measurable_const)) (hL 0) (hhead x))
    have hi := ih hGm (fun i => hL i.succ) hGlip
    have heq : variance C (μ.prod ν) = variance F (Measure.pi (fun _ : Fin (n+1) => μ)) := by
      have hh := he.variance_fun_comp hm.aemeasurable
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using hh
    rw [heq] at hp
    rw [Fin.sum_univ_succ]
    exact hp.trans (add_le_add le_rfl hi)

section GaussianConcentration
variable {S : Type*} [Fintype S]

lemma log_finitePartition_coordinate_lipschitz {n : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (B : S → ℝ) (A : S → Fin n → ℝ)
    (L : Fin n → ℝ) (hA : ∀ x i, |A x i| ≤ L i) (t : ℝ)
    (i : Fin n) (g h : Fin n → ℝ) (hgh : ∀ j, j ≠ i → g j = h j) :
    |Real.log (finitePartition w (fun x => B x+t*linearGaussian A g x))-
      Real.log (finitePartition w (fun x => B x+t*linearGaussian A h x))| ≤
      (|t| *L i)*|g i-h i| := by
  apply log_finitePartition_lipschitz hw
  intro x
  have he : linearGaussian A g x-linearGaussian A h x = A x i*(g i-h i) := by
    unfold linearGaussian
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · ring
    · intro j _ hji
      rw [hgh j hji]; ring
    · simp
  have he' : B x+t*linearGaussian A g x-(B x+t*linearGaussian A h x) =
      t*(linearGaussian A g x-linearGaussian A h x) := by ring
  rw [he', he, abs_mul, abs_mul]
  calc
    _ ≤ |t| *(L i*|g i-h i|) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hA x i) (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

lemma variance_gaussian_log_finitePartition {n : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (B : S → ℝ) (A : S → Fin n → ℝ)
    (L : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i) (hA : ∀ x i, |A x i| ≤ L i) (t : ℝ) :
    variance (fun g => Real.log (finitePartition w (fun x => B x+t*linearGaussian A g x)))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) ≤ t^2*∑ i, (L i)^2 := by
  have hb := variance_gaussian_coordinatewise n
    (continuous_log_finitePartition hw B A t).measurable
    (L := fun i => |t| *L i) (fun i => mul_nonneg (abs_nonneg _) (hL i))
    (log_finitePartition_coordinate_lipschitz hw B A L hA t)
  have he : (∑ i, (|t| *L i)^2) = t^2*∑ i, (L i)^2 := by
    simp_rw [mul_pow, sq_abs, Finset.mul_sum]
  rwa [he] at hb

end GaussianConcentration

lemma abs_spinTensor_independent {N : ℕ} (p : ℕ) (x y : Spin N)
    (a : Fin p → Fin N) : |spinTensor p x a| = |spinTensor p y a| := by
  unfold spinTensor
  simp_rw [Finset.abs_prod, abs_div, abs_spinValue]

lemma abs_bulkCoefficient_independent {N : ℕ} (v : ℕ → ℝ) (x y : Spin N)
    (a : BulkCoordinate N) : |bulkCoefficient v x a| = |bulkCoefficient v y a| := by
  unfold bulkCoefficient
  rw [abs_mul, abs_mul, abs_spinTensor_independent _ x y]

lemma abs_indexedBulkCoefficient_independent {N : ℕ} (v : ℕ → ℝ) (x y : Spin N)
    (i : Fin (Fintype.card (BulkCoordinate N)+1)) :
    |indexedBulkCoefficient N v x i| = |indexedBulkCoefficient N v y i| := by
  refine Fin.cases rfl (fun j => ?_) i
  exact abs_bulkCoefficient_independent v x y _

lemma bulk_gaussian_variance {N : ℕ} (hN : 0 < N)
    {w : Spin N → ℝ} (hw : GibbsReference w) (B : Spin N → ℝ)
    (v : ℕ → ℝ) (hv : ∀ j, |v j| ≤ 2) (s : ℝ) :
    variance (fun g => Real.log (finitePartition w
      (fun x => B x+s*linearGaussian (indexedBulkCoefficient N v) g x)))
      (Measure.pi (fun _ : Fin (Fintype.card (BulkCoordinate N)+1) => gaussianReal 0 1)) ≤
      (4/3)*s^2 := by
  let x₀ : Spin N := fun _ => 0
  have hb := variance_gaussian_log_finitePartition hw B (indexedBulkCoefficient N v)
    (fun i => |indexedBulkCoefficient N v x₀ i|) (fun _ => abs_nonneg _)
    (fun x i => (abs_indexedBulkCoefficient_independent v x x₀ i).le) s
  have he : (∑ i, |indexedBulkCoefficient N v x₀ i|^2) = bulkCovariance N v 1 := by
    simp_rw [sq_abs, pow_two]
    change gaussianCross (indexedBulkCoefficient N v) (indexedBulkCoefficient N v) x₀ x₀ = _
    rw [indexedBulkCoefficient_covariance, spinOverlap_diag hN]
  rw [he] at hb
  have hc := (le_abs_self (bulkCovariance N v 1)).trans
    (bulkCovariance_abs_le N v hv (by norm_num))
  calc
    _ ≤ s^2*bulkCovariance N v 1 := hb
    _ ≤ s^2*(4/3) := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = _ := by ring

variable {S : Type*} [Fintype S]

def replicaMean {n r : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (D : (Fin r → S) → ℝ) (g : Fin n → ℝ) : ℝ :=
  ∑ σ, replicaGibbs w B C g σ*D σ

def expectedReplica {n r : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (D : (Fin r → S) → ℝ) : ℝ :=
  ∫ g, replicaMean w B C D g ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)

lemma replicaMean_abs_le {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) {D : (Fin r → S) → ℝ}
    {K : ℝ} (hD : ∀ σ, |D σ| ≤ K) (g : Fin n → ℝ) :
    |replicaMean w B C D g| ≤ K := by
  calc
    _ ≤ ∑ σ, replicaGibbs w B C g σ*|D σ| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
    _ ≤ ∑ σ : Fin r → S, replicaGibbs w B C g σ*K := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (hD σ) (replicaGibbs_nonneg hw B C g σ)
    _ = K := by rw [← Finset.sum_mul, replicaGibbs_sum hw, one_mul]

lemma integrable_replicaMean {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (D : (Fin r → S) → ℝ) :
    Integrable (replicaMean w B C D) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply Integrable.of_bound
    (continuous_finsetSum _ (fun σ _ => (continuous_replicaGibbs hw B C σ).mul continuous_const)).aestronglyMeasurable
    (∑ σ, |D σ|)
  apply ae_of_all
  intro g
  exact replicaMean_abs_le hw B C (fun σ =>
    Finset.single_le_sum (fun τ _ => abs_nonneg (D τ)) (Finset.mem_univ σ)) g

lemma integrable_linear_mul_replica {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (x : S) (σ : Fin r → S) :
    Integrable (fun g => linearGaussian A g x*replicaGibbs w B C g σ)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply (integrable_linearGaussian A x).mul_bdd
    (continuous_replicaGibbs hw B C σ).aestronglyMeasurable (c := 1)
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
  exact replicaGibbs_le_one hw B C g σ

lemma integrable_replica_covariance {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (x : S) (σ : Fin r → S) :
    Integrable (fun g => replicaGibbs w B C g σ*
      (∑ l, (gaussianCross A C x (σ l)-∑ z, gaussianGibbs w B C g z*gaussianCross A C x z)))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  let K := ∑ z, |gaussianCross A C x z|
  apply Integrable.of_bound
    ((continuous_replicaGibbs hw B C σ).mul
      (continuous_finsetSum _ (fun l _ => continuous_const.sub
        (continuous_finsetSum _ (fun z _ =>
          (continuous_gaussianGibbs hw B C z).mul continuous_const))))).aestronglyMeasurable
    (∑ l, (|gaussianCross A C x (σ l)|+K))
  apply ae_of_all
  intro g
  simp only [Pi.mul_apply, Pi.sub_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
  calc
    _ ≤ 1*|∑ l, (gaussianCross A C x (σ l)-∑ z, gaussianGibbs w B C g z*gaussianCross A C x z)| :=
      mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      exact (abs_sub _ _).trans (add_le_add le_rfl
        (finiteGibbs_average_bound hw _ _ (fun z =>
          show |gaussianCross A C x z| ≤ ∑ y, |gaussianCross A C x y| from
            Finset.single_le_sum (fun y _ => abs_nonneg (gaussianCross A C x y)) (Finset.mem_univ z))))

lemma gaussian_replica_test_insertion {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    (∫ g, ∑ σ : Fin (r+1) → S,
      D σ*(linearGaussian A g (σ 0)*replicaGibbs w B C g σ)
      ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
    ∫ g, ∑ σ : Fin (r+1) → S, D σ*(replicaGibbs w B C g σ*
      (∑ l, (gaussianCross A C (σ 0) (σ l)-
        ∑ z, gaussianGibbs w B C g z*gaussianCross A C (σ 0) z)))
      ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
  rw [integral_finsetSum _ (fun σ _ => (integrable_linear_mul_replica hw B A C (σ 0) σ).const_mul (D σ)),
    integral_finsetSum _ (fun σ _ => (integrable_replica_covariance hw B A C (σ 0) σ).const_mul (D σ))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_const_mul, integral_const_mul, gaussian_replica_insertion hw]

lemma replicaMean_marginal_zero {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (F : S → ℝ) (g : Fin n → ℝ) :
    replicaMean w B C (fun σ : Fin (r+1) → S => F (σ 0)) g =
      ∑ x, gaussianGibbs w B C g x*F x := by
  classical
  unfold replicaMean
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1) => S))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have he (τ : Fin r → S) :
      replicaGibbs w B C g ((Fin.consEquiv (fun _ : Fin (r+1) => S)) (x,τ))*
        F (((Fin.consEquiv (fun _ : Fin (r+1) => S)) (x,τ)) 0) =
      gaussianGibbs w B C g x*F x*replicaGibbs w B C g τ := by
    simp [replicaGibbs, Fin.consEquiv, Fin.prod_univ_succ]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, replicaGibbs_sum hw, mul_one]

end IsingPerceptron

end

end OAI
