import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SpinSpaceIntegrable

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

abbrev slaterDirectDensity {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (z : SlaterParticle) : ℝ := ∑ i : Fin n, ‖φ i z‖^2

abbrev slaterExchangeDensity {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (z : SlaterParticle × SlaterParticle) : ℝ :=
  ‖∑ i : Fin n, φ i z.1 * conj (φ i z.2)‖^2

lemma slater_repulsion_spinSpace {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) :
    formRepulsion (slaterForm φ) = (1/2:ℝ) * ∑ j : Fin n, ∑ k : Fin n,
      if j ≠ k then ∫ z, ‖slater φ z‖^2 / ‖(z j).2-(z k).2‖
        ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure) else 0 := by
  rw [formRepulsion_ordered]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j ≠ k
  · simp only [ite_eq_left hjk]
    exact (spinSpace_integral _ (slater_coulomb_integrable hφ hc j k hjk)).symm
  · simp only [ite_eq_right hjk,Finset.sum_const_zero]

theorem slaterForm_repulsion {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z) * φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    formRepulsion (slaterForm φ) = (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
      (slaterDirectDensity φ z.1 * slaterDirectDensity φ z.2 - slaterExchangeDensity φ z) /
        ‖z.1.2-z.2.2‖ ∂slaterParticleMeasure.prod slaterParticleMeasure := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hi (j k : Fin n) (hjk : j ≠ k) :
      Integrable (fun z : Fin n → SlaterParticle => ‖(z j).2-(z k).2‖⁻¹ * ‖slater φ z‖^2)
        (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
    simpa only [div_eq_mul_inv,mul_comm] using slater_coulomb_integrable hφ hc j k hjk
  have ht := slater_two_body hl ho (fun z : SlaterParticle × SlaterParticle => ‖z.1.2-z.2.2‖⁻¹) hi
  rw [slater_repulsion_spinSpace hφ hc]
  simpa only [div_eq_mul_inv,mul_comm] using congrArg (fun x : ℝ => (1/2:ℝ)*x) ht

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma smooth_pair_integrable {n : ℕ} {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x => ‖f x‖^2 / ‖x i-x j‖) :=
  pair_integrable i j hij (hf.continuous.memLp_of_hasCompactSupport hc)
    (fun _a => (smooth_derivative_continuous hf _).memLp_of_hasCompactSupport (compact_derivative hc _))
    (fun a _g hg hgc => smooth_weak_gradient hf hc hg hgc (direction i a))

lemma smooth_nuclear_integrable {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun x => ‖f x‖^2 / ‖x‖) :=
  linear_coulomb_integrable (ContinuousLinearMap.id ℝ Space)
    (fun a => EuclideanSpace.single a 1) (fun _ => rfl)
    (hf.continuous.memLp_of_hasCompactSupport hc)
    (fun _a => (smooth_derivative_continuous hf _).memLp_of_hasCompactSupport (compact_derivative hc _))
    (fun a _g hg hgc => smooth_weak_gradient hf hc hg hgc (EuclideanSpace.single a 1))

lemma orbital_coulomb_product_integrable {f g : SlaterParticle → ℂ}
    (hf : ∀ s, ContDiff ℝ ∞ (fun x : Space => f (s,x)))
    (hg : ∀ s, ContDiff ℝ ∞ (fun x : Space => g (s,x)))
    (hfc : ∀ s, HasCompactSupport (fun x : Space => f (s,x)))
    (hgc : ∀ s, HasCompactSupport (fun x : Space => g (s,x))) :
    Integrable (fun z : SlaterParticle × SlaterParticle =>
      (‖f z.1‖^2 * ‖g z.2‖^2) / ‖z.1.2-z.2.2‖)
      (slaterParticleMeasure.prod slaterParticleMeasure) := by
  apply ((measurePreserving_finTwoArrow slaterParticleMeasure).integrable_comp_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding).mp
  change Integrable (fun z : Fin 2 → SlaterParticle =>
    (‖f (z 0)‖^2 * ‖g (z 1)‖^2) / ‖(z 0).2-(z 1).2‖)
      (Measure.pi fun _ : Fin 2 => slaterParticleMeasure)
  apply spinSpace_integrable
  · have hfm := (continuous_prod_of_discrete_left.mpr (fun s => (hf s).continuous)).measurable
    have hgm := (continuous_prod_of_discrete_left.mpr (fun s => (hg s).continuous)).measurable
    exact (((hfm.comp (measurable_pi_apply 0)).norm.pow_const 2).mul
      ((hgm.comp (measurable_pi_apply 1)).norm.pow_const 2)).div
      (((measurable_pi_apply 0).snd.sub (measurable_pi_apply 1).snd).norm)
  · intro s
    let φ : Fin 2 → SlaterParticle → ℂ := ![f,g]
    have hφ (i : Fin 2) (t : Fin 2) : ContDiff ℝ ∞ (fun x : Space => φ i (t,x)) := by
      fin_cases i
      · exact hf t
      · exact hg t
    have hc (i : Fin 2) (t : Fin 2) : HasCompactSupport (fun x : Space => φ i (t,x)) := by
      fin_cases i
      · exact hfc t
      · exact hgc t
    have hi := smooth_pair_integrable (slater_spatial_tensor_smooth hφ s 1)
      (slater_spatial_tensor_compact hc s 1) (0 : Fin 2) 1 (by decide)
    simpa only [slaterTensor,Fin.prod_univ_two,Equiv.Perm.one_apply,φ,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,norm_mul,mul_pow,
      slaterParticles] using hi

lemma slater_direct_coulomb_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) :
    Integrable (fun z : SlaterParticle × SlaterParticle =>
      ((∑ i : Fin n, ‖φ i z.1‖^2) * (∑ i : Fin n, ‖φ i z.2‖^2)) / ‖z.1.2-z.2.2‖)
      (slaterParticleMeasure.prod slaterParticleMeasure) := by
  simp only [Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact orbital_coulomb_product_integrable (hφ j) (hφ i) (hc j) (hc i)

lemma orbital_nuclear_integrable {φ : SlaterParticle → ℂ}
    (hφ : ∀ s, ContDiff ℝ ∞ (fun x : Space => φ (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => φ (s,x))) :
    Integrable (fun z => ‖φ z‖^2 / ‖z.2‖) slaterParticleMeasure := by
  have hm : Measurable (fun z : SlaterParticle => ‖φ z‖^2 / ‖z.2‖) :=
    (((continuous_prod_of_discrete_left.mpr (fun s => (hφ s).continuous)).measurable.norm).pow_const 2).div
      measurable_snd.norm
  exact (integrable_prod_iff hm.aestronglyMeasurable).mpr
    ⟨Eventually.of_forall (fun s => smooth_nuclear_integrable (hφ s) (hc s)),Integrable.of_finite⟩

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma memLp_potential_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} {V : α → ℝ} (hf : Measurable f) (hV : Measurable V)
    (hVn : ∀ x, 0 ≤ V x) (hi : Integrable (fun x => V x * ‖f x‖^2) μ) :
    MemLp (fun x => (Real.sqrt (V x) : ℂ)*f x) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    ((Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hV)).mul hf).aestronglyMeasurable).mpr
  change Integrable (fun x => ‖(Real.sqrt (V x) : ℂ)*f x‖^2) μ
  simpa only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hVn _)] using hi

lemma slaterForm_nuclear {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    formNuclear (slaterForm φ) = ∑ i : Fin n, ∫ z : SlaterParticle,
      ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hi (i : Fin n) : Integrable (fun z => ‖z.2‖⁻¹*‖φ i z‖^2) slaterParticleMeasure := by
    simpa only [div_eq_mul_inv,mul_comm] using orbital_nuclear_integrable (hφ i) (hc i)
  have hv (i : Fin n) := memLp_potential_mul
    (continuous_prod_of_discrete_left.mpr (fun s => (hφ i s).continuous)).measurable
    measurable_snd.norm.inv (fun z : SlaterParticle => inv_nonneg.mpr (norm_nonneg z.2)) (hi i)
  have ht := slater_nonnegative_potential hl ho (fun z : SlaterParticle => ‖z.2‖⁻¹)
    (fun z => inv_nonneg.mpr (norm_nonneg z.2)) hv
  have his (j : Fin n) := slater_nuclear_integrable hφ hc j
  have hs : (∫ z : Fin n → SlaterParticle, (∑ j, ‖(z j).2‖⁻¹)*‖slater φ z‖^2
      ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure)) = formNuclear (slaterForm φ) := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun j _ => by
      simpa only [div_eq_mul_inv,mul_comm] using his j)]
    unfold formNuclear
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∫ z : Fin n → SlaterParticle, ‖slater φ z‖^2 / ‖(z j).2‖
          ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [div_eq_mul_inv,mul_comm]
      _ = _ := spinSpace_integral _ (his j)
  rw [hs] at ht
  simpa only [div_eq_mul_inv,mul_comm] using ht

theorem slaterForm_repulsion_le_direct {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    formRepulsion (slaterForm φ) ≤ (1/2:ℝ)*∫ z : SlaterParticle × SlaterParticle,
      (slaterDirectDensity φ z.1 * slaterDirectDensity φ z.2) / ‖z.1.2-z.2.2‖
        ∂slaterParticleMeasure.prod slaterParticleMeasure := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hi (j k : Fin n) (hjk : j ≠ k) :
      Integrable (fun z : Fin n → SlaterParticle => ‖(z j).2-(z k).2‖⁻¹*‖slater φ z‖^2)
        (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
    simpa only [div_eq_mul_inv,mul_comm] using slater_coulomb_integrable hφ hc j k hjk
  have hd : Integrable (fun z : SlaterParticle × SlaterParticle =>
      ‖z.1.2-z.2.2‖⁻¹ * ((∑ i, ‖φ i z.1‖^2)*(∑ i, ‖φ i z.2‖^2)))
        (slaterParticleMeasure.prod slaterParticleMeasure) := by
    simpa only [div_eq_mul_inv,mul_comm] using slater_direct_coulomb_integrable hφ hc
  have ht := slater_two_body_le_direct hl ho (fun z : SlaterParticle × SlaterParticle => ‖z.1.2-z.2.2‖⁻¹)
    (fun z => inv_nonneg.mpr (norm_nonneg _)) hi hd
  rw [slater_repulsion_spinSpace hφ hc]
  simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 1/2)

end CoulombAtom

end

end OAI
