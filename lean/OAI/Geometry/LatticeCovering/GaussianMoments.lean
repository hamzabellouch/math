import OAI.Geometry.LatticeCovering.MeanHoles

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.Assembly
open PrimeKernel MeasureTheory Inputs Filter Topology
open scoped Pointwise




theorem all_dimensions_main_reduction_circuits {α β γ C₀ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hC₀ : 0 ≤ C₀)
    (hGaussian : ∀ᶠ n : ℕ in atTop, GaussianPositions α β γ C₀ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_main_reduction_circuits hα hβ hγ hC₀ hGaussian
  exact FiniteDimensions.absorb_finitely_many_dimensions ⟨C,h⟩


end SingleLatticeCovering.Assembly

end

noncomputable section
namespace SingleLatticeCovering.Assembly
open PrimeKernel Inputs MeasureTheory Filter
open scoped Pointwise




theorem main_reduction_to_EK_via_circuits {α β γ C₀ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hC₀ : 0 ≤ C₀)
    (hEK : ∀ᶠ n : ℕ in atTop, EldanKlartagAt α β γ C₀ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  exact all_dimensions_main_reduction_circuits hα (div_pos hβ (by norm_num)) hγ hC₀
    (gaussianPositions_of_eventual_EldanKlartagAt hβ hγ hEK)


end SingleLatticeCovering.Assembly

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

section




noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace BigOperators


lemma coordinate_memLp {n : ℕ} {μ : Measure (E n)} {p : ℝ≥0∞}
    (hμ : MemLp id p μ) (i : Fin n) : MemLp (fun x : E n => x i) p μ := by
  simpa only [Function.comp_def,id_eq,EuclideanSpace.proj,PiLp.proj_apply] using
    hμ.continuousLinearMap_comp (EuclideanSpace.proj i : E n →L[ℝ] ℝ)

lemma isotropic_coordinate_second {n : ℕ} {μ : Measure (E n)}
    (hiso : IsIsotropic μ) (i : Fin n) : (∫ x, (x i)^2 ∂μ)=1 := by
  have h := hiso.2 (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
  simpa only [EuclideanSpace.inner_single_left,one_mul,EuclideanSpace.inner_single_right,
    PiLp.single_apply,mul_one,one_pow,←sq,map_one,ite_true] using h

lemma isotropic_norm_sq {n : ℕ} {μ : Measure (E n)}
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) : (∫ x, ‖x‖^2 ∂μ)=(n : ℝ) := by
  have hi (i : Fin n) : Integrable (fun x : E n => (x i)^2) μ :=
    (coordinate_memLp hμ i).integrable_sq
  have he (x : E n) : ‖x‖^2=∑ i, (x i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]
  simp only [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [isotropic_coordinate_second hiso,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]

end SingleLatticeCovering.Isotropization

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators

lemma integral_norm_le_sqrt_second {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  have H := variance_nonneg (fun x => |f x|) μ
  rw [variance_eq_sub (by simpa only [Real.norm_eq_abs] using hf.norm)] at H
  simp only [Pi.pow_apply,sq_abs] at H
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))).mpr (by linarith)

lemma inner_memLp_two {n : ℕ} {μ : Measure (E n)} (hμ : MemLp id 2 μ) (x : E n) :
    MemLp (fun y : E n => ⟪x,y⟫) 2 μ := by
  simpa only [Function.comp_def,id_eq,innerSL_apply_apply] using
    hμ.continuousLinearMap_comp (innerSL ℝ x : E n →L[ℝ] ℝ)

lemma isotropic_abs_inner_integral {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (x : E n) :
    (∫ y, |⟪x,y⟫| ∂μ) ≤ ‖x‖ := by
  have H := integral_norm_le_sqrt_second (inner_memLp_two hμ x)
  have he : (∫ y, ⟪x,y⟫^2 ∂μ)=‖x‖^2 := by
    simpa only [pow_two,real_inner_self_eq_norm_sq] using hiso.2 x x
  rw [he,Real.sqrt_sq (norm_nonneg x)] at H
  exact H

lemma isotropic_norm_integral {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) :
    (∫ x, ‖x‖ ∂μ) ≤ Real.sqrt (n : ℝ) := by
  have H := integral_norm_le_sqrt_second hμ.norm
  simpa only [id_eq,abs_norm,isotropic_norm_sq hμ hiso] using H

lemma exp_negative_lipschitz {u v : ℝ} (hu : u ≤ 0) (hv : v ≤ 0) :
    |Real.exp u-Real.exp v| ≤ |u-v| := by
  wlog huv : u ≤ v generalizing u v
  · rw [abs_sub_comm (Real.exp u),abs_sub_comm u]
    exact this hv hu (le_of_not_ge huv)
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr huv)),
    abs_of_nonpos (sub_nonpos.mpr huv)]
  have hlow := Real.add_one_le_exp (u-v)
  have hpos : 0 ≤ 1-Real.exp (u-v) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (sub_nonpos.mpr huv))
  have hmul : Real.exp v*(1-Real.exp (u-v)) ≤ 1-Real.exp (u-v) :=
    mul_le_of_le_one_left hpos (Real.exp_le_one_iff.mpr hv)
  rw [mul_sub,mul_one,←Real.exp_add] at hmul
  rw [show v+(u-v)=u by ring] at hmul
  linarith

def radialGaussianAverage {n : ℕ} (μ : Measure (E n)) (s : ℝ) : ℝ :=
  ∫ x, Real.exp (-s^2*‖x‖^2/2) ∂μ

lemma gaussianKernel_bounded {n : ℕ} (s : ℝ) (x : E n) :
    |Real.exp (-s^2*‖x‖^2/2)| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg s)) (sq_nonneg _)) (by norm_num))

lemma gaussianKernel_integrable {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] (s : ℝ) :
    Integrable (fun x => Real.exp (-s^2*‖x‖^2/2)) μ := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded s x)

lemma gaussianKernel_covariance_bound {n : ℕ} (s : ℝ) (x y : E n) :
    |Real.exp (-s^2*‖x-y‖^2/2)-Real.exp (-s^2*‖x‖^2/2)*Real.exp (-s^2*‖y‖^2/2)|
      ≤ s^2*|⟪x,y⟫| := by
  rw [←Real.exp_add]
  have hn (z : E n) : -s^2*‖z‖^2/2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg s)) (sq_nonneg _)) (by norm_num)
  have H := exp_negative_lipschitz (hn (x-y)) (add_nonpos (hn x) (hn y))
  have he : -s^2*‖x-y‖^2/2-(-s^2*‖x‖^2/2+ -s^2*‖y‖^2/2)=s^2*⟪x,y⟫ := by
    rw [norm_sub_sq_real]
    ring
  simpa only [he,abs_mul,abs_of_nonneg (sq_nonneg s)] using H



end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

noncomputable def phase {n : ℕ} (s : ℝ) (x g : E n) : ℂ :=
  Complex.exp ((s*⟪x,g⟫ : ℝ)*Complex.I)

lemma norm_phase {n : ℕ} (s : ℝ) (x g : E n) : ‖phase s x g‖=1 := by
  simp [phase,Complex.norm_exp]

lemma charFun_phase {n : ℕ} (μ : Measure (E n)) (s : ℝ) (g : E n) :
    charFun μ (s•g) = ∫ x, phase s x g ∂μ := by
  simp only [charFun_apply,phase,inner_smul_right,Complex.ofReal_mul]

lemma phase_gaussian_integral {n : ℕ} (s : ℝ) (x : E n) :
    (∫ g, phase s x g ∂stdGaussian (E n))=(Real.exp (-s^2*‖x‖^2/2) : ℂ) := by
  have H := charFun_stdGaussian (s•x)
  rw [charFun_apply] at H
  have he : (fun g : E n => Complex.exp ((⟪g,s•x⟫ : ℝ)*Complex.I))=phase s x := by
    funext g
    simp only [phase,inner_smul_right,real_inner_comm]
  rw [he] at H
  rw [norm_smul,Real.norm_eq_abs,←Complex.ofReal_pow,mul_pow,sq_abs] at H
  simpa only [Complex.ofReal_exp,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,neg_mul] using H

lemma phase_product_integrable {n : ℕ} (μ ν : Measure (E n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : ℝ) :
    Integrable (fun p : E n × E n => phase s p.1 p.2) (μ.prod ν) := by
  apply (integrable_const (1:ℝ)).mono' (by unfold phase; fun_prop)
  exact Filter.Eventually.of_forall (fun p => (norm_phase s p.1 p.2).le)

lemma gaussian_char_average {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] (s : ℝ) :
    (∫ g, charFun μ (s•g) ∂stdGaussian (E n))=(radialGaussianAverage μ s : ℂ) := by
  simp only [charFun_phase]
  rw [integral_integral_swap (phase_product_integrable (stdGaussian (E n)) μ s |>.congr (by
    exact Filter.Eventually.of_forall (fun p => by change phase s p.1 p.2 = phase s p.2 p.1; simp only [phase,real_inner_comm])))]
  simp only [phase_gaussian_integral]
  rw [integral_complex_ofReal]
  rfl

lemma phase_sub {n : ℕ} (s : ℝ) (x y g : E n) :
    phase s (x-y) g=phase s x g*conj (phase s y g) := by
  simp only [phase,inner_sub_left,mul_sub,Complex.ofReal_sub,sub_mul,Complex.exp_sub,
    ←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,Complex.exp_neg]
  exact div_eq_mul_inv _ _

lemma charFun_differenceLaw {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] (t : E n) :
    charFun ((μ.prod μ).map (fun p : E n × E n => p.1-p.2)) t = (‖charFun μ t‖^2 : ℝ) := by
  rw [charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  have hint : Integrable (fun p : E n × E n => Complex.exp ((⟪p.1-p.2,t⟫ : ℝ)*Complex.I)) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun p => by simp [Complex.norm_exp])
  rw [integral_prod _ hint]
  have he (x y : E n) : Complex.exp ((⟪x-y,t⟫ : ℝ)*Complex.I) =
      Complex.exp ((⟪x,t⟫ : ℝ)*Complex.I)*conj (Complex.exp ((⟪y,t⟫ : ℝ)*Complex.I)) := by
    simpa only [phase,one_mul] using phase_sub 1 x y t
  simp only [he,integral_const_mul,integral_mul_const,integral_conj,←charFun_apply]
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]

lemma gaussian_char_secondMoment {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)‖^2 ∂stdGaussian (E n))=
      ∫ x, ∫ y, Real.exp (-s^2*‖x-y‖^2/2) ∂μ ∂μ := by
  let ν := (μ.prod μ).map (fun p : E n × E n => p.1-p.2)
  have : IsProbabilityMeasure ν := inferInstance
  have H := gaussian_char_average ν s
  simp only [ν,charFun_differenceLaw,integral_complex_ofReal] at H
  have H' : (∫ g, ‖charFun μ (s•g)‖^2 ∂stdGaussian (E n))=radialGaussianAverage ν s :=
    Complex.ofReal_injective H
  rw [H',radialGaussianAverage,integral_map (by fun_prop) (by fun_prop)]
  apply integral_prod
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded s (p.1-p.2))



end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

lemma charFun_gaussian_integrable {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    Integrable (fun g => charFun μ (s•g)) (stdGaussian (E n)) := by
  apply (integrable_const (1:ℝ)).mono' ((continuous_charFun.comp (by fun_prop)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun _ => norm_charFun_le_one _)

lemma charFun_gaussian_sq_integrable {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    Integrable (fun g => ‖charFun μ (s•g)‖^2) (stdGaussian (E n)) := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun _ => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _))

lemma complex_center_sq (z : ℂ) (a : ℝ) :
    ‖z-(a:ℂ)‖^2=‖z‖^2-2*a*z.re+a^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,sub_zero]
  ring

lemma gaussian_char_variance_identity {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖^2 ∂stdGaussian (E n))=
      (∫ g, ‖charFun μ (s•g)‖^2 ∂stdGaussian (E n))-(radialGaussianAverage μ s)^2 := by
  have hr : Integrable (fun g => (charFun μ (s•g)).re) (stdGaussian (E n)) :=
    (charFun_gaussian_integrable μ s).re
  have hc := hr.const_mul (2*radialGaussianAverage μ s)
  simp only [complex_center_sq]
  rw [integral_add (f := fun g => ‖charFun μ (s•g)‖^2-2*radialGaussianAverage μ s*(charFun μ (s•g)).re)
      (g := fun _ => (radialGaussianAverage μ s)^2)
      ((charFun_gaussian_sq_integrable μ s).sub hc) (integrable_const _),
    integral_sub (f := fun g => ‖charFun μ (s•g)‖^2)
      (g := fun g => 2*radialGaussianAverage μ s*(charFun μ (s•g)).re)
      (charFun_gaussian_sq_integrable μ s) hc,
    integral_const_mul]
  have H : (∫ g, (charFun μ (s•g)).re ∂stdGaussian (E n))=radialGaussianAverage μ s := by
    have HH := integral_re (charFun_gaussian_integrable μ s)
    change (∫ g, (charFun μ (s•g)).re ∂stdGaussian (E n)) =
      (∫ g, charFun μ (s•g) ∂stdGaussian (E n)).re at HH
    rw [HH,gaussian_char_average,Complex.ofReal_re]
  rw [H,integral_const,probReal_univ,one_smul]
  ring

lemma gaussianKernel_prod_integrable {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] (s : ℝ) :
    Integrable (fun p : E n × E n => Real.exp (-s^2*‖p.1-p.2‖^2/2)) (μ.prod μ) := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded s (p.1-p.2))

lemma gaussian_char_variance_kernel {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖^2 ∂stdGaussian (E n))=
      ∫ p : E n × E n, (Real.exp (-s^2*‖p.1-p.2‖^2/2)-
        Real.exp (-s^2*‖p.1‖^2/2)*Real.exp (-s^2*‖p.2‖^2/2)) ∂μ.prod μ := by
  rw [gaussian_char_variance_identity,gaussian_char_secondMoment,
    integral_sub (gaussianKernel_prod_integrable μ s)
      ((gaussianKernel_integrable μ s).mul_prod (gaussianKernel_integrable μ s)),
    integral_prod _ (gaussianKernel_prod_integrable μ s),
    integral_prod_mul (fun x : E n => Real.exp (-s^2*‖x‖^2/2))
      (fun x : E n => Real.exp (-s^2*‖x‖^2/2))]
  simp only [radialGaussianAverage,pow_two]

lemma abs_inner_prod_integrable {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) : Integrable (fun p : E n × E n => |⟪p.1,p.2⟫|) (μ.prod μ) := by
  have hn : Integrable (fun x : E n => ‖x‖) μ := by
    simpa only [id_eq] using (hμ.integrable (by norm_num)).norm
  apply (hn.mul_prod hn).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_abs] using abs_real_inner_le_norm p.1 p.2)

lemma isotropic_abs_inner_prod_integral {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) :
    (∫ p : E n × E n, |⟪p.1,p.2⟫| ∂μ.prod μ) ≤ Real.sqrt (n : ℝ) := by
  have hi := abs_inner_prod_integrable hμ
  rw [integral_prod _ hi]
  exact (integral_mono hi.integral_prod_left
    (by simpa only [id_eq] using (hμ.integrable (by norm_num)).norm)
    (isotropic_abs_inner_integral hμ hiso)).trans (isotropic_norm_integral hμ hiso)



lemma gaussian_char_variance_bound {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖^2 ∂stdGaussian (E n))
      ≤ s^2*Real.sqrt (n : ℝ) := by
  rw [gaussian_char_variance_kernel]
  have hi := (gaussianKernel_prod_integrable μ s).sub
    ((gaussianKernel_integrable μ s).mul_prod (gaussianKernel_integrable μ s))
  calc
    _ ≤ ∫ p : E n × E n, s^2*|⟪p.1,p.2⟫| ∂μ.prod μ :=
      integral_mono hi ((abs_inner_prod_integrable hμ).const_mul _)
        (fun p => (le_abs_self _).trans (gaussianKernel_covariance_bound s p.1 p.2))
    _ = s^2*(∫ p : E n × E n, |⟪p.1,p.2⟫| ∂μ.prod μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (isotropic_abs_inner_prod_integral hμ hiso) (sq_nonneg s)


end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

abbrev MatrixSpace (n k : ℕ) := EuclideanSpace ℝ (Fin n × Fin k)

noncomputable def rowApply {n k : ℕ} (g : MatrixSpace n k) (t : E k) : E n :=
  WithLp.toLp 2 (fun i => ∑ j : Fin k, g (i,j)*t j)

noncomputable def colApply {n k : ℕ} (g : MatrixSpace n k) (x : E n) : E k :=
  WithLp.toLp 2 (fun j => ∑ i : Fin n, g (i,j)*x i)

noncomputable def tensor {n k : ℕ} (x : E n) (t : E k) : MatrixSpace n k :=
  WithLp.toLp 2 (fun p => x p.1*t p.2)

lemma continuous_rowApply {n k : ℕ} : Continuous (fun p : MatrixSpace n k × E k => rowApply p.1 p.2) := by
  unfold rowApply
  fun_prop

lemma continuous_colApply {n k : ℕ} : Continuous (fun p : MatrixSpace n k × E n => colApply p.1 p.2) := by
  unfold colApply
  fun_prop

lemma inner_colApply {n k : ℕ} (g : MatrixSpace n k) (x : E n) (t : E k) :
    ⟪colApply g x,t⟫=⟪x,rowApply g t⟫ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    colApply,rowApply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma inner_rowApply {n k : ℕ} (g : MatrixSpace n k) (x : E n) (t : E k) :
    ⟪rowApply g t,x⟫=⟪g,tensor x t⟫ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    rowApply,tensor,Finset.mul_sum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma norm_tensor_sq {n k : ℕ} (x : E n) (t : E k) : ‖tensor x t‖^2=‖x‖^2*‖t‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,tensor,Real.norm_eq_abs,
    sq_abs,mul_pow,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

lemma rowApply_gaussian_law {n k : ℕ} (t : E k) :
    (stdGaussian (MatrixSpace n k)).map (fun g => rowApply g t)=
      (stdGaussian (E n)).map (fun x => ‖t‖•x) := by
  have hm : Measurable (fun g : MatrixSpace n k => rowApply g t) :=
    (continuous_rowApply.comp (continuous_id.prodMk continuous_const)).measurable
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_apply,integral_map hm.aemeasurable (by fun_prop),
    charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  simp only [inner_rowApply,inner_smul_left,conj_trivial]
  have he (z : E n) : (‖t‖*⟪z,x⟫ : ℝ)=⟪z,‖t‖•x⟫ := by rw [inner_smul_right]
  simp only [he,←charFun_apply,charFun_stdGaussian]
  congr 1
  rw [←Complex.ofReal_pow,←Complex.ofReal_pow,norm_tensor_sq,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_pow]
  push_cast
  ring

lemma radialGaussianAverage_nonneg {n : ℕ} (μ : Measure (E n)) (s : ℝ) :
    0 ≤ radialGaussianAverage μ s := integral_nonneg (fun _ => (Real.exp_pos _).le)

lemma radialGaussianAverage_le_one {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    radialGaussianAverage μ s ≤ 1 := by
  unfold radialGaussianAverage
  calc
    _ ≤ ∫ _ : E n, (1:ℝ) ∂μ := integral_mono (gaussianKernel_integrable μ s)
      (integrable_const _) (fun x => (le_abs_self _).trans (gaussianKernel_bounded s x))
    _ = 1 := by simp

lemma gaussian_char_mean_deviation {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖ ∂stdGaussian (E n))
      ≤ Real.sqrt (s^2*Real.sqrt (n : ℝ)) := by
  have hb (g : E n) : ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖ ≤ 2 := by
    calc
      _ ≤ ‖charFun μ (s•g)‖+‖(radialGaussianAverage μ s : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1+1 := add_le_add (norm_charFun_le_one _) (by
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (radialGaussianAverage_nonneg μ s)]
          using radialGaussianAverage_le_one μ s)
      _ = 2 := by norm_num
  have hlp : MemLp (fun g => ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖) 2 (stdGaussian (E n)) :=
    MemLp.of_bound (by fun_prop) 2 (Filter.Eventually.of_forall (fun g => by simpa only [norm_norm] using hb g))
  have H := integral_norm_le_sqrt_second hlp
  simp only [abs_norm] at H
  exact H.trans (Real.sqrt_le_sqrt (gaussian_char_variance_bound hμ hiso s))

lemma gaussian_matrix_char_deviation {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) (t : E k) :
    (∫ g : MatrixSpace n k, ‖charFun μ (s•rowApply g t)-
      (radialGaussianAverage μ (s*‖t‖) : ℂ)‖ ∂stdGaussian (MatrixSpace n k))
      ≤ Real.sqrt ((s*‖t‖)^2*Real.sqrt (n : ℝ)) := by
  have hm : Measurable (fun g : MatrixSpace n k => rowApply g t) :=
    (continuous_rowApply.comp (continuous_id.prodMk continuous_const)).measurable
  have hi := integral_map (μ := stdGaussian (MatrixSpace n k)) hm.aemeasurable
    (f := fun x : E n => ‖charFun μ (s•x)-(radialGaussianAverage μ (s*‖t‖) : ℂ)‖) (by fun_prop)
  rw [←hi,rowApply_gaussian_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [smul_smul]
  exact gaussian_char_mean_deviation hμ hiso _


end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

lemma isotropic_stdGaussian (n : ℕ) : IsIsotropic (stdGaussian (E n)) := by
  refine ⟨integral_id_stdGaussian,fun u v => ?_⟩
  have H := covarianceBilin_apply (μ := stdGaussian (E n)) IsGaussian.memLp_two_id u v
  simp only [id_eq,integral_id_stdGaussian,sub_zero,covarianceBilin_stdGaussian
    ] at H
  exact H.symm

lemma continuous_radialGaussianAverage {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] :
    Continuous (radialGaussianAverage μ) := by
  apply continuous_of_dominated (bound := fun _ => (1:ℝ))
  · intro s; fun_prop
  · intro s
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded s x)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun x => by fun_prop)

lemma matrix_char_deviation_bound {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (a : ℝ) (g : MatrixSpace n k) (t : E k) :
    ‖charFun μ (a•rowApply g t)-(radialGaussianAverage μ (a*‖t‖) : ℂ)‖ ≤ 2 := by
  calc
    _ ≤ ‖charFun μ (a•rowApply g t)‖+‖(radialGaussianAverage μ (a*‖t‖) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1+1 := add_le_add (norm_charFun_le_one _) (by
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (radialGaussianAverage_nonneg μ _)]
        using radialGaussianAverage_le_one μ (a*‖t‖))
    _ = 2 := by norm_num

lemma continuous_matrix_char_deviation {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ] (a : ℝ) :
    Continuous (fun p : MatrixSpace n k × E k =>
      ‖charFun μ (a•rowApply p.1 p.2)-(radialGaussianAverage μ (a*‖p.2‖) : ℂ)‖) := by
  have hr := continuous_radialGaussianAverage μ
  have hc := continuous_rowApply (n := n) (k := k)
  exact ((continuous_charFun.comp (hc.const_smul a)).sub
    (Complex.continuous_ofReal.comp (hr.comp (continuous_snd.norm.const_mul a)))).norm

lemma matrix_char_deviation_integrable {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ] (a : ℝ) :
    Integrable (fun p : MatrixSpace n k × E k =>
      ‖charFun μ (a•rowApply p.1 p.2)-(radialGaussianAverage μ (a*‖p.2‖) : ℂ)‖)
      ((stdGaussian (MatrixSpace n k)).prod (stdGaussian (E k))) := by
  apply (integrable_const (2:ℝ)).mono' (continuous_matrix_char_deviation a).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by simpa only [norm_norm] using matrix_char_deviation_bound a p.1 p.2)

noncomputable def matrixSmoothingError {n k : ℕ} (μ : Measure (E n)) (a : ℝ) (g : MatrixSpace n k) : ℝ :=
  ∫ t, ‖charFun μ (a•rowApply g t)-(radialGaussianAverage μ (a*‖t‖) : ℂ)‖ ∂stdGaussian (E k)

lemma matrixSmoothingError_nonneg {n k : ℕ} (μ : Measure (E n)) (a : ℝ) (g : MatrixSpace n k) :
    0 ≤ matrixSmoothingError μ a g := integral_nonneg (fun _ => norm_nonneg _)

lemma matrixSmoothingError_integrable {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ] (a : ℝ) :
    Integrable (matrixSmoothingError (k := k) μ a) (stdGaussian (MatrixSpace n k)) :=
  (matrix_char_deviation_integrable a).integral_prod_left

lemma matrixSmoothingError_mean {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (a : ℝ) :
    (∫ g : MatrixSpace n k, matrixSmoothingError μ a g ∂stdGaussian (MatrixSpace n k)) ≤
      |a| *Real.sqrt (Real.sqrt (n : ℝ))*Real.sqrt (k : ℝ) := by
  unfold matrixSmoothingError
  rw [integral_integral_swap (matrix_char_deviation_integrable a)]
  have he (t : E k) : Real.sqrt ((a*‖t‖)^2*Real.sqrt (n : ℝ))=
      (|a| *Real.sqrt (Real.sqrt (n : ℝ)))*‖t‖ := by
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_mul,abs_norm]
    ring
  calc
    _ ≤ ∫ t : E k, (|a| *Real.sqrt (Real.sqrt (n : ℝ)))*‖t‖ ∂stdGaussian (E k) := by
      apply integral_mono (matrix_char_deviation_integrable a).integral_prod_right
        (IsGaussian.integrable_id.norm.const_mul _)
      intro t
      simpa only [he,id_eq] using gaussian_matrix_char_deviation hμ hiso a t
    _ = (|a| *Real.sqrt (Real.sqrt (n : ℝ)))*(∫ t : E k, ‖t‖ ∂stdGaussian (E k)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (isotropic_norm_integral IsGaussian.memLp_two_id (isotropic_stdGaussian k)) (by positivity)

noncomputable def smoothedProjection {n k : ℕ} (μ : Measure (E n)) (s r : ℝ)
    (g : MatrixSpace n k) (y : E k) : ℝ :=
  ∫ x, Real.exp (-r^2*‖y-s•colApply g x‖^2/2) ∂μ

noncomputable def radialSmoothedModel {n k : ℕ} (μ : Measure (E n)) (s r : ℝ) (y : E k) : ℂ :=
  ∫ t, phase r y t*(radialGaussianAverage μ ((-r*s)*‖t‖) : ℂ) ∂stdGaussian (E k)

lemma phase_projected_sub {n k : ℕ} (s r : ℝ) (g : MatrixSpace n k) (y t : E k) (x : E n) :
    phase r (y-s•colApply g x) t=phase r y t*phase (-r*s) x (rowApply g t) := by
  simp only [phase,inner_sub_left,inner_smul_left,conj_trivial,inner_colApply,←Complex.exp_add]
  congr 1
  push_cast
  ring

lemma projected_phase_integrable {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) (y : E k) :
    Integrable (fun p : E n × E k => phase r (y-s•colApply g p.1) p.2)
      (μ.prod (stdGaussian (E k))) := by
  have hc : Continuous (fun x : E n => colApply g x) :=
    continuous_colApply.comp (continuous_const.prodMk continuous_id)
  apply (integrable_const (1:ℝ)).mono' (by unfold phase; fun_prop)
  exact Filter.Eventually.of_forall (fun p => (norm_phase _ _ _).le)

lemma smoothedProjection_fourier {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) (y : E k) :
    (smoothedProjection μ s r g y : ℂ)=
      ∫ t, phase r y t*charFun μ ((-r*s)•rowApply g t) ∂stdGaussian (E k) := by
  unfold smoothedProjection
  rw [←integral_complex_ofReal]
  simp_rw [←phase_gaussian_integral]
  rw [integral_integral_swap (projected_phase_integrable μ s r g y)]
  simp only [phase_projected_sub,integral_const_mul,←charFun_phase]

lemma smoothedProjection_uniform_error {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) (y : E k) :
    ‖(smoothedProjection μ s r g y : ℂ)-radialSmoothedModel μ s r y‖ ≤
      matrixSmoothingError μ (-r*s) g := by
  rw [smoothedProjection_fourier,radialSmoothedModel]
  have hr : Integrable (fun t : E k => phase r y t*(radialGaussianAverage μ ((-r*s)*‖t‖) : ℂ)) (stdGaussian (E k)) := by
    apply (integrable_const (1:ℝ)).mono' ((by
      have hh := continuous_radialGaussianAverage μ
      unfold phase
      fun_prop) : AEStronglyMeasurable _ _)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [norm_mul,norm_phase,one_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (radialGaussianAverage_nonneg μ _)]
      exact radialGaussianAverage_le_one μ _)
  have hf : Integrable (fun t : E k => phase r y t*charFun μ ((-r*s)•rowApply g t)) (stdGaussian (E k)) := by
    apply (integrable_const (1:ℝ)).mono' (by
      have hc : Continuous (fun t : E k => rowApply g t) := continuous_rowApply.comp (continuous_const.prodMk continuous_id)
      unfold phase
      fun_prop)
    exact Filter.Eventually.of_forall (fun t => by simpa only [norm_mul,norm_phase,one_mul] using norm_charFun_le_one ((-r*s)•rowApply g t))
  rw [←integral_sub hf hr]
  calc
    _ ≤ ∫ t : E k, ‖phase r y t*charFun μ ((-r*s)•rowApply g t)-phase r y t*(radialGaussianAverage μ ((-r*s)*‖t‖) : ℂ)‖ ∂stdGaussian (E k) := norm_integral_le_integral_norm _
    _ = matrixSmoothingError μ (-r*s) g := by simp only [←mul_sub,norm_mul,norm_phase,one_mul,matrixSmoothingError]



theorem exists_uniform_smoothed_projection {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s r : ℝ) :
    ∃ g : MatrixSpace n k, ∀ y : E k,
      ‖(smoothedProjection μ s r g y : ℂ)-radialSmoothedModel μ s r y‖ ≤
        |r*s| *Real.sqrt (Real.sqrt (n : ℝ))*Real.sqrt (k : ℝ) := by
  obtain ⟨g,hg⟩ := exists_le_integral (matrixSmoothingError_integrable (k := k) (μ := μ) (-r*s))
  refine ⟨g,fun y => (smoothedProjection_uniform_error μ s r g y).trans (hg.trans ?_)⟩
  simpa only [neg_mul,abs_neg] using matrixSmoothingError_mean (k := k) hμ hiso (-r*s)




end SingleLatticeCovering.GaussianProjection


end
end

end OAI
