import OAI.Combinatorics.SparsestCut.CubePoincare

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubeGeometry
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
noncomputable section
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => CubePoincare.cube (m := m)

lemma pi_uniform : Measure.pi (fun _ : Fin m => GaussianCDF.uniform)=
    (2:ℝ≥0∞)⁻¹^m • (volume : Measure (Fin m → ℝ)).restrict
      (univ.pi (fun _ => Ioo (-1:ℝ) 1)) := by
  apply Measure.pi_eq
  intro s hs
  change (2:ℝ≥0∞)⁻¹^m * ((Measure.pi (fun _ : Fin m => (volume : Measure ℝ))).restrict (univ.pi (fun _ => Ioo (-1:ℝ) 1))) (univ.pi s)=_
  rw [Measure.restrict_pi_pi,Measure.pi_pi]
  simp only [GaussianCDF.uniform,Measure.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma cube_ac : μ ≪ (volume : Measure E) := by
  have h : Measure.pi (fun _ : Fin m => GaussianCDF.uniform) ≪ (volume : Measure (Fin m → ℝ)) := by
    rw [pi_uniform]
    exact (Measure.restrict_le_self.absolutelyContinuous).smul_left _
  have hh := h.map (show Measurable (WithLp.toLp 2 : (Fin m → ℝ) → E) by fun_prop)
  rw [(PiLp.volume_preserving_toLp (Fin m)).map_eq] at hh
  exact hh

lemma uniform_mem : ∀ᵐ t ∂GaussianCDF.uniform, t∈Ioo (-1:ℝ) 1 := by
  have h : GaussianCDF.uniform ≪ volume.restrict (Ioo (-1:ℝ) 1) :=
    (Measure.AbsolutelyContinuous.refl _).smul_left _
  exact h.ae_le (ae_restrict_mem measurableSet_Ioo)

lemma cube_mem : ∀ᵐ x ∂μ, ∀ j, |x j|<1 := by
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  apply ae_all_iff.mpr
  intro j
  have h := (measurePreserving_eval (fun _ : Fin m => GaussianCDF.uniform) j).quasiMeasurePreserving.ae uniform_mem
  filter_upwards [h] with x hx
  exact abs_lt.mpr hx

lemma uniform_pow (k : ℕ) : (∫ t, t^k ∂GaussianCDF.uniform)=
    (1-(-1:ℝ)^(k+1))/(2*(k+1)) := by
  rw [GaussianCDF.uniform,integral_smul_measure,restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),integral_pow]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofNat,smul_eq_mul,one_pow]
  field_simp

lemma uniform_pow_integrable (k : ℕ) : Integrable (fun t : ℝ => t^k) GaussianCDF.uniform := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards [uniform_mem] with t ht
  rw [Real.norm_eq_abs,abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg t) (abs_lt.mpr ht).le k).trans_eq (one_pow k)

lemma coordinate_preserving (j : Fin m) : MeasurePreserving (fun x : E => x j) μ GaussianCDF.uniform := by
  refine ⟨by fun_prop,?_⟩
  rw [CubePoincare.cube,Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval (fun _ : Fin m => GaussianCDF.uniform) j).map_eq

lemma coordinate_pow (j : Fin m) (k : ℕ) : (∫ x : E, (x j)^k ∂μ)=
    (1-(-1:ℝ)^(k+1))/(2*(k+1)) := by
  rw [← uniform_pow k,← (coordinate_preserving j).map_eq]
  exact (integral_map (by fun_prop) (continuous_id.pow k).aestronglyMeasurable).symm

lemma coordinate_pow_integrable (j : Fin m) (k : ℕ) : Integrable (fun x : E => (x j)^k) μ :=
  ((coordinate_preserving j).integrable_comp (continuous_id.pow k).aestronglyMeasurable).mpr (uniform_pow_integrable k)

lemma cube_norm : ∀ᵐ x : E ∂μ, ‖x‖≤Real.sqrt m := by
  filter_upwards [cube_mem] with x hx
  have h : ‖x‖^2≤(m:ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin m, (1:ℝ) := by
        apply Finset.sum_le_sum; intro j _
        rw [Real.norm_eq_abs,sq_abs]
        nlinarith [abs_lt.mp (hx j)]
      _ = _ := by simp
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m),norm_nonneg x,Real.sqrt_nonneg (m:ℝ)]

lemma bounded_integrable {f : E → ℝ} (hf : AEStronglyMeasurable f μ) {B : ℝ}
    (hb : ∀ᵐ x ∂μ, |f x|≤B) : Integrable f μ :=
  (integrable_const B).mono' hf (by simpa only [Real.norm_eq_abs] using hb)

lemma pair_norm_bound : ∀ᵐ z : E × E ∂(μ).prod μ, ‖z.1-z.2‖≤2*Real.sqrt m := by
  have hp : ∀ᵐ z : E × E ∂(μ).prod μ, ‖z.1‖≤Real.sqrt m ∧ ‖z.2‖≤Real.sqrt m := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [cube_norm (m := m)] with x hx
    filter_upwards [cube_norm (m := m)] with y hy
    exact ⟨hx,hy⟩
  filter_upwards [hp] with z hz
  exact (norm_sub_le _ _).trans (by linarith [hz.1,hz.2])

lemma pair_norm_integrable : Integrable (fun z : E × E => ‖z.1-z.2‖) ((μ).prod μ) := by
  apply (integrable_const (2*Real.sqrt m)).mono' (by fun_prop)
  simpa only [Real.norm_eq_abs,abs_norm] using pair_norm_bound (m := m)

lemma coordinate_difference_sq (j : Fin m) :
    (∫ z : E × E, (z.1 j-z.2 j)^2 ∂(μ).prod μ)=2/3 := by
  have h1 : Integrable (fun x : E => x j) μ := by simpa using coordinate_pow_integrable j 1
  have h2 := coordinate_pow_integrable j 2
  have he : (fun z : E × E => (z.1 j-z.2 j)^2) =
      (fun z => (z.1 j)^2+(z.2 j)^2-2*(z.1 j*z.2 j)) := by funext z; ring
  rw [he]
  have hsub := integral_sub ((h2.comp_fst μ).add (h2.comp_snd μ)) ((h1.mul_prod h1).const_mul 2)
  simp only [Pi.add_apply] at hsub
  rw [hsub]
  have hadd := integral_add (h2.comp_fst μ) (h2.comp_snd μ)
  rw [hadd,integral_const_mul,integral_prod_mul (fun x : E => x j) (fun x : E => x j)]
  have he0 : (∫ x : E, x j ∂μ)=0 := by simpa using coordinate_pow j 1
  have he2 : (∫ x : E, (x j)^2 ∂μ)=1/3 := by
    have hh := coordinate_pow j 2
    norm_num at hh ⊢
    exact hh
  rw [integral_fun_fst (fun x : E => (x j)^2),integral_fun_snd (fun x : E => (x j)^2)]
  simp [he0,he2]
  norm_num

lemma coordinate_difference_sq_integrable (j : Fin m) :
    Integrable (fun z : E × E => (z.1 j-z.2 j)^2) ((μ).prod μ) := by
  have h1 : Integrable (fun x : E => x j) μ := by simpa using coordinate_pow_integrable j 1
  have h2 := coordinate_pow_integrable j 2
  convert ((h2.comp_fst μ).add (h2.comp_snd μ)).sub ((h1.mul_prod h1).const_mul 2) using 1
  ext z
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

lemma pair_norm_sq_integral : (∫ z : E × E, ‖z.1-z.2‖^2 ∂(μ).prod μ)=2*(m:ℝ)/3 := by
  have hnorm (z : E × E) : ‖z.1-z.2‖^2=∑ j, (z.1 j-z.2 j)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    funext j
    simp only [PiLp.sub_apply,Real.norm_eq_abs,sq_abs]
  simp_rw [hnorm]
  rw [integral_finsetSum _ (fun j _ => coordinate_difference_sq_integrable j)]
  simp only [coordinate_difference_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma pair_norm_average (hm : 0 < m) :
    Real.sqrt m/3≤∫ z : E × E, ‖z.1-z.2‖ ∂(μ).prod μ := by
  have hsq : Integrable (fun z : E × E => ‖z.1-z.2‖^2) ((μ).prod μ) := by
    apply (integrable_const ((2*Real.sqrt m)^2)).mono' (by fun_prop)
    filter_upwards [pair_norm_bound (m := m)] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hh := integral_mono_ae hsq (pair_norm_integrable.const_mul (2*Real.sqrt m)) (by
    filter_upwards [pair_norm_bound (m := m)] with z hz
    exact (show ‖z.1-z.2‖^2≤2*Real.sqrt m*‖z.1-z.2‖ by nlinarith [norm_nonneg (z.1-z.2)]))
  rw [pair_norm_sq_integral,integral_const_mul] at hh
  have hp : 0<Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)
  nlinarith

end
end UniformSparsestCut.CubeGeometry

end

end OAI
