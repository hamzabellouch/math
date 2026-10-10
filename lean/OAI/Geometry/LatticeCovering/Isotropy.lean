import OAI.Geometry.LatticeCovering.Horizontal

namespace OAI

section
section
noncomputable section
open Set Module MeasureTheory
open scoped BigOperators Pointwise

namespace SingleLatticeCovering.FiniteDimensions
open Filter MeasureTheory
open scoped Pointwise BigOperators




lemma absorb_finitely_many_dimensions
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (L : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology L),
        IsZLattice ℝ L ∧ K+(L : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal / ZLattice.covolume L ≤ C*(n : ℝ)*Real.log (n : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (L : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology L),
        IsZLattice ℝ L ∧ K+(L : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal / ZLattice.covolume L ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  classical
  obtain ⟨C,hC⟩ := h
  obtain ⟨N,hN⟩ := eventually_atTop.mp hC
  let f : ℕ → ℝ := fun n => (2*(n : ℝ))^n / ((n : ℝ)*Real.log (n : ℝ))
  have hf : ∀ n, 0 ≤ f n := fun n => div_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  let S := ∑ n ∈ Finset.range N, f n
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n _ => hf n)
  refine ⟨1+|C|+S,by positivity,?_⟩
  intro n hn K hK hc hi
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  by_cases hlarge : N ≤ n
  · obtain ⟨L,hd,hfull,hcover,hbound⟩ := hN n hlarge K hK hc hi
    refine ⟨L,hd,hfull,hcover,hbound.trans ?_⟩
    gcongr
    exact le_trans (le_abs_self C) (by linarith)
  · obtain ⟨L,hd,hfull,hcover,hbound⟩ := finite_dimension_cover (by omega) K hK hc hi
    refine ⟨L,hd,hfull,hcover,hbound.trans ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hfS : f n ≤ S := Finset.single_le_sum (fun i _ => hf i) hnN
    have hff : f n ≤ 1+|C|+S := hfS.trans (by linarith [abs_nonneg C])
    rw [mul_assoc]
    exact (div_le_iff₀ (mul_pos hnr hlog)).mp hff


end SingleLatticeCovering.FiniteDimensions

end
end

section

noncomputable section
namespace SingleLatticeCovering.Assembly
open MeasureTheory Inputs Filter Topology
open scoped Pointwise




theorem all_dimensions_main_reduction {α β γ C₀ CR : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hC₀ : 0 ≤ C₀) (hCR : 0 ≤ CR)
    (hGaussian : ∀ᶠ n : ℕ in atTop, GaussianPositions α β γ C₀ n)
    (hMean : ∀ m : ℕ, 2 ≤ m → ∀ Dh : ℝ, 0 < Dh → Nonempty (MeanHoleModel m Dh CR)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_main_reduction hα hβ hγ hC₀ hCR hGaussian hMean
  exact FiniteDimensions.absorb_finitely_many_dimensions ⟨C,h⟩


end SingleLatticeCovering.Assembly

end
end

section



noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def uniformLaw {n : ℕ} (K : Set (E n)) : Measure (E n) :=
  (volume K)⁻¹ • volume.restrict K

lemma volume_pos {n : ℕ} {K : Set (E n)} (hi : (interior K).Nonempty) : 0 < volume K :=
  (isOpen_interior.measure_pos volume hi).trans_le (measure_mono interior_subset)

lemma uniform_probability {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) : IsProbabilityMeasure (uniformLaw K) :=
  cond_isProbabilityMeasure_of_finite (ne_of_gt (volume_pos hi)) hK.measure_ne_top

lemma continuous_memLp_uniform {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    {f : E n → F} (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p (uniformLaw K) := by
  let := uniform_probability hK hi
  obtain ⟨C,hC⟩ := (hK.image hf).isBounded.exists_norm_le
  apply MemLp.of_bound hf.aestronglyMeasurable C
  apply ae_smul_measure (c := (volume K)⁻¹)
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC _ (mem_image_of_mem _ hx)

lemma continuous_eq_on_interior {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    {f g : E n → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[uniformLaw K] g) : EqOn f g (interior K) := by
  have h' : f =ᵐ[volume.restrict K] g :=
    (ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr hK.measure_ne_top)).mp h
  exact Measure.eqOn_open_of_ae_eq (μ := volume)
    (ae_restrict_of_ae_restrict_of_subset interior_subset h') isOpen_interior
    hf.continuousOn hg.continuousOn



lemma inner_not_constant_on_interior {n : ℕ} {K : Set (E n)}
    (hi : (interior K).Nonempty) {v : E n} (hv : v ≠ 0) (c : ℝ) :
    ¬EqOn (fun x => ⟪v,x⟫) (fun _ => c) (interior K) := by
  intro h
  obtain ⟨z,hz⟩ := hi
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let t := r/(2*(‖v‖+1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hdist : dist (z+t • v) z < r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(‖v‖+1))).mpr
    nlinarith [norm_nonneg v]
  have hz' := h (hball hdist)
  have hz0 := h hz
  simp only [inner_add_right,real_inner_smul_right] at hz'
  have hself : 0 < ⟪v,v⟫ := real_inner_self_pos.mpr hv
  nlinarith



lemma covariance_positive {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) {v : E n} (hv : v ≠ 0) :
    0 < covarianceBilin (uniformLaw K) v v := by
  let := uniform_probability hK hi
  have hμ : MemLp id 2 (uniformLaw K) := continuous_memLp_uniform hK hi continuous_id 2
  have hf : MemLp (fun x : E n => ⟪v,x⟫) 2 (uniformLaw K) :=
    continuous_memLp_uniform hK hi (by fun_prop) 2
  rw [covarianceBilin_self hμ]
  refine lt_of_le_of_ne (variance_nonneg _ _) ?_
  intro hzero
  have heq := ae_eq_integral_of_variance_eq_zero hf hzero.symm
  exact inner_not_constant_on_interior hi hv _
    (continuous_eq_on_interior hK (by fun_prop) continuous_const heq)





lemma positive_form_normalization {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hs : ∀ x y, B x y=B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ T : E n ≃L[ℝ] E n, ∀ x y, B (T x) (T y)=⟪x,y⟫ := by
  classical
  let Q := B.toBilinForm.toQuadraticMap
  obtain ⟨w,hw,⟨e⟩⟩ : ∃ w : Fin n → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
      Q.Equivalent (QuadraticMap.weightedSumSquares ℝ w) := by
    have hdim : Module.finrank ℝ (E n)=n := finrank_euclideanSpace_fin
    have hh := QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared Q
    rw [hdim] at hh
    exact hh
  have hw1 : ∀ i, w i=1 := by
    intro i
    have hz : e.symm (Pi.single i (1 : ℝ)) ≠ 0 := by
      intro h
      have hh := congrArg e h
      have : (Pi.single i (1 : ℝ) : Fin n → ℝ)=0 := by simp at hh
      have := congrFun this i
      simp at this
    have he := e.symm.map_app (Pi.single i (1 : ℝ))
    have hwp : 0 < w i := by
      have hq : 0 < Q (e.symm (Pi.single i (1 : ℝ))) := hp _ hz
      rw [he] at hq
      simpa [QuadraticMap.weightedSumSquares_apply,Pi.single_apply] using hq
    rcases hw i with h | h | h
    · linarith
    · linarith
    · exact h
  let T : E n ≃L[ℝ] E n :=
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans e.symm.toLinearEquiv).toContinuousLinearEquiv
  have hdiag : ∀ x : E n, B (T x) (T x)=⟪x,x⟫ := by
    intro x
    have he := e.symm.map_app (WithLp.ofLp x)
    change B (T x) (T x)=_ at he
    rw [he]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [QuadraticMap.weightedSumSquares_apply,hw1,one_smul,star_trivial]
    rfl
  refine ⟨T,fun x y => ?_⟩
  have h := hdiag (x+y)
  simp only [map_add,_root_.add_apply,inner_add_left,inner_add_right] at h
  rw [hdiag x,hdiag y,hs (T y) (T x),real_inner_comm x y] at h
  linarith




def adjointEquiv {n : ℕ} (T : E n ≃L[ℝ] E n) : E n ≃L[ℝ] E n where
  toLinearEquiv :=
    { toLinearMap := T.toContinuousLinearMap.adjoint.toLinearMap
      invFun := T.symm.toContinuousLinearMap.adjoint
      left_inv x := by
        change (T.symm.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap.adjoint) x=x
        rw [←ContinuousLinearMap.adjoint_comp]
        have h : T.toContinuousLinearMap.comp T.symm.toContinuousLinearMap=
            ContinuousLinearMap.id ℝ (E n) := by ext x; simp
        rw [h,ContinuousLinearMap.adjoint_id]
        rfl
      right_inv x := by
        change (T.toContinuousLinearMap.adjoint.comp T.symm.toContinuousLinearMap.adjoint) x=x
        rw [←ContinuousLinearMap.adjoint_comp]
        have h : T.symm.toContinuousLinearMap.comp T.toContinuousLinearMap=
            ContinuousLinearMap.id ℝ (E n) := by ext x; simp
        rw [h,ContinuousLinearMap.adjoint_id]
        rfl }
  continuous_toFun := T.toContinuousLinearMap.adjoint.continuous
  continuous_invFun := T.symm.toContinuousLinearMap.adjoint.continuous

lemma adjointEquiv_adjoint {n : ℕ} (T : E n ≃L[ℝ] E n) :
    (adjointEquiv T).toContinuousLinearMap.adjoint=T.toContinuousLinearMap :=
  ContinuousLinearMap.adjoint_adjoint _

end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace




def centeredEquiv {n : ℕ} (μ : Measure (E n)) (A : E n ≃L[ℝ] E n) : E n ≃ᵃ[ℝ] E n :=
  (AffineEquiv.constVAdd ℝ (E n) (-(∫ x, x ∂μ))).trans A.toLinearEquiv.toAffineEquiv

lemma map_centeredEquiv {n : ℕ} (μ : Measure (E n)) (A : E n ≃L[ℝ] E n) :
    μ.map (centeredEquiv μ A)=(μ.map (fun x => -(∫ x, x ∂μ)+x)).map A := by
  rw [Measure.map_map A.continuous.measurable (by fun_prop)]
  rfl

lemma memLp_translate {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (c : E n) : MemLp id 2 (μ.map (fun x => c+x)) := by
  have hc : MemLp (fun _ : E n => c) 2 μ := memLp_const c
  have hsum : MemLp (fun x : E n => c+x) 2 μ := hc.add hμ
  exact (measurableEmbedding_addLeft c).memLp_map_measure_iff.mpr hsum

lemma memLp_centered {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) : MemLp id 2 (μ.map (fun x => -(∫ x, x ∂μ)+x)) :=
  memLp_translate hμ _

lemma centeredEquiv_mean {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (A : E n ≃L[ℝ] E n) :
    (∫ x, x ∂μ.map (centeredEquiv μ A))=0 := by
  have hcent := memLp_centered hμ
  rw [map_centeredEquiv]
  change (∫ x, x ∂(μ.map (fun x => -(∫ z, z ∂μ)+x)).map A.toContinuousLinearMap)=0
  rw [A.toContinuousLinearMap.integral_id_map (hcent.integrable (by simp)),
    integral_map (by fun_prop) (by fun_prop)]
  change A (∫ x, -(∫ z, z ∂μ)+x ∂μ)=0
  rw [integral_add (f := fun _ : E n => -(∫ z, z ∂μ)) (g := fun x : E n => x)
    (integrable_const _) (hμ.integrable (by simp))]
  simp

lemma centeredEquiv_covariance {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (A : E n ≃L[ℝ] E n) (u v : E n) :
    covarianceBilin (μ.map (centeredEquiv μ A)) u v=
      covarianceBilin μ (A.toContinuousLinearMap.adjoint u) (A.toContinuousLinearMap.adjoint v) := by
  rw [map_centeredEquiv]
  change covarianceBilin ((μ.map (fun x => -(∫ z, z ∂μ)+x)).map A.toContinuousLinearMap) u v=_
  rw [covarianceBilin_map (memLp_centered hμ) A.toContinuousLinearMap]
  rw [covarianceBilin_map_const_add]



theorem uniform_affine_isotropization {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) :
    ∃ e : E n ≃ᵃ[ℝ] E n,
      (∫ x, x ∂(uniformLaw K).map e)=0 ∧
      ∀ u v : E n, covarianceBilin ((uniformLaw K).map e) u v=⟪u,v⟫ := by
  let : IsProbabilityMeasure (uniformLaw K) := uniform_probability hK hi
  have hμ : MemLp id 2 (uniformLaw K) := continuous_memLp_uniform hK hi continuous_id 2
  have hs : ∀ x y : E n, covarianceBilin (uniformLaw K) x y=
      covarianceBilin (uniformLaw K) y x := fun x y => covarianceBilin_comm x y
  have hp : ∀ x : E n, x ≠ 0 → 0 < covarianceBilin (uniformLaw K) x x :=
    fun x hx => covariance_positive hK hi hx
  obtain ⟨T,hT⟩ := positive_form_normalization (covarianceBilin (uniformLaw K)) hs hp
  refine ⟨centeredEquiv (uniformLaw K) (adjointEquiv T),centeredEquiv_mean hμ _,?_⟩
  intro u v
  rw [centeredEquiv_covariance hμ,adjointEquiv_adjoint]
  exact hT u v



end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace




def affineMeasurableEquiv {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) : E n ≃ᵐ E n where
  toEquiv := e.toEquiv
  measurable_toFun := e.toAffineMap.continuous_of_finiteDimensional.measurable
  measurable_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional.measurable

lemma affine_map_volume {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) :
    volume.map e=ENNReal.ofReal |(LinearMap.det e.linear.toLinearMap)⁻¹| • volume := by
  have he : (e : E n → E n)=(fun x => x+e 0) ∘ (e.linear.toLinearMap : E n → E n) := by
    funext x
    simpa using e.map_vadd (0 : E n) x
  rw [he,←Measure.map_map (by fun_prop) e.linear.toLinearMap.continuous_of_finiteDimensional.measurable]
  rw [map_linearMap_addHaar_eq_smul_addHaar volume e.linear.isUnit_det'.ne_zero,
    Measure.map_smul _ (by fun_prop),map_add_right_eq_self]

lemma affine_volume_factor_pos {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) :
    0 < ENNReal.ofReal |(LinearMap.det e.linear.toLinearMap)⁻¹| := by
  apply ENNReal.ofReal_pos.mpr
  exact abs_pos.mpr (inv_ne_zero e.linear.isUnit_det'.ne_zero)



lemma map_uniformLaw {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) (K : Set (E n)) :
    (uniformLaw K).map e=uniformLaw (e '' K) := by
  let em := affineMeasurableEquiv e
  let c := ENNReal.ofReal |(LinearMap.det e.linear.toLinearMap)⁻¹|
  have hc : c ≠ 0 := ne_of_gt (affine_volume_factor_pos e)
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hmap : volume.map em=c • volume := affine_map_volume e
  have hpre : em ⁻¹' (e '' K)=K := by
    change e ⁻¹' (e '' K)=K
    exact Set.preimage_image_eq _ e.injective
  have hval : volume K=c*volume (e '' K) := by
    have h := congrArg (fun μ : Measure (E n) => μ (e '' K)) hmap
    rw [em.map_apply,hpre] at h
    exact h
  have hrestr : (volume.restrict K).map em=c • volume.restrict (e '' K) := by
    have h := em.restrict_map volume (e '' K)
    rw [hmap,Measure.restrict_smul,hpre] at h
    exact h.symm
  change ((volume K)⁻¹ • volume.restrict K).map em= _
  rw [Measure.map_smul _ em.measurable.aemeasurable,hrestr,smul_smul]
  unfold uniformLaw
  congr 1
  rw [hval,ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
  calc
    c⁻¹*(volume (e '' K))⁻¹*c=(c⁻¹*c)*(volume (e '' K))⁻¹ := by ac_rfl
    _ = (volume (e '' K))⁻¹ := by rw [ENNReal.inv_mul_cancel hc hct,one_mul]



theorem isotropic_affine_body {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) :
    ∃ e : E n ≃ᵃ[ℝ] E n,
      (∫ x, x ∂uniformLaw (e '' K))=0 ∧
      ∀ u v : E n, covarianceBilin (uniformLaw (e '' K)) u v=⟪u,v⟫ := by
  obtain ⟨e,hmean,hcov⟩ := uniform_affine_isotropization hK hi
  rw [map_uniformLaw] at hmean hcov
  exact ⟨e,hmean,hcov⟩






def LogConcave {n : ℕ} (f : E n → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∀ (x y : E n) (a b : ℝ), 0 < a → 0 < b → a+b=1 →
    f x ^ a * f y ^ b ≤ f (a • x+b • y)

def uniformPdf {n : ℕ} (K : Set (E n)) : E n → ℝ :=
  K.indicator (fun _ => ((volume K)⁻¹).toReal)

lemma uniformPdf_measurable {n : ℕ} {K : Set (E n)} (hK : MeasurableSet K) :
    Measurable (uniformPdf K) := measurable_const.indicator hK

lemma uniformPdf_nonneg {n : ℕ} (K : Set (E n)) (x : E n) : 0 ≤ uniformPdf K x := by
  exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x

lemma uniformPdf_logConcave {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) : LogConcave (uniformPdf K) := by
  have hvol : volume K ≠ 0 := ne_of_gt (volume_pos hi)
  have hC : 0 < ((volume K)⁻¹).toReal := ENNReal.toReal_pos
    (ENNReal.inv_ne_zero.mpr hK.measure_ne_top) (ENNReal.inv_ne_top.mpr hvol)
  refine ⟨uniformPdf_nonneg K,fun x y a b ha hb hab => ?_⟩
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have hz := hc hx hy (le_of_lt ha) (le_of_lt hb) hab
      simp only [uniformPdf,Set.indicator_of_mem hx,Set.indicator_of_mem hy,Set.indicator_of_mem hz]
      rw [←Real.rpow_add hC,hab,Real.rpow_one]
    · simp only [uniformPdf,Set.indicator_of_notMem hy,Real.zero_rpow (ne_of_gt hb),mul_zero]
      exact uniformPdf_nonneg K _
  · simp only [uniformPdf,Set.indicator_of_notMem hx,Real.zero_rpow (ne_of_gt ha),zero_mul]
    exact uniformPdf_nonneg K _

lemma uniformLaw_eq_withDensity {n : ℕ} {K : Set (E n)} (hK : MeasurableSet K)
    (hi : (interior K).Nonempty) :
    uniformLaw K=volume.withDensity (fun x => ENNReal.ofReal (uniformPdf K x)) := by
  have hct : (volume K)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (ne_of_gt (volume_pos hi))
  have he : (fun x => ENNReal.ofReal (uniformPdf K x))=
      K.indicator (fun _ => (volume K)⁻¹) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [uniformPdf,Set.indicator_of_mem hx]
      exact ENNReal.ofReal_toReal hct
    · simp [uniformPdf,hx]
  rw [he,withDensity_indicator hK,withDensity_const]
  rfl



def IsIsotropic {n : ℕ} (μ : Measure (E n)) : Prop :=
  (∫ x, x ∂μ)=0 ∧ ∀ u v : E n, (∫ x, ⟪u,x⟫*⟪v,x⟫ ∂μ)=⟪u,v⟫

lemma covariance_isotropy {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hmean : (∫ x, x ∂μ)=0)
    (hcov : ∀ u v : E n, covarianceBilin μ u v=⟪u,v⟫) : IsIsotropic μ := by
  refine ⟨hmean,fun u v => ?_⟩
  have h := hcov u v
  rw [covarianceBilin_apply hμ] at h
  simp only [id_eq] at h
  rw [hmean] at h
  simpa using h




end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

lemma affine_body_properties {n : ℕ} (e : E n ≃ᵃ[ℝ] E n)
    {K : Set (E n)} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty := by
  let H : E n ≃ₜ E n :=
    { toEquiv := e.toEquiv
      continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  refine ⟨hK.image H.continuous,hc.affine_image e.toAffineMap,?_⟩
  change (interior (H '' K)).Nonempty
  rw [←H.image_interior]
  exact hi.image H




theorem isotropic_logConcave_affine_body {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    ∃ e : E n ≃ᵃ[ℝ] E n,
      IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty ∧
      IsProbabilityMeasure (uniformLaw (e '' K)) ∧ MemLp id 2 (uniformLaw (e '' K)) ∧
      IsIsotropic (uniformLaw (e '' K)) ∧
      Measurable (uniformPdf (e '' K)) ∧ LogConcave (uniformPdf (e '' K)) ∧
      uniformLaw (e '' K)=volume.withDensity (fun x => ENNReal.ofReal (uniformPdf (e '' K) x)) := by
  obtain ⟨e,hmean,hcov⟩ := isotropic_affine_body hK hi
  obtain ⟨hK',hc',hi'⟩ := affine_body_properties e hK hc hi
  have hprob := uniform_probability hK' hi'
  let := hprob
  have hmem : MemLp id 2 (uniformLaw (e '' K)) :=
    continuous_memLp_uniform hK' hi' continuous_id 2
  exact ⟨e,hK',hc',hi',hprob,hmem,covariance_isotropy hmem hmean hcov,
    uniformPdf_measurable hK'.measurableSet,uniformPdf_logConcave hK' hc' hi',
    uniformLaw_eq_withDensity hK'.measurableSet hi'⟩



end SingleLatticeCovering.Isotropization

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]



lemma map_snd_restrict {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [SFinite μ] (ν : Measure F) [SFinite ν]
    {K : Set (E × F)} (hK : MeasurableSet K) :
    Measure.map Prod.snd ((μ.prod ν).restrict K)=ν.withDensity (fun y => μ (fiber K y)) := by
  ext U hU
  rw [Measure.map_apply measurable_snd hU,Measure.restrict_apply (measurable_snd hU),
    Measure.prod_apply_symm ((measurable_snd hU).inter hK),withDensity_apply _ hU,
    ←lintegral_indicator hU]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ U
  · simp only [Set.indicator_of_mem hy]
    congr 1
    ext x
    simp [fiber,hy]
  · simp only [Set.indicator_of_notMem hy]
    have he : (fun x : E => (x,y)) ⁻¹' (Prod.snd ⁻¹' U ∩ K)=∅ := by ext x; simp [hy]
    rw [he,measure_empty]

lemma measurable_fiber_measure {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [SFinite μ]
    {K : Set (E × F)} (hK : MeasurableSet K) : Measurable (fun y => μ (fiber K y)) :=
  measurable_measure_prodMk_right hK




lemma map_snd_uniform (μ : Measure E) [SFinite μ] (ν : Measure F) [SFinite ν]
    {K : Set (E × F)} (hK : MeasurableSet K) :
    Measure.map Prod.snd (((μ.prod ν) K)⁻¹ • (μ.prod ν).restrict K)=
      ν.withDensity (fun y => ((μ.prod ν) K)⁻¹*μ (fiber K y)) := by
  rw [Measure.map_smul _ (by fun_prop),map_snd_restrict μ ν hK]
  exact (withDensity_smul _ (measurable_fiber_measure μ hK)).symm

lemma canonical_density_ae (μ : Measure E) [SFinite μ] (ν : Measure F) [SigmaFinite ν]
    {K : Set (E × F)} (hK : MeasurableSet K) {g : F → ℝ≥0∞} (hg : AEMeasurable g ν)
    (heq : Measure.map Prod.snd (((μ.prod ν) K)⁻¹ • (μ.prod ν).restrict K)=ν.withDensity g) :
    (fun y => ((μ.prod ν) K)⁻¹*μ (fiber K y))=ᵐ[ν] g := by
  rw [map_snd_uniform μ ν hK] at heq
  exact (withDensity_eq_iff_of_sigmaFinite ((measurable_fiber_measure μ hK).const_mul _).aemeasurable hg).mp heq

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

lemma continuous_gaussian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] : Continuous (gaussian F) := by
  unfold gaussian
  fun_prop




lemma canonical_gaussian_lower_of_ae (μ : Measure E) [IsAddHaarMeasure μ]
    (ν : Measure F) [IsAddHaarMeasure ν] {K : Set (E × F)} (hK : IsCompact K)
    {V S : ℝ} (hV : 0 ≤ V)
    (hae : ∀ᵐ y ∂ν, ‖y‖ < S → V*gaussian F y/2 ≤ (μ (fiber K y)).toReal) :
    ∀ y : F, ‖y‖ < S → V*gaussian F y/2 ≤ (μ (fiber K y)).toReal := by
  have hg : Continuous (fun y : F => ENNReal.ofReal (V*gaussian F y/2)) := by
    exact ENNReal.continuous_ofReal.comp ((continuous_const.mul continuous_gaussian).div_const 2)
  have hae' : ∀ᵐ y ∂ν, ‖y‖ < S → ENNReal.ofReal (V*gaussian F y/2) ≤ μ (fiber K y) := by
    filter_upwards [hae] with y hy hys
    exact ENNReal.ofReal_le_of_le_toReal (hy hys)
  have hall := canonical_marginal_lower μ ν hK hg hae'
  intro y hy
  have hf := (fiber_compact hK y).measure_ne_top (μ := μ)
  have hh := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hf).mpr (hall y hy)
  rwa [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg hV (gaussian_pos y).le) (by norm_num))] at hh




lemma canonical_gaussian_lower_of_density (μ : Measure E) [IsAddHaarMeasure μ]
    (ν : Measure F) [IsAddHaarMeasure ν] {K : Set (E × F)} (hK : IsCompact K)
    (hK0 : (μ.prod ν) K ≠ 0) {S : ℝ} {g : F → ℝ≥0∞} (hg : AEMeasurable g ν)
    (heq : Measure.map Prod.snd (((μ.prod ν) K)⁻¹ • (μ.prod ν).restrict K)=ν.withDensity g)
    (hlower : ∀ᵐ y ∂ν, ‖y‖ < S → ENNReal.ofReal (gaussian F y/2) ≤ g y) :
    ∀ y : F, ‖y‖ < S → ((μ.prod ν) K).toReal*gaussian F y/2 ≤
      (μ (fiber K y)).toReal := by
  apply canonical_gaussian_lower_of_ae μ ν hK ENNReal.toReal_nonneg
  filter_upwards [canonical_density_ae μ ν hK.measurableSet hg heq,hlower] with y hy hl hys
  rw [←hy] at hl
  have hmul := mul_le_mul' (le_refl ((μ.prod ν) K)) (hl hys)
  rw [←mul_assoc,ENNReal.mul_inv_cancel hK0 (hK.measure_ne_top (μ := μ.prod ν)),one_mul] at hmul
  have ht := ENNReal.toReal_mono ((fiber_compact hK y).measure_ne_top (μ := μ)) hmul
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (div_nonneg (gaussian_pos y).le (by norm_num))] at ht
  simpa only [mul_div_assoc] using ht




end SingleLatticeCovering.Sections

end
end

section

noncomputable section

end
end
end

end OAI
