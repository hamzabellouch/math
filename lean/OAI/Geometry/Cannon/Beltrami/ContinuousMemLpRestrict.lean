import Mathlib
import OAI.Geometry.Cannon.Boundary.Thin
import OAI.Geometry.Cannon.PlaneTopology.Straight
import OAI.Geometry.Cannon.Beltrami.DirichletPullback

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

noncomputable section
open Set Metric Filter Topology

noncomputable section
open Set Filter Topology Metric

namespace CannonBeltrami
open MeasureTheory Set Metric

lemma continuous_memLp_restrict_compact {f : ℂ → ℂ} (hf : Continuous f)
    {S : Set ℂ} (hS : IsCompact S) : MemLp f 2 (volume.restrict S) := by
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨B,hB⟩ := isBounded_iff_forall_norm_le.mp (hS.image hf).isBounded
  apply MemLp.of_bound hf.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
  exact hB _ ⟨z,hz,rfl⟩

lemma partialZ_norm_le (F : ℂ → ℂ) (z : ℂ) : ‖partialZ F z‖ ≤ ‖fderiv ℝ F z‖ := by
  unfold partialZ
  rw [norm_div]
  have hx := (fderiv ℝ F z).le_opNorm (1:ℂ)
  have hy := (fderiv ℝ F z).le_opNorm Complex.I
  have hh := norm_sub_le (fderiv ℝ F z 1) (Complex.I*fderiv ℝ F z Complex.I)
  simp only [norm_one,mul_one,Complex.norm_I,norm_mul,one_mul] at hx hy hh
  norm_num
  linarith

lemma l2_restrict_integral_norm_sq {f : ℂ → ℂ} {S : Set ℂ}
    (hf : MemLp f 2 (volume.restrict S)) :
    (∫ z in S, ‖f z‖^2)=‖hf.toLp‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz,real_inner_self_eq_norm_sq]

theorem smooth_local_energy_bound (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F : ℂ → ℂ))
    {S : Set ℂ} (hS : IsCompact S) {K B : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|)
    (hb : ∀ z ∈ S, ‖F z‖ ≤ B) :
    (∫ z in S, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2) ≤ K*volume.real (closedBall (0:ℂ) B) := by
  have hh := dirichlet_pullback_le F hF (fun z : ℂ => z) contDiff_id hS hK hD
  have hi : (∫ z in S, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2) ≤ K*volume.real (F '' S) := by
    have hid (w : ℂ) : fderiv ℝ (fun z : ℂ => z) w=ContinuousLinearMap.id ℝ ℂ :=
      fderiv_id
    simp only [Function.comp_def,hid,ContinuousLinearMap.norm_id,one_pow,
      setIntegral_const,smul_eq_mul,mul_one] at hh
    exact hh
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply measureReal_mono _ (isCompact_closedBall (0:ℂ) B).measure_ne_top
  rintro _ ⟨z,hz,rfl⟩
  simpa only [mem_closedBall,dist_zero_right] using hb z hz

lemma smooth_partialZ_l2_bound (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ ∞ (F : ℂ → ℂ))
    {S : Set ℂ} (hS : IsCompact S) {K B : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|)
    (hb : ∀ z ∈ S, ‖F z‖ ≤ B) :
    let h := continuous_memLp_restrict_compact (contDiff_partials hF).1.continuous hS
    ‖h.toLp‖ ≤ K*volume.real (closedBall (0:ℂ) B)+1 := by
  dsimp only
  let h := continuous_memLp_restrict_compact (contDiff_partials hF).1.continuous hS
  have hs : ‖h.toLp‖^2 ≤ K*volume.real (closedBall (0:ℂ) B) := by
    rw [← l2_restrict_integral_norm_sq h]
    apply le_trans ?_ (smooth_local_energy_bound F (hF.of_le (by simp)) hS hK hD hb)
    apply setIntegral_mono_on h.norm.integrable_sq
      (((hF.of_le (by simp) : ContDiff ℝ 1 (F : ℂ → ℂ)).continuous_fderiv (by simp)).norm.pow 2
        |>.continuousOn.integrableOn_compact hS) hS.measurableSet
    intro z _
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (partialZ_norm_le F z)
  have hp : 0 ≤ K*volume.real (closedBall (0:ℂ) B) := mul_nonneg hK measureReal_nonneg
  nlinarith [norm_nonneg h.toLp]

end CannonBeltrami

namespace CannonBeltrami
open MeasureTheory Filter Set Metric
open scoped Topology SchwartzMap ContDiff

lemma smooth_integration_by_parts (F : ℂ → ℂ) (hf : ContDiff ℝ 1 F)
    (φ : SchwartzMap ℂ ℂ) (hc : HasCompactSupport (φ : ℂ → ℂ)) (v : ℂ) :
    (∫ z, F z*fderiv ℝ (φ : ℂ → ℂ) z v) = -(∫ z, fderiv ℝ F z v*φ z) := by
  have hdf : Continuous (fun z => fderiv ℝ F z v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (fun z => fderiv ℝ (φ : ℂ → ℂ) z v) :=
    (φ.smooth'.continuous_fderiv (by simp)).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hdf.mul φ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hf.continuous.mul hdφ).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left
  · exact (hf.continuous.mul φ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · intro z _; exact hf.differentiable (by simp) z
  · intro z _; exact φ.differentiable z

lemma tendsto_l2_test (f : ℕ → Lp ℂ 2 (volume : Measure ℂ))
    {g : Lp ℂ 2 (volume : Measure ℂ)} (ht : Tendsto f atTop (𝓝 g)) (φ : SchwartzMap ℂ ℂ) :
    Tendsto (fun n => ∫ z, φ z*f n z) atTop (𝓝 (∫ z, φ z*g z)) := by
  have h := ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.tendsto g).comp ht
  have h' := PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp h φ
  simpa only [Function.comp_def,Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] using h'

lemma integral_test_add_const (f : Lp ℂ 2 (volume : Measure ℂ))
    (φ : SchwartzMap ℂ ℂ) (v : ℂ) :
    (∫ z, (v+f z)*φ z) = v*(∫ z, φ z)+(∫ z, φ z*f z) := by
  have hi : Integrable (fun z => φ z*f z) := (φ.memLp 2 volume).integrable_mul (Lp.memLp f)
  simp_rw [add_mul]
  rw [integral_add (φ.integrable.const_mul v) (by simpa only [mul_comm] using hi),integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact .of_forall (fun z => mul_comm _ _)

lemma bounded_displacement_test_tendsto (F : ℕ → ℂ → ℂ) (G : ℂ → ℂ)
    (hf : ∀ n, Continuous (F n)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n z, ‖F n z-z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)))
    (φ : SchwartzMap ℂ ℂ) (hc : HasCompactSupport (φ : ℂ → ℂ)) (v : ℂ) :
    Tendsto (fun n => ∫ z, F n z*fderiv ℝ (φ : ℂ → ℂ) z v) atTop
      (𝓝 (∫ z, G z*fderiv ℝ (φ : ℂ → ℂ) z v)) := by
  let D : ℂ → ℂ := fun z => fderiv ℝ (φ : ℂ → ℂ) z v
  have hd : Continuous D := (φ.smooth'.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcD : HasCompactSupport D := hc.fderiv_apply ℝ v
  have hdom : Integrable (fun z => (‖z‖+‖C‖)*‖D z‖) :=
    ((continuous_norm.add continuous_const).mul hd.norm).integrable_of_hasCompactSupport
      hcD.norm.mul_left
  apply tendsto_integral_of_dominated_convergence (fun z => (‖z‖+‖C‖)*‖D z‖)
    (fun n => ((hf n).mul hd).aestronglyMeasurable) hdom
  · intro n
    exact .of_forall (fun z => by
      change ‖F n z*D z‖ ≤ _
      rw [norm_mul, Real.norm_of_nonneg hC]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hh := norm_le_norm_add_norm_sub z (F n z)
      rw [norm_sub_rev] at hh
      exact hh.trans (add_le_add le_rfl (hb n z)))
  · exact .of_forall (fun z => (ht z).mul_const (D z))

theorem smooth_limit_weak_derivative (F : ℕ → ℂ → ℂ) (G : ℂ → ℂ)
    (hf : ∀ n, ContDiff ℝ 1 (F n)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n z, ‖F n z-z‖ ≤ C) (ht : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)))
    (v : ℂ) (d : ℕ → Lp ℂ 2 (volume : Measure ℂ)) (a : Lp ℂ 2 (volume : Measure ℂ))
    (hd : ∀ n, ∀ᵐ z ∂volume, fderiv ℝ (F n) z v=v+d n z)
    (hdt : Tendsto d atTop (𝓝 a)) :
    ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, G z*fderiv ℝ (φ : ℂ → ℂ) z v) = -(∫ z, (v+a z)*φ z) := by
  intro φ hc
  have hleft := bounded_displacement_test_tendsto F G (fun n => (hf n).continuous) hC hb ht φ hc v
  have hright : Tendsto (fun n => -(∫ z, (v+d n z)*φ z)) atTop
      (𝓝 (-(∫ z, (v+a z)*φ z))) := by
    simp_rw [integral_test_add_const]
    exact (tendsto_const_nhds.add (tendsto_l2_test d hdt φ)).neg
  apply tendsto_nhds_unique hleft
  apply hright.congr
  intro n
  rw [smooth_integration_by_parts (F n) (hf n) φ hc v]
  congr 1
  apply integral_congr_ae
  filter_upwards [hd n] with z hz
  rw [hz]

end CannonBeltrami

namespace CannonBeltrami

lemma smooth_partial_integration_by_parts (F : ℂ → ℂ) (hf : ContDiff ℝ 1 F)
    (φ : SchwartzMap ℂ ℂ) (hc : HasCompactSupport (φ : ℂ → ℂ)) :
    (∫ z, F z*partialZ φ z)=-(∫ z, partialZ F z*φ z) ∧
    (∫ z, F z*partialBar φ z)=-(∫ z, partialBar F z*φ z) := by
  have hfx (v : ℂ) : Integrable (fun z => F z*fderiv ℝ (φ : ℂ → ℂ) z v) :=
    (hf.continuous.mul ((φ.smooth'.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hdx (v : ℂ) : Integrable (fun z => fderiv ℝ F z v*φ z) :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul φ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have h1 := smooth_integration_by_parts F hf φ hc 1
  have hI := smooth_integration_by_parts F hf φ hc Complex.I
  have hz1 : (fun z => F z*partialZ φ z)=
      (fun z => (F z*fderiv ℝ (φ : ℂ → ℂ) z 1-Complex.I*(F z*fderiv ℝ (φ : ℂ → ℂ) z Complex.I))/2) := by
    ext z; unfold partialZ; ring
  have hz2 : (fun z => partialZ F z*φ z)=
      (fun z => (fderiv ℝ F z 1*φ z-Complex.I*(fderiv ℝ F z Complex.I*φ z))/2) := by
    ext z; unfold partialZ; ring
  have hb1 : (fun z => F z*partialBar φ z)=
      (fun z => (F z*fderiv ℝ (φ : ℂ → ℂ) z 1+Complex.I*(F z*fderiv ℝ (φ : ℂ → ℂ) z Complex.I))/2) := by
    ext z; unfold partialBar; ring
  have hb2 : (fun z => partialBar F z*φ z)=
      (fun z => (fderiv ℝ F z 1*φ z+Complex.I*(fderiv ℝ F z Complex.I*φ z))/2) := by
    ext z; unfold partialBar; ring
  rw [hz1,hz2,hb1,hb2]
  simp only [integral_div,integral_sub (hfx 1) ((hfx Complex.I).const_mul _),
    integral_sub (hdx 1) ((hdx Complex.I).const_mul _),
    integral_add (hfx 1) ((hfx Complex.I).const_mul _),
    integral_add (hdx 1) ((hdx Complex.I).const_mul _),integral_const_mul,h1,hI]
  constructor <;> ring

lemma compact_test_tendsto (F : ℕ → ℂ → ℂ) (G : ℂ → ℂ)
    (hf : ∀ n, Continuous (F n))
    (hb : ∀ S : Set ℂ, IsCompact S → ∃ B : ℝ, 0 ≤ B ∧ ∀ n z, z ∈ S → ‖F n z‖ ≤ B)
    (ht : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)))
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ z, F n z*ψ z) atTop (𝓝 (∫ z, G z*ψ z)) := by
  obtain ⟨B,hB,hbB⟩ := hb (tsupport ψ) hc
  have hdom : Integrable (fun z => B*‖ψ z‖) :=
    (continuous_const.mul hψ.norm).integrable_of_hasCompactSupport hc.norm.mul_left
  apply tendsto_integral_of_dominated_convergence (fun z => B*‖ψ z‖)
    (fun n => ((hf n).mul hψ).aestronglyMeasurable) hdom
  · intro n
    exact .of_forall (fun z => by
      change ‖F n z*ψ z‖ ≤ _
      rw [norm_mul]
      by_cases hz : ψ z=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_right (hbB n z (subset_tsupport _ hz)) (norm_nonneg _))
  · exact .of_forall (fun z => (ht z).mul_const (ψ z))

lemma hasCompactSupport_partials {φ : ℂ → ℂ} (hc : HasCompactSupport φ) :
    HasCompactSupport (partialZ φ) ∧ HasCompactSupport (partialBar φ) := by
  unfold partialZ partialBar
  simp only [div_eq_mul_inv]
  exact ⟨((hc.fderiv_apply ℝ 1).sub ((hc.fderiv_apply ℝ Complex.I).mul_left)).mul_right,
    ((hc.fderiv_apply ℝ 1).add ((hc.fderiv_apply ℝ Complex.I).mul_left)).mul_right⟩

end CannonBeltrami

noncomputable section
open Set Filter Topology

namespace CannonHilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma real_hilbert_biddual_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro A
  let R := InnerProductSpace.toDual ℝ E
  let B : E →L[ℝ] ℝ := A.comp R.toContinuousLinearEquiv.toContinuousLinearMap
  let x := R.symm B
  refine ⟨x,?_⟩
  ext L
  obtain ⟨y,rfl⟩ := R.surjective L
  change R y x=A (R y)
  have h : R x y=A (R y) := by
    change (R (R.symm B)) y=A (R y)
    rw [R.apply_symm_apply]
    rfl
  dsimp only [R] at h ⊢
  rw [InnerProductSpace.toDual_apply_apply,real_inner_comm,← InnerProductSpace.toDual_apply_apply]
  exact h

lemma bounded_weak_closure_compact (S : Set E) (hS : Bornology.IsBounded S) :
    IsCompact (closure (toWeakSpace ℝ E '' S)) := by
  apply NormedSpace.isCompact_closure_of_isBounded
  · simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ E).injective] using hS
  · have hs : Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
      intro A
      obtain ⟨x,hx⟩ := real_hilbert_biddual_surjective (StrongDual.toWeakDual.symm A)
      refine ⟨toWeakSpace ℝ E x,?_⟩
      change StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℝ E x)=A
      rw [hx]
      exact StrongDual.toWeakDual.apply_symm_apply A
    rw [hs.range_eq]
    exact subset_univ _

theorem bounded_weak_filter_limit (f : ℕ → E) {B : ℝ} (hB : ∀ n, ‖f n‖ ≤ B) :
    ∃ a : E, ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun n => toWeakSpace ℝ E (f n)) l (𝓝 (toWeakSpace ℝ E a)) := by
  have hb : Bornology.IsBounded (range f) :=
    isBounded_iff_forall_norm_le.mpr ⟨B,by rintro _ ⟨n,rfl⟩; exact hB n⟩
  have hc := bounded_weak_closure_compact (range f) hb
  let g : ℕ → WeakSpace ℝ E := fun n => toWeakSpace ℝ E (f n)
  obtain ⟨a,_,ha⟩ := hc.exists_mapClusterPt (u:=g) (f:=atTop) (Filter.le_principal_iff.mpr (by
    change ∀ᶠ n : ℕ in atTop, g n ∈ closure (toWeakSpace ℝ E '' range f)
    exact .of_forall (fun n => subset_closure ⟨f n,mem_range_self n,rfl⟩)))
  refine ⟨(toWeakSpace ℝ E).symm a,atTop ⊓ Filter.comap g (𝓝 a),?_,inf_le_left,?_⟩
  · exact Filter.neBot_inf_comap_iff_map.mpr (by simpa only [MapClusterPt,ClusterPt,inf_comm] using ha)
  · simp only [(toWeakSpace ℝ E).apply_symm_apply]
    exact Filter.map_le_iff_le_comap.mpr inf_le_right

end CannonHilbert

namespace CannonHilbert
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma weak_real_eval_tendsto {ι : Type*} {l : Filter ι} {f : ι → E} {a : E}
    (ht : Tendsto (fun i => toWeakSpace ℝ E (f i)) l (𝓝 (toWeakSpace ℝ E a)))
    (A : E →L[ℝ] ℝ) : Tendsto (fun i => A (f i)) l (𝓝 (A a)) := by
  exact (WeakBilin.eval_continuous _ A).tendsto (toWeakSpace ℝ E a) |>.comp ht

lemma weak_complex_eval_tendsto {ι : Type*} {l : Filter ι} {f : ι → E} {a : E}
    (ht : Tendsto (fun i => toWeakSpace ℝ E (f i)) l (𝓝 (toWeakSpace ℝ E a)))
    (A : E →L[ℝ] ℂ) : Tendsto (fun i => A (f i)) l (𝓝 (A a)) := by
  have hre := weak_real_eval_tendsto ht (Complex.reCLM.comp A)
  have him := weak_real_eval_tendsto ht (Complex.imCLM.comp A)
  have h := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  simpa only [ContinuousLinearMap.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    Function.comp_def,Complex.re_add_im] using h

variable [InnerProductSpace ℂ E]

lemma weak_inner_tendsto {ι : Type*} {l : Filter ι} {f : ι → E} {a : E}
    (ht : Tendsto (fun i => toWeakSpace ℝ E (f i)) l (𝓝 (toWeakSpace ℝ E a)))
    (v : E) : Tendsto (fun i => inner ℂ v (f i)) l (𝓝 (inner ℂ v a)) :=
  weak_complex_eval_tendsto ht ((innerSL ℂ v).restrictScalars ℝ)

theorem strong_weak_inner_tendsto {ι : Type*} {l : Filter ι} {f v : ι → E} {a b : E}
    (ht : Tendsto (fun i => toWeakSpace ℝ E (f i)) l (𝓝 (toWeakSpace ℝ E a)))
    (hv : Tendsto v l (𝓝 b)) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖f i‖ ≤ B) :
    Tendsto (fun i => inner ℂ (v i) (f i)) l (𝓝 (inner ℂ b a)) := by
  have hz : Tendsto (fun i => ‖v i-b‖*‖B‖) l (𝓝 0) := by
    simpa using ((hv.sub_const b).norm.mul_const ‖B‖)
  have he : Tendsto (fun i => inner ℂ (v i-b) (f i)) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) hz
    rw [Real.norm_of_nonneg hB]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _))
  have hh := he.add (weak_inner_tendsto ht b)
  simpa only [inner_sub_left,sub_add_cancel,zero_add] using hh
end CannonHilbert

open MeasureTheory
open scoped ENNReal

namespace CannonHilbert
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma dominated_toLp_zero {f : ℕ → X → ℂ} (hf : ∀ n, MemLp (f n) 2 ν)
    {g : X → ℂ} (hg : MemLp g 2 ν)
    (hb : ∀ n, ∀ᵐ x ∂ν, ‖f n x‖ ≤ ‖g x‖)
    (hl : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 0) := by
  have hb' : ∀ n, (fun x => ‖f n x‖ₑ ^ (2:ℝ)) ≤ᵐ[ν] (fun x => ‖g x‖ₑ ^ (2:ℝ)) := by
    intro n
    filter_upwards [hb n] with x hx
    exact ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.mpr hx) (by norm_num)
  have hfin : (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂ν) ≠ ⊤ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num) hg.eLpNorm_lt_top).ne
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => ‖f n x‖ₑ ^ (2:ℝ)) atTop (𝓝 (0:ℝ≥0∞)) := by
    filter_upwards [hl] with x hx
    have hc : Continuous (fun t : ℝ≥0∞ => t^(2:ℝ)) := ENNReal.continuous_rpow_const
    simpa only [Function.comp_def,enorm, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ)<2)] using
      hc.continuousAt.tendsto.comp (ENNReal.tendsto_coe.mpr hx.nnnorm)
  have hi := tendsto_lintegral_of_dominated_convergence' _
    (fun n => (hf n).aestronglyMeasurable.enorm.pow_const (2:ℝ)) hb' hfin hlim
  have heLp : Tendsto (fun n => eLpNorm (f n) 2 ν) atTop (𝓝 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (hf _).aestronglyMeasurable]
    have hc : Continuous (fun t : ℝ≥0∞ => t^(1/2:ℝ)) := ENNReal.continuous_rpow_const
    simpa [Function.comp_def] using hc.continuousAt.tendsto.comp hi
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf (0 : X → ℂ) (MemLp.zero : MemLp (0 : X → ℂ) 2 ν)).mpr
    (by simpa using heLp)
  simpa using h

lemma bounded_mul_memLp {μ ψ : X → ℂ} (hm : AEStronglyMeasurable μ ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖μ x‖ ≤ k) (hψ : MemLp ψ 2 ν) :
    MemLp (fun x => μ x*ψ x) 2 ν := by
  apply hψ.of_le_mul (c:=k) (hm.mul hψ.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖μ x*ψ x‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

lemma integral_mul_eq_inner (a : Lp ℂ 2 ν) {ψ : X → ℂ} (hψ : MemLp ψ 2 ν) :
    (∫ x, a x*ψ x ∂ν)=inner ℂ hψ.star.toLp a := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hψ.star.coeFn_toLp] with x hx
  simp only [RCLike.inner_apply,hx,Pi.star_apply]
  change a x*ψ x=a x*star (star (ψ x))
  rw [star_star]

lemma weak_integral_test_tendsto {ι : Type*} {l : Filter ι}
    {f : ι → Lp ℂ 2 ν} {a : Lp ℂ 2 ν}
    (ht : Tendsto (fun i => toWeakSpace ℝ (Lp ℂ 2 ν) (f i)) l
      (𝓝 (toWeakSpace ℝ (Lp ℂ 2 ν) a))) {ψ : X → ℂ} (hψ : MemLp ψ 2 ν) :
    Tendsto (fun i => ∫ x, f i x*ψ x ∂ν) l (𝓝 (∫ x, a x*ψ x ∂ν)) := by
  simp only [integral_mul_eq_inner _ hψ]
  exact weak_inner_tendsto ht hψ.star.toLp

lemma coefficient_test_strong_tendsto (μ : ℕ → X → ℂ) (m : X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) ν) (hm₀ : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n, ∀ᵐ x ∂ν, ‖μ n x‖ ≤ k)
    (hb₀ : ∀ᵐ x ∂ν, ‖m x‖ ≤ k)
    (ht : ∀ᵐ x ∂ν, Tendsto (fun n => μ n x) atTop (𝓝 (m x)))
    {ψ : X → ℂ} (hψ : MemLp ψ 2 ν) :
    Tendsto (fun n => (bounded_mul_memLp (hm n) (hb n) hψ).star.toLp) atTop
      (𝓝 (bounded_mul_memLp hm₀ hb₀ hψ).star.toLp) := by
  let u (n : ℕ) : Lp ℂ 2 ν := (bounded_mul_memLp (hm n) (hb n) hψ).star.toLp
  let v : Lp ℂ 2 ν := (bounded_mul_memLp hm₀ hb₀ hψ).star.toLp
  have he (n : ℕ) : (u n-v : Lp ℂ 2 ν) =ᵐ[ν] fun x => star (μ n x*ψ x)-star (m x*ψ x) := by
    filter_upwards [Lp.coeFn_sub (u n) v,
      (bounded_mul_memLp (hm n) (hb n) hψ).star.coeFn_toLp,
      (bounded_mul_memLp hm₀ hb₀ hψ).star.coeFn_toLp] with x h1 h2 h3
    change (u n : X → ℂ) x=star (μ n x*ψ x) at h2
    change (v : X → ℂ) x=star (m x*ψ x) at h3
    simpa only [Pi.sub_apply,h2,h3] using h1
  have hd (n : ℕ) : ∀ᵐ x ∂ν, ‖(u n-v : Lp ℂ 2 ν) x‖ ≤ ‖((2*k:ℝ):ℂ)*ψ x‖ := by
    filter_upwards [he n,hb n,hb₀] with x hx h1 h2
    rw [hx,← star_sub,norm_star,← sub_mul,norm_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤2*k)]
    exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _)
  have hl : ∀ᵐ x ∂ν, Tendsto (fun n => (u n-v : Lp ℂ 2 ν) x) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.mpr he,ht] with x h1 h2
    simp only [h1]
    simpa using ((h2.mul_const (ψ x)).star.sub_const (star (m x*ψ x)))
  have hh := dominated_toLp_zero (fun n => Lp.memLp (u n-v))
    (hψ.const_mul ((2*k:ℝ):ℂ)) hd hl
  simp only [Lp.toLp_coeFn] at hh
  exact tendsto_sub_nhds_zero_iff.mp hh

lemma weak_moving_integral_test_tendsto {l : Filter ℕ} (hl : l ≤ atTop)
    {f : ℕ → Lp ℂ 2 ν} {a : Lp ℂ 2 ν}
    (hw : Tendsto (fun n => toWeakSpace ℝ (Lp ℂ 2 ν) (f n)) l
      (𝓝 (toWeakSpace ℝ (Lp ℂ 2 ν) a))) {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ n, ‖f n‖ ≤ B)
    (μ : ℕ → X → ℂ) (m : X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) ν) (hm₀ : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n, ∀ᵐ x ∂ν, ‖μ n x‖ ≤ k)
    (hb₀ : ∀ᵐ x ∂ν, ‖m x‖ ≤ k)
    (ht : ∀ᵐ x ∂ν, Tendsto (fun n => μ n x) atTop (𝓝 (m x)))
    {ψ : X → ℂ} (hψ : MemLp ψ 2 ν) :
    Tendsto (fun n => ∫ x, f n x*(μ n x*ψ x) ∂ν) l
      (𝓝 (∫ x, a x*(m x*ψ x) ∂ν)) := by
  simp only [integral_mul_eq_inner _ (bounded_mul_memLp (hm _) (hb _) hψ),
    integral_mul_eq_inner _ (bounded_mul_memLp hm₀ hb₀ hψ)]
  exact strong_weak_inner_tendsto hw
    ((coefficient_test_strong_tendsto μ m hm hm₀ hk hb hb₀ ht hψ).mono_left hl) hB hfB
end CannonHilbert

namespace CannonBeltrami
open CannonHilbert

theorem local_weak_beltrami_limit (F : ℕ → ℂ ≃ₜ ℂ) (G : ℂ → ℂ)
    (hf : ∀ n, ContDiff ℝ ∞ (F n : ℂ → ℂ))
    (hlocal : ∀ S : Set ℂ, IsCompact S → ∃ B : ℝ, 0 ≤ B ∧ ∀ n z, z ∈ S → ‖F n z‖ ≤ B)
    (hlim : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)))
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ n z, ‖fderiv ℝ (F n : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F n : ℂ → ℂ) z).det|)
    (μ : ℕ → ℂ → ℂ) (m : ℂ → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (μ n) volume) (hm₀ : AEStronglyMeasurable m volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ n z, ‖μ n z‖ ≤ k) (hb₀ : ∀ z, ‖m z‖ ≤ k)
    (hμ : ∀ᵐ z ∂volume, Tendsto (fun n => μ n z) atTop (𝓝 (m z)))
    (he : ∀ n z, partialBar (F n) z=μ n z*partialZ (F n) z)
    {S : Set ℂ} (hS : IsCompact S) :
    ∃ a : Lp ℂ 2 (volume.restrict S),
      ∀ φ : SchwartzMap ℂ ℂ, tsupport (φ : ℂ → ℂ) ⊆ S →
        (∫ z, G z*partialZ φ z)=-(∫ z in S, a z*φ z) ∧
        (∫ z, G z*partialBar φ z)=-(∫ z in S, a z*(m z*φ z)) := by
  let ν := volume.restrict S
  have hLp (n : ℕ) : MemLp (partialZ (F n)) 2 ν :=
    continuous_memLp_restrict_compact (contDiff_partials (hf n)).1.continuous hS
  let f (n : ℕ) : Lp ℂ 2 ν := (hLp n).toLp
  obtain ⟨B,hB,hbB⟩ := hlocal S hS
  let C := K*volume.real (closedBall (0:ℂ) B)+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (n : ℕ) : ‖f n‖ ≤ C :=
    smooth_partialZ_l2_bound (F n) (hf n) hS hK (hD n) (hbB n)
  obtain ⟨a,l,hl,hlTop,ha⟩ := bounded_weak_filter_limit f hbound
  let : l.NeBot := hl
  refine ⟨a,?_⟩
  intro φ hφS
  have hcφ : HasCompactSupport (φ : ℂ → ℂ) := hS.of_isClosed_subset (isClosed_tsupport _) hφS
  have hφ : MemLp (φ : ℂ → ℂ) 2 ν := continuous_memLp_restrict_compact φ.continuous hS
  have hφout (z : ℂ) (hz : z ∉ S) : φ z=0 := by
    by_contra hn
    exact hz (hφS (subset_tsupport _ hn))
  have htestZ := weak_integral_test_tendsto ha hφ
  have htestBar := weak_moving_integral_test_tendsto hlTop ha hC hbound μ m
    (fun n => (hm n).restrict) hm₀.restrict hk
    (fun n => .of_forall (hb n)) (.of_forall hb₀) (ae_restrict_of_ae hμ) hφ
  have hidZ (n : ℕ) : (∫ z in S, f n z*φ z)=(∫ z, partialZ (F n) z*φ z) := by
    calc
      _ = ∫ z in S, partialZ (F n) z*φ z := by
        apply integral_congr_ae
        filter_upwards [(hLp n).coeFn_toLp] with z hz
        rw [hz]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hφout z hz,mul_zero])
  have hidBar (n : ℕ) : (∫ z in S, f n z*(μ n z*φ z))=(∫ z, partialBar (F n) z*φ z) := by
    calc
      _ = ∫ z in S, partialBar (F n) z*φ z := by
        apply integral_congr_ae
        filter_upwards [(hLp n).coeFn_toLp] with z hz
        rw [hz,he]; ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hφout z hz,mul_zero])
  have hp := hasCompactSupport_partials hcφ
  have hz := compact_test_tendsto (fun n z => F n z) G (fun n => (F n).continuous)
    hlocal hlim (partialZ φ) (contDiff_partials φ.smooth').1.continuous hp.1
  have hb' := compact_test_tendsto (fun n z => F n z) G (fun n => (F n).continuous)
    hlocal hlim (partialBar φ) (contDiff_partials φ.smooth').2.continuous hp.2
  have hparts (n : ℕ) := smooth_partial_integration_by_parts (F n)
    ((hf n).of_le (by simp)) φ hcφ
  constructor
  · have ht : Tendsto (fun n => ∫ z, F n z*partialZ φ z) l (𝓝 (-(∫ z in S, a z*φ z))) := by
      simpa only [ν,hidZ, (hparts _).1] using htestZ.neg
    exact tendsto_nhds_unique (hz.mono_left hlTop) ht
  · have ht : Tendsto (fun n => ∫ z, F n z*partialBar φ z) l (𝓝 (-(∫ z in S, a z*(m z*φ z)))) := by
      simpa only [ν,hidBar, (hparts _).2] using htestBar.neg
    exact tendsto_nhds_unique (hb'.mono_left hlTop) ht
end CannonBeltrami

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

end OAI
