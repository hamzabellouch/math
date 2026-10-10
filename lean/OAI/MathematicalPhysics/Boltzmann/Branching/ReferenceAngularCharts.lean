import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceCollisionGeometry

namespace OAI

section

/-! # Local unit-sphere coordinates at the minorization collision -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def incomingTangent : V →L[ℝ] V := (EuclideanSpace.proj 0).smulRight beamAxis
def normalTangent : V →L[ℝ] V :=
  (EuclideanSpace.proj 1).smulRight secondAxis +
    ((1 / Real.sqrt 2 : ℝ) • EuclideanSpace.proj 2).smulRight (firstAxis-beamAxis)

def incomingChart (z : V) : V := NormedSpace.normalize (firstAxis+incomingTangent z)
def normalChart (z : V) : V := NormedSpace.normalize (minorizationNormal+normalTangent z)
def minorizationChart (z : V) : V := child (incomingChart z) beamAxis (normalChart z)

@[simp] theorem incomingChart_zero : incomingChart 0 = firstAxis := by
  simp [incomingChart,NormedSpace.normalize_eq_self_of_norm_eq_one axis_norms.1]

@[simp] theorem normalChart_zero : normalChart 0 = minorizationNormal := by
  simp [normalChart,NormedSpace.normalize_eq_self_of_norm_eq_one minorizationNormal_norm]

@[simp] theorem minorizationChart_zero : minorizationChart 0 = 0 := by
  simp [minorizationChart,minorization_child_zero]

theorem incomingChart_hasFDerivAt : HasFDerivAt incomingChart incomingTangent 0 := by
  apply normalize_fderiv ((incomingTangent.hasFDerivAt).const_add firstAxis)
  · simpa using axis_norms.1
  · intro z
    simp [incomingTangent,inner_smul_right,first_beam_inner]

theorem normalChart_hasFDerivAt : HasFDerivAt normalChart normalTangent 0 := by
  apply normalize_fderiv ((normalTangent.hasFDerivAt).const_add minorizationNormal)
  · simpa using minorizationNormal_norm
  · intro z
    simp [normalTangent,minorizationNormal,inner_add_left,inner_add_right,
      inner_sub_right,inner_smul_left,inner_smul_right,
      firstAxis,secondAxis,beamAxis,EuclideanSpace.inner_single_left,
      EuclideanSpace.single]

theorem incomingChart_contDiffAt : ContDiffAt ℝ 1 incomingChart 0 := by
  have h : ContDiffAt ℝ 1 (fun z => firstAxis+incomingTangent z) (0 : V) :=
    (contDiff_const.add incomingTangent.contDiff).contDiffAt
  have hn : firstAxis+incomingTangent 0 ≠ 0 := by
    simpa using norm_ne_zero_iff.mp (by rw [axis_norms.1]; norm_num)
  exact (h.norm ℝ hn).inv (norm_ne_zero_iff.mpr hn) |>.smul h

theorem normalChart_contDiffAt : ContDiffAt ℝ 1 normalChart 0 := by
  have h : ContDiffAt ℝ 1 (fun z => minorizationNormal+normalTangent z) (0 : V) :=
    (contDiff_const.add normalTangent.contDiff).contDiffAt
  have hn : minorizationNormal+normalTangent 0 ≠ 0 := by
    simpa using norm_ne_zero_iff.mp (by rw [minorizationNormal_norm]; norm_num)
  exact (h.norm ℝ hn).inv (norm_ne_zero_iff.mpr hn) |>.smul h

theorem minorizationChart_contDiffAt : ContDiffAt ℝ 1 minorizationChart 0 := by
  have hu := incomingChart_contDiffAt
  have hn : incomingChart 0-beamAxis ≠ 0 := by
    rw [incomingChart_zero]
    exact norm_ne_zero_iff.mp (by rw [first_beam_norms.2]; positivity)
  exact (ContDiffAt.const_smul (1/2 : ℝ) (hu.add contDiffAt_const)).add
    ((((hu.sub contDiffAt_const).norm ℝ hn).div contDiffAt_const (by norm_num)).smul normalChart_contDiffAt)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The full derivative of the reference collision chart -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def minorizationDerivative : V →L[ℝ] V :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).smulRight (minorizationDirections i)

theorem incomingChart_distance_derivative :
    HasFDerivAt (fun z => ‖incomingChart z-beamAxis‖)
      ((-1/Real.sqrt 2 : ℝ) • (EuclideanSpace.proj 0 : V →L[ℝ] ℝ)) 0 := by
  have hs := (incomingChart_hasFDerivAt.sub_const beamAxis).norm_sq.sqrt
    (by rw [incomingChart_zero,first_beam_norms.2]; positivity)
  convert hs using 1
  · funext z
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · ext z
    simp only [incomingChart_zero,first_beam_norms.2,
      Real.sqrt_sq (Real.sqrt_nonneg 2),smul_apply,
      ContinuousLinearMap.comp_apply,innerSL_apply_apply,incomingTangent,
      ContinuousLinearMap.smulRight_apply,inner_smul_right,inner_sub_left,
      first_beam_inner,real_inner_self_eq_norm_sq,axis_norms.2.2,one_pow]
    simp only [smul_eq_mul]
    ring

theorem minorizationChart_hasFDerivAt :
    HasFDerivAt minorizationChart minorizationDerivative 0 := by
  have hn : HasFDerivAt (fun z => ‖incomingChart z-beamAxis‖/2)
      ((1/2 : ℝ) • ((-1/Real.sqrt 2 : ℝ) • (EuclideanSpace.proj 0 : V →L[ℝ] ℝ))) 0 := by
    convert incomingChart_distance_derivative.const_smul (1/2 : ℝ) using 1
    ext z
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
  have h := ((incomingChart_hasFDerivAt.add_const beamAxis).const_smul (1/2 : ℝ)).add
    (hn.smul normalChart_hasFDerivAt)
  convert h using 1
  · rfl
  · ext1 z
    simp only [minorizationDerivative,
      ContinuousLinearMap.smulRight_apply,Fin.sum_univ_three,minorizationDirections,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      add_apply,smul_apply,
      incomingTangent,normalTangent,
      incomingChart_zero,normalChart_zero,first_beam_norms.2,minorizationNormal]
    have hroot : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    simp only [smul_smul,smul_add,smul_sub,smul_eq_mul]
    ext i
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    field_simp
    rw [hsq]
    ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A radial extension of the outgoing angular chart -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def normalRadialChart (z : V) : V := ((1/2 : ℝ)+z 0) • normalChart z

def normalRadialDerivative : V →L[ℝ] V :=
  (EuclideanSpace.proj 0).smulRight minorizationNormal + (1/2 : ℝ) • normalTangent

theorem normalRadialChart_hasFDerivAt :
    HasFDerivAt normalRadialChart normalRadialDerivative 0 := by
  have h := ((EuclideanSpace.proj 0 : V →L[ℝ] ℝ).hasFDerivAt.const_add (1/2 : ℝ)).smul
    normalChart_hasFDerivAt
  convert h using 1
  · rfl
  · ext1 z
    simp [normalRadialDerivative,add_comm]

theorem normalRadialChart_contDiffAt : ContDiffAt ℝ 1 normalRadialChart 0 := by
  exact (contDiffAt_const.add (EuclideanSpace.proj 0 : V →L[ℝ] ℝ).contDiff.contDiffAt).smul
    normalChart_contDiffAt

theorem normalRadialDerivative_injective : Function.Injective normalRadialDerivative := by
  intro x y h
  have hz : normalRadialDerivative (x-y) = 0 := by rw [map_sub,h,sub_self]
  have h₀ := congrArg (fun z : V => z 0) hz
  have h₁ := congrArg (fun z : V => z 1) hz
  have h₂ := congrArg (fun z : V => z 2) hz
  simp [normalRadialDerivative,normalTangent,minorizationNormal,firstAxis,secondAxis,
    beamAxis,EuclideanSpace.single] at h₀ h₁ h₂
  have hp : 0 < (Real.sqrt 2)⁻¹ := by positivity
  have hz₀ : x 0-y 0 = 0 := by nlinarith [h₀,h₂]
  have hz₁ : x 1-y 1 = 0 := by simpa using h₁
  have hz₂ : x 2-y 2 = 0 := by nlinarith [h₀,h₂]
  ext i
  fin_cases i
  · exact sub_eq_zero.mp hz₀
  · exact sub_eq_zero.mp hz₁
  · exact sub_eq_zero.mp hz₂

def normalRadialEquiv : V ≃L[ℝ] V :=
  (LinearEquiv.ofBijective normalRadialDerivative.toLinearMap
    ⟨normalRadialDerivative_injective,
      LinearMap.surjective_of_injective normalRadialDerivative_injective⟩).toContinuousLinearEquiv

theorem normalRadialChart_hasStrictFDerivAt :
    HasStrictFDerivAt normalRadialChart (normalRadialEquiv : V →L[ℝ] V) 0 := by
  apply normalRadialChart_contDiffAt.hasStrictFDerivAt' _ (by norm_num)
  exact normalRadialChart_hasFDerivAt

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Radial volume estimates for the outgoing angular chart -/

noncomputable section

open MeasureTheory Set Metric
open scoped Topology ENNReal NNReal RealInnerProductSpace Pointwise

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem normalTangent_inner (z : V) : inner ℝ minorizationNormal (normalTangent z) = 0 := by
  simp [normalTangent,minorizationNormal,inner_add_left,inner_add_right,
    inner_sub_right,inner_smul_left,inner_smul_right,firstAxis,secondAxis,
    beamAxis,EuclideanSpace.inner_single_left,EuclideanSpace.single]

theorem normalChart_norm (z : V) : ‖normalChart z‖ = 1 := by
  apply NormedSpace.norm_normalize
  intro h
  have hi : inner ℝ minorizationNormal (minorizationNormal+normalTangent z) = 1 := by
    rw [inner_add_right,real_inner_self_eq_norm_sq,minorizationNormal_norm,normalTangent_inner]
    norm_num
  rw [h,inner_zero_right] at hi
  norm_num at hi

def angularSphere (z : V) : Sphere :=
  ⟨normalChart z,mem_sphere_zero_iff_norm.mpr (normalChart_norm z)⟩

theorem angularSphere_measurable : Measurable angularSphere := by
  apply Measurable.subtype_mk
  unfold normalChart NormedSpace.normalize
  fun_prop

theorem normalRadialChart_volume_lower :
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧ r ≤ 1/4 ∧ 0 < K ∧
      ∀ T : Set V, T ⊆ ball (0 : V) r →
        volume T ≤ (K : ℝ≥0∞)^3 * volume (normalRadialChart '' T) := by
  obtain ⟨S,hS0,hS,happrox⟩ := normalRadialChart_hasStrictFDerivAt.approximates_deriv_on_open_nhds
  have hN : 0 < ‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊ :=
    normalRadialEquiv.nnnorm_symm_pos
  have hc : ‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊⁻¹/2 <
      ‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊⁻¹ :=
    NNReal.half_lt_self (ne_of_gt (inv_pos.mpr hN))
  let K := (‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊⁻¹-
    ‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊⁻¹/2)⁻¹
  have hK : 0 < K := inv_pos.mpr (tsub_pos_iff_lt.mpr hc)
  obtain ⟨r,hr,hrS⟩ := Metric.isOpen_iff.mp hS 0 hS0
  refine ⟨min r (1/4),K,lt_min hr (by norm_num),min_le_right _ _,hK,?_⟩
  intro T hT
  exact antilipschitzOn_volume_image_le (happrox.antilipschitz (Or.inr hc))
    (hT.trans ((ball_subset_ball (min_le_left _ _)).trans hrS))

theorem normalRadialChart_mem_cone {r : ℝ} (hr : r ≤ 1/4) {A : Set Sphere}
    {z : V} (hz : z ∈ ball (0 : V) r) (hA : angularSphere z ∈ A) :
    normalRadialChart z ∈ Ioo (0 : ℝ) 1 • (Subtype.val '' A) := by
  have hn : ‖z‖ < r := by simpa only [mem_ball,dist_zero_right] using hz
  have hcoord : |z 0| ≤ ‖z‖ := PiLp.norm_apply_le z 0
  have hlo := neg_abs_le (z 0)
  have hup := le_abs_self (z 0)
  refine ⟨(1/2 : ℝ)+z 0,⟨by linarith,by linarith⟩,normalChart z,?_,rfl⟩
  exact ⟨angularSphere z,hA,rfl⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A local inverse of the physical reference collision chart -/

noncomputable section

open scoped Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem minorizationDerivative_injective :
    Function.Injective minorizationDerivative := by
  intro x y h
  have hz : minorizationDerivative (x-y) = 0 := by rw [map_sub,h,sub_self]
  have hs : ∑ i : Fin 3, ((x-y) i) • minorizationDirections i = 0 := by
    simpa only [minorizationDerivative,sum_apply,
      ContinuousLinearMap.smulRight_apply,EuclideanSpace.coe_proj] using hz
  ext i
  have hi := Fintype.linearIndependent_iff.mp minorizationDirections_independent
    (fun j => (x-y) j) hs i
  exact sub_eq_zero.mp hi

def minorizationLinearEquiv : V ≃L[ℝ] V :=
  (LinearEquiv.ofBijective minorizationDerivative.toLinearMap
    ⟨minorizationDerivative_injective,
      LinearMap.surjective_of_injective minorizationDerivative_injective⟩).toContinuousLinearEquiv

theorem minorizationChart_hasStrictFDerivAt :
    HasStrictFDerivAt minorizationChart (minorizationLinearEquiv : V →L[ℝ] V) 0 := by
  apply minorizationChart_contDiffAt.hasStrictFDerivAt' _ (by norm_num)
  exact minorizationChart_hasFDerivAt

def collisionLocalEquiv : OpenPartialHomeomorph V V :=
  minorizationChart_hasStrictFDerivAt.toOpenPartialHomeomorph minorizationChart

theorem collisionLocalEquiv_function : (collisionLocalEquiv : V → V) = minorizationChart := rfl

theorem collisionLocalEquiv_source : (0 : V) ∈ collisionLocalEquiv.source :=
  minorizationChart_hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source

theorem collisionLocalEquiv_target : (0 : V) ∈ collisionLocalEquiv.target := by
  have h := collisionLocalEquiv.map_source collisionLocalEquiv_source
  change minorizationChart 0 ∈ collisionLocalEquiv.target at h
  rwa [minorizationChart_zero] at h

theorem collisionLocalEquiv_contains_ball :
    ∃ r > 0, Metric.ball (0 : V) r ⊆ collisionLocalEquiv.target :=
  Metric.isOpen_iff.mp collisionLocalEquiv.open_target 0 collisionLocalEquiv_target

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Parameter volume is controlled by actual outgoing sphere area -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Pointwise

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem sphere_cone_volume_le {A : Set Sphere} (hA : MeasurableSet A) :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) ≤ sphereArea A := by
  have he : sphereArea A = (3 : ℝ≥0∞) *
      volume (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) := by
    simpa only [sphereArea,finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat] using
      (volume : Measure V).toSphere_apply' hA
  rw [he]
  calc
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) =
        (1 : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) := (one_mul _).symm
    _ ≤ _ := by gcongr; norm_num

theorem angularSphere_measure_bound :
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧ 0 < K ∧
      (volume.restrict (ball (0 : V) r)).map angularSphere ≤
        (K : ℝ≥0∞)^3 • sphereArea := by
  obtain ⟨r,K,hr,hrq,hK,hbound⟩ := normalRadialChart_volume_lower
  refine ⟨r,K,hr,hK,Measure.le_iff.mpr ?_⟩
  intro A hA
  rw [Measure.map_apply angularSphere_measurable hA,
    Measure.restrict_apply (angularSphere_measurable hA),Measure.smul_apply,smul_eq_mul]
  let T := angularSphere ⁻¹' A ∩ ball (0 : V) r
  have hT : T ⊆ ball (0 : V) r := inter_subset_right
  have hcone : normalRadialChart '' T ⊆ Ioo (0 : ℝ) 1 • (Subtype.val '' A) := by
    rintro _ ⟨z,hz,rfl⟩
    exact normalRadialChart_mem_cone hrq hz.2 hz.1
  refine (hbound T hT).trans ?_
  gcongr 1
  exact (measure_mono hcone).trans (sphere_cone_volume_le hA)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Splitting the inactive radial coordinate from angular parameters -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def angularSplit : V ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))))

theorem angularSplit_apply (z : V) : angularSplit z = (z 0,(z 1,z 2)) := rfl

theorem angularSplit_measurePreserving : MeasurePreserving angularSplit :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurePreserving.id volume).prod (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))))

def parameterSphere (p : ℝ × ℝ) : Sphere :=
  angularSphere (WithLp.toLp 2 ![0,p.1,p.2])

theorem parameterSphere_measurable : Measurable parameterSphere := by
  apply angularSphere_measurable.comp
  fun_prop

theorem angularSphere_factor (z : V) : angularSphere z = parameterSphere (z 1,z 2) := by
  apply Subtype.ext
  change normalChart z = normalChart (WithLp.toLp 2 ![0,z 1,z 2])
  simp [normalChart,normalTangent]

theorem angularSplit_map_restrict {I : Set ℝ} {B : Set (ℝ × ℝ)}
    (hI : MeasurableSet I) (hB : MeasurableSet B) :
    (volume.restrict (angularSplit ⁻¹' (I ×ˢ B))).map angularSphere =
      volume I • (volume.restrict B).map parameterSphere := by
  have hm : (volume.restrict (angularSplit ⁻¹' (I ×ˢ B))).map angularSplit =
      (volume.restrict I).prod (volume.restrict B) := by
    rw [(angularSplit_measurePreserving.restrict_preimage (hI.prod hB)).map_eq,
      Measure.prod_restrict]
    rfl
  have hf : angularSphere = (parameterSphere ∘ Prod.snd) ∘ angularSplit := by
    funext z
    exact angularSphere_factor z
  rw [hf,← Measure.map_map (parameterSphere_measurable.comp measurable_snd) angularSplit.measurable,hm,
    ← Measure.map_map parameterSphere_measurable measurable_snd,Measure.map_snd_prod,
    Measure.map_smul,Measure.restrict_apply_univ]
  exact parameterSphere_measurable.aemeasurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive volume in the image of the reference collision chart -/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem minorizationChart_volume_lower :
    ∃ (U : Set V) (r : ℝ) (K : ℝ≥0), IsOpen U ∧ (0 : V) ∈ U ∧ U ⊆ ball (0 : V) 1 ∧ 0 < r ∧ 0 < K ∧
      ∀ s : Set V, s ⊆ ball (0 : V) r →
        volume s ≤ (K : ℝ≥0∞)^3 * volume (U ∩ minorizationChart ⁻¹' s) := by
  obtain ⟨S,hS,happrox⟩ := minorizationChart_hasStrictFDerivAt.approximates_deriv_on_nhds
    (c := 1) (Or.inr zero_lt_one)
  obtain ⟨O,hOS,hO,hO0⟩ := _root_.mem_nhds_iff.mp hS
  let U := (O ∩ collisionLocalEquiv.source) ∩ ball (0 : V) 1
  have hU : IsOpen U := (hO.inter collisionLocalEquiv.open_source).inter isOpen_ball
  have hU0 : (0 : V) ∈ U := ⟨⟨hO0,collisionLocalEquiv_source⟩,mem_ball_self (by norm_num)⟩
  have hUS : U ⊆ S := fun _ hx => hOS hx.1.1
  have hUI : IsOpen (minorizationChart '' U) :=
    collisionLocalEquiv.isOpen_image_of_subset_source hU (fun _ hx => hx.1.2)
  have hI0 : (0 : V) ∈ minorizationChart '' U := ⟨0,hU0,minorizationChart_zero⟩
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hUI 0 hI0
  let K := ‖(minorizationLinearEquiv : V →L[ℝ] V)‖₊+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : LipschitzOnWith K minorizationChart U := by
    intro x hx y hy
    exact (happrox.mono_set hUS).lipschitz ⟨x,hx⟩ ⟨y,hy⟩
  refine ⟨U,r,K,hU,hU0,inter_subset_right,hr,hK,?_⟩
  intro s hs
  have hcover : s ⊆ minorizationChart '' (U ∩ minorizationChart ⁻¹' s) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hrU (hs hy)
    exact ⟨x,⟨hx,hy⟩,rfl⟩
  exact (measure_mono hcover).trans
    (lipschitz_volume_image_le (hL.mono inter_subset_left))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Two-dimensional angular parameter patches and sphere area -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def angularInterval (d : ℝ) : Set ℝ := Ioo (-d) d
def angularSquare (d : ℝ) : Set (ℝ × ℝ) := angularInterval d ×ˢ angularInterval d

theorem angular_box_subset_ball {d : ℝ} (hd : 0 < d) :
    angularSplit ⁻¹' (angularInterval d ×ˢ angularSquare d) ⊆ ball (0 : V) (4*d) := by
  intro z hz
  change (-d < z 0 ∧ z 0 < d) ∧ (-d < z 1 ∧ z 1 < d) ∧ (-d < z 2 ∧ z 2 < d) at hz
  have hs {x : ℝ} (hx : -d < x ∧ x < d) : x^2 < d^2 := by
    nlinarith [mul_pos (sub_pos.mpr hx.2) (show 0 < d+x by linarith [hx.1])]
  have hnorm : ‖z‖^2 = z 0^2+z 1^2+z 2^2 := by
    simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
  rw [mem_ball,dist_zero_right]
  nlinarith [hs hz.1,hs hz.2.1,hs hz.2.2,norm_nonneg z]

theorem angularSquare_weighted_measure_bound :
    ∃ (d : ℝ) (K : ℝ≥0), 0 < d ∧ 0 < K ∧
      volume (angularInterval d) • (volume.restrict (angularSquare d)).map parameterSphere ≤
        (K : ℝ≥0∞)^3 • sphereArea := by
  obtain ⟨r,K,hr,hK,hbound⟩ := angularSphere_measure_bound
  have hd : 0 < r/4 := div_pos hr (by norm_num)
  refine ⟨r/4,K,hd,hK,?_⟩
  rw [← angularSplit_map_restrict (I := angularInterval (r/4)) (B := angularSquare (r/4))
    measurableSet_Ioo (measurableSet_Ioo.prod measurableSet_Ioo)]
  apply le_trans (Measure.map_mono ?_ angularSphere_measurable) hbound
  apply Measure.restrict_mono
  · simpa only [mul_div_cancel₀ r (by norm_num : (4 : ℝ) ≠ 0)] using angular_box_subset_ball hd
  · exact le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A finite positive domination constant for the angular probability law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem angularInterval_volume (d : ℝ) :
    volume (angularInterval d) = ENNReal.ofReal (2*d) := by
  rw [angularInterval,Real.volume_Ioo]
  congr 1
  ring

theorem sphereProbability_rescale :
    ENNReal.ofReal (4*Real.pi) • sphereProbability = sphereArea := by
  rw [sphereProbability,smul_smul,ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,
    one_smul]

theorem parameterSphere_dominated :
    ∃ (d : ℝ) (C : ℝ≥0∞), 0 < d ∧ C ≠ 0 ∧ C ≠ ⊤ ∧
      (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability := by
  obtain ⟨d,K,hd,hK,hbound⟩ := angularSquare_weighted_measure_bound
  let I := volume (angularInterval d)
  let P := ENNReal.ofReal (4*Real.pi)
  let C := I⁻¹ * (K : ℝ≥0∞)^3 * P
  have hI0 : I ≠ 0 := by dsimp [I]; rw [angularInterval_volume d]; positivity
  have hIt : I ≠ ⊤ := by dsimp [I]; rw [angularInterval_volume d]; exact ENNReal.ofReal_ne_top
  have hP0 : P ≠ 0 := by dsimp [P]; positivity
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKn : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  have hC0 : C ≠ 0 := mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hIt)
    (pow_ne_zero 3 hKn)) hP0
  have hCt : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)) hPt
  refine ⟨d,C,hd,hC0,hCt,Measure.le_iff.mpr ?_⟩
  intro A hA
  have hb := hbound A
  simp only [Measure.smul_apply,smul_eq_mul] at hb ⊢
  have hrescale := congrArg (fun μ : Measure Sphere => μ A) sphereProbability_rescale
  simp only [Measure.smul_apply,smul_eq_mul] at hrescale
  calc
    ((volume.restrict (angularSquare d)).map parameterSphere) A =
        I⁻¹ * (I * ((volume.restrict (angularSquare d)).map parameterSphere) A) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hI0 hIt,one_mul]
    _ ≤ I⁻¹ * ((K : ℝ≥0∞)^3 * sphereArea A) := by gcongr
    _ = C * sphereProbability A := by
      rw [← hrescale]
      simp only [C,P,mul_assoc]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Rotating the outgoing chart to the incoming transverse direction -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def angularRotationLinear : V →L[ℝ] V :=
  (-(Real.sqrt 2)⁻¹ • ((EuclideanSpace.proj 0 : V →L[ℝ] ℝ)+EuclideanSpace.proj 2)).smulRight firstAxis +
  (EuclideanSpace.proj 1).smulRight secondAxis +
  ((Real.sqrt 2)⁻¹ • ((EuclideanSpace.proj 0 : V →L[ℝ] ℝ)-EuclideanSpace.proj 2)).smulRight beamAxis

theorem angularRotationLinear_norm (v : V) : ‖angularRotationLinear v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,angularRotationLinear,
    firstAxis,secondAxis,beamAxis,EuclideanSpace.single]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp
  nlinarith

def angularRotationIsometry : V →ₗᵢ[ℝ] V where
  toLinearMap := angularRotationLinear.toLinearMap
  norm_map' := angularRotationLinear_norm

def angularRotation : V ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofSurjective angularRotationIsometry
    (LinearMap.surjective_of_injective angularRotationIsometry.injective)

theorem angularRotation_normal : angularRotation minorizationNormal = firstAxis := by
  change angularRotationLinear minorizationNormal = firstAxis
  ext i
  fin_cases i <;> simp [angularRotationLinear,minorizationNormal,firstAxis,secondAxis,
    beamAxis,EuclideanSpace.single]
  all_goals
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith

theorem angularRotation_second : angularRotation secondAxis = secondAxis := by
  change angularRotationLinear secondAxis = secondAxis
  simp [angularRotationLinear,firstAxis,secondAxis,beamAxis,EuclideanSpace.single]

theorem angularRotation_tangent :
    angularRotation ((Real.sqrt 2)⁻¹ • (firstAxis-beamAxis)) = beamAxis := by
  change angularRotationLinear ((Real.sqrt 2)⁻¹ • (firstAxis-beamAxis)) = beamAxis
  ext i
  fin_cases i <;> simp [angularRotationLinear,firstAxis,secondAxis,beamAxis,EuclideanSpace.single]
  all_goals
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The incoming angular patch uses the same probability measure bound -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem angularRotation_normalize (v : V) :
    angularRotation (NormedSpace.normalize v) = NormedSpace.normalize (angularRotation v) := by
  simp [NormedSpace.normalize]

def incomingParameterSphere : (ℝ × ℝ) → Sphere :=
  sphereRotation angularRotation ∘ parameterSphere

def incomingPatch (z : V) : V := angularRotation (normalChart z)

theorem incomingParameterSphere_measurable : Measurable incomingParameterSphere :=
  (sphereRotation angularRotation).measurable.comp parameterSphere_measurable

theorem incomingPatch_zero : incomingPatch 0 = firstAxis := by
  rw [incomingPatch,normalChart_zero,angularRotation_normal]

theorem incomingPatch_hasFDerivAt :
    HasFDerivAt incomingPatch (angularRotation.toContinuousLinearEquiv.toContinuousLinearMap.comp
      normalTangent) 0 :=
  angularRotation.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp 0
    normalChart_hasFDerivAt

theorem incomingPatch_contDiffAt : ContDiffAt ℝ 1 incomingPatch 0 :=
  angularRotation.toContinuousLinearEquiv.contDiff.contDiffAt.comp 0 normalChart_contDiffAt

theorem incomingPatch_tangent (z : V) :
    angularRotation (normalTangent z) = z 1 • secondAxis+z 2 • beamAxis := by
  have hv : normalTangent z = z 1 • secondAxis+
      z 2 • ((Real.sqrt 2)⁻¹ • (firstAxis-beamAxis)) := by
    simp [normalTangent,smul_smul,div_eq_mul_inv,mul_comm]
  rw [hv,map_add,map_smul,map_smul,angularRotation_second,angularRotation_tangent]

theorem incomingParameterSphere_value (p : ℝ × ℝ) :
    (incomingParameterSphere p : V) =
      NormedSpace.normalize (firstAxis+p.1 • secondAxis+p.2 • beamAxis) := by
  change angularRotation (normalChart (WithLp.toLp 2 ![0,p.1,p.2])) = _
  rw [normalChart,angularRotation_normalize,map_add,angularRotation_normal,incomingPatch_tangent]
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  congr 1
  abel

theorem paired_parameterSphere_dominated :
    ∃ (d : ℝ) (C : ℝ≥0∞), 0 < d ∧ C ≠ 0 ∧ C ≠ ⊤ ∧
      (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability ∧
      (volume.restrict (angularSquare d)).map incomingParameterSphere ≤ C • sphereProbability := by
  obtain ⟨d,C,hd,hC0,hCt,hbound⟩ := parameterSphere_dominated
  refine ⟨d,C,hd,hC0,hCt,hbound,?_⟩
  have h := Measure.map_mono hbound (sphereRotation angularRotation).measurable
  rw [Measure.map_map (sphereRotation angularRotation).measurable parameterSphere_measurable,
    Measure.map_smul,(sphereRotation_probability angularRotation).map_eq] at h
  · exact h
  · exact (sphereRotation angularRotation).measurable.aemeasurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The collision chart with preceding velocity and unused angle as parameters -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev CollisionParameters := V × ℝ
abbrev CollisionFamilySpace := CollisionParameters × V

def collisionParameterBase : CollisionParameters := (beamAxis,0)
def collisionFamilyBase : CollisionFamilySpace := (collisionParameterBase,0)
def incidentDirection (t : ℝ) (z : V) : V :=
  NormedSpace.normalize (firstAxis+t • secondAxis+incomingTangent z)
def collisionFamily (p : CollisionParameters) (z : V) : V :=
  child (child p.1 (-beamAxis) (incidentDirection p.2 z)) beamAxis (normalChart z)
def collisionFamilyExtension (w : CollisionFamilySpace) : CollisionFamilySpace :=
  (w.1,collisionFamily w.1 w.2)

theorem child_opposite_beam (n : V) : child beamAxis (-beamAxis) n = n := by
  have he : beamAxis-(-beamAxis) = (2 : ℝ) • beamAxis := by module
  simp only [child,add_neg_cancel,smul_zero,he,norm_smul,Real.norm_ofNat,axis_norms.2.2,
    mul_one,div_self (by norm_num : (2 : ℝ) ≠ 0),one_smul,zero_add]

theorem collisionFamily_slice (z : V) :
    collisionFamily collisionParameterBase z = minorizationChart z := by
  simp [collisionFamily,collisionParameterBase,incidentDirection,child_opposite_beam,
    incomingChart,minorizationChart]

theorem collisionFamily_at_base : collisionFamily collisionParameterBase 0 = 0 := by
  rw [collisionFamily_slice,minorizationChart_zero]

theorem collisionFamilyExtension_at_base :
    collisionFamilyExtension collisionFamilyBase = collisionFamilyBase := by
  simp only [collisionFamilyExtension,collisionFamilyBase,collisionFamily_at_base]

private theorem normalize_contDiffAt {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f : D → V} {x : D} (hf : ContDiffAt ℝ 1 f x) (hne : f x ≠ 0) :
    ContDiffAt ℝ 1 (fun y => NormedSpace.normalize (f y)) x :=
  ((hf.norm ℝ hne).inv (norm_ne_zero_iff.mpr hne)).smul hf

private theorem child_contDiffAt {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f g n : D → V} {x : D} (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x)
    (hn : ContDiffAt ℝ 1 n x) (hne : f x ≠ g x) :
    ContDiffAt ℝ 1 (fun y => child (f y) (g y) (n y)) x := by
  exact (ContDiffAt.const_smul (1/2 : ℝ) (hf.add hg)).add
    ((((hf.sub hg).norm ℝ (sub_ne_zero.mpr hne)).div contDiffAt_const (by norm_num)).smul hn)

theorem incidentDirection_contDiffAt :
    ContDiffAt ℝ 1 (fun w : CollisionFamilySpace => incidentDirection w.1.2 w.2)
      collisionFamilyBase := by
  apply normalize_contDiffAt
  · change ContDiffAt ℝ 1
      (fun w : CollisionFamilySpace => firstAxis+w.1.2 • secondAxis+incomingTangent w.2) _
    fun_prop
  · change firstAxis+(0 : ℝ) • secondAxis+incomingTangent 0 ≠ 0
    simp only [zero_smul,add_zero,map_zero]
    exact norm_ne_zero_iff.mp (by rw [axis_norms.1]; norm_num)

theorem collisionFamily_contDiffAt :
    ContDiffAt ℝ 1 (fun w : CollisionFamilySpace => collisionFamily w.1 w.2)
      collisionFamilyBase := by
  apply child_contDiffAt
  · apply child_contDiffAt
    · fun_prop
    · exact contDiffAt_const
    · exact incidentDirection_contDiffAt
    · change beamAxis ≠ -beamAxis
      intro h
      have hz : beamAxis = 0 := by
        have he : (2 : ℝ) • beamAxis = 0 := by
          simpa only [two_smul,neg_add_cancel] using congrArg (fun v : V => v+beamAxis) h
        exact (smul_eq_zero.mp he).resolve_left (by norm_num)
      have := axis_norms.2.2
      rw [hz,norm_zero] at this
      norm_num at this
  · exact contDiffAt_const
  · exact normalChart_contDiffAt.comp (f := fun w : CollisionFamilySpace => w.2)
      collisionFamilyBase contDiffAt_snd
  · change child beamAxis (-beamAxis) (incidentDirection 0 0) ≠ beamAxis
    rw [child_opposite_beam]
    have hv : incidentDirection 0 0 = firstAxis := by
      simp [incidentDirection,NormedSpace.normalize_eq_self_of_norm_eq_one axis_norms.1]
    rw [hv]
    intro h
    have hi := first_beam_inner
    rw [h,real_inner_self_eq_norm_sq,axis_norms.2.2] at hi
    norm_num at hi

theorem collisionFamilyExtension_contDiffAt :
    ContDiffAt ℝ 1 collisionFamilyExtension collisionFamilyBase :=
  (by fun_prop : ContDiffAt ℝ 1 (fun w : CollisionFamilySpace => w.1) collisionFamilyBase).prodMk
    collisionFamily_contDiffAt

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The collision family has an invertible derivative including its parameters -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def collisionFamilyDerivative : CollisionFamilySpace →L[ℝ] CollisionFamilySpace :=
  fderiv ℝ collisionFamilyExtension collisionFamilyBase

theorem collisionFamilyExtension_hasFDerivAt :
    HasFDerivAt collisionFamilyExtension collisionFamilyDerivative collisionFamilyBase :=
  (collisionFamilyExtension_contDiffAt.differentiableAt (by norm_num)).hasFDerivAt

theorem collisionFamilyDerivative_fst (w : CollisionFamilySpace) :
    (collisionFamilyDerivative w).1 = w.1 := by
  have hf : (ContinuousLinearMap.fst ℝ CollisionParameters V).comp collisionFamilyDerivative =
      ContinuousLinearMap.fst ℝ CollisionParameters V :=
    collisionFamilyExtension_hasFDerivAt.fst.unique hasFDerivAt_fst
  exact congrArg (fun f : CollisionFamilySpace →L[ℝ] CollisionParameters => f w) hf

theorem collisionFamilyDerivative_slice (z : V) :
    collisionFamilyDerivative (0,z) = (0,minorizationDerivative z) := by
  have h := collisionFamilyExtension_hasFDerivAt.comp (0 : V)
    (hasFDerivAt_prodMk_right collisionParameterBase (0 : V))
  have hs : HasFDerivAt (fun z : V => (collisionParameterBase,minorizationChart z))
      (collisionFamilyDerivative.comp (ContinuousLinearMap.inr ℝ CollisionParameters V)) 0 := by
    simpa only [Function.comp_def,collisionFamilyExtension,collisionFamily_slice] using! h
  have hh := hs.unique ((hasFDerivAt_const collisionParameterBase (0 : V)).prodMk
    minorizationChart_hasFDerivAt)
  exact congrArg (fun f : V →L[ℝ] CollisionFamilySpace => f z) hh

theorem collisionFamilyDerivative_injective : Function.Injective collisionFamilyDerivative := by
  intro x y hxy
  have hu : collisionFamilyDerivative (x-y) = 0 := by rw [map_sub,hxy,sub_self]
  have hp : (x-y).1 = 0 := by
    rw [← collisionFamilyDerivative_fst]
    exact congrArg Prod.fst hu
  have he : x-y = (0,(x-y).2) := Prod.ext hp rfl
  rw [he,collisionFamilyDerivative_slice] at hu
  have hz : (x-y).2 = 0 := minorizationDerivative_injective (by
    simpa using congrArg Prod.snd hu)
  exact sub_eq_zero.mp (Prod.ext hp hz)

def collisionFamilyLinearEquiv : CollisionFamilySpace ≃L[ℝ] CollisionFamilySpace :=
  (LinearEquiv.ofBijective collisionFamilyDerivative.toLinearMap
    ⟨collisionFamilyDerivative_injective,
      LinearMap.surjective_of_injective collisionFamilyDerivative_injective⟩).toContinuousLinearEquiv

theorem collisionFamilyExtension_hasStrictFDerivAt :
    HasStrictFDerivAt collisionFamilyExtension
      (collisionFamilyLinearEquiv : CollisionFamilySpace →L[ℝ] CollisionFamilySpace)
      collisionFamilyBase := by
  apply collisionFamilyExtension_contDiffAt.hasStrictFDerivAt' _ (by norm_num)
  exact collisionFamilyExtension_hasFDerivAt

def collisionFamilyLocalEquiv : OpenPartialHomeomorph CollisionFamilySpace CollisionFamilySpace :=
  collisionFamilyExtension_hasStrictFDerivAt.toOpenPartialHomeomorph collisionFamilyExtension

theorem collisionFamilyLocalEquiv_source : collisionFamilyBase ∈ collisionFamilyLocalEquiv.source :=
  collisionFamilyExtension_hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source

theorem collisionFamilyLocalEquiv_target : collisionFamilyBase ∈ collisionFamilyLocalEquiv.target := by
  have h := collisionFamilyLocalEquiv.map_source collisionFamilyLocalEquiv_source
  change collisionFamilyExtension collisionFamilyBase ∈ collisionFamilyLocalEquiv.target at h
  rwa [collisionFamilyExtension_at_base] at h

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform local coverage for nearby preceding velocities -/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology NNReal ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem collisionFamily_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ (a δ : ℝ) (K : ℝ≥0), 0 < a ∧ a ≤ ε ∧ 0 < δ ∧ δ ≤ a ∧ 0 < K ∧
      ∀ p ∈ ball collisionParameterBase δ,
        LipschitzOnWith K (collisionFamily p) (ball (0 : V) a) ∧
        ball (0 : V) δ ⊆ collisionFamily p '' ball (0 : V) a := by
  obtain ⟨S,hS,happrox⟩ := collisionFamilyExtension_hasStrictFDerivAt.approximates_deriv_on_nhds
    (c := 1) (Or.inr zero_lt_one)
  have hsource : collisionFamilyLocalEquiv.source ∈ 𝓝 collisionFamilyBase :=
    collisionFamilyLocalEquiv.open_source.mem_nhds collisionFamilyLocalEquiv_source
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp (inter_mem hS hsource)
  let a := min r ε
  have ha : 0 < a := lt_min hr hε
  have hU : ball collisionFamilyBase a ⊆ S ∩ collisionFamilyLocalEquiv.source :=
    (ball_subset_ball (min_le_left _ _)).trans hrS
  have hopen : IsOpen (collisionFamilyExtension '' ball collisionFamilyBase a) :=
    collisionFamilyLocalEquiv.isOpen_image_of_subset_source isOpen_ball
      (hU.trans inter_subset_right)
  have hbase : collisionFamilyBase ∈ collisionFamilyExtension '' ball collisionFamilyBase a :=
    ⟨collisionFamilyBase,mem_ball_self ha,collisionFamilyExtension_at_base⟩
  obtain ⟨b,hb,hbI⟩ := Metric.isOpen_iff.mp hopen collisionFamilyBase hbase
  let δ := min b a
  let K := ‖(collisionFamilyLinearEquiv : CollisionFamilySpace →L[ℝ] CollisionFamilySpace)‖₊+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : LipschitzOnWith K collisionFamilyExtension (ball collisionFamilyBase a) := by
    intro x hx y hy
    exact (happrox.mono_set (hU.trans inter_subset_left)).lipschitz ⟨x,hx⟩ ⟨y,hy⟩
  refine ⟨a,δ,K,ha,min_le_right _ _,lt_min hb ha,min_le_right _ _,hK,?_⟩
  intro p hp
  have hpa : p ∈ ball collisionParameterBase a := ball_subset_ball (min_le_right b a) hp
  have hpair {z : V} (hz : z ∈ ball (0 : V) a) : (p,z) ∈ ball collisionFamilyBase a := by
    change (p,z) ∈ ball (collisionParameterBase,0) a
    rw [← ball_prod_same]
    exact ⟨hpa,hz⟩
  constructor
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [collisionFamilyExtension,dist_prod_same_left] using
      hL.dist_le_mul (p,x) (hpair hx) (p,y) (hpair hy)
  · intro y hy
    have hpy : (p,y) ∈ ball collisionFamilyBase δ := by
      change (p,y) ∈ ball (collisionParameterBase,0) δ
      rw [← ball_prod_same]
      exact ⟨hp,hy⟩
    obtain ⟨⟨q,z⟩,hz,he⟩ := hbI (ball_subset_ball (min_le_left b a) hpy)
    have hq : q = p := congrArg Prod.fst he
    subst q
    refine ⟨z,?_,congrArg Prod.snd he⟩
    change (p,z) ∈ ball (collisionParameterBase,0) a at hz
    rw [← ball_prod_same] at hz
    exact hz.2

theorem collisionFamily_uniform_volume {ε : ℝ} (hε : 0 < ε) :
    ∃ (a δ : ℝ) (K : ℝ≥0), 0 < a ∧ a ≤ ε ∧ 0 < δ ∧ δ ≤ a ∧ 0 < K ∧
      ∀ p ∈ ball collisionParameterBase δ, ∀ A : Set V, A ⊆ ball (0 : V) δ →
        volume A ≤ (K : ℝ≥0∞)^3 * volume (ball (0 : V) a ∩ collisionFamily p ⁻¹' A) := by
  obtain ⟨a,δ,K,ha,haε,hδ,hδa,hK,hfamily⟩ := collisionFamily_uniform hε
  refine ⟨a,δ,K,ha,haε,hδ,hδa,hK,?_⟩
  intro p hp A hA
  have hcover : A ⊆ collisionFamily p '' (ball (0 : V) a ∩ collisionFamily p ⁻¹' A) := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := (hfamily p hp).2 (hA hy)
    exact ⟨z,⟨hz,hy⟩,rfl⟩
  exact (measure_mono hcover).trans
    (lipschitz_volume_image_le ((hfamily p hp).1.mono inter_subset_left))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The actual two-angle collision law dominates its local parameter patch -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance angularSquare_isFinite (d : ℝ) : IsFiniteMeasure (volume.restrict (angularSquare d)) where
  measure_univ_lt_top := by
    rw [Measure.restrict_apply_univ]
    change (volume : Measure ℝ).prod volume (Ioo (-d) d ×ˢ Ioo (-d) d) < ⊤
    rw [Measure.prod_prod,Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

def sphereCollision (p : Sphere × Sphere) : V := child (p.1 : V) beamAxis (p.2 : V)
def pairedChart (p : (ℝ × ℝ) × (ℝ × ℝ)) : V :=
  sphereCollision (incomingParameterSphere p.1,parameterSphere p.2)
def twoSphereCollision : Measure V := (sphereProbability.prod sphereProbability).map sphereCollision

theorem sphereCollision_measurable : Measurable sphereCollision := by
  unfold sphereCollision child
  fun_prop

theorem pairedChart_measurable : Measurable pairedChart :=
  sphereCollision_measurable.comp
    (incomingParameterSphere_measurable.prodMap parameterSphere_measurable)

theorem pairedChart_measure_le {d : ℝ} {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hout : (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability)
    (hin : (volume.restrict (angularSquare d)).map incomingParameterSphere ≤ C • sphereProbability) :
    ((volume.restrict (angularSquare d)).prod (volume.restrict (angularSquare d))).map pairedChart ≤
      C^2 • twoSphereCollision := by
  have : IsFiniteMeasure (C • sphereProbability) := ⟨by
    rw [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact hCt.lt_top⟩
  have h := Measure.map_mono (Measure.prod_mono hin hout) sphereCollision_measurable
  rw [Measure.map_prod_map _ _ incomingParameterSphere_measurable parameterSphere_measurable,
    Measure.map_map sphereCollision_measurable
      (incomingParameterSphere_measurable.prodMap parameterSphere_measurable),
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    Measure.map_smul] at h
  · simpa only [pairedChart,twoSphereCollision,Function.comp_def,pow_two] using! h
  · exact sphereCollision_measurable.aemeasurable

theorem exists_pairedChart_measure_le :
    ∃ (d : ℝ) (C : ℝ≥0∞), 0 < d ∧ C ≠ 0 ∧ C ≠ ⊤ ∧
      ((volume.restrict (angularSquare d)).prod (volume.restrict (angularSquare d))).map pairedChart ≤
        C^2 • twoSphereCollision := by
  obtain ⟨d,C,hd,hC0,hCt,hout,hin⟩ := paired_parameterSphere_dominated
  exact ⟨d,C,hd,hC0,hCt,pairedChart_measure_le hCt hout hin⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Volume-preserving coordinates for the four collision angles -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def familyCoordinates : (ℝ × V) ≃ᵐ ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) angularSplit).trans
    MeasurableEquiv.prodAssoc.symm

theorem familyCoordinates_apply (t : ℝ) (z : V) :
    familyCoordinates (t,z) = ((t,z 0),(z 1,z 2)) := rfl

theorem familyCoordinates_measurePreserving : MeasurePreserving familyCoordinates :=
  ((MeasurePreserving.id volume).prod angularSplit_measurePreserving).trans
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc volume_preserving_prodAssoc)

def twoCollisionMap (v : V) (p : Sphere × Sphere) : V :=
  child (child v (-beamAxis) (p.1 : V)) beamAxis (p.2 : V)

def familyChart (v : V) (p : (ℝ × ℝ) × (ℝ × ℝ)) : V :=
  twoCollisionMap v (incomingParameterSphere p.1,parameterSphere p.2)

def twoCollisionLaw (v : V) : Measure V :=
  (sphereProbability.prod sphereProbability).map (twoCollisionMap v)

theorem twoCollisionMap_measurable (v : V) : Measurable (twoCollisionMap v) := by
  unfold twoCollisionMap child
  fun_prop

theorem familyChart_measurable (v : V) : Measurable (familyChart v) :=
  (twoCollisionMap_measurable v).comp
    (incomingParameterSphere_measurable.prodMap parameterSphere_measurable)

theorem familyChart_coordinates (v : V) (t : ℝ) (z : V) :
    familyChart v (familyCoordinates (t,z)) = collisionFamily (v,t) z := by
  change child (child v (-beamAxis) (incomingParameterSphere (t,z 0) : V)) beamAxis
    (parameterSphere (z 1,z 2) : V) = _
  rw [incomingParameterSphere_value]
  have hn : (parameterSphere (z 1,z 2) : V) = normalChart z :=
    (congrArg Subtype.val (angularSphere_factor z)).symm
  rw [hn]
  rfl

theorem familyChart_measure_le {d : ℝ} {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hout : (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability)
    (hin : (volume.restrict (angularSquare d)).map incomingParameterSphere ≤ C • sphereProbability)
    (v : V) :
    ((volume.restrict (angularSquare d)).prod (volume.restrict (angularSquare d))).map (familyChart v) ≤
      C^2 • twoCollisionLaw v := by
  have : IsFiniteMeasure (C • sphereProbability) := ⟨by
    rw [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact hCt.lt_top⟩
  have h := Measure.map_mono (Measure.prod_mono hin hout) (twoCollisionMap_measurable v)
  rw [Measure.map_prod_map _ _ incomingParameterSphere_measurable parameterSphere_measurable,
    Measure.map_map (twoCollisionMap_measurable v)
      (incomingParameterSphere_measurable.prodMap parameterSphere_measurable),
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.map_smul] at h
  · simpa only [familyChart,twoCollisionLaw,Function.comp_def,pow_two] using! h
  · exact (twoCollisionMap_measurable v).aemeasurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Averaging the uniform collision-chart volume estimate over the unused angle -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def familyWindowMeasure (a δ : ℝ) : Measure (ℝ × V) :=
  (volume.restrict (Ioo (-δ) δ)).prod (volume.restrict (ball (0 : V) a))

def familyWindowMap (v : V) (w : ℝ × V) : V := collisionFamily (v,w.1) w.2

theorem familyWindowMap_measurable (v : V) : Measurable (familyWindowMap v) := by
  unfold familyWindowMap collisionFamily incidentDirection normalChart NormedSpace.normalize child
  fun_prop

theorem familyWindowMeasure_preimage (v : V) (a δ : ℝ) {A : Set V} (hA : MeasurableSet A) :
    familyWindowMeasure a δ (familyWindowMap v ⁻¹' A) =
      ∫⁻ t in Ioo (-δ) δ, volume (ball (0 : V) a ∩ collisionFamily (v,t) ⁻¹' A) := by
  rw [familyWindowMeasure,Measure.prod_apply ((familyWindowMap_measurable v) hA)]
  apply lintegral_congr
  intro t
  have hs : MeasurableSet (Prod.mk t ⁻¹' (familyWindowMap v ⁻¹' A)) :=
    measurable_prodMk_left ((familyWindowMap_measurable v) hA)
  rw [Measure.restrict_apply hs]
  change volume (collisionFamily (v,t) ⁻¹' A ∩ ball (0 : V) a) = _
  rw [inter_comm]

theorem uniform_family_window_volume {ε : ℝ} (hε : 0 < ε) :
    ∃ (a δ : ℝ) (K : ℝ≥0), 0 < a ∧ a ≤ ε ∧ 0 < δ ∧ δ ≤ a ∧ 0 < K ∧
      ∀ v ∈ ball beamAxis δ, ∀ A : Set V, MeasurableSet A → A ⊆ ball (0 : V) δ →
        ENNReal.ofReal (2*δ) * volume A ≤ (K : ℝ≥0∞)^3 *
          ((familyWindowMeasure a δ).map (familyWindowMap v)) A := by
  obtain ⟨a,δ,K,ha,haε,hδ,hδa,hK,hbound⟩ := collisionFamily_uniform_volume hε
  refine ⟨a,δ,K,ha,haε,hδ,hδa,hK,?_⟩
  intro v hv A hA hAsub
  have hp (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : (v,t) ∈ ball collisionParameterBase δ := by
    change (v,t) ∈ ball (beamAxis,(0 : ℝ)) δ
    rw [← ball_prod_same]
    refine ⟨hv,?_⟩
    simpa only [mem_ball,Real.dist_eq,sub_zero,abs_lt,mem_Ioo] using ht
  rw [Measure.map_apply (familyWindowMap_measurable v) hA,
    familyWindowMeasure_preimage v a δ hA]
  calc
    ENNReal.ofReal (2*δ) * volume A = ∫⁻ _t in Ioo (-δ) δ, volume A := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
      rw [show δ- -δ = 2*δ by ring,mul_comm]
    _ ≤ ∫⁻ t in Ioo (-δ) δ,
        (K : ℝ≥0∞)^3 * volume (ball (0 : V) a ∩ collisionFamily (v,t) ⁻¹' A) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hbound (v,t) (hp t ht) A hAsub
    _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A collision window on which both chosen beam probabilities stay positive -/

noncomputable section

open MeasureTheory Set Metric

namespace BoltzmannNonuniqueness.ReferenceGeometry

def firstCollisionFamily (w : CollisionFamilySpace) : V :=
  child w.1.1 (-beamAxis) (incidentDirection w.1.2 w.2)

theorem firstCollisionFamily_at_base : firstCollisionFamily collisionFamilyBase = firstAxis := by
  rw [firstCollisionFamily]
  change child beamAxis (-beamAxis) (incidentDirection 0 0) = firstAxis
  rw [child_opposite_beam]
  simp [incidentDirection,NormedSpace.normalize_eq_self_of_norm_eq_one axis_norms.1]

theorem firstCollisionFamily_continuousAt :
    ContinuousAt firstCollisionFamily collisionFamilyBase := by
  have hn := incidentDirection_contDiffAt.continuousAt
  have hv : ContinuousAt (fun w : CollisionFamilySpace => w.1.1) collisionFamilyBase := by
    fun_prop
  change ContinuousAt (fun w : CollisionFamilySpace =>
    (1/2 : ℝ) • (w.1.1 + -beamAxis) + (‖w.1.1 - -beamAxis‖/2) •
      incidentDirection w.1.2 w.2) collisionFamilyBase
  exact ((hv.add continuousAt_const).const_smul (1/2 : ℝ)).add
    (((hv.sub continuousAt_const).norm.div_const 2).smul hn)

def localCollisionCore : Set V := ball firstAxis (1/4)

theorem localCollisionCore_measurable : MeasurableSet localCollisionCore := measurableSet_ball

theorem norm_le_two_of_near_unit {v e : V} (he : ‖e‖ = 1) (hv : v ∈ ball e (1/4)) :
    ‖v‖ ≤ 2 := by
  have ht := dist_triangle v e (0 : V)
  rw [dist_zero_right,dist_zero_right,he] at ht
  have hd : dist v e < 1/4 := hv
  linarith

theorem localCollisionCore_norm {v : V} (hv : v ∈ localCollisionCore) : ‖v‖ ≤ 2 :=
  norm_le_two_of_near_unit axis_norms.1 hv

theorem localCollisionCore_distance {v : V} (hv : v ∈ localCollisionCore) :
    1 ≤ ‖v-beamAxis‖ := by
  have ht := dist_triangle firstAxis v beamAxis
  rw [dist_eq_norm,first_beam_norms.2,dist_comm firstAxis v,dist_eq_norm v beamAxis] at ht
  have hd : dist v firstAxis < 1/4 := hv
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem beam_neighborhood_distance {v : V} (hv : v ∈ ball beamAxis (1/4)) :
    1 ≤ ‖v+beamAxis‖ := by
  have ht := dist_triangle beamAxis v (-beamAxis)
  have hb : dist beamAxis (-beamAxis) = 2 := by
    rw [dist_eq_norm,show beamAxis-(-beamAxis) = (2 : ℝ) • beamAxis by module,
      norm_smul,Real.norm_ofNat,axis_norms.2.2,mul_one]
  rw [hb,dist_comm beamAxis v,dist_eq_norm v (-beamAxis),sub_neg_eq_add] at ht
  have hd : dist v beamAxis < 1/4 := hv
  linarith

theorem collision_window_good : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧
    ∀ w ∈ ball collisionFamilyBase ε, firstCollisionFamily w ∈ localCollisionCore := by
  obtain ⟨r,hr,h⟩ := Metric.continuousAt_iff.mp firstCollisionFamily_continuousAt
    (1/4) (by norm_num)
  refine ⟨min r (1/4),lt_min hr (by norm_num),min_le_right _ _,?_⟩
  intro w hw
  have hd : dist w collisionFamilyBase < r := lt_of_lt_of_le hw (min_le_left _ _)
  have hh := h hd
  change dist (firstCollisionFamily w) firstAxis < 1/4
  simpa only [firstCollisionFamily_at_base] using hh

theorem familyWindow_good {ε a δ : ℝ} (ha : a ≤ ε) (hδ : δ ≤ a)
    (hgood : ∀ w ∈ ball collisionFamilyBase ε, firstCollisionFamily w ∈ localCollisionCore)
    {v : V} (hv : v ∈ ball beamAxis δ) {t : ℝ} (ht : t ∈ Ioo (-δ) δ)
    {z : V} (hz : z ∈ ball (0 : V) a) :
    firstCollisionFamily ((v,t),z) ∈ localCollisionCore := by
  apply hgood
  change ((v,t),z) ∈ ball ((beamAxis,(0 : ℝ)),(0 : V)) ε
  rw [← ball_prod_same,← ball_prod_same]
  refine ⟨⟨(ball_subset_ball (hδ.trans ha)) hv,?_⟩,(ball_subset_ball ha) hz⟩
  have hh : dist t (0 : ℝ) < δ := by
    simpa only [Real.dist_eq,sub_zero,abs_lt,mem_Ioo] using ht
  exact hh.trans_le (hδ.trans ha)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
