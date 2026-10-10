import OAI.Probability.LatticePassage.StationaryCalibration

namespace OAI

namespace CompanionFPP
open MeasureTheory Filter Topology
namespace DirectionalCalibration
variable {d : Vertex} (C : DirectionalCalibration d)

lemma integrable (x y : Vertex) : Integrable (fun ω => C.value ω x y) environmentLaw :=
  MemLp.integrable (by norm_num) (C.memLp x y)

lemma mean_translation (a x y : Vertex) :
    (∫ ω, C.value ω (a+x) (a+y) ∂environmentLaw) =
      ∫ ω, C.value ω x y ∂environmentLaw := by
  calc
    _ = ∫ ω, C.value (environmentTranslation a ω) x y ∂environmentLaw := by
      apply integral_congr_ae
      filter_upwards [C.covariant] with ω hω
      exact (hω a x y).symm
    _ = _ := by
      have h := integral_map (μ := environmentLaw) (measurable_environmentTranslation a).aemeasurable
        (C.measurable x y).aestronglyMeasurable
      rw [(environmentTranslation_preserving a).map_eq] at h
      exact h.symm

noncomputable def meanHom : Vertex →+ ℝ where
  toFun x := ∫ ω, C.value ω 0 x ∂environmentLaw
  map_zero' := by
    apply integral_eq_zero_of_ae
    filter_upwards [C.additive] with ω hω
    have h := hω 0 0 0
    change C.value ω 0 0 = 0
    linarith
  map_add' x y := by
    have he : (∫ ω, C.value ω 0 (x+y) ∂environmentLaw) =
        (∫ ω, C.value ω 0 x ∂environmentLaw) + (∫ ω, C.value ω x (x+y) ∂environmentLaw) := by
      rw [← integral_add (C.integrable 0 x) (C.integrable x (x+y))]
      apply integral_congr_ae
      filter_upwards [C.additive] with ω hω
      exact hω 0 x (x+y)
    have ht := C.mean_translation x 0 y
    simp only [add_zero] at ht
    exact he.trans (congrArg (_ + ·) ht)

lemma meanHom_direction : C.meanHom d = directionalMeanConstant d := C.directional_mean

lemma scaleVertex_eq_nsmul (n : ℕ) (x : Vertex) : scaleVertex n x = n • x := by
  ext <;> simp [scaleVertex]

lemma meanHom_scale (n : ℕ) (x : Vertex) : C.meanHom (scaleVertex n x) = (n : ℝ)*C.meanHom x := by
  rw [scaleVertex_eq_nsmul, map_nsmul, nsmul_eq_mul]

lemma meanHom_le_mean (x : Vertex) :
    C.meanHom x ≤ ∫ ω, passageTime ω 0 x ∂environmentLaw := by
  apply integral_mono_ae (C.integrable 0 x) (integrable_passageTime 0 x)
  filter_upwards [C.dominated] with ω hω
  exact (le_abs_self _).trans (hω 0 x)

theorem meanHom_le_directionalMeanConstant (x : Vertex) : C.meanHom x ≤ directionalMeanConstant x := by
  apply ge_of_tendsto (meanPassageSequence_tendsto x)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := C.meanHom_le_mean (scaleVertex n x)
  rw [C.meanHom_scale] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change (n : ℝ)*C.meanHom x ≤ meanPassageSequence x n at h
  exact (le_div_iff₀ hn').mpr (by simpa only [mul_comm (C.meanHom x)] using h)

lemma meanHom_coordinates (x : Vertex) :
    C.meanHom x = (x.1 : ℝ)*C.meanHom (1,0)+(x.2 : ℝ)*C.meanHom (0,1) := by
  have he : x = x.1 • ((1,0) : Vertex) + x.2 • ((0,1) : Vertex) := by ext <;> simp
  conv_lhs => rw [he, map_add, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul]

noncomputable def meanLinear : Plane →ₗ[ℝ] ℝ where
  toFun x := x.1*C.meanHom (1,0)+x.2*C.meanHom (0,1)
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' c x := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

lemma meanLinear_embed (x : Vertex) : C.meanLinear (embed x) = C.meanHom x :=
  (C.meanHom_coordinates x).symm

lemma mean_value (x y : Vertex) :
    (∫ ω, C.value ω x y ∂environmentLaw) = C.meanHom (y-x) := by
  change (∫ ω, C.value ω x y ∂environmentLaw) = ∫ ω, C.value ω 0 (y-x) ∂environmentLaw
  have h := C.mean_translation x 0 (y-x)
  simpa only [add_zero, add_sub_cancel] using h

theorem meanHom_eq_of_flat_neighborhood (h : Vertex →+ ℝ)
    (hd : directionalMeanConstant d = h d)
    (hflat : ∀ e ∈ ({(1,0),(0,1)} : Finset Vertex), ∃ n : ℕ,
      directionalMeanConstant (scaleVertex n d+e) = h (scaleVertex n d+e) ∧
      directionalMeanConstant (scaleVertex n d-e) = h (scaleVertex n d-e)) :
    C.meanHom = h := by
  have heq (e : Vertex) (he : e ∈ ({(1,0),(0,1)} : Finset Vertex)) : C.meanHom e = h e := by
    obtain ⟨n,hp,hm⟩ := hflat e he
    have hbase : C.meanHom (scaleVertex n d) = h (scaleVertex n d) := by
      rw [scaleVertex_eq_nsmul, map_nsmul, map_nsmul, C.meanHom_direction, hd]
    have h₁ := C.meanHom_le_directionalMeanConstant (scaleVertex n d+e)
    have h₂ := C.meanHom_le_directionalMeanConstant (scaleVertex n d-e)
    rw [hp, map_add, map_add, hbase] at h₁
    rw [hm, map_sub, map_sub, hbase] at h₂
    linarith
  ext x
  have hx : x = x.1 • ((1,0) : Vertex) + x.2 • ((0,1) : Vertex) := by ext <;> simp
  rw [hx, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul,
    heq (1,0) (by simp), heq (0,1) (by simp)]

end DirectionalCalibration

theorem exists_calibration_prescribed_mean (d : Vertex) (h : Vertex →+ ℝ)
    (hd : directionalMeanConstant d = h d)
    (hflat : ∀ e ∈ ({(1,0),(0,1)} : Finset Vertex), ∃ n : ℕ,
      directionalMeanConstant (scaleVertex n d+e) = h (scaleVertex n d+e) ∧
      directionalMeanConstant (scaleVertex n d-e) = h (scaleVertex n d-e)) :
    ∃ C : DirectionalCalibration d, ∀ x y,
      (∫ ω, C.value ω x y ∂environmentLaw) = h (y-x) := by
  obtain ⟨C⟩ := exists_directionalCalibration d
  refine ⟨C,fun x y => ?_⟩
  rw [C.mean_value, C.meanHom_eq_of_flat_neighborhood h hd hflat]

end CompanionFPP

end OAI
