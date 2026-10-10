import OAI.Analysis.HenonEmden.Model

namespace OAI

universe uE

section LineCoordinates

open MeasureTheory Set Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden.LineCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def transverse (e : sphere (0:E) 1) : Submodule ℝ E := (ℝ ∙ (e : E))ᗮ
omit [InnerProductSpace ℝ E] in
lemma norm_unit (e : sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using e.2
lemma inner_transverse (e : sphere (0:E) 1) (z : transverse e) : inner ℝ (e:E) (z:E) = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2

def join (e : sphere (0:E) 1) : WithLp 2 (transverse e × ℝ) →ₗᵢ[ℝ] E where
  toFun z := z.fst.1 + z.snd • (e:E)
  map_add' z z' := by simp only [WithLp.add_fst,WithLp.add_snd,Submodule.coe_add,add_smul]; abel
  map_smul' r z := by
    simp only [WithLp.smul_fst,WithLp.smul_snd,Submodule.coe_smul_of_tower,smul_eq_mul,
      smul_add,smul_smul,RingHom.id_apply]
  norm_map' z := by
    change ‖(z.fst:E)+z.snd • (e:E)‖ = ‖z‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_add_sq_real,real_inner_comm,inner_smul_left,inner_transverse,mul_zero,mul_zero,add_zero,
      norm_smul,norm_unit,mul_one,Real.norm_eq_abs,sq_abs,WithLp.prod_norm_sq_eq_of_L2,
      Real.norm_eq_abs,sq_abs]
    rfl

lemma join_surjective (e : sphere (0:E) 1) : Function.Surjective (join e) := by
  intro x
  let t := inner ℝ (e:E) x
  have hz : x-t • (e:E) ∈ transverse e := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    simp only [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,norm_unit,one_pow,mul_one,t,sub_self]
  refine ⟨WithLp.toLp 2 (⟨x-t • (e:E),hz⟩,t),?_⟩
  change (x-t • (e:E))+t • (e:E) = x
  abel

def isometry (e : sphere (0:E) 1) : WithLp 2 (transverse e × ℝ) ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective (join e) (join_surjective e)

@[simp] lemma isometry_apply (e : sphere (0:E) 1) (z : WithLp 2 (transverse e × ℝ)) :
    isometry e z = (z.fst:E)+z.snd • (e:E) := rfl

lemma norm_join_sq (e : sphere (0:E) 1) (z : transverse e) (s : ℝ) :
    ‖(z:E)+s • (e:E)‖^2 = ‖z‖^2+s^2 := by
  simpa only [isometry_apply,WithLp.toLp_fst,WithLp.toLp_snd,Real.norm_eq_abs,sq_abs] using
    congrArg (fun t : ℝ => t^2) ((isometry e).norm_map (WithLp.toLp 2 (z,s))) |>.trans
      (WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (z,s)))

variable [MeasurableSpace E] [BorelSpace E]

def measurableEquiv (e : sphere (0:E) 1) : (transverse e × ℝ) ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 _).trans (isometry e).toMeasurableEquiv

@[simp] lemma measurableEquiv_apply (e : sphere (0:E) 1) (z : transverse e × ℝ) :
    measurableEquiv e z = (z.1:E)+z.2 • (e:E) := rfl

lemma measurePreserving [FiniteDimensional ℝ E] (e : sphere (0:E) 1) :
    MeasurePreserving (measurableEquiv e) (volume.prod volume) volume := by
  exact (isometry e).measurePreserving.comp (WithLp.volume_preserving_toLp (transverse e) ℝ)

lemma continuous_measurableEquiv (e : sphere (0:E) 1) : Continuous (measurableEquiv e) := by
  change Continuous (fun z : transverse e × ℝ => (z.1:E)+z.2 • (e:E))
  fun_prop

lemma distance_sq (e : sphere (0:E) 1) (z z' : transverse e × ℝ) :
    dist (measurableEquiv e z) (measurableEquiv e z')^2 = ‖z.1-z'.1‖^2+(z.2-z'.2)^2 := by
  rw [dist_eq_norm]
  have he : measurableEquiv e z-measurableEquiv e z' = ((z.1-z'.1 : transverse e):E)+(z.2-z'.2) • (e:E) := by
    simp only [measurableEquiv_apply,Submodule.coe_sub,sub_smul]; abel
  rw [he,norm_join_sq]

lemma parallel (e : sphere (0:E) 1) (z : transverse e × ℝ) (s : ℝ) :
    measurableEquiv e (z.1,z.2+s) = measurableEquiv e z+s • (e:E) := by
  simp only [measurableEquiv_apply,add_smul]; abel

omit [MeasurableSpace E] [BorelSpace E] in
lemma transverse_nontrivial [FiniteDimensional ℝ E] (h : 2 ≤ Module.finrank ℝ E)
    (e : sphere (0:E) 1) : Nontrivial (transverse e) := by
  apply (Module.finrank_pos_iff (R := ℝ)).mp
  have he : (e:E) ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_unit]; norm_num)
  have hh := (ℝ ∙ (e:E)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton he] at hh
  change 0 < Module.finrank ℝ ((ℝ ∙ (e:E))ᗮ)
  omega

end HenonLaneEmden.LineCoordinates
end
end LineCoordinates

end OAI
