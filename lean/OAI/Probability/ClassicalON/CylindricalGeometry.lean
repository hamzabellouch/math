import OAI.Probability.ClassicalON.AmplitudeLaw

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ClassicalON

theorem planarCos_sq_add_sin_sq (θ : PlanarAngle) : planarCos θ^2+planarSin θ^2=1 := by
  have h := Circle.normSq_coe (AddCircle.toCircle θ)
  simpa [Complex.normSq_apply,planarCos,planarSin,planarCharacter,pow_two] using h

theorem planarCos_add (θ φ : PlanarAngle) :
    planarCos (θ+φ)=planarCos θ*planarCos φ-planarSin θ*planarSin φ := by
  simp [planarCos,planarSin,planarCharacter_add,Complex.mul_re]

theorem planarSin_add (θ φ : PlanarAngle) :
    planarSin (θ+φ)=planarSin θ*planarCos φ+planarCos θ*planarSin φ := by
  simp [planarCos,planarSin,planarCharacter_add,Complex.mul_im,add_comm]

theorem signValue_sq (τ : Bool) : signValue τ^2=1 := by cases τ <;> norm_num [signValue]

theorem transverseAmplitude_sq (r : Amplitude) : transverseAmplitude r^2=1-(r:ℝ)^2 := by
  apply Real.sq_sqrt
  have h0:=r.property.1
  have h1:=r.property.2
  nlinarith

theorem normSq_three (v : EuclideanSpace ℝ (Fin 3)) : ‖v‖^2=v 0^2+v 1^2+v 2^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ,add_assoc]

def cylindricalSpin (r : Amplitude) (τ : Bool) (θ : PlanarAngle) : Spin 3 :=
  ⟨WithLp.toLp 2 ![(r:ℝ)*signValue τ,transverseAmplitude r*planarCos θ,
    transverseAmplitude r*planarSin θ],by
    rw [mem_sphere_zero_iff_norm]
    have h := planarCos_sq_add_sin_sq θ
    have hq := transverseAmplitude_sq r
    have ht := signValue_sq τ
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [normSq_three]
    change ((r:ℝ)*signValue τ)^2+(transverseAmplitude r*planarCos θ)^2+
      (transverseAmplitude r*planarSin θ)^2=1^2
    calc
      _ = (r:ℝ)^2*signValue τ^2+transverseAmplitude r^2*(planarCos θ^2+planarSin θ^2) := by ring
      _ = 1^2 := by rw [ht,h,hq]; ring⟩

theorem continuous_cylindricalSpin :
    Continuous (fun p : Amplitude×Bool×PlanarAngle => cylindricalSpin p.1 p.2.1 p.2.2) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Amplitude×Bool×PlanarAngle => (p.1:ℝ)*signValue p.2.1)
    exact continuous_fst.subtype_val.mul ((show Continuous signValue from continuous_of_discreteTopology).comp (continuous_fst.comp continuous_snd))
  · exact (continuous_transverseAmplitude.comp continuous_fst).mul
      (continuous_planarCos.comp (continuous_snd.comp continuous_snd))
  · exact (continuous_transverseAmplitude.comp continuous_fst).mul
      (continuous_planarSin.comp (continuous_snd.comp continuous_snd))

def cylinderLinear (τ : Bool) (θ : PlanarAngle) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun v := WithLp.toLp 2 ![signValue τ*v 0,
    planarCos θ*v 1-planarSin θ*v 2,planarSin θ*v 1+planarCos θ*v 2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a v := by ext i; fin_cases i <;> simp <;> ring

theorem cylinderLinear_norm (τ : Bool) (θ : PlanarAngle) (v : EuclideanSpace ℝ (Fin 3)) :
    ‖cylinderLinear τ θ v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normSq_three,normSq_three]
  have h := planarCos_sq_add_sin_sq θ
  have ht := signValue_sq τ
  change (signValue τ*v 0)^2+(planarCos θ*v 1-planarSin θ*v 2)^2+
    (planarSin θ*v 1+planarCos θ*v 2)^2=_
  nlinarith [congrArg (fun a : ℝ => a*(v 1^2+v 2^2)) h,
    congrArg (fun a : ℝ => a*v 0^2) ht]

def cylinderRotation (τ : Bool) (θ : PlanarAngle) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearIsometryEquiv.ofSurjective
    {cylinderLinear τ θ with norm_map' := cylinderLinear_norm τ θ}
    (LinearMap.surjective_of_injective
      (show Function.Injective (cylinderLinear τ θ) from
        (show EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) from
          {cylinderLinear τ θ with norm_map' := cylinderLinear_norm τ θ}).injective))

@[simp] theorem cylinderRotation_apply (τ : Bool) (θ : PlanarAngle) (v : EuclideanSpace ℝ (Fin 3)) :
    cylinderRotation τ θ v=cylinderLinear τ θ v := rfl

end ClassicalON

end

end OAI
