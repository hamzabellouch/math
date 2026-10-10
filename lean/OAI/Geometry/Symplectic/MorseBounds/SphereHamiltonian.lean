import OAI.Geometry.Symplectic.MorseBounds.SphereForm
import OAI.Geometry.Symplectic.MorseBounds.SphereSmooth

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.SphereHamiltonian
open MorseArnold.SphereCaps MorseArnold.SphereSymplectic MorseArnold.Geometry
open scoped Manifold ContDiff
noncomputable section
local instance sphereHamiltonianFinrank : Fact (Module.finrank ℝ R3 = 2 + 1) := ⟨by simp [R3]⟩

def ambientVelocity (l eps s : ℝ) (p : S2) : R3 :=
  vec3 (-angularSpeed l eps s ((p : R3) 2) * (p : R3) 1)
    (angularSpeed l eps s ((p : R3) 2) * (p : R3) 0) 0

lemma ambientVelocity_range (l eps s : ℝ) (p : S2) :
    ambientVelocity l eps s p ∈ (tangentInclusion p).range := by
  rw [tangentInclusion, range_mvfderiv_subtypeVal (n := 2)]
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  simp [inner_formula,ambientVelocity]
  ring

def velocity (l eps s : ℝ) (p : S2) : TangentSpace (𝓡 2) p :=
  (ambientVelocity_range l eps s p).choose

lemma tangent_velocity (l eps s : ℝ) (p : S2) :
    tangentInclusion p (velocity l eps s p) = ambientVelocity l eps s p :=
  (ambientVelocity_range l eps s p).choose_spec

lemma vec3_time_deriv {a b c : ℝ → ℝ} {a' b' c' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (hc : HasDerivAt c c' t) :
    HasDerivAt (fun r => vec3 (a r) (b r) (c r)) (vec3 a' b' c') t := by
  have hpi : HasDerivAt (fun r => ![a r,b r,c r]) ![a',b',c'] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt.comp_hasDerivAt t hpi

lemma rotateAmbient_deriv (a t : ℝ) (p : R3) :
    HasDerivAt (fun r => rotateAmbient (r*a) p)
      (vec3 (-a * (rotateAmbient (t*a) p) 1)
        (a * (rotateAmbient (t*a) p) 0) 0) t := by
  have ht : HasDerivAt (fun r : ℝ => r*a) a t := by
    simpa using (hasDerivAt_id t).mul_const a
  have hc := ht.cos
  have hs := ht.sin
  have h := vec3_time_deriv ((hc.mul_const (p 0)).sub (hs.mul_const (p 1)))
    ((hs.mul_const (p 0)).add (hc.mul_const (p 1))) (hasDerivAt_const t (p 2))
  convert h using 1 <;> simp [rotateAmbient]
  ring_nf

lemma sphereFlow_ambient_deriv (l eps s t : ℝ) (p : S2) :
    HasDerivAt (fun r => (sphereFlow l eps s r p : R3))
      (ambientVelocity l eps s (sphereFlow l eps s t p)) t := by
  exact rotateAmbient_deriv (angularSpeed l eps s ((p : R3) 2)) t p

lemma sphereFlow_ode (l eps s t : ℝ) (p : S2) :
    HasMFDerivAt 𝓘(ℝ) (𝓡 2) (fun r => sphereFlow l eps s r p) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (velocity l eps s (sphereFlow l eps s t p))) := by
  have hp := (sphereFlow_smooth l eps s).comp
    (contMDiff_id.prodMk (contMDiff_const (c := p)))
  have hd := (hp.mdifferentiable (by simp) t).hasMFDerivAt
  have he := (contMDiff_coe_sphere (E := R3) (n := 2) (m := (∞ : ℕ∞ω))).mdifferentiable
    (by simp) (sphereFlow l eps s t p)
  have hc := he.hasMFDerivAt.comp t hd
  have hconvert (Space : Type) [NormedAddCommGroup Space] [NormedSpace ℝ Space]
      (curve : ℝ → Space) (derivative : Space) (time : ℝ)
      (hderiv : HasDerivAt curve derivative time) :
      HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, Space) curve time
        ((ContinuousLinearMap.id ℝ ℝ).smulRight derivative) :=
    hderiv.hasFDerivAt.hasMFDerivAt
  have hf := hconvert R3 _ _ _ (sphereFlow_ambient_deriv l eps s t p)
  have heq := hc.mfderiv.symm.trans hf.mfderiv
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  apply injective_mvfderiv_subtypeVal_sphere (sphereFlow l eps s t p)
  have h := congrArg (fun L => L r) heq
  change tangentInclusion (sphereFlow l eps s t p)
    (mfderiv 𝓘(ℝ) (𝓡 2) (fun u => sphereFlow l eps s u p) t r) =
      r • ambientVelocity l eps s (sphereFlow l eps s t p) at h
  change tangentInclusion (sphereFlow l eps s t p)
    (mfderiv 𝓘(ℝ) (𝓡 2) (fun u => sphereFlow l eps s u p) t r) =
    tangentInclusion (sphereFlow l eps s t p) (r • velocity l eps s (sphereFlow l eps s t p))
  rw [map_smul,tangent_velocity]
  exact h

lemma hamiltonian_differential (l eps s : ℝ) (p : S2) (v : TangentSpace (𝓡 2) p) :
    mvfderiv (𝓡 2) (fun p : S2 => sphereHamiltonian l eps s ((p : R3) 2)) p v =
      deriv (sphereHamiltonian l eps s) ((p : R3) 2) * (tangentInclusion p v) 2 := by
  let h : R3 → ℝ := fun p => sphereHamiltonian l eps s (p 2)
  have hh := (sphereHamiltonian_deriv l eps s ((p : R3) 2)).hasFDerivAt.comp (p : R3)
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt
  have hc := hh.hasMFDerivAt.comp p
    ((contMDiff_coe_sphere (E := R3) (n := 2) (m := (∞ : ℕ∞ω))).mdifferentiable
      (by simp) p).hasMFDerivAt
  have hd := congrArg (fun L => L v) hc.mfderiv
  rw [(sphereHamiltonian_deriv l eps s ((p : R3) 2)).deriv]
  change mvfderiv (𝓡 2) (fun p : S2 => sphereHamiltonian l eps s ((p : R3) 2)) p v =
    (tangentInclusion p v) 2 * (l * angularSpeed l eps s ((p : R3) 2)) at hd
  exact hd.trans (mul_comm _ _)

theorem sphere_hamiltonian_flow (l eps s : ℝ) (hl : 0 < l) :
    ∃ (omega : SymplecticForm (n := 2) (M := S2))
      (V : (p : S2) → TangentSpace (𝓡 2) p),
      (∀ p u v, omega.form p u v = l * standardArea (p : R3)
        (tangentInclusion p u) (tangentInclusion p v)) ∧
      ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun p : S2 => sphereHamiltonian l eps s ((p : R3) 2)) ∧
      (∀ p, omega.form p (V p) =
        mvfderiv (𝓡 2) (fun p : S2 => sphereHamiltonian l eps s ((p : R3) 2)) p) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × S2 => sphereFlow l eps s q.1 q.2) ∧
      (∀ p, sphereFlow l eps s 0 p = p) ∧
      (∀ t u p, sphereFlow l eps s (t+u) p =
        sphereFlow l eps s t (sphereFlow l eps s u p)) ∧
      (∀ t p, HasMFDerivAt 𝓘(ℝ) (𝓡 2) (fun r => sphereFlow l eps s r p) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (V (sphereFlow l eps s t p)))) := by
  obtain ⟨w,hw⟩ := scaled_standardSphere_symplectic l hl
  refine ⟨w,velocity l eps s,hw,?_,?_,sphereFlow_smooth l eps s,
    (sphereFlow_laws l eps s).1,(sphereFlow_laws l eps s).2,sphereFlow_ode l eps s⟩
  · exact (sphereHamiltonian_smooth l eps s).contMDiff.comp height_smooth
  · intro p
    ext v
    rw [hw, ← tangentInclusion, tangent_velocity,hamiltonian_differential]
    apply sphere_hamiltonian_equation
    exact (inner_formula (p : R3) (tangentInclusion p v)) ▸ tangent_orthogonal p v

end
end MorseArnold.SphereHamiltonian

end

end OAI
