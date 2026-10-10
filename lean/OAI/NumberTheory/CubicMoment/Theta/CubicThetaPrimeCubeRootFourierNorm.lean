import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootFourierProducts

namespace OAI

/-! The norm of the actual cubic-scale Fourier projection is the
Fourier transform of its translation correlations. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootResidueL2_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (u v : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    inner ℂ (cubicThetaPrimeCubeRootResidueL2 hp r u) v=
      inner ℂ u (cubicThetaPrimeCubeRootResidueL2 hp (-r) v) := by
  have he := (cubicThetaPrimeCubeRootResidueL2 hp r).inner_map_map u
    (cubicThetaPrimeCubeRootResidueL2 hp (-r) v)
  rw [←cubicThetaPrimeCubeRootResidueL2_add,add_neg_cancel,
    cubicThetaPrimeCubeRootResidueL2_zero] at he
  exact he

lemma cubicThetaPrimeCubeRootFourierL2_pair_projection {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (u v : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp k u)
      (cubicThetaPrimeCubeRootFourierL2 hp k v)=
    inner ℂ u (cubicThetaPrimeCubeRootFourierL2 hp k v) := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  let w := cubicThetaPrimeCubeRootFourierL2 hp k v
  have hterm (r : Residues (p^3)) :
      inner ℂ (star (ψ (k*r)) • cubicThetaPrimeCubeRootResidueL2 hp r u) w=
        inner ℂ u w := by
    rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),starRingEnd_apply,star_star,
      cubicThetaPrimeCubeRootResidueL2_adjoint]
    change ψ (k*r)*inner ℂ u (cubicThetaPrimeCubeRootResidueL2 hp (-r)
      (cubicThetaPrimeCubeRootFourierL2 hp k v))=inner ℂ u w
    rw [cubicThetaPrimeCubeRootFourierL2_eigen,
      inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),←mul_assoc]
    have hc : ψ (k*r)*ψ (k*(-r))=1 := by
      rw [←AddChar.map_add_eq_mul,←mul_add,add_neg_cancel,mul_zero,AddChar.map_zero_eq_one]
    rw [hc,one_mul]
  have hcard : (Fintype.card (Residues (p^3)):ℂ)=(norm (p^3):ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card (pow_ne_zero 3 hp.2.ne_zero)]
    simpa only [Complex.ofReal_natCast] using congrArg Complex.ofReal (normNat_cast (p^3))
  change inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp k u) w=inner ℂ u w
  rw [cubicThetaPrimeCubeRootFourierL2_apply,
    inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),sum_inner]
  change star ((norm (p^3):ℂ)⁻¹)*(∑ r : Residues (p^3),
    inner ℂ (star (ψ (k*r)) • cubicThetaPrimeCubeRootResidueL2 hp r u) w)=_
  have hs : star ((norm (p^3):ℂ)⁻¹)=(norm (p^3):ℂ)⁻¹ := by
    have hn : star (norm (p^3):ℂ)=(norm (p^3):ℂ) :=
      (congrArg (fun z : ℂ => star z) hcard).symm.trans ((star_natCast _).trans hcard)
    exact (star_inv₀ (norm (p^3):ℂ)).trans (congrArg (fun z : ℂ => z⁻¹) hn)
  rw [hs]
  simp only [hterm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
  rw [inv_mul_cancel_left₀
    (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (pow_ne_zero 3 hp.2.ne_zero)).ne')]

theorem cubicThetaPrimeCubeRootFourierL2_norm_correlation {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3))
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    (‖cubicThetaPrimeCubeRootFourierL2 hp k u‖^2:ℂ)=
      (norm (p^3):ℂ)⁻¹*∑ r : Residues (p^3),
        star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r))*
          inner ℂ u (cubicThetaPrimeCubeRootResidueL2 hp r u) := by
  calc
    _ = inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp k u)
        (cubicThetaPrimeCubeRootFourierL2 hp k u) :=
      (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) _).symm
    _ = inner ℂ u (cubicThetaPrimeCubeRootFourierL2 hp k u) :=
      cubicThetaPrimeCubeRootFourierL2_pair_projection hp k u u
    _ = _ := by
      rw [cubicThetaPrimeCubeRootFourierL2_apply,
        inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),inner_sum]
      simp only [inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp)]

end CubicFirstMoment

end

end OAI
