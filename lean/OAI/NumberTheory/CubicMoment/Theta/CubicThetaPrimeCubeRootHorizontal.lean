import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootHorizontal

namespace OAI

/-! Actual finite cubic-root projections select the corresponding
horizontal Fourier frequencies. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootHorizontal_translate {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) (x : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeRootHorizontal (cubicThetaPrimeCubeRootSectionTranslate hp x F) v hv z=
      cubicThetaPrimeRootHorizontal F v hv (z+3*(x:ℂ)/((p^3:Eisenstein):ℂ)) := by
  change F.val (cubicThetaPrimeCubeRootElement hp x • cubicThetaHorizontalPoint v hv z)=
    F.val (cubicThetaHorizontalPoint v hv (z+3*(x:ℂ)/((p^3:Eisenstein):ℂ)))
  congr 1
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeCubeRootElement hp x) (z,v)=_
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaMobius_translation]
  push_cast
  rfl

lemma cubicThetaPrimeCubeRootFiniteFourier_value {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3))
    (F : cubicThetaPrimeCubeRootFiniteSections hp) (y : CubicThetaPoint) :
    (cubicThetaPrimeCubeRootFiniteFourier hp k F).val.val y=
      (norm (p^3):ℂ)⁻¹*∑ r : Residues (p^3),
        star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r))*
          (cubicThetaPrimeCubeRootSectionTranslate hp (residueRepresentative (p^3) r) F.val).val y := by
  let ev : cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] ℂ :=
    { toFun := fun G => G.val.val y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  change ev (cubicThetaPrimeCubeRootFiniteFourier hp k F)=_
  rw [cubicThetaPrimeCubeRootFiniteFourier_apply,map_smul,map_sum]
  rfl

lemma cubicThetaPrimeCubeRootFiniteFourier_horizontal_function {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3)) (F : cubicThetaPrimeCubeRootFiniteSections hp)
    (v : ℝ) (hv : 0<v) :
    (cubicThetaPrimeRootHorizontal (cubicThetaPrimeCubeRootFiniteFourier hp k F).val v hv : ℂ → ℂ)=
      fun z => (norm (p^3):ℂ)⁻¹*∑ r : Residues (p^3),
        star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r))*
          cubicThetaPrimeRootHorizontal F.val v hv
            (z+3*(residueRepresentative (p^3) r:ℂ)/((p^3:Eisenstein):ℂ)) := by
  classical
  funext z
  change (cubicThetaPrimeCubeRootFiniteFourier hp k F).val.val (cubicThetaHorizontalPoint v hv z)=_
  rw [cubicThetaPrimeCubeRootFiniteFourier_value]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [show (cubicThetaPrimeCubeRootSectionTranslate hp (residueRepresentative (p^3) r) F.val).val
      (cubicThetaHorizontalPoint v hv z)=_ from
    cubicThetaPrimeCubeRootHorizontal_translate hp F.val (residueRepresentative (p^3) r) v hv z]

lemma cubicThetaCubeResidueFourier_sum {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k j : Residues (p^3)) (c : ℂ) :
    (∑ r : Residues (p^3),star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r))*
      (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (r*j)*c))=
      (if j=k then (norm (p^3):ℂ) else 0)*c := by
  classical
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  have he (r : Residues (p^3)) : star (ψ (k*r))*(ψ (r*j)*c)=
      (ψ (r*j)*star (ψ (r*k)))*c := by
    rw [mul_comm r k]
    ac_rfl
  change (∑ r : Residues (p^3),star (ψ (k*r))*(ψ (r*j)*c))=_
  simp_rw [he]
  rw [←Finset.sum_mul,cubicThetaResidueFourier_orthogonal (p^3) (pow_ne_zero 3 hp.2.ne_zero) j k]
  have hcard : (Fintype.card (Residues (p^3)):ℂ)=(norm (p^3):ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card (pow_ne_zero 3 hp.2.ne_zero)]
    exact congrArg (fun x : ℝ => (x:ℂ)) (normNat_cast (p^3))
  rw [hcard]

theorem cubicThetaPrimeCubeRootFiniteFourier_horizontal {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (F : cubicThetaPrimeCubeRootFiniteSections hp)
    (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient h
      (cubicThetaPrimeRootHorizontal (cubicThetaPrimeCubeRootFiniteFourier hp k F).val v hv)=
      if Ideal.Quotient.mk (modulus (p^3)) h=k then
        cubicThetaHorizontalFourierCoefficient h (cubicThetaPrimeRootHorizontal F.val v hv)
      else 0 := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  let f := cubicThetaPrimeRootHorizontal F.val v hv
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  let c := cubicThetaHorizontalFourierCoefficient h f
  have hphase (r : Residues (p^3)) :
      cubicThetaHorizontalCharacter h (3*(residueRepresentative (p^3) r:ℂ)/((p^3:Eisenstein):ℂ))=
        ψ (r*Ideal.Quotient.mk (modulus (p^3)) h) := by
    rw [cubicThetaHorizontalCharacter_fraction h (p^3) _ (pow_ne_zero 3 hp.2.ne_zero),
      map_mul,residueRepresentative_spec,mul_comm]
  have hterm (r : Residues (p^3)) :
      cubicThetaHorizontalFourierCoefficient h (fun z => star (ψ (k*r))*
        f (z+3*(residueRepresentative (p^3) r:ℂ)/((p^3:Eisenstein):ℂ)))=
        star (ψ (k*r))*(ψ (r*Ideal.Quotient.mk (modulus (p^3)) h)*c) := by
    rw [cubicThetaHorizontalFourier_const_mul]
    rw [cubicThetaHorizontalFourier_translate h f (cubicThetaPrimeRootHorizontal_periodic F.val v hv)]
    rw [hphase]
  rw [cubicThetaPrimeCubeRootFiniteFourier_horizontal_function,cubicThetaHorizontalFourier_const_mul]
  change (norm (p^3):ℂ)⁻¹*cubicThetaHorizontalFourierCoefficient h
    (fun z => ∑ r : Residues (p^3),star (ψ (k*r))*
      f (z+3*(residueRepresentative (p^3) r:ℂ)/((p^3:Eisenstein):ℂ)))=_
  rw [cubicThetaHorizontalFourier_sum Finset.univ h _ (by
    intro r _
    exact continuous_const.mul (f.continuous.comp (continuous_id.add continuous_const)))]
  simp only [hterm]
  change (norm (p^3):ℂ)⁻¹*(∑ r : Residues (p^3),star (ψ (k*r))*
    (ψ (r*Ideal.Quotient.mk (modulus (p^3)) h)*c))=_
  rw [cubicThetaCubeResidueFourier_sum hp]
  split_ifs <;> simp [Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (pow_ne_zero 3 hp.2.ne_zero)).ne',c,f]

end CubicFirstMoment

end

end OAI
