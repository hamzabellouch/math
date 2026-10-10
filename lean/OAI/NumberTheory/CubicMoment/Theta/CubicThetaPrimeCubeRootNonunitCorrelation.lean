import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootSecondIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootTracePairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootL2Algebra

namespace OAI

/-! Both intermediate valuation classes vanish in the actual completed
cube-root correlation, by the proved integral identities and density. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_translate_zero_of_integral {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein)
    (h : ∀ F G : cubicThetaSmoothTests,
      (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
        G.val.val (cubicThetaPrimeCubeRootElement hp x • z) ∂cubicThetaPointMeasure)=0)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootLiftL2 hp v))=0 := by
  apply cubicThetaGlobalMassClosure_dense.induction_on₂
    (p:=fun u v => inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootLiftL2 hp v))=0) ?_ ?_ u v
  · apply isClosed_eq _ continuous_const
    exact ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp continuous_fst).inner
      ((cubicThetaPrimeCubeRootTranslateL2 hp x).continuous.comp
        ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp continuous_snd))
  · intro F G
    simp only [cubicThetaPrimeCubeRootLiftL2_smooth,cubicThetaPrimeCubeRootNormalizedRestriction,
      LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeCubeRootTranslateL2_finite]
    rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),
      inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),
      cubicThetaPrimeCubeRootFinite_pairing]
    change _*(_*(∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
      G.val.val (cubicThetaPrimeCubeRootElement hp x • z) ∂cubicThetaPointMeasure))=0
    rw [h F G,mul_zero,mul_zero]

theorem cubicThetaPrimeCubeRoot_single_correlation_zero {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein) (hx : ¬p∣x) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp (p*x) (cubicThetaPrimeCubeRootLiftL2 hp v))=0 :=
  cubicThetaPrimeCubeRoot_translate_zero_of_integral hp (p*x)
    (fun F G => cubicThetaPrimeCubeRoot_single_integral_zero hp x hx F.val G.val) u v

theorem cubicThetaPrimeCubeRoot_square_correlation_zero {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein) (hx : ¬p∣x) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp (p^2*x) (cubicThetaPrimeCubeRootLiftL2 hp v))=0 :=
  cubicThetaPrimeCubeRoot_translate_zero_of_integral hp (p^2*x)
    (fun F G => cubicThetaPrimeCubeRoot_square_integral_zero hp x hx F G) u v

theorem cubicThetaPrimeCubeRoot_nonunit_correlation_zero {p : Eisenstein}
    (hp : primaryPrime p) (r : Residues (p^3)) (hr : ¬IsUnit r) (hr0 : r≠0)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootLiftL2 hp v))=0 := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective r
  have hx : p∣x := by
    by_contra h
    exact hr (residue_isUnit_of_isCoprime (hp.2.coprime_iff_not_dvd.mpr h).pow_left)
  obtain ⟨a,rfl⟩ := hx
  rw [cubicThetaPrimeCubeRootResidueL2_mk]
  by_cases ha : p∣a
  · obtain ⟨b,rfl⟩ := ha
    have hb : ¬p∣b := by
      rintro ⟨c,rfl⟩
      apply hr0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply Ideal.mem_span_singleton.mpr
      exact ⟨c,by ring⟩
    simpa only [←mul_assoc,←pow_two] using cubicThetaPrimeCubeRoot_square_correlation_zero hp b hb u v
  · exact cubicThetaPrimeCubeRoot_single_correlation_zero hp a ha u v

end CubicFirstMoment

end

end OAI
