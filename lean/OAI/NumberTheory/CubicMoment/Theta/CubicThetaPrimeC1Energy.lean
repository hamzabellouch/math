import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergyInvariant

namespace OAI

/-! C1 sections and their continuous intrinsic energy on the prime
cover. Both the value and energy transform under the same Atkin map. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeC1Sections {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (cubicThetaPrimeSections hp) where
  carrier := {F | ContDiffOn ℝ 1 (cubicThetaPrimeSectionFunction hp F) {y : ℂ × ℝ | 0<y.2}}
  zero_mem' := contDiffOn_const
  add_mem' := by
    intro F G hF hG
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    exact hF.const_smul c

def cubicThetaPrimeC1Atkin {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeC1Sections hp →ₗ[ℂ] cubicThetaPrimeC1Sections hp where
  toFun F := ⟨cubicThetaPrimeAtkinSection hp F.val,cubicThetaPrimeAtkinSection_c1 hp F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

def cubicThetaPrimeQuotientEnergy {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) : CubicThetaPrimeCover hp → ℝ :=
  Quotient.lift (cubicThetaPrimeSectionEnergy hp F.val) (by
    intro x y hxy
    obtain ⟨g,hg⟩ := hxy
    dsimp only at hg
    rw [←hg,cubicThetaPrimeSectionEnergy_invariant hp F.val F.property])

@[simp] lemma cubicThetaPrimeQuotientEnergy_apply {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (x : CubicThetaPoint) :
    cubicThetaPrimeQuotientEnergy hp F (cubicThetaPrimeCoverMap hp x)=
      cubicThetaPrimeSectionEnergy hp F.val x := rfl

lemma cubicThetaPrimeQuotientEnergy_nonneg {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (q : CubicThetaPrimeCover hp) :
    0≤cubicThetaPrimeQuotientEnergy hp F q := by
  induction q using Quotient.inductionOn with
  | h x =>
    exact mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)

lemma cubicThetaPrimeQuotientEnergy_continuous {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) : Continuous (cubicThetaPrimeQuotientEnergy hp F) := by
  apply (cubicThetaPrimeCoverMap_open hp).isQuotientMap.continuous_iff.mpr
  exact cubicThetaPrimeSectionEnergy_continuous hp F.val F.property

lemma cubicThetaPrimeC1Atkin_energy {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) (q : CubicThetaPrimeCover hp) :
    cubicThetaPrimeQuotientEnergy hp (cubicThetaPrimeC1Atkin hp F) q=
      cubicThetaPrimeQuotientEnergy hp F (cubicThetaPrimeCoverAtkinMap hp q) := by
  induction q using Quotient.inductionOn with
  | h x => exact cubicThetaPrimeAtkinSection_energy hp F.val F.property x

theorem cubicThetaPrimeC1Atkin_energy_integral {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) :
    (∫ q, cubicThetaPrimeQuotientEnergy hp (cubicThetaPrimeC1Atkin hp F) q
      ∂cubicThetaPrimeCoverMeasure hp)=
      ∫ q, cubicThetaPrimeQuotientEnergy hp F q ∂cubicThetaPrimeCoverMeasure hp := by
  simp_rw [cubicThetaPrimeC1Atkin_energy]
  exact (cubicThetaPrimeCoverAtkin_measurePreserving hp).integral_comp
    (cubicThetaPrimeCoverAtkinHomeomorph hp).measurableEmbedding
    (cubicThetaPrimeQuotientEnergy hp F)

end CubicFirstMoment

end

end OAI
