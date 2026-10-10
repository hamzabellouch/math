import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeGradient

namespace OAI

/-! Actual C1 sections of finite mass and gradient energy on the prime
cover, with both coordinates retained as genuine L2 vectors. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeFiniteEnergy {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (cubicThetaPrimeC1Sections hp) where
  carrier := {F | MemLp (cubicThetaPrimeSectionRepresentative hp F.val) 2 (cubicThetaPrimeCoverMeasure hp) ∧
    MemLp (cubicThetaPrimeGradientRepresentative hp F) 2 (cubicThetaPrimeCoverMeasure hp)}
  zero_mem' := by
    refine ⟨MemLp.zero,?_⟩
    have hz : cubicThetaPrimeSectionFunction hp (0 : cubicThetaPrimeSections hp)=0 := rfl
    have he : cubicThetaPrimeGradientRepresentative hp 0=0 := by
      funext q
      ext i
      simp [cubicThetaPrimeGradientRepresentative,cubicThetaPrimeSectionGradient,
        cubicThetaPrimeSectionDifferential,hz]
    rw [he]
    exact MemLp.zero
  add_mem' := by
    intro F G hF hG
    refine ⟨hF.1.add hG.1,?_⟩
    have he : cubicThetaPrimeGradientRepresentative hp (F+G)=
        cubicThetaPrimeGradientRepresentative hp F+cubicThetaPrimeGradientRepresentative hp G :=
      funext (fun _ => cubicThetaPrimeSectionGradient_add hp F G _)
    rw [he]
    exact hF.2.add hG.2
  smul_mem' := by
    intro c F hF
    refine ⟨hF.1.const_smul c,?_⟩
    have he : cubicThetaPrimeGradientRepresentative hp (c • F)=
        c • cubicThetaPrimeGradientRepresentative hp F :=
      funext (fun _ => cubicThetaPrimeSectionGradient_smul hp c F _)
    rw [he]
    exact hF.2.const_smul c

def cubicThetaPrimeEnergyValue {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteEnergy hp →ₗ[ℂ] CubicThetaPrimeL2 hp where
  toFun F := F.property.1.toLp _
  map_add' F G := MemLp.toLp_add F.property.1 G.property.1
  map_smul' c F := MemLp.toLp_const_smul c F.property.1

def cubicThetaPrimeEnergyGradient {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteEnergy hp →ₗ[ℂ] CubicThetaPrimeGradientL2 hp where
  toFun F := F.property.2.toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(F+G).property.2.coeFn_toLp,F.property.2.coeFn_toLp,
      G.property.2.coeFn_toLp,Lp.coeFn_add (F.property.2.toLp _) (G.property.2.toLp _)]
      with q hFG hF hG ha
    simp only [Pi.add_apply] at ha
    rw [hFG,ha,hF,hG]
    exact cubicThetaPrimeSectionGradient_add hp F.val G.val _
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(c • F).property.2.coeFn_toLp,F.property.2.coeFn_toLp,
      Lp.coeFn_smul c (F.property.2.toLp _)] with q hCF hF ha
    simp only [Pi.smul_apply,RingHom.id_apply] at ha ⊢
    rw [hCF,ha,hF]
    exact cubicThetaPrimeSectionGradient_smul hp c F.val _

def cubicThetaPrimeEnergyAtkin {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteEnergy hp →ₗ[ℂ] cubicThetaPrimeFiniteEnergy hp where
  toFun F := ⟨cubicThetaPrimeC1Atkin hp F.val,
    cubicThetaPrimeAtkinSection_memLp hp F.val.val F.property.1,
    cubicThetaPrimeAtkinGradient_memLp hp F.val F.property.2⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeEnergyValue_atkin_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaPrimeEnergyValue hp (cubicThetaPrimeEnergyAtkin hp F)‖=
      ‖cubicThetaPrimeEnergyValue hp F‖ :=
  cubicThetaPrimeAtkinSection_L2_norm hp F.val.val F.property.1

lemma cubicThetaPrimeEnergyGradient_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaPrimeEnergyGradient hp F‖^2=
      ∫ q, cubicThetaPrimeQuotientEnergy hp F.val q ∂cubicThetaPrimeCoverMeasure hp := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [F.property.2.coeFn_toLp] with q hq
  change ‖(F.property.2.toLp _) q‖^2=_
  rw [hq,cubicThetaPrimeGradientRepresentative_norm_sq]

lemma cubicThetaPrimeEnergyGradient_atkin_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaPrimeEnergyGradient hp (cubicThetaPrimeEnergyAtkin hp F)‖=
      ‖cubicThetaPrimeEnergyGradient hp F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPrimeEnergyGradient_norm_sq,cubicThetaPrimeEnergyGradient_norm_sq]
  exact cubicThetaPrimeC1Atkin_energy_integral hp F.val

end CubicFirstMoment

end

end OAI
