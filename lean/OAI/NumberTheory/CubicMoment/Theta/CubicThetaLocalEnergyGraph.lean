import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalEnergyJet

namespace OAI

/-! The local graph of genuine compact smooth sections and its closed
Hilbert energy space. The value and derivative entries remain tied to the
same localized section throughout the construction. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

abbrev CubicThetaLocalEnergyAmbient := Lp CubicThetaLocalJet 2 (volume : Measure (ℂ × ℝ))

lemma cubicThetaLocalEnergyJet_add {f g : ℂ × ℝ → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (y : ℂ × ℝ) :
    cubicThetaLocalEnergyJet (f+g) y=cubicThetaLocalEnergyJet f y+cubicThetaLocalEnergyJet g y := by
  ext i
  fin_cases i <;>
    simp [cubicThetaLocalEnergyJet,fderiv_add (hf y) (hg y),smul_add]

lemma cubicThetaLocalEnergyJet_smul (c : ℂ) {f : ℂ × ℝ → ℂ}
    (hf : Differentiable ℝ f) (y : ℂ × ℝ) :
    cubicThetaLocalEnergyJet (c • f) y=c • cubicThetaLocalEnergyJet f y := by
  ext i
  fin_cases i <;>
    simp [cubicThetaLocalEnergyJet,fderiv_const_smul (hf y) c] <;> ring

lemma cubicThetaTestLocalization_add (φ : ℂ × ℝ → ℂ) (F G : cubicThetaSmoothTests) :
    cubicThetaTestLocalization φ ((F+G : cubicThetaSmoothTests) : CubicThetaSection)=cubicThetaTestLocalization φ F+cubicThetaTestLocalization φ G := by
  funext y
  change φ y*(F.val.val _+G.val.val _)=φ y*F.val.val _+φ y*G.val.val _
  exact mul_add _ _ _

lemma cubicThetaTestLocalization_smul (φ : ℂ × ℝ → ℂ) (c : ℂ) (F : cubicThetaSmoothTests) :
    cubicThetaTestLocalization φ ((c • F : cubicThetaSmoothTests) : CubicThetaSection)=c • cubicThetaTestLocalization φ F := by
  funext y
  change φ y*(c*F.val.val _)=c*(φ y*F.val.val _)
  ring

lemma cubicThetaLocalSectionJet_memLp {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F)) 2
      (volume : Measure (ℂ × ℝ)) :=
  cubicThetaLocalEnergyJet_memLp ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
    (cubicThetaTestLocalization_compact hc F) (tsupport_mul_subset_left.trans hp)

def cubicThetaLocalEnergyGraph {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaSmoothTests →ₗ[ℂ] CubicThetaLocalEnergyAmbient where
  toFun F := (cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(cubicThetaLocalSectionJet_memLp hφ hc hp (F+G)).coeFn_toLp,
      (cubicThetaLocalSectionJet_memLp hφ hc hp F).coeFn_toLp,
      (cubicThetaLocalSectionJet_memLp hφ hc hp G).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _)
        ((cubicThetaLocalSectionJet_memLp hφ hc hp G).toLp _)] with y hFG hF hG hadd
    simp only [Pi.add_apply] at hadd
    rw [hFG,hadd,hF,hG,cubicThetaTestLocalization_add]
    exact cubicThetaLocalEnergyJet_add
      ((cubicThetaTestLocalization_smooth hφ hp F).differentiable (by simp))
      ((cubicThetaTestLocalization_smooth hφ hp G).differentiable (by simp)) y
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(cubicThetaLocalSectionJet_memLp hφ hc hp (c • F)).coeFn_toLp,
      (cubicThetaLocalSectionJet_memLp hφ hc hp F).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _)] with y hCF hF hsmul
    simp only [Pi.smul_apply] at hsmul
    simp only [RingHom.id_apply]
    rw [hCF,hsmul,hF,cubicThetaTestLocalization_smul]
    exact cubicThetaLocalEnergyJet_smul c
      ((cubicThetaTestLocalization_smooth hφ hp F).differentiable (by simp)) y

def cubicThetaLocalEnergySpace {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) :
    Submodule ℂ CubicThetaLocalEnergyAmbient :=
  (cubicThetaLocalEnergyGraph hφ hc hp).range.topologicalClosure

instance cubicThetaLocalEnergySpace_complete {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) :
    CompleteSpace (cubicThetaLocalEnergySpace hφ hc hp) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

end CubicFirstMoment

end

end OAI
