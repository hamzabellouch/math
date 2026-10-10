import OAI.Analysis.LipschitzHilbert.Estimates.WeightedTranslatedProfiles
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarProfileBounds

namespace OAI

/-! The actual profile constant used by the packet estimates is controlled
uniformly for the polynomially weighted translated profiles. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

abbrev PlanarSchwartz := SchwartzMap (ℝ×ℝ) ℂ

def profileVerticalCLM : PlanarSchwartz →L[ℝ] PlanarSchwartz :=
  ((SchwartzMap.evalCLM ℂ (ℝ×ℝ) ℂ (0,1)).comp
    (SchwartzMap.fderivCLM ℂ (ℝ×ℝ) ℂ)).restrictScalars ℝ

def profileHorizontalCLM : PlanarSchwartz →L[ℝ] PlanarSchwartz :=
  ((SchwartzMap.evalCLM ℂ (ℝ×ℝ) ℂ (1,0)).comp
    (SchwartzMap.fderivCLM ℂ (ℝ×ℝ) ℂ)).restrictScalars ℝ

def profileJetCLM (i : Fin 3) : PlanarSchwartz →L[ℝ] PlanarSchwartz :=
  if i=0 then ContinuousLinearMap.id ℝ _ else if i=1 then profileVerticalCLM
    else profileVerticalCLM.comp profileVerticalCLM

theorem profileJetCLM_apply (i : Fin 3) (F : PlanarSchwartz) :
    profileJetCLM i F=planarVerticalJet F i := by
  fin_cases i <;> rfl

def envelopeSeminorm (n : ℕ) : Seminorm ℝ PlanarSchwartz :=
  (SchwartzMap.seminorm ℝ 0 0).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun z : ℝ×ℝ => (planarPolynomialWeight n z:ℂ))).restrictScalars ℝ).toLinearMap

theorem envelopeSeminorm_continuous (n : ℕ) : Continuous (envelopeSeminorm n) :=
  ((schwartz_withSeminorms ℝ (ℝ×ℝ) ℂ).continuous_seminorm (0,0)).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun z : ℝ×ℝ => (planarPolynomialWeight n z:ℂ))).continuous)

theorem envelopeSeminorm_apply (n : ℕ) (F : PlanarSchwartz) :
    envelopeSeminorm n F+1=planarEnvelopeConstant F n := rfl

def profileControlSeminorm (n : ℕ) : Seminorm ℝ PlanarSchwartz :=
  ∑ i : Fin 3, (
    (envelopeSeminorm n).comp (profileJetCLM i).toLinearMap+
    (envelopeSeminorm n).comp (profileHorizontalCLM.comp (profileJetCLM i)).toLinearMap+
    (envelopeSeminorm n).comp (profileVerticalCLM.comp (profileJetCLM i)).toLinearMap)

theorem profileControlSeminorm_continuous (n : ℕ) : Continuous (profileControlSeminorm n) := by
  unfold profileControlSeminorm
  apply Seminorm.continuous_finsetSum
  intro i _
  exact (((envelopeSeminorm_continuous n).comp (profileJetCLM i).continuous).add
    ((envelopeSeminorm_continuous n).comp
      (profileHorizontalCLM.comp (profileJetCLM i)).continuous)).add
        ((envelopeSeminorm_continuous n).comp
          (profileVerticalCLM.comp (profileJetCLM i)).continuous)

theorem profileControlSeminorm_apply (n : ℕ) (F : PlanarSchwartz) :
    planarProfileConstant F n=profileControlSeminorm n F+9 := by
  have hpoint (i : Fin 3) :
      planarEnvelopeConstant (planarVerticalJet F i) n+
        planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet F i)) n+
        planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet F i)) n=
      (envelopeSeminorm n (profileJetCLM i F)+
        envelopeSeminorm n (profileHorizontalCLM (profileJetCLM i F))+
        envelopeSeminorm n (profileVerticalCLM (profileJetCLM i F)))+3 := by
    simp only [profileJetCLM_apply]
    change (envelopeSeminorm n (planarVerticalJet F i)+1)+
      (envelopeSeminorm n (planarHorizontalDerivative (planarVerticalJet F i))+1)+
      (envelopeSeminorm n (planarVerticalDerivative (planarVerticalJet F i))+1)=_
    change (envelopeSeminorm n (planarVerticalJet F i)+1)+
      (envelopeSeminorm n (planarHorizontalDerivative (planarVerticalJet F i))+1)+
      (envelopeSeminorm n (planarVerticalDerivative (planarVerticalJet F i))+1)=
        (envelopeSeminorm n (planarVerticalJet F i)+
          envelopeSeminorm n (planarHorizontalDerivative (planarVerticalJet F i))+
          envelopeSeminorm n (planarVerticalDerivative (planarVerticalJet F i)))+3
    ring
  unfold planarProfileConstant
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  simp [profileControlSeminorm]

theorem uniform_translated_profile_bound (F : PlanarSchwartz) (n : ℕ) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace, ∀ a : ℝ×ℝ, ‖a‖≤‖nu‖ →
      planarProfileConstant (weightedTranslatedProfile F q nu a) n≤C := by
  obtain ⟨q₀,C,hC,hbound⟩ := weightedTranslatedProfile_bounded F
    (profileControlSeminorm n) (profileControlSeminorm_continuous n)
  refine ⟨q₀,C+9,by linarith only [hC],?_⟩
  intro q hq nu a ha
  rw [profileControlSeminorm_apply]
  exact add_le_add (hbound q hq nu a ha) le_rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
