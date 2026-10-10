import OAI.NumberTheory.DirichletL.Energy.StageReserveSchedule
import OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentSuccessorPaidParameters
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

def sourcePaid (Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh:ℝ):ℝ:=
  (Bcap+Bcap)*emask+ell+er+(delta+reserveAmp+thetaSource)/6+thetaClip/3+κ*mesh

theorem literal_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hB:0≤Bcap)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(ell epsSrc epsMask deltaSrc thetaSrc deltaAmp reserveAmp thetaSource thetaClip
      er primeLoss physicalLoss highReflection zeroReflection saving:ℝ)
    (hell:ell≤stageLoss M Bcap ε k)
    (he0:0≤epsSrc)(he:epsSrc≤reserve M Bcap ε)
    (hemask:(Bcap+Bcap)*epsMask≤reserve M Bcap ε)
    (hdsrc:deltaSrc≤reserve M Bcap ε)(htsrc:thetaSrc≤reserve M Bcap ε)
    (hda:0≤deltaAmp)(hra:0≤reserveAmp)(hts:0≤thetaSource)(htc:0≤thetaClip)
    (hsmall:deltaAmp+reserveAmp+thetaSource≤reserve M Bcap ε)
    (hclip:thetaClip≤reserve M Bcap ε)(her:er≤reserve M Bcap ε)
    (hcommon:epsSrc*Bcommon≤reserve M Bcap ε)
    (hprime:primeLoss≤reserve M Bcap ε)(hphysical:physicalLoss≤reserve M Bcap ε)
    (hhigh:highReflection≤reserve M Bcap ε)(hzero:zeroReflection≤reserve M Bcap ε)
    (hsaving:2*amplification ε+deltaAmp+reserveAmp≤saving):
    ∀j:Fin 4,
      losses epsSrc deltaSrc thetaSrc Bcap j+
        lossVector (amplification ε) deltaAmp reserveAmp
          (sourcePaid Bcap epsMask ell er deltaAmp reserveAmp thetaSource thetaClip κ (mesh M Bcap κ ε))
          epsSrc M saving j+
        epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      stageLoss M Bcap ε (k+1):=by
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<reserve M Bcap ε:=hb.2.2.2.1
  have hs:0≤amplification ε:=hb.1.le
  have hother:epsSrc*Bcommon+primeLoss+physicalLoss≤48*reserve M Bcap ε:=by linarith
  have hextra:epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      50*reserve M Bcap ε:=by linarith
  have hdf:deltaAmp+reserveAmp≤reserve M Bcap ε:=by linarith
  have hdelta:deltaAmp≤reserve M Bcap ε:=by linarith
  have hres:reserveAmp≤reserve M Bcap ε:=by linarith
  have hmain:=successor_with_references M Bcap κ ε hM hB hκ hε k
    er deltaSrc epsSrc (deltaAmp+reserveAmp+thetaSource) ((Bcap+Bcap)*epsMask) thetaClip
    (epsSrc*Bcommon+primeLoss+physicalLoss) highReflection zeroReflection
    her hdsrc he hsmall hemask hclip hother hhigh hzero
  have hone:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaSrc thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdsrc htsrc hres he0 le_rfl hextra
  have hdiag:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaAmp thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdelta htsrc hres he0 le_rfl hextra
  have htail:=one_time_with_new_cost M Bcap κ ε hM hB hκ hε k 0
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection) (by positivity) hextra
  intro j
  fin_cases j <;> simp only [losses,lossVector,Matrix.cons_val,Fin.reduceFinMk]
  · dsimp [sourcePaid,edge] at hmain ⊢
    linarith
  · dsimp [exceptional] at hone
    linarith [hone.1]
  · dsimp [diagonal] at hdiag
    linarith [hdiag.2]
  · linarith

theorem chosen_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε;
    let es:=r/(Bcommon+1);
    let em:=r/(Bcap+Bcap+1);
    0<es ∧ es≤1 ∧ 0<em ∧ 0<r/4 ∧ 0<2*amplification ε+1 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤stageLoss M Bcap ε k→
      highReflection≤r→zeroReflection≤r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es M (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤stageLoss M Bcap ε (k+1):=by
  dsimp only
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<reserve M Bcap ε:=hb.2.2.2.1
  have hs:0<amplification ε:=hb.1
  have hrsmall:reserve M Bcap ε≤amplification ε/100:=min_le_left _ _
  have hr1:reserve M Bcap ε≤1:=by linarith [hb.2.1]
  have hes:0<reserve M Bcap ε/(Bcommon+1):=by positivity
  have hem:0<reserve M Bcap ε/(Bcap+Bcap+1):=by positivity
  have hesle:reserve M Bcap ε/(Bcommon+1)≤reserve M Bcap ε:=by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hemscale:(Bcap+Bcap)*(reserve M Bcap ε/(Bcap+Bcap+1))≤reserve M Bcap ε:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hescale:(reserve M Bcap ε/(Bcommon+1))*Bcommon≤reserve M Bcap ε:=by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,hesle.trans hr1,hem,by positivity,by positivity,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero
  apply literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    (reserve M Bcap ε/(Bcommon+1)) (reserve M Bcap ε/(Bcap+Bcap+1))
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    highReflection zeroReflection (2*amplification ε+1)
    hell hes.le hesle hemscale
  all_goals first | exact hescale | exact hhigh | exact hzero | positivity | linarith

end SevenEighths.CenteredMomentEnergyFirstStageLossBudget

end

end OAI
