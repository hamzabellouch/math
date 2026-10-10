import OAI.Geometry.Relativity.CKS.CollarRawDEC
import OAI.Geometry.Relativity.CKS.CollarThinPrimitives

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
lemma thinRaw_acceleration (p : RawNullInput) :
    accelerationCoefficient (nP (rawNullMap (thinRaw p)))=accelerationCoefficient (nP (rawNullMap p)) := by
  funext a
  simp only [accelerationCoefficient,thin_mc0,thin_mz]

lemma thinRaw_Q (p : RawNullInput) :
    coordinateQ (nP (rawNullMap (thinRaw p)))=coordinateQ (nP (rawNullMap p)) := by
  simp only [coordinateQ,normalizedMean,normalizedSpeed,physicalLJet,physicalTJet,thinRaw_acceleration,thin_mz,thin_mw,thin_mq,thin_mS,thin_mE,thin_mT,thin_mX,thin_mc0,thin_mc1,thin_mc2,thin_mc3,thin_mc4]
lemma thinRaw_Z (p : RawNullInput) :
    coordinateZ (nP (rawNullMap (thinRaw p)))=coordinateZ (nP (rawNullMap p)) := by
  funext a
  simp only [coordinateZ,normalizedMean,normalizedSpeed,physicalLJet,physicalTJet,thinRaw_acceleration,thin_mz,thin_mw,thin_mq,thin_mS,thin_mE,thin_mT,thin_mEr,thin_mc0,thin_mc1,thin_mc2,thin_mc4]
lemma thinRaw_ratio (p : RawNullInput) :
    nullRatio (nP (rawNullMap (thinRaw p)))=nullRatio (nP (rawNullMap p)) := by
  simp only [nullRatio,nullD,normalizedSpeed,thin_mz,thin_mc0,thin_mc1,thin_mc4]
lemma thinRaw_smallNull (p : RawNullInput) (r : ℝ) :
    coordinateSmallNull (rawNullMap (thinRaw p)) r=coordinateSmallNull (rawNullMap p) r := by
  simp only [coordinateSmallNull,nullD,nullRatio,normalizedSpeed,physicalNullQuadratic,physicalNullEta,thinRaw_acceleration,thin_mz,thin_mw,thin_mq,thin_mS,thin_mE,thin_mT,thin_mX,thin_mc0,thin_mc1,thin_mc4,thin_nF,thin_nFr]
lemma thinRaw_DEC (p : RawNullInput) (r : ℝ) :
    coordinateDEC (rawNullMap (thinRaw p)) r ↔ coordinateDEC (rawNullMap p) r := by
  simp only [coordinateDEC,coordinateEnergy,thinRaw_Q,thinRaw_Z,thinRaw_smallNull,thinRaw_ratio,thin_mq,thin_mz]
lemma thinRaw_old (p : RawNullInput) : thinRaw (rawNullOriginal p)=rawNullOriginal (thinRaw p) := rfl
lemma thinRaw_angular (p : RawNullInput) : rawAngularMatrix (thinRaw p)=rawAngularMatrix p := rfl

end
end CKSAngularGeometry

end

end OAI
