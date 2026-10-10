import OAI.Geometry.Relativity.CKS.CollarRawNull
import OAI.Geometry.Relativity.CKS.ConeSupport

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def thinTensor (t : RawTensorData) : RawTensorData :=
  (((fun i => if i=3 then constantJet (t.1.1 i).1 else t.1.1 i),t.1.2),t.2)
def thinRaw (p : RawNullInput) : RawNullInput :=
  ((p.1.1,(p.1.2.1,thinTensor p.1.2.2)),p.2)

lemma thinQ (p : RawNullInput) : rawQ (thinRaw p).1=rawQ p.1 := rfl
lemma thinC (p : RawNullInput) : rawC (thinRaw p).1=rawC p.1 := rfl
lemma thinD (p : RawNullInput) : rawD (thinRaw p).1=rawD p.1 := rfl
lemma thinT (p : RawNullInput) : rawT (thinRaw p).1=rawT p.1 := rfl
lemma thinF (p : RawNullInput) : rawF (thinRaw p).1=rawF p.1 := rfl
lemma thinL (p : RawNullInput) : rawL (thinRaw p).1=rawL p.1 := rfl
lemma thinTr (p : RawNullInput) : (rawTr (thinRaw p).1).1=(rawTr p.1).1 := rfl
lemma thinA (p : RawNullInput) : rawA (thinRaw p).1=rawA p.1 := by
  unfold rawA rawLapseInput
  rw [thinT,thinF,thinD]
  rfl
lemma thinX (p : RawNullInput) : rawX (thinRaw p).1=rawX p.1 := by
  funext i k
  unfold rawX rawLambda
  rw [thinA,thinQ,thinC]
  rfl
attribute [local irreducible] rawA rawX rawQ rawD rawT rawL rawF rawTr

lemma thin_mz (p : RawNullInput) : mz (nP (rawNullMap (thinRaw p)))=mz (nP (rawNullMap p)) := by
  simp only [mz,nP,rawNullMap,rawMomentumInput,rz,thinRaw]
lemma thin_mw (p : RawNullInput) : mw (nP (rawNullMap (thinRaw p)))=mw (nP (rawNullMap p)) := by
  simp only [mw,nP,rawNullMap,rawMomentumInput,rwgt,thinRaw]
lemma thin_mq (p : RawNullInput) : mq (nP (rawNullMap (thinRaw p)))=mq (nP (rawNullMap p)) := by
  simp only [mq,nP,rawNullMap,rawMomentumInput]
  rw [thinQ]
lemma thin_mS (p : RawNullInput) : mS (nP (rawNullMap (thinRaw p)))=mS (nP (rawNullMap p)) := by
  simp only [mS,nP,rawNullMap,rawMomentumInput,rawS,re,rshift,thinRaw]
lemma thin_mE (p : RawNullInput) : mE (nP (rawNullMap (thinRaw p)))=mE (nP (rawNullMap p)) := by
  simp only [mE,nP,rawNullMap,rawMomentumInput,re,reta,thinRaw,thinTensor]
lemma thin_mT (p : RawNullInput) : mT (nP (rawNullMap (thinRaw p)))=mT (nP (rawNullMap p)) := by
  simp only [mT,nP,rawNullMap,rawMomentumInput]
  change (1-re p.1) • traceFreeJet (rawQ (thinRaw p).1) (rtau p.1) =
    (1-re p.1) • traceFreeJet (rawQ p.1) (rtau p.1)
  rw [thinQ]
lemma thin_mEr (p : RawNullInput) : mEr (nP (rawNullMap (thinRaw p)))=mEr (nP (rawNullMap p)) := by
  simp only [mEr,nP,rawNullMap,rawMomentumInput,re,retar,reta,rθ,thinRaw,thinTensor]
lemma thin_mX (p : RawNullInput) : mX (nP (rawNullMap (thinRaw p)))=mX (nP (rawNullMap p)) := by
  simp only [mX,nP,rawNullMap,rawMomentumInput]
  exact thinX p
lemma thin_mc0 (p : RawNullInput) : mc (nP (rawNullMap (thinRaw p))) 0=mc (nP (rawNullMap p)) 0 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput,Matrix.cons_val_zero]
  exact thinA p
lemma thin_mc1 (p : RawNullInput) : mc (nP (rawNullMap (thinRaw p))) 1=mc (nP (rawNullMap p)) 1 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact thinT p
lemma thin_mc2 (p : RawNullInput) : mc (nP (rawNullMap (thinRaw p))) 2=mc (nP (rawNullMap p)) 2 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput]
  exact thinL p
lemma thin_mc4 (p : RawNullInput) : mc (nP (rawNullMap (thinRaw p))) 4=mc (nP (rawNullMap p)) 4 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput]
  exact thinD p
lemma thin_mc3 (p : RawNullInput) : (mc (nP (rawNullMap (thinRaw p))) 3).1=(mc (nP (rawNullMap p)) 3).1 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput]
  exact thinTr p
lemma thin_nF (p : RawNullInput) : nF (rawNullMap (thinRaw p))=nF (rawNullMap p) := by
  simp only [nF,rawNullMap]
  exact thinF p
lemma thin_nFr (p : RawNullInput) : nFr (rawNullMap (thinRaw p))=nFr (rawNullMap p) := by
  simp only [nFr,rawNullMap,re,rθ,thinRaw]

end
end CKSAngularGeometry

end

end OAI
