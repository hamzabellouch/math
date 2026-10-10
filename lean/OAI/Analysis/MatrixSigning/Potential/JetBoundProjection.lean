import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Parameters
import OAI.Analysis.MatrixSigning.Potential.NormTCoord
import OAI.Analysis.MatrixSigning.Matrices.JetBoundTightPart

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
local instance : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance : NormedAddCommGroup (PairHilbert d) := inferInstance
local instance : NormedSpace ℝ (PairHilbert d) := inferInstance
local instance : NormedAddCommGroup (H d × H d) := inferInstance
local instance : NormedSpace ℝ (H d × H d) := inferInstance
local instance : NormedAddCommGroup (PairHilbert d × PairHilbert d) := inferInstance
local instance : NormedSpace ℝ (PairHilbert d × PairHilbert d) := inferInstance
local instance : NormedAddCommGroup (Vars d) := inferInstance
local instance : NormedSpace ℝ (Vars d) := inferInstance
private local instance : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace
local instance : NormedAddCommGroup (E →L[ℝ] Vars d) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] Vars d) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] H d) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] H d) := inferInstance

lemma jetBound_projection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : E →L[ℝ] Vars d) (L : Vars d →L[ℝ] F) {z : E} {B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hL : ‖L‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) :
    JetBound (L.comp Z) z B := by
  apply JetBound.linear _ _ (le_trans (norm_comp_contractions L Z hL hZ) hB)
  exact (L.le_opNorm (Z z)).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
    (by simpa only [one_mul] using hz))

lemma norm_tracePair_le {B : ℝ} (hd : (d:ℝ)+1 ≤ B) :
    ‖innerSL ℝ (identityPair d)‖ ≤ 2*B := by
  have hB : 0 ≤ B := le_trans (by positivity) hd
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  exact (norm_inner_le_norm (𝕜 := ℝ) (identityPair d) v).trans
    (mul_le_mul_of_nonneg_right ((norm_identityPair_le_dimension (d := d)).trans (show 2*((d:ℝ)+1) ≤ 2*B by linarith)) (norm_nonneg v))

lemma jetBound_pairHilbert {f g : E → H d} {z : E} {C D : ℝ}
    (hf : ContDiffAt ℝ 3 f z) (hg : ContDiffAt ℝ 3 g z)
    (hfB : JetBound f z C) (hgB : JetBound g z D) :
    JetBound (fun v => (pairEquiv d).symm (f v,g v)) z (2*(C+D)) :=
  (hfB.prod hf hg hgB).linear_comp (pairEquiv d).symm.toContinuousLinearMap
    (hf.prodMk hg) norm_pairEquiv_symm_le

lemma jetBound_tracePart (Z : E →L[ℝ] Vars d) {z : E} {B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) :
    JetBound (fun v => inner ℝ (identityPair d) (pCoord d (Z v))-1) z (2*B*B+1) := by
  let p : E →L[ℝ] PairHilbert d := (pCoord d).comp Z
  have hpB := jetBound_projection Z (pCoord d) hZ norm_pCoord_le hz hB
  have htrace := hpB.linear_comp (innerSL ℝ (identityPair d)) p.contDiff.contDiffAt (norm_tracePair_le hd)
  have hh := htrace.sub
    ((innerSL ℝ (identityPair d)).contDiff.contDiffAt.comp z p.contDiff.contDiffAt)
    (contDiffAt_const (c := (1:ℝ))) (JetBound.const (1:ℝ) z)
  simp only [Function.comp_def,norm_one] at hh
  exact hh

lemma kktJet_numeric {B : ℝ} (hB : 1 ≤ B) :
    2*B*B+1+(2*((B*B+6*B^4+B+8*B*B)+(B*B+6*B^4+B+8*B*B))+
      2*((42*B^5+8*B*B+B*B)+(42*B^5+8*B*B+B*B))) ≤ 300*B^5 := by
  have h15 : B ≤ B^5 := by simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1≤5)
  have h25 : B^2 ≤ B^5 := pow_le_pow_right₀ hB (by norm_num)
  have h45 : B^4 ≤ B^5 := pow_le_pow_right₀ hB (by norm_num)
  have h05 : 1 ≤ B^5 := one_le_pow₀ hB
  nlinarith

lemma jetBound_kktPrimal (Z : E →L[ℝ] Vars d) {S : E → H d}
    {η : E → H d →L[ℝ] H d} {z : E} {ε B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) (_hε : |ε| ≤ B)
    (hX : xCoord d (Z z) ∈ pd d) (hY : yCoord d (Z z) ∈ pd d)
    (hiX : ‖invH (xCoord d (Z z))‖ ≤ B) (hiY : ‖invH (yCoord d (Z z))‖ ≤ B)
    (_hM : ‖mCoord d (Z z)‖ ≤ 1) (_hN : ‖nCoord d (Z z)‖ ≤ 1)
    (hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
    (hSB : JetBound S z B) (hηB : JetBound η z B) :
    JetBound (fun v => (kktSystem ε (S v) (η v) (Z v)).2.1) z
      (2*((B*B+6*B^4+B+8*B*B)+(B*B+6*B^4+B+8*B*B))) := by

  let t : E →L[ℝ] ℝ := (tCoord d).comp Z
  let X : E →L[ℝ] H d := (xCoord d).comp Z
  let Y : E →L[ℝ] H d := (yCoord d).comp Z
  have ht := jetBound_projection Z (tCoord d) hZ norm_tCoord_le hz hB
  have hXB := jetBound_projection Z (xCoord d) hZ norm_xCoord_le hz hB
  have hYB := jetBound_projection Z (yCoord d) hZ norm_yCoord_le hz hB
  have hXL : ‖X‖ ≤ 1 := norm_comp_contractions _ _ norm_xCoord_le hZ
  have hYL : ‖Y‖ ≤ 1 := norm_comp_contractions _ _ norm_yCoord_le hZ
  have hI := (norm_one_le_dimension (d := d)).trans hd
  let T := B*B+6*B^4+B+8*B*B
  have h₁ : JetBound (fun v => t v • (Hermitian.one : H d)-invH (X v)-S v-η v (Y v)) z T :=
    jetBound_tightPart t X Y hB hI ht hXL hYB hX hiX hS hη hSB hηB
  have h₂ : JetBound (fun v => t v • (Hermitian.one : H d)-invH (Y v)-(-S v)-η v (X v)) z T :=
    jetBound_tightPart t Y X hB hI ht hYL hXB hY hiY hS.neg hη hSB.neg hηB
  have hc₁ := contDiffAt_tightPart t.contDiff.contDiffAt X.contDiff.contDiffAt Y.contDiff.contDiffAt hS hη hX
  have hc₂ := contDiffAt_tightPart t.contDiff.contDiffAt Y.contDiff.contDiffAt X.contDiff.contDiffAt hS.neg hη hY
  have h := jetBound_pairHilbert hc₁ hc₂ h₁ h₂
  simp only [sub_neg_eq_add] at h
  exact h

lemma jetBound_kktDual (Z : E →L[ℝ] Vars d) {S : E → H d}
    {η : E → H d →L[ℝ] H d} {z : E} {ε B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) (hε : |ε| ≤ B)
    (hX : xCoord d (Z z) ∈ pd d) (hY : yCoord d (Z z) ∈ pd d)
    (hiX : ‖invH (xCoord d (Z z))‖ ≤ B) (hiY : ‖invH (yCoord d (Z z))‖ ≤ B)
    (hM : ‖mCoord d (Z z)‖ ≤ 1) (hN : ‖nCoord d (Z z)‖ ≤ 1)
    (_hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
    (_hSB : JetBound S z B) (hηB : JetBound η z B) :
    JetBound (fun v => (kktSystem ε (S v) (η v) (Z v)).2.2) z
      (2*((42*B^5+8*B*B+B*B)+(42*B^5+8*B*B+B*B))) := by

  let X : E →L[ℝ] H d := (xCoord d).comp Z
  let Y : E →L[ℝ] H d := (yCoord d).comp Z
  let P : E →L[ℝ] H d := (mCoord d).comp Z
  let Q : E →L[ℝ] H d := (nCoord d).comp Z
  have hPB := jetBound_projection Z (mCoord d) hZ norm_mCoord_le hz hB
  have hQB := jetBound_projection Z (nCoord d) hZ norm_nCoord_le hz hB
  have hXL : ‖X‖ ≤ 1 := norm_comp_contractions _ _ norm_xCoord_le hZ
  have hYL : ‖Y‖ ≤ 1 := norm_comp_contractions _ _ norm_yCoord_le hZ
  have hPL : ‖P‖ ≤ 1 := norm_comp_contractions _ _ norm_mCoord_le hZ
  have hQL : ‖Q‖ ≤ 1 := norm_comp_contractions _ _ norm_nCoord_le hZ
  have hI := (norm_one_le_dimension (d := d)).trans hd
  let U := 42*B^5+8*B*B+B*B
  have h₃ : JetBound (fun v => sandwich (invH (X v)) (P v)-η v (Q v)-ε • (Hermitian.one : H d)) z U :=
    jetBound_stationaryPart X P Q ε hB hI hε hXL hPL hM hQB hX hiX hη hηB
  have h₄ : JetBound (fun v => sandwich (invH (Y v)) (Q v)-η v (P v)-ε • (Hermitian.one : H d)) z U :=
    jetBound_stationaryPart Y Q P ε hB hI hε hYL hQL hN hPB hY hiY hη hηB
  have hc₃ := contDiffAt_stationaryPart ε X.contDiff.contDiffAt P.contDiff.contDiffAt Q.contDiff.contDiffAt hη hX
  have hc₄ := contDiffAt_stationaryPart ε Y.contDiff.contDiffAt Q.contDiff.contDiffAt P.contDiff.contDiffAt hη hY
  exact jetBound_pairHilbert hc₃ hc₄ h₃ h₄

lemma jetBound_kktGiven (Z : E →L[ℝ] Vars d) {S : E → H d}
    {η : E → H d →L[ℝ] H d} {z : E} {ε B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) (hε : |ε| ≤ B)
    (hX : xCoord d (Z z) ∈ pd d) (hY : yCoord d (Z z) ∈ pd d)
    (hiX : ‖invH (xCoord d (Z z))‖ ≤ B) (hiY : ‖invH (yCoord d (Z z))‖ ≤ B)
    (hM : ‖mCoord d (Z z)‖ ≤ 1) (hN : ‖nCoord d (Z z)‖ ≤ 1)
    (hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
    (hSB : JetBound S z B) (hηB : JetBound η z B) :
    JetBound (fun v => kktSystem ε (S v) (η v) (Z v)) z (300*B^5) := by
  have ht := jetBound_tracePart Z hZ hz hB hd
  have hp := jetBound_kktPrimal Z hZ hz hB hd hε hX hY hiX hiY hM hN hS hη hSB hηB
  have hy := jetBound_kktDual Z hZ hz hB hd hε hX hY hiX hiY hM hN hS hη hSB hηB
  have hc := contDiffAt_kktGiven ε hS hη Z.contDiff.contDiffAt hX hY
  have hb := ht.prod hc.fst hc.snd (hp.prod hc.snd.fst hc.snd.snd hy)
  have he : JetBound (fun v => kktSystem ε (S v) (η v) (Z v)) z
      (2*B*B+1+(2*((B*B+6*B^4+B+8*B*B)+(B*B+6*B^4+B+8*B*B))+
      2*((42*B^5+8*B*B+B*B)+(42*B^5+8*B*B+B*B)))) := hb
  exact he.mono (kktJet_numeric hB)
end
end CurrentKS.Variational

end OAI
