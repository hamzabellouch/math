import Mathlib
import OAI.Probability.SKGap.Stability.StableFields
import OAI.Probability.SKGap.Localization.RecipeError
import OAI.Probability.SKGap.Stability.ImplicitNode

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n Unit κ σ)

lemma implicitSource_control (t : SourceTree (Fin n→ℝ)) (y : VectorFields n) (x : Spin n)
    {C Q R L V Z B Cp E : ℝ}
    (hC : 0≤C) (hQ : 0≤Q) (hR : 0≤R) (hL : 0≤L) (hV : 0≤V)
    (hY : SmallBound y x B) (hp : SmallBound (D.implicitPartial y) x Cp)
    (hE : ‖derivativeMatrix (D.H ()) x-t.fieldMatrix D.j D.J‖≤E)
    (hs : ∀s,SegmentRegular D.H D.θ (D.seedFunction 1 s) (D.seedDerivative 1 s) x C)
    (ha : SegmentRegular D.H D.θ (D.auxFunction 1 0) (D.auxDerivative 1 0) x C)
    (ht : vectorNorm (parameterIncrement D.θ x)≤V)
    (hQ4 : (∑i,∑k,(primaryIncrement D.H x i k)^4)≤Q^4)
    (hQr : ∀i,(∑k,(primaryIncrement D.H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement D.H x i i)^2)≤L^2)
    (hZ : (∑α,‖derivativeVector (D.θ α) x‖)+4*(Q^2+R*V+V^2)+2*(Q+L+V)≤Z) :
    TraceControl (D.implicitSourcePrimitive t y x)
      (((∑s,C*vectorNorm (D.seed s)*Z)+C*B*Z)+Cp*E) := by
  have hc (s : VectorFields n) {S : ℝ} (hS : SmallBound s x S)
      (F : Fin n→Args (ι:=Unit) (κ:=κ)→ℝ)
      (F' : Fin n→Args (ι:=Unit) (κ:=κ)→Args (ι:=Unit) (κ:=κ)→L[ℝ]ℝ)
      (hF : SegmentRegular D.H D.θ F F' x C) : TraceControl (sourceError D.H D.θ F F' s x) (C*S*Z) :=
    (sourceError_control D.H D.θ F F' s x hF hS.nonneg hV hQ hR hL hS.size hS.derivative ht hQ4 hQr hQd).mono
      (mul_le_mul_of_nonneg_left hZ (mul_nonneg hC hS.nonneg))
  have hs' := TraceControl.sum (fun s=>hc (fun _=>D.seed s) (SmallBound.seed _ x) _ _ (hs s))
  have ha' := hc y hY _ _ ha
  have hp' := (small_diagonal_control
    (derivativeMatrix (D.H ()) x-t.fieldMatrix D.j D.J) (D.implicitPartial y x)).mono
      (mul_le_mul hp.size hE (norm_nonneg _) hp.nonneg)
  have H:=(hs'.add ha').add hp'
  simpa only [implicitSourcePrimitive,sourceAtoms,Fin.sum_univ_one] using H

lemma implicitField_control (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n) (x : Spin n) (hn : 0<n)
    {P R B Cp E : ℝ} (hP : 0≤P) (hR : 0≤R)
    (hW : SmallBound w x B) (hp : SmallBound (D.implicitPartial y) x Cp)
    (hE : ‖derivativeMatrix (D.predecessor ()) x-t.sourceMatrix D.j D.J‖≤E)
    (hm : ∀i,|D.predecessor () x i|≤1)
    (hdm : SKGap.opNorm (derivativeMatrix (D.predecessor ()) x)≤P)
    (hda : ∀i,∑k,(derivativeMatrix D.implicitCoefficient x i k)^2≤R^2) :
    TraceControl (D.implicitFieldPrimitive t w y x)
      (|D.j| *(Cp*E)+|D.j| *(Cp*(1+2*P)+3*B*R)) := by
  have hmE : TraceControl
      ((D.j*siteMean (D.implicitPartial y) x) •
        (derivativeMatrix (D.predecessor ()) x-t.sourceMatrix D.j D.J)) (|D.j| *(Cp*E)) := by
    simpa only [smul_smul] using ((small_mean_control
      (derivativeMatrix (D.predecessor ()) x-t.sourceMatrix D.j D.J)
      (D.implicitPartial y) x hn).mono
        (mul_le_mul hp.size hE (norm_nonneg _) hp.nonneg)).smul D.j
  have hpE := primary_averageError_control (D.implicitPartial y) (D.predecessor ()) x hn
    hp.nonneg hP hp.derivative hm hdm
  have haE : TraceControl (averageError (siteMean D.implicitCoefficient) w x) (3*B*R) := by
    apply (averageError_control (siteMean D.implicitCoefficient) w x).mono
    have H:=coefficient_mean_difference D.implicitCoefficient x hR hda
    have h1 := add_le_add hW.size (mul_le_mul_of_nonneg_left hW.derivative (by norm_num : (0:ℝ)≤2))
    exact (mul_le_mul h1 H (norm_nonneg _) (by linarith [hW.nonneg])).trans_eq (by ring)
  simpa only [implicitFieldPrimitive,neg_smul] using hmE.neg.sub ((hpE.add haE).smul D.j)

omit [Fintype σ] in
lemma implicit_inverse_left (x : Spin n) (ha : ∀i,0≤D.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (D.implicitCoefficient x) 1*
      (D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*SKGap.pathDiagonal (D.implicitCoefficient x) 1).PosDef) :
    WordLetter.inverse.exactEval D.j (D.implicitCoefficient x) D.J*
      (1-Matrix.diagonal (D.implicitCoefficient x)*(D.J-(D.j*siteMean D.implicitCoefficient x) • 1))=1 := by
  have hu:=SKGap.ResolventIdentity.inverse_one_sub_square_mul_unit
    (SKGap.pathDiagonal (D.implicitCoefficient x) 1) (D.J-(D.j*siteMean D.implicitCoefficient x) • 1) hS.isUnit
  rw [SKGap.pathDiagonal_square ha] at hu
  have hi:=Matrix.nonsing_inv_mul _ (((1-Matrix.diagonal (D.implicitCoefficient x)*(D.J-(D.j*siteMean D.implicitCoefficient x) • 1)).isUnit_iff_isUnit_det).mp hu)
  have hq : (D.j/(n:ℝ))*(∑i,D.implicitCoefficient x i)=D.j*siteMean D.implicitCoefficient x := by
    simp only [siteMean];ring
  simpa only [WordLetter.exactEval,Fintype.card_fin,hq] using hi

theorem implicit_error_trace (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n)
    (hW : w=D.sourceOf 1 (fun _=>y)) (hY : y=D.fieldOf 1 (fun _=>w) (fun _=>y)) (x : Spin n)
    (ha0 : ∀i,0≤D.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (D.implicitCoefficient x) 1*
      (D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*SKGap.pathDiagonal (D.implicitCoefficient x) 1).PosDef)
    {C F A M : ℝ} {L : ℕ}
    (hs : TraceControl (D.implicitSourcePrimitive t y x) C)
    (hf : TraceControl (D.implicitFieldPrimitive t w y x) F)
    (ha : ∀i,|D.implicitCoefficient x i|≤A)
    (hwords : ClosedWordTestBound D.j (D.implicitCoefficient x) D.J A M L)
    (v : OrdinaryWord n) (hlen : v.length+3≤L) (hv : wordBounded A v) :
    |trace (matrixWord D.J v*(derivativeMatrix w x-D.implicitRetainedSource t y x))|≤(C+F)*M ∧
    |trace (matrixWord D.J v*(derivativeMatrix y x-D.implicitRetainedField t y x))|≤
      ((1+|D.j*siteMean D.implicitCoefficient x|)*(C+F)+F)*M := by
  obtain ⟨he,he'⟩:=D.implicit_error_solved t w y hW hY x (D.implicit_inverse_left x ha0 hS)
  exact implicit_source_field_trace _ _ _ _ _ _ _ _ he he' hs hf ha hwords v hlen hv

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
