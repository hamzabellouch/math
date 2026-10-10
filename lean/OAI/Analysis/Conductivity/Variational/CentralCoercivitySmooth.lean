import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralEnergySpace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def centralAmbientEnergy (s : Fin 3 → ℝ) (u : CentralAmbient s) : ℝ :=
  ‖centralAmbientD s u‖^2+
    ∑ i : Fin 3,‖spectralGraphWeight (torusRate s) (centralAmbientT s i u)‖^2

lemma centralAmbientEnergy_nonneg (s : Fin 3 → ℝ) (u : CentralAmbient s) :
    0≤centralAmbientEnergy s u := add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma continuous_centralAmbientEnergy (s : Fin 3 → ℝ) : Continuous (centralAmbientEnergy s) := by
  apply Continuous.add ((centralAmbientD s).continuous.norm.pow 2)
  exact continuous_finsetSum _ (fun i _ =>
    (((spectralGraphWeight (torusRate s)).comp (centralAmbientT s i)).continuous.norm.pow 2))

lemma centralAmbientD_shift (s : Fin 3 → ℝ) (u : CentralAmbient s) (a : ℝ) :
    centralAmbientD s (u-a • centralAmbientOne s)=centralAmbientD s u := by simp only [map_sub,map_smul,centralAmbientD_one,smul_zero,sub_zero]

lemma centralAmbientWeight_shift (s : Fin 3 → ℝ) (u : CentralAmbient s) (a : ℝ) (i : Fin 3) :
    spectralGraphWeight (torusRate s) (centralAmbientT s i (u-a • centralAmbientOne s))=
      spectralGraphWeight (torusRate s) (centralAmbientT s i u) := by
  simp only [map_sub,map_smul,centralAmbientWeight_one,smul_zero,sub_zero]

lemma centralAmbientEnergy_shift (s : Fin 3 → ℝ) (u : CentralAmbient s) (a : ℝ) :
    centralAmbientEnergy s (u-a • centralAmbientOne s)=centralAmbientEnergy s u := by
  simp only [centralAmbientEnergy,centralAmbientD_shift,centralAmbientWeight_shift]

lemma centralAmbientQ_shift (s : Fin 3 → ℝ) (u : CentralAmbient s) (a : ℝ) :
    centralAmbientQ s (u-a • centralAmbientOne s)=centralAmbientQ s u := by
  simp only [map_sub,map_smul,centralAmbientQ_one,smul_zero,sub_zero]

def centralCoercivityBase : ℝ :=
  1+centralPoincareConstant+3*centralTraceConstant*(192+2*centralPoincareConstant)

lemma centralCoercivityBase_ge : 1≤centralCoercivityBase := by
  have hP := centralPoincareConstant_nonneg
  have hT := centralTraceConstant_pos
  dsimp [centralCoercivityBase]
  nlinarith

lemma centralCoercivityBase_pos : 0<centralCoercivityBase := lt_of_lt_of_le zero_lt_one centralCoercivityBase_ge

lemma central_smooth_anchor_norm (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    ‖centralEmbedL s (f-centralAnchorAverage 0 f • centralSmoothOne)‖^2≤
      centralCoercivityBase*centralAmbientEnergy s (centralEmbedL s f) := by
  let a := centralAnchorAverage 0 f
  let g : centralSmoothFunctions := f-a • centralSmoothOne
  have hg : centralEmbedL s g=centralEmbedL s f-a • centralAmbientOne s := by
    dsimp [g,centralAmbientOne]
    simp only [map_sub,map_smul]
  have hD : centralJetD (centralSmoothJet g)=centralAmbientD s (centralEmbedL s f) := by
    rw [←centralAmbientD_embed s g,hg,centralAmbientD_shift]
  have hP : (∫ z in centralClosed,(g z)^2)≤
      centralPoincareConstant*‖centralAmbientD s (centralEmbedL s f)‖^2 := by
    rw [centralAmbientD_embed,centralSmoothJet_gradient_norm]
    simpa [g,a,centralSmoothOne,localVariance] using central_physical_poincare (central_smooth f)
  have ht (i : Fin 3) : ‖centralTraceFourier g i‖^2≤
      (centralTraceConstant*(192+2*centralPoincareConstant))*‖centralAmbientD s (centralEmbedL s f)‖^2 := by
    have hh := centralTrace_anchor_bound g i
    rw [hD] at hh
    apply hh.trans
    calc
      _≤centralTraceConstant*(192*‖centralAmbientD s (centralEmbedL s f)‖^2+
          2*(centralPoincareConstant*‖centralAmbientD s (centralEmbedL s f)‖^2)) := by
        apply mul_le_mul_of_nonneg_left _ centralTraceConstant_pos.le
        linarith only [hP]
      _=_ := by ring
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => ht i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  norm_num only [Nat.cast_ofNat] at hsum
  have hw (i : Fin 3) :
      spectralGraphWeight (torusRate s) (centralSmoothTrace s g i)=
        spectralGraphWeight (torusRate s) (centralAmbientT s i (centralEmbedL s f)) := by
    rw [←centralAmbientT_embed s g i,hg,centralAmbientWeight_shift]
  change ‖centralEmbedL s g‖^2≤_
  rw [centralEmbed_norm,hD]
  simp only [hw,Finset.sum_add_distrib]
  have hW : 0≤∑ i : Fin 3,‖spectralGraphWeight (torusRate s) (centralAmbientT s i (centralEmbedL s f))‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hge := centralCoercivityBase_ge
  dsimp only [centralAmbientEnergy]
  have hcoef : centralCoercivityBase=1+centralPoincareConstant+
      3*(centralTraceConstant*(192+2*centralPoincareConstant)) := by unfold centralCoercivityBase; ring
  have hWW := mul_le_mul_of_nonneg_right hge hW
  rw [one_mul] at hWW
  rw [hcoef] at hWW ⊢
  nlinarith only [hP,hsum,hWW]

lemma central_smooth_projected_bound (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    ‖centralAmbientQ s (centralEmbedL s f)‖^2≤
      (‖centralAmbientQ s‖^2*centralCoercivityBase)*centralAmbientEnergy s (centralEmbedL s f) := by
  let g : centralSmoothFunctions := f-centralAnchorAverage 0 f • centralSmoothOne
  have hh : centralAmbientQ s (centralEmbedL s g)=centralAmbientQ s (centralEmbedL s f) := by
    have hg : centralEmbedL s g=centralEmbedL s f-centralAnchorAverage 0 f • centralAmbientOne s := by
      dsimp [g,centralAmbientOne]
      simp only [map_sub,map_smul]
    rw [hg,centralAmbientQ_shift]
  have hn := (centralAmbientQ s).le_opNorm (centralEmbedL s g)
  have hn2 := mul_self_le_mul_self (norm_nonneg _) hn
  rw [hh] at hn2
  have hb := central_smooth_anchor_norm s f
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖centralAmbientQ s‖)
  nlinarith only [hn2,hm]

end ScalarConductivity

end

end OAI
