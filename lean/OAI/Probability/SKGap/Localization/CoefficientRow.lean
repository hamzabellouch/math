import Mathlib
import OAI.Probability.SKGap.Localization.LocalCoefficient
import OAI.Probability.SKGap.Localization.Operation

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma row_vectorNorm_le_opNorm (D : Interaction n) (i : Fin n) :
    vectorNorm (D i) ≤ SKGap.opNorm D := by
  have h0 : 0≤SKGap.opNorm D := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq h0
  simp only [←sq,vectorNorm_sq]
  exact SKGap.SourceError.matrix_row_square_le D i

lemma local_argument_row_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (x : Spin n) (i : Fin n) :
    vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) ≤
      (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖) := by
  have hQ (l : ι) : vectorNorm (fun k=>|derivativeMatrix (H l) x i k|)≤SKGap.opNorm (derivativeMatrix (H l) x) := by
    rw [vectorNorm_abs]; exact row_vectorNorm_le_opNorm _ _
  have hT (α : κ) : vectorNorm (fun k=>|halfDiff k (θ α) x|)=‖derivativeVector (θ α) x‖ := by
    rw [vectorNorm_abs]; rfl
  calc
    _ ≤ vectorNorm (fun k=>(∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|)) :=
      vectorNorm_mono fun k=>by
        have hp : 0≤(∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|) :=
          add_nonneg (Finset.sum_nonneg fun _ _=>abs_nonneg _) (Finset.sum_nonneg fun _ _=>abs_nonneg _)
        simpa only [abs_of_nonneg (norm_nonneg _),abs_of_nonneg hp] using local_argument_bound H θ x i k
    _ ≤ vectorNorm (fun k=>∑l,|derivativeMatrix (H l) x i k|)+
        vectorNorm (fun k=>∑α,|halfDiff k (θ α) x|) := vectorNorm_add _ _
    _ ≤ (∑l,vectorNorm (fun k=>|derivativeMatrix (H l) x i k|))+
        ∑α,vectorNorm (fun k=>|halfDiff k (θ α) x|) := by
      apply add_le_add
      · convert! vectorNorm_sum (fun l k=>|derivativeMatrix (H l) x i k|) using 1
        congr 1; ext k; simp
      · convert! vectorNorm_sum (fun α k=>|halfDiff k (θ α) x|) using 1
        congr 1; ext k; simp
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun l _=>hQ l) (by simp only [hT]; rfl)

lemma coefficient_row_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i : Fin n) {L : ℝ} (hL : 0≤L)
    (hF : ∀k t, t∈Set.Icc (0:ℝ) 1→HasFDerivAt (F i)
      (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (hBound : ∀k t, t∈Set.Icc (0:ℝ) 1→
      ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))‖≤L) :
    vectorNorm (derivativeMatrix (coefficient H θ F) x i) ≤
      L*((∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)) := by
  calc
    _ ≤ vectorNorm (fun k=>L*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) :=
      vectorNorm_mono fun k=>by
        rw [abs_of_nonneg (mul_nonneg hL (norm_nonneg _))]
        exact coefficient_lipschitz k (fun y=>localArgs H θ y i) x (F i) (F' i) hL (hF k) (hBound k)
    _ = L*vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) := by
      convert! vectorNorm_smul L (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) using 1
      rw [abs_of_nonneg hL]
    _ ≤ _ := mul_le_mul_of_nonneg_left (local_argument_row_bound H θ x i) hL

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

structure SmallBound (U : VectorFields n) (x : Spin n) (C : ℝ) : Prop where
  nonneg : 0≤C
  size : vectorNorm (U x)≤C
  derivative : ‖derivativeMatrix U x‖≤C

lemma derivativeMatrix_add (U V : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>U x i+V x i) x=derivativeMatrix U x+derivativeMatrix V x := by
  ext i k; simp only [derivativeMatrix,halfDiff,Matrix.add_apply]; ring

lemma derivativeMatrix_sum {ι : Type*} [Fintype ι] (U : ι→VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>∑l,U l x i) x=∑l,derivativeMatrix (U l) x := by
  ext i k; simp only [Matrix.sum_apply,derivativeMatrix,halfDiff_sum]

lemma SmallBound.mono {U : VectorFields n} {x : Spin n} {C D : ℝ}
    (h : SmallBound U x C) (hCD : C≤D) : SmallBound U x D :=
  ⟨h.nonneg.trans hCD,h.size.trans hCD,h.derivative.trans hCD⟩

lemma SmallBound.seed (s : Fin n→ℝ) (x : Spin n) :
    SmallBound (fun _=>s) x (vectorNorm s) := by
  refine ⟨vectorNorm_nonneg _,le_rfl,?_⟩
  have he : derivativeMatrix (fun _=>s) x=0 := by ext i k; simp [derivativeMatrix,halfDiff]
  rw [he,norm_zero]; exact vectorNorm_nonneg _

lemma SmallBound.add {U V : VectorFields n} {x : Spin n} {C D : ℝ}
    (hU : SmallBound U x C) (hV : SmallBound V x D) :
    SmallBound (fun x i=>U x i+V x i) x (C+D) := by
  refine ⟨add_nonneg hU.nonneg hV.nonneg,(vectorNorm_add _ _).trans (add_le_add hU.size hV.size),?_⟩
  rw [derivativeMatrix_add]
  exact (norm_add_le _ _).trans (add_le_add hU.derivative hV.derivative)

lemma SmallBound.smul {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (c : ℝ) : SmallBound (fun x i=>c*U x i) x (|c| *C) := by
  refine ⟨mul_nonneg (abs_nonneg _) hU.nonneg,?_,?_⟩
  · calc
      _ = |c| *vectorNorm (U x) := vectorNorm_smul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hU.size (abs_nonneg _)
  · rw [derivativeMatrix_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hU.derivative (abs_nonneg _)

lemma SmallBound.sub {U V : VectorFields n} {x : Spin n} {C D : ℝ}
    (hU : SmallBound U x C) (hV : SmallBound V x D) :
    SmallBound (fun x i=>U x i-V x i) x (C+D) := by
  simpa only [abs_neg,abs_one,one_mul,neg_one_mul,sub_eq_add_neg] using hU.add (hV.smul (-1))

lemma SmallBound.sum {ι : Type*} [Fintype ι] {U : ι→VectorFields n} {x : Spin n} {C : ι→ℝ}
    (hU : ∀l,SmallBound (U l) x (C l)) :
    SmallBound (fun x i=>∑l,U l x i) x (∑l,C l) := by
  refine ⟨Finset.sum_nonneg fun l _=>(hU l).nonneg,?_,?_⟩
  · have h:= (vectorNorm_sum (fun l=>U l x)).trans (Finset.sum_le_sum fun l _=>(hU l).size)
    convert! h using 1
    congr 1; ext i; simp
  · rw [derivativeMatrix_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _=>(hU l).derivative)

lemma SmallBound.coefficient {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (a : VectorFields n) {A R : ℝ}
    (hA : 0≤A) (hR : 0≤R) (ha : ∀i,|a x i|≤A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    SmallBound (fun x i=>a x i*U x i) x (C*(A+3*R)) := by
  refine ⟨mul_nonneg hU.nonneg (by positivity),?_,?_⟩
  · exact ((vectorNorm_mul _ _ hA ha).trans (mul_le_mul_of_nonneg_left hU.size hA)).trans
      (by nlinarith [mul_nonneg hU.nonneg hR])
  · calc
      _ ≤ A*‖derivativeMatrix U x‖+R*vectorNorm (U x)+2*R*‖derivativeMatrix U x‖ :=
        source_frobenius a U x hA hR ha hda
      _ ≤ A*C+R*C+2*R*C := add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hU.derivative hA) (mul_le_mul_of_nonneg_left hU.size hR))
        (mul_le_mul_of_nonneg_left hU.derivative (by positivity))
      _ = _ := by ring

lemma SmallBound.linear {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (J : Interaction n) :
    SmallBound (fun x=>J.mulVec (U x)) x (SKGap.opNorm J*C) := by
  refine ⟨mul_nonneg (norm_nonneg _) hU.nonneg,
    (vectorNorm_matrix_mul _ _).trans (mul_le_mul_of_nonneg_left hU.size (norm_nonneg _)),?_⟩
  have he : derivativeMatrix (fun x=>J.mulVec (U x)) x=J*derivativeMatrix U x := by
    convert! derivativeMatrix_linear J U (fun _=>0) x using 1
    simp only [zero_add]; rfl
  rw [he]
  exact (SKGap.frobenius_mul_le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hU.derivative (norm_nonneg _))

lemma SmallBound.primaryCorrection {U : VectorFields n} {x : Spin n} {C P : ℝ}
    (hU : SmallBound U x C) (m : VectorFields n) (hn : 0<n) (hP : 0≤P)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤P) :
    SmallBound (fun y i=>siteMean U y*m y i) x (C*(1+3*P)) := by
  refine ⟨mul_nonneg hU.nonneg (by positivity),?_,
    primary_mean_frobenius U m x hn hU.nonneg hP hU.size hU.derivative hm hdm⟩
  exact ((primary_mean_size U m x hn hm).trans hU.size).trans (by nlinarith [mul_nonneg hU.nonneg hP])

lemma SmallBound.auxiliaryCorrection {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (a : VectorFields n) {A R : ℝ}
    (hA : 0≤A) (hR : 0≤R) (ha : ∀i,|a x i|≤A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    SmallBound (fun y i=>siteMean a y*U y i) x (C*(A+3*R)) := by
  apply hU.coefficient (fun x _=>siteMean a x) hA hR (fun _=>coefficient_mean_value a x hA ha)
  intro i
  have H:=pow_le_pow_left₀ (norm_nonneg _) (coefficient_mean_difference a x hR hda) 2
  simpa only [derivativeMatrix,derivativeVector,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using H

end SKGapCutoff.Recipe

end
end

end OAI
