import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiNormAlgebra
import OAI.Geometry.PrescribedPotential.CompactHomogeneousBounds

namespace OAI

/-! Calabi Residual Bound. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def ricciRight (H : Matrix (Fin n) (Fin n) ℂ) (T : ConnectionTensor n) : ConnectionTensor n :=
  fun i => T i*H + ∑ q, H q i • T q

def ricciLeft (H : Matrix (Fin n) (Fin n) ℂ) (T : ConnectionTensor n) : ConnectionTensor n :=
  fun i => H*T i

def calabiResidual (H : Matrix (Fin n) (Fin n) ℂ) (D T : ConnectionTensor n) : ℝ :=
  (tensorPairAt 1 1 (D-ricciRight H T) T + tensorPairAt 1 1 T (D-ricciLeft H T)).re

lemma continuous_ricciRight : Continuous
    (fun q : Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n => ricciRight q.1 q.2) := by
  apply continuous_pi
  intro i
  apply Continuous.add
  · exact ((continuous_apply i).comp continuous_snd).mul continuous_fst
  · apply continuous_finsetSum
    intro q _
    exact ((continuous_apply_apply q i).comp continuous_fst).smul
      ((continuous_apply q).comp continuous_snd)

lemma continuous_ricciLeft : Continuous
    (fun q : Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n => ricciLeft q.1 q.2) := by
  exact continuous_pi (fun i => continuous_fst.mul ((continuous_apply i).comp continuous_snd))

lemma ricciRight_smul (H : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (T : ConnectionTensor n) :
    ricciRight H (r • T) = r • ricciRight H T := by
  funext i
  simp only [ricciRight,Pi.smul_apply,smul_mul_assoc,smul_add,Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact smul_comm _ _ _

lemma ricciLeft_smul (H : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (T : ConnectionTensor n) :
    ricciLeft H (r • T) = r • ricciLeft H T := by
  funext i
  change H*(r • T i) = r • (H*T i)
  exact mul_smul_comm _ _ _

lemma calabiResidual_homogeneous (H : Matrix (Fin n) (Fin n) ℂ)
    (D T : ConnectionTensor n) (r : ℝ) :
    calabiResidual H (r • D) (r • T) = r^2*calabiResidual H D T := by
  unfold calabiResidual
  rw [ricciRight_smul,ricciLeft_smul,← smul_sub,← smul_sub,tensorPairAt_one_smul,tensorPairAt_one_smul]
  simp only [← mul_add,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

lemma continuous_calabiResidual : Continuous
    (fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n =>
      calabiResidual p.1.1 p.1.2 p.2) := by
  have hH := continuous_fst.comp (continuous_fst (X := Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n)
    (Y := ConnectionTensor n))
  have hD := continuous_snd.comp (continuous_fst (X := Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n)
    (Y := ConnectionTensor n))
  have hT := continuous_snd (X := Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) (Y := ConnectionTensor n)
  have hR : Continuous (fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n =>
      ricciRight p.1.1 p.2) := continuous_ricciRight.comp (f := fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n => (p.1.1,p.2)) (hH.prodMk hT)
  have hL : Continuous (fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n =>
      ricciLeft p.1.1 p.2) := continuous_ricciLeft.comp (f := fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n => (p.1.1,p.2)) (hH.prodMk hT)
  have hA : Continuous (fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n =>
      tensorPairAt 1 1 (p.1.2-ricciRight p.1.1 p.2) p.2) :=
    tensorPairAt_one_continuous.comp (f := fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n => (p.1.2-ricciRight p.1.1 p.2,p.2))
      ((hD.sub hR).prodMk hT)
  have hB : Continuous (fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n =>
      tensorPairAt 1 1 p.2 (p.1.2-ricciLeft p.1.1 p.2)) :=
    tensorPairAt_one_continuous.comp (f := fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n => (p.2,p.1.2-ricciLeft p.1.1 p.2))
      (hT.prodMk (hD.sub hL))
  exact Complex.continuous_re.comp (f := fun p : (Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n) × ConnectionTensor n =>
    tensorPairAt 1 1 (p.1.2-ricciRight p.1.1 p.2) p.2 +
      tensorPairAt 1 1 p.2 (p.1.2-ricciLeft p.1.1 p.2)) (hA.add hB)

lemma tensorSquare_controls_norm : ∃ δ : ℝ, 0 < δ ∧ ∀ T : ConnectionTensor n, δ*‖T‖^2 ≤ tensorSquare T := by
  obtain ⟨δ,hδ,h⟩ := compact_homogeneous_positive (K := (univ : Set Unit)) isCompact_univ
    (fun (_ : Unit) (T : ConnectionTensor n) => tensorSquare T)
    (continuous_tensorSquare.comp continuous_snd).continuousOn
    (fun _ _ _ hT => tensorSquare_pos hT) (fun _ _ r T => tensorSquare_smul r T)
  exact ⟨δ,hδ,fun T => h () (mem_univ _) T⟩

lemma calabiResidual_compact_bound {X : Type*} [TopologicalSpace X] {L : Set X} (hL : IsCompact L)
    (H : X → Matrix (Fin n) (Fin n) ℂ) (D : X → ConnectionTensor n)
    (hH : ContinuousOn H L) (hD : ContinuousOn D L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ T : ConnectionTensor n,
      |calabiResidual (H x) (D x) T| ≤ C*(1+tensorSquare T) := by
  let E := ℝ × ConnectionTensor n
  let F : X → E → ℝ := fun x v => calabiResidual (H x) (v.1 • D x) v.2
  have hc : ContinuousOn (fun q : X × E => F q.1 q.2) (L ×ˢ Metric.closedBall 0 1) := by
    have hx := continuous_fst.continuousOn (s := L ×ˢ Metric.closedBall (0:E) 1)
    have h1 := (continuous_fst.comp continuous_snd).continuousOn
      (s := L ×ˢ Metric.closedBall (0:E) 1)
    have h2 := (continuous_snd.comp continuous_snd).continuousOn
      (s := L ×ˢ Metric.closedBall (0:E) 1)
    exact continuous_calabiResidual.comp_continuousOn
      (f := fun q : X × E => ((H q.1,q.2.1 • D q.1),q.2.2))
      (((hH.comp hx (fun _ h => h.1)).prodMk (h1.smul (hD.comp hx (fun _ h => h.1)))).prodMk h2)
  have hh (x : X) (_ : x ∈ L) (r : ℝ) (v : E) : F x (r • v) = r^2*F x v := by
    change calabiResidual (H x) ((r*v.1) • D x) (r • v.2) = _
    rw [mul_smul,calabiResidual_homogeneous]
  obtain ⟨B,hB,hbound⟩ := compact_homogeneous_bound hL 2 (by decide) F hc hh
  obtain ⟨δ,hδ,hnorm⟩ := tensorSquare_controls_norm (n := n)
  refine ⟨B*(1+δ⁻¹),mul_nonneg hB (by positivity),?_⟩
  intro x hx T
  have hb := hbound x hx (1,T)
  change |calabiResidual (H x) ((1:ℝ) • D x) T| ≤ B*‖((1:ℝ),T)‖^2 at hb
  rw [one_smul] at hb
  have hp : ‖((1:ℝ),T)‖^2 ≤ 1+‖T‖^2 := by
    rw [Prod.norm_def,Real.norm_eq_abs,abs_one]
    rcases le_total 1 ‖T‖ with ht | ht
    · rw [max_eq_right ht]
      linarith
    · rw [max_eq_left ht]
      nlinarith [sq_nonneg ‖T‖]
  have ht : ‖T‖^2 ≤ δ⁻¹*tensorSquare T := by
    have hh := mul_le_mul_of_nonneg_left (hnorm T) (inv_nonneg.mpr hδ.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ hδ.ne',one_mul] using hh
  have hs := tensorSquare_nonneg T
  have hh : B*(1+‖T‖^2) ≤ B*(1+δ⁻¹)*(1+tensorSquare T) := by
    have hh : 1+‖T‖^2 ≤ (1+δ⁻¹)*(1+tensorSquare T) := by
      have hd : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
      nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hB
  exact hb.trans ((mul_le_mul_of_nonneg_left hp hB).trans hh)
end KaehlerCalculus

end
end

end OAI
