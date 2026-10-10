import Mathlib
import OAI.Analysis.Conductivity.Flux.TorusBoxFlux

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma torusCellIntegral_eq_box {T t : ℝ} (hT : 0≤T) {f : Coord3→ℝ}
    (hf : Continuous (fun x : Fin 2→ℝ => f ![t,x 0,x 1])) :
    torusCellIntegral T f t=∫ x in Icc (0:Fin 2→ℝ) (fun _ => T),f ![t,x 0,x 1] := by
  symm
  simpa only [torusCellIntegral,Pi.zero_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
    integral_coord2_Icc (a:=(0:Fin 2→ℝ)) (b:=fun _ => T) (fun _ => hT) hf

lemma torusCellIntegral_add {T t : ℝ} (hT : 0≤T) {f g : Coord3→ℝ}
    (hf : Continuous (fun x : Fin 2→ℝ => f ![t,x 0,x 1]))
    (hg : Continuous (fun x : Fin 2→ℝ => g ![t,x 0,x 1])) :
    torusCellIntegral T (fun x => f x+g x) t=torusCellIntegral T f t+torusCellIntegral T g t := by
  rw [torusCellIntegral_eq_box hT (hf.add hg),torusCellIntegral_eq_box hT hf,
    torusCellIntegral_eq_box hT hg]
  exact integral_add (hf.continuousOn.integrableOn_compact isCompact_Icc)
    (hg.continuousOn.integrableOn_compact isCompact_Icc)

lemma torusCellIntegral_const (T t c : ℝ) : torusCellIntegral T (fun _ => c) t=T^2*c := by
  simp only [torusCellIntegral,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  ring

lemma torusCellIntegral_smul (T t c : ℝ) (f : Coord3→ℝ) :
    torusCellIntegral T (fun x => c*f x) t=c*torusCellIntegral T f t := by
  simp only [torusCellIntegral,intervalIntegral.integral_const_mul]

lemma halfspace_slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ t : ℝ} {f : Coord3→E} (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f {x | δ<x 0}) (ht : δ<t) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Fin 2→ℝ => f ![t,y 0,y 1]) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hc : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Fin 2→ℝ => ![t,y 0,y 1]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact (hf.contDiffAt ((axial_halfspace_open δ).mem_nhds ht)).comp y hc.contDiffAt

end ScalarConductivity

end
end

end OAI
