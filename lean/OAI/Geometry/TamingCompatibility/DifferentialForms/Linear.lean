import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ContDiffApply

namespace OAI

noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {E D P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
  {k : ℕ}

def oneLinear (a : Form (E := E) 1) : E →L[ℝ] ℝ := (ofSubsingletonLIE (0 : Fin 1)).symm a
lemma oneLinear_apply (a : Form (E := E) 1) (u : E) : oneLinear a u = a ![u] := by
  change a (fun _ => u) = a ![u]
  congr 1
  ext i
  fin_cases i
  rfl

def wedgeTwo (a b : Form (E := E) 2) : Form (E := E) 4 :=
  volumeSquare (a+b) - volumeSquare a - volumeSquare b

lemma volumeSquare_apply_vec (F : Form (E := E) 2) (v : Fin 4 → E) :
    volumeSquare F v = F ![v 0,v 1] * F ![v 2,v 3] -
      F ![v 0,v 2] * F ![v 1,v 3] + F ![v 0,v 3] * F ![v 1,v 2] := by
  have hv : v = ![v 0,v 1,v 2,v 3] := by ext i; fin_cases i <;> rfl
  nth_rw 1 [hv]
  exact volumeSquare_apply F _ _ _ _

lemma volumeSquare_comp (F : Form (E := E) 2) (L : D →L[ℝ] E) :
    (volumeSquare F).compContinuousLinearMap L = volumeSquare (F.compContinuousLinearMap L) := by
  ext v
  rw [compContinuousLinearMap_apply,volumeSquare_apply_vec,volumeSquare_apply_vec]
  have he (u w : D) : (F.compContinuousLinearMap L) ![u,w] = F ![L u,L w] := by
    change F (L ∘ ![u,w]) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  simp only [Function.comp_apply,he]

lemma wedgeTwo_comp (a b : Form (E := E) 2) (L : D →L[ℝ] E) :
    (wedgeTwo a b).compContinuousLinearMap L = wedgeTwo (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) := by
  have hs (a b : Form (E := E) 4) :
      (a-b).compContinuousLinearMap L = a.compContinuousLinearMap L - b.compContinuousLinearMap L := by
    ext v
    rfl
  have ha : (a+b).compContinuousLinearMap L = a.compContinuousLinearMap L+b.compContinuousLinearMap L := by
    ext v
    rfl
  simp only [wedgeTwo,hs,volumeSquare_comp,ha]

lemma wedgeTwo_apply (a b : Form (E := E) 2) (u v w z : E) :
    wedgeTwo a b ![u,v,w,z] = a ![u,v] * b ![w,z] - a ![u,w] * b ![v,z] +
      a ![u,z] * b ![v,w] + a ![w,z] * b ![u,v] - a ![v,z] * b ![u,w] + a ![v,w] * b ![u,z] := by
  simp only [wedgeTwo, ContinuousAlternatingMap.sub_apply,volumeSquare_apply,
    ContinuousAlternatingMap.add_apply]
  ring

lemma wedgeOne_apply_four (a : E →L[ℝ] ℝ) (b : Form (E := E) 3) (u v w z : E) :
    wedgeOne a b ![u,v,w,z] = a u * b ![v,w,z] - a v * b ![u,w,z] +
      a w * b ![u,v,z] - a z * b ![u,v,w] := by
  rw [wedgeOne, alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 4) ![u,v,w,z] = ![v,w,z] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 4) ![u,v,w,z] = ![u,w,z] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 4) ![u,v,w,z] = ![u,v,z] := by ext i; fin_cases i <;> rfl
  have h3 : Fin.removeNth (3 : Fin 4) ![u,v,w,z] = ![u,v,w] := by ext i; fin_cases i <;> rfl
  simp [Fin.sum_univ_succ,h0,h1,h2,h3,ContinuousLinearMap.smulRight_apply,sub_eq_add_neg]
  ring

lemma wedgeOne_comp (a : E →L[ℝ] ℝ) (b : Form (E := E) k) (L : D →L[ℝ] E) :
    (wedgeOne a b).compContinuousLinearMap L = wedgeOne (a ∘L L) (b.compContinuousLinearMap L) := by
  ext v
  simp only [wedgeOne,compContinuousLinearMap_apply,alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,Function.comp_apply]
  congr 1

lemma oneLinear_comp (a : Form (E := E) 1) (L : D →L[ℝ] E) :
    oneLinear (a.compContinuousLinearMap L) = oneLinear a ∘L L := by
  ext u
  rfl

lemma wedgeOne_contDiffOn {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ E)
    {U : Set P} {n : WithTop ℕ∞} {a : P → Form (E := E) 1} {b : P → Form (E := E) 2}
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U) :
    ContDiffOn ℝ n (fun x => wedgeOne (oneLinear (a x)) (b x)) U := by
  apply FormSmooth.contDiffOn_of_basis bas
  intro v
  have hv : (fun i => bas (v i)) = ![bas (v 0),bas (v 1),bas (v 2)] := by ext i; fin_cases i <;> rfl
  simp_rw [hv,wedgeOne_apply_three,oneLinear_apply]
  have h₁ (w : Fin 1 → E) := (ContinuousAlternatingMap.apply ℝ E ℝ w).contDiff.comp_contDiffOn ha
  have h₂ (w : Fin 2 → E) := (ContinuousAlternatingMap.apply ℝ E ℝ w).contDiff.comp_contDiffOn hb
  exact ((h₁ _).mul (h₂ _)).sub ((h₁ _).mul (h₂ _)) |>.add ((h₁ _).mul (h₂ _))

lemma extDeriv_one (a : E → Form (E := E) 1) (x u v : E) :
    extDeriv a x ![u,v] = (fderiv ℝ a x u) ![v] - (fderiv ℝ a x v) ![u] := by
  rw [extDeriv,alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 2) ![u,v] = ![v] := by ext i; fin_cases i; rfl
  have h1 : Fin.removeNth (1 : Fin 2) ![u,v] = ![u] := by ext i; fin_cases i; rfl
  simp [Fin.sum_univ_succ,h0,h1,sub_eq_add_neg]

lemma extDeriv_two (b : E → Form (E := E) 2) (x u v w : E) :
    extDeriv b x ![u,v,w] = (fderiv ℝ b x u) ![v,w] -
      (fderiv ℝ b x v) ![u,w] + (fderiv ℝ b x w) ![u,v] := by
  rw [extDeriv,alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 3) ![u,v,w] = ![v,w] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 3) ![u,v,w] = ![u,w] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 3) ![u,v,w] = ![u,v] := by ext i; fin_cases i <;> rfl
  simp [Fin.sum_univ_succ,h0,h1,h2,sub_eq_add_neg]
  ring

lemma extDeriv_three (b : E → Form (E := E) 3) (x u v w z : E) :
    extDeriv b x ![u,v,w,z] = (fderiv ℝ b x u) ![v,w,z] -
      (fderiv ℝ b x v) ![u,w,z] + (fderiv ℝ b x w) ![u,v,z] - (fderiv ℝ b x z) ![u,v,w] := by
  rw [extDeriv,alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 4) ![u,v,w,z] = ![v,w,z] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 4) ![u,v,w,z] = ![u,w,z] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 4) ![u,v,w,z] = ![u,v,z] := by ext i; fin_cases i <;> rfl
  have h3 : Fin.removeNth (3 : Fin 4) ![u,v,w,z] = ![u,v,w] := by ext i; fin_cases i <;> rfl
  simp [Fin.sum_univ_succ,h0,h1,h2,h3,sub_eq_add_neg]
  ring

lemma fderiv_eval {k : ℕ} {a : E → Form (E := D) k} {x : E}
    (ha : DifferentiableAt ℝ a x) (v : Fin k → D) (u : E) :
    fderiv ℝ (fun y => a y v) x u = (fderiv ℝ a x u) v := by
  exact congrArg (fun L : E →L[ℝ] ℝ => L u)
    (((ContinuousAlternatingMap.apply ℝ D ℝ v).hasFDerivAt.comp x ha.hasFDerivAt).fderiv)

def wedgeOneBilinear : Form (E := E) 1 →L[ℝ] Form (E := E) k →L[ℝ] Form (E := E) (k+1) :=
  ((ContinuousLinearMap.compL ℝ (Form (E := E) k) (E →L[ℝ] Form (E := E) k)
    (Form (E := E) (k+1))) (alternatizeUncurryFinCLM ℝ E ℝ)) ∘L
    ContinuousLinearMap.smulRightL ℝ E (Form (E := E) k) ∘L
      (ofSubsingletonLIE (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma wedgeOneBilinear_apply (a : Form (E := E) 1) (b : Form (E := E) k) :
    (wedgeOneBilinear (E := E) (k := k)) a b = wedgeOne (oneLinear a) b := rfl

lemma fderiv_wedgeOne {a : E → Form (E := E) 1} {b : E → Form (E := E) k}
    {x : E} (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (u : E) :
    fderiv ℝ (fun y => wedgeOne (oneLinear (a y)) (b y)) x u =
      wedgeOne (oneLinear (a x)) (fderiv ℝ b x u) +
      wedgeOne (oneLinear (fderiv ℝ a x u)) (b x) := by
  exact congrArg (fun L : E →L[ℝ] Form (E := E) (k+1) => L u)
    ((wedgeOneBilinear (E := E) (k := k)).hasFDerivAt_of_bilinear ha.hasFDerivAt hb.hasFDerivAt).fderiv

lemma extDeriv_wedgeOne {a : E → Form (E := E) 1} {b : E → Form (E := E) 2}
    {x : E} (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    extDeriv (fun y => wedgeOne (oneLinear (a y)) (b y)) x =
      wedgeTwo (extDeriv a x) (b x) - wedgeOne (oneLinear (a x)) (extDeriv b x) := by
  ext v
  have hv : v = ![v 0,v 1,v 2,v 3] := by ext i; fin_cases i <;> rfl
  rw [hv,extDeriv_three,ContinuousAlternatingMap.sub_apply,wedgeTwo_apply,wedgeOne_apply_four]
  simp only [fderiv_wedgeOne ha hb,ContinuousAlternatingMap.add_apply,
    wedgeOne_apply_three,oneLinear_apply,extDeriv_one,extDeriv_two]
  ring

end TamingCompatibility.ExteriorForms

end

end OAI
