import Mathlib

namespace OAI

noncomputable section
open scoped Manifold ContDiff

namespace TamingCompatibility

end TamingCompatibility
end

section

section

section

section

noncomputable section
namespace TamingCompatibility.FormSmooth
open ContinuousAlternatingMap
variable {E D F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : WithTop ℕ∞} {U : Set D}

lemma contDiffOn_apply {k : ℕ} {α : D → E [⋀^Fin k]→L[ℝ] F} {v : Fin k → D → E}
    (hα : ContDiffOn ℝ n α U) (hv : ∀ i, ContDiffOn ℝ n (v i) U) :
    ContDiffOn ℝ n (fun x => α x (fun i => v i x)) U := by
  induction k with
  | zero =>
    convert (ContinuousAlternatingMap.apply ℝ E F (Fin.elim0 : Fin 0 → E)).contDiff.comp_contDiffOn hα using 1
    ext x
    change α x (fun i => v i x) = α x Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  | succ k ih =>
    let a : D → E [⋀^Fin k]→L[ℝ] F := fun x => (α x).curryLeft (v 0 x)
    have ha : ContDiffOn ℝ n a U := by
      exact (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).contDiff.comp_contDiffOn hα).clm_apply (hv 0))
    have h := ih ha (fun i => hv i.succ)
    convert h using 1
    ext x
    change α x (fun i => v i x) = α x (Matrix.vecCons (v 0 x) (fun i => v i.succ x))
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma contDiffOn_apply_two {α : D → E [⋀^Fin 2]→L[ℝ] F} {v w : D → E}
    (hα : ContDiffOn ℝ n α U) (hv : ContDiffOn ℝ n v U) (hw : ContDiffOn ℝ n w U) :
    ContDiffOn ℝ n (fun x => α x ![v x,w x]) U := by
  have h : ∀ i : Fin 2, ContDiffOn ℝ n (![v,w] i) U := by
    intro i
    fin_cases i
    · exact hv
    · exact hw
  convert contDiffOn_apply hα h using 1
  ext x
  congr 1
  ext i
  fin_cases i <;> rfl

lemma contDiffOn_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {k : ℕ} {α : D → E [⋀^Fin k]→L[ℝ] ℝ}
    (h : ∀ a : Fin k → ι, ContDiffOn ℝ n (fun x => α x (fun i => b (a i))) U) :
    ContDiffOn ℝ n α U := by
  let L : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ((Fin k → ι) → ℝ) :=
    ContinuousLinearMap.pi (fun a => ContinuousAlternatingMap.apply ℝ E ℝ (fun i => b (a i)))
  have hL : Function.Injective L := by
    intro a c hac
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    apply b.ext_alternating
    intro v _
    exact congrArg (fun f => f v) hac
  let R := L.toLinearMap.leftInverse.toContinuousLinearMap
  have hr : ∀ a, R (L a) = a :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hL)
  have hl : ContDiffOn ℝ n (fun x => L (α x)) U := contDiffOn_pi.mpr h
  simpa only [Function.comp_def,hr] using R.contDiff.comp_contDiffOn hl

end TamingCompatibility.FormSmooth
noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {degree : ℕ}

abbrev Form (k : ℕ) := E [⋀^Fin k]→L[ℝ] ℝ

def wedgeOne (a : E →L[ℝ] ℝ) (b : Form (E := E) degree) : Form (E := E) (degree+1) :=
  alternatizeUncurryFin (a.smulRight b)

def wedgeOneRight (b : Form (E := E) degree) :
    (E →L[ℝ] ℝ) →L[ℝ] Form (E := E) (degree+1) :=
  alternatizeUncurryFinCLM ℝ E ℝ ∘L
    (ContinuousLinearMap.smulRightL ℝ E (Form (E := E) degree)).flip b

lemma wedgeOneRight_apply (b : Form (E := E) degree) (a : E →L[ℝ] ℝ) :
    wedgeOneRight b a = wedgeOne a b := rfl

lemma wedgeOne_apply_two (a : E →L[ℝ] ℝ) (b : Form (E := E) 1) (u v : E) :
    wedgeOne a b ![u,v] = a u * b ![v] - a v * b ![u] := by
  rw [wedgeOne, alternatizeUncurryFin_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_one, zero_add, one_smul, neg_smul, add_zero]
  have h0 : Fin.removeNth (0 : Fin 2) ![u,v] = ![v] := by ext i; fin_cases i; rfl
  have h1 : Fin.removeNth (1 : Fin 2) ![u,v] = ![u] := by ext i; fin_cases i; rfl
  change a u * b (Fin.removeNth (0 : Fin 2) ![u,v]) -
    a v * b (Fin.removeNth (1 : Fin 2) ![u,v]) = _
  rw [h0,h1]

lemma wedgeOne_apply_three (a : E →L[ℝ] ℝ) (b : Form (E := E) 2) (u v w : E) :
    wedgeOne a b ![u,v,w] = a u * b ![v,w] - a v * b ![u,w] + a w * b ![u,v] := by
  rw [wedgeOne, alternatizeUncurryFin_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_one, zero_add, one_smul, neg_smul, add_zero]
  have h0 : Fin.removeNth (0 : Fin 3) ![u,v,w] = ![v,w] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 3) ![u,v,w] = ![u,w] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 3) ![u,v,w] = ![u,v] := by ext i; fin_cases i <;> rfl
  simp [h0, h1, h2, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg]
  ring

def volumeSquare (F : Form (E := E) 2) : Form (E := E) 4 :=
  (1/4 : ℝ) • alternatizeUncurryFin
    (wedgeOneRight F ∘L (ofSubsingletonLIE (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L F.curryLeft)

lemma two_swap (F : Form (E := E) 2) (u v : E) : F ![v,u] = -F ![u,v] := by
  have hv : ![u,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,u] := by
    ext i
    fin_cases i <;> simp
  simpa only [hv, ContinuousAlternatingMap.coe_toAlternatingMap] using F.map_swap ![u,v] (by decide : (0 : Fin 2) ≠ 1)

lemma volumeSquare_apply (F : Form (E := E) 2) (u v w z : E) :
    volumeSquare F ![u,v,w,z] = F ![u,v] * F ![w,z] -
      F ![u,w] * F ![v,z] + F ![u,z] * F ![v,w] := by
  rw [volumeSquare, ContinuousAlternatingMap.smul_apply, alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 4) ![u,v,w,z] = ![v,w,z] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 4) ![u,v,w,z] = ![u,w,z] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 4) ![u,v,w,z] = ![u,v,z] := by ext i; fin_cases i <;> rfl
  have h3 : Fin.removeNth (3 : Fin 4) ![u,v,w,z] = ![u,v,w] := by ext i; fin_cases i <;> rfl
  have hv (a b : E) : F (Matrix.vecCons a (fun _ : Fin 1 => b)) = F ![a,b] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  have huv := two_swap F u v
  have huw := two_swap F u w
  have huz := two_swap F u z
  have hvw := two_swap F v w
  have hvz := two_swap F v z
  have hwz := two_swap F w z
  simp [Fin.sum_univ_succ, h0,h1,h2,h3, wedgeOneRight_apply,
    wedgeOne_apply_three, hv, huv,huw,huz,hvw,hvz,hwz]
  ring

end TamingCompatibility.ExteriorForms
noncomputable section

end
end
end
end
end
end
end

end OAI
