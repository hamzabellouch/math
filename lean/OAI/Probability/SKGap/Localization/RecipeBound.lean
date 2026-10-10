import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryRecipe

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix

def recipeBudget (c S : ℝ) (a : ℕ) : ℝ := c*(S+∑b:Fin a,recipeBudget c S b)
termination_by a

lemma recipeBudget_nonneg {c S : ℝ} (hc : 0≤c) (hS : 0≤S) (a : ℕ) : 0≤recipeBudget c S a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    rw [recipeBudget]
    exact mul_nonneg hc (add_nonneg hS (Finset.sum_nonneg fun b _=>ih b b.isLt))

def recipeCost (A R L P j : ℝ) (d : ℕ) : ℝ :=
  (A+3*R)*(1+L+|j| *((d:ℝ)*(1+3*P)+1))

lemma recipeCost_nonneg {A R L P j : ℝ} {d : ℕ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) :
    0≤recipeCost A R L P j d := by unfold recipeCost; positivity

lemma recipeCost_ge {A R L P j : ℝ} {d : ℕ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) :
    A+3*R ≤ recipeCost A R L P j d := by
  have hT : 0≤A+3*R := by positivity
  have hd : 0≤|j| *((d:ℝ)*(1+3*P)+1) := by positivity
  unfold recipeCost
  nlinarith [mul_nonneg hT hL,mul_nonneg hT hd]

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

theorem evaluation_small (N : ℕ) (x : Spin n) (hn : 0<n) {A R L P S : ℝ}
    (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) (hS : 0≤S)
    (hJ : SKGap.opNorm D.J≤L) (hseed : (∑s,vectorNorm (D.seed s))≤S)
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (hs : ∀a≤N,∀s,CoefficientBound (D.seedCoefficient a s) x A R)
    (ha : ∀a≤N,∀b,CoefficientBound (D.auxCoefficient a b) x A R)
    (hsp : ∀a≤N,∀l s,CoefficientBound (D.seedPartial a l s) x A R)
    (hap : ∀a≤N,∀l b,CoefficientBound (D.auxPartial a l b) x A R) :
    ∀a≤N,
      SmallBound (D.source a) x (recipeBudget (recipeCost A R L P D.j (Fintype.card ι)) S a) ∧
      SmallBound (D.auxiliary a) x (recipeBudget (recipeCost A R L P D.j (Fintype.card ι)) S a) ∧
      ∀l,SmallBound (D.sourcePartial a l) x (recipeBudget (recipeCost A R L P D.j (Fintype.card ι)) S a) := by
  let c:=recipeCost A R L P D.j (Fintype.card ι)
  have hc : 0≤c := recipeCost_nonneg hA hR hL hP
  have hT : 0≤A+3*R := by positivity
  have hcg : A+3*R≤c := recipeCost_ge hA hR hL hP
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro haN
    let B : Fin a→ℝ := fun b=>recipeBudget c S b
    let I : ℝ := S+∑b,B b
    let Z : ℝ := I*(A+3*R)
    have hB : ∀b,0≤B b := fun b=>recipeBudget_nonneg hc hS b
    have hI : 0≤I := add_nonneg hS (Finset.sum_nonneg fun b _=>hB b)
    have hY : ∀b:Fin a,SmallBound (D.auxiliary b) x (B b) := fun b=>(ih b b.isLt (b.isLt.le.trans haN)).2.1
    have hW : ∀b:Fin a,SmallBound (D.source b) x (B b) := fun b=>(ih b b.isLt (b.isLt.le.trans haN)).1
    have hw : SmallBound (D.sourceOf a (fun b=>D.auxiliary b)) x Z :=
      (D.sourceOf_bound a _ x B hY (hs a haN) (ha a haN)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,B b) ≤ I from add_le_add hseed le_rfl) hT)
    have hp : ∀l,SmallBound (D.partialOf a l (fun b=>D.auxiliary b)) x Z := fun l=>
      (D.partialOf_bound a l _ x B hY (hsp a haN l) (hap a haN l)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,B b) ≤ I from add_le_add hseed le_rfl) hT)
    have hZ : Z≤recipeBudget c S a := by
      rw [recipeBudget]
      exact (mul_le_mul_of_nonneg_left hcg hI).trans_eq (by dsimp [I,B]; ring)
    have hf:=D.fieldOf_bound a (fun b=>D.source b) (fun b=>D.auxiliary b) x hn B hL hP hJ hw hp hW hm hdm (ha a haN)
    have hfC : (L*Z+|D.j| *((Fintype.card ι:ℝ)*(Z*(1+3*P))))+
          |D.j| *((∑b,B b)*(A+3*R))≤recipeBudget c S a := by
      rw [recipeBudget]
      change _ ≤ c*I
      dsimp [c,recipeCost,Z,I]
      have h1 : 0≤(S+∑b,B b)*(A+3*R) := mul_nonneg hI hT
      have h2 : 0≤|D.j| *(S*(A+3*R)) := mul_nonneg (abs_nonneg _) (mul_nonneg hS hT)
      nlinarith only [h1,h2]
    refine ⟨?_,?_,?_⟩
    · rw [D.source_eq]; exact hw.mono hZ
    · rw [D.auxiliary_eq]; exact hf.mono hfC
    · intro l; exact (hp l).mono hZ

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
