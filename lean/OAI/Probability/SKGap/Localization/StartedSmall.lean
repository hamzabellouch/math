import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryClosure
import OAI.Probability.SKGap.Matrix.StartedNodeTrace

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
variable {n : ℕ}

def startedBudget (c S B : ℝ) (a : ℕ) : ℝ :=
  c*(S+∑b:Fin a,startedBudget c S B b)+B
termination_by a
lemma startedBudget_nonneg {c S B : ℝ} (hc : 0≤c) (hS : 0≤S) (hB : 0≤B) (a : ℕ) :
    0≤ startedBudget c S B a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    rw [startedBudget]
    exact add_nonneg (mul_nonneg hc (add_nonneg hS (Finset.sum_nonneg fun b _=>ih b b.isLt))) hB
lemma startedBudget_ge {c S B : ℝ} (hc : 0≤c) (hS : 0≤S) (hB : 0≤B) (a : ℕ) :
    B≤ startedBudget c S B a := by
  rw [startedBudget]
  exact le_add_of_nonneg_left (mul_nonneg hc (add_nonneg hS
    (Finset.sum_nonneg fun b _=>startedBudget_nonneg hc hS hB b)))

namespace OrdinaryData
open Primary Matrix
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

theorem started_evaluation_small (w y : VectorFields n) (N : ℕ) (x : Spin n) (hn : 0<n)
    {A R L P S B : ℝ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) (hS : 0≤S) (hB : 0≤B)
    (hw₀ : SmallBound w x B) (hy₀ : SmallBound y x B)
    (hJ : SKGap.opNorm D.J≤L) (hseed : (∑s,vectorNorm (D.seed s))≤S)
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (hs : ∀a≤N,∀s,CoefficientBound (D.seedCoefficient a s) x A R)
    (ha : ∀a≤N,∀b,CoefficientBound (D.auxCoefficient a b) x A R)
    (hsp : ∀a≤N,∀l s,CoefficientBound (D.seedPartial a l s) x A R)
    (hap : ∀a≤N,∀l b,CoefficientBound (D.auxPartial a l b) x A R) :
    ∀a≤N,
      SmallBound (D.startedSource w y a) x (startedBudget (recipeCost A R L P D.j (Fintype.card ι)) S B a) ∧
      SmallBound (D.startedAuxiliary w y a) x (startedBudget (recipeCost A R L P D.j (Fintype.card ι)) S B a) ∧
      ∀l,SmallBound (D.startedPartial w y a l) x (startedBudget (recipeCost A R L P D.j (Fintype.card ι)) S B a) := by
  let c:=recipeCost A R L P D.j (Fintype.card ι)
  have hc : 0≤c:=recipeCost_nonneg hA hR hL hP
  have hT : 0≤A+3*R:=by positivity
  have hcg : A+3*R≤c:=recipeCost_ge hA hR hL hP
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro haN
    let V : Fin a→ℝ:=fun b=>startedBudget c S B b
    let I:=S+∑b,V b
    let Z:=I*(A+3*R)
    have hV : ∀b,0≤V b:=fun b=>startedBudget_nonneg hc hS hB b
    have hI : 0≤I:=add_nonneg hS (Finset.sum_nonneg fun b _=>hV b)
    have hY : ∀b:Fin a,SmallBound (D.startedAuxiliary w y b) x (V b):=
      fun b=>(ih b b.isLt (b.isLt.le.trans haN)).2.1
    have hW : ∀b:Fin a,SmallBound (D.startedSource w y b) x (V b):=
      fun b=>(ih b b.isLt (b.isLt.le.trans haN)).1
    have hw : SmallBound (D.sourceOf a (fun b=>D.startedAuxiliary w y b)) x Z:=
      (D.sourceOf_bound a _ x V hY (hs a haN) (ha a haN)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,V b)≤I from
          add_le_add hseed le_rfl) hT)
    have hp : ∀l,SmallBound (D.partialOf a l (fun b=>D.startedAuxiliary w y b)) x Z:=fun l=>
      (D.partialOf_bound a l _ x V hY (hsp a haN l) (hap a haN l)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,V b)≤I from
          add_le_add hseed le_rfl) hT)
    have hZ : Z≤ startedBudget c S B a:=by
      rw [startedBudget]
      exact (mul_le_mul_of_nonneg_left hcg hI).trans (by dsimp [I,V];nlinarith only [hB])
    have hf:=D.fieldOf_bound a (fun b=>D.startedSource w y b) (fun b=>D.startedAuxiliary w y b)
      x hn V hL hP hJ hw hp hW hm hdm (ha a haN)
    have hfC : (L*Z+|D.j| *((Fintype.card ι:ℝ)*(Z*(1+3*P))))+
        |D.j| *((∑b,V b)*(A+3*R))≤ startedBudget c S B a:=by
      rw [startedBudget]
      change _≤c*I+B
      dsimp [c,recipeCost,Z,I]
      have h1 : 0≤(S+∑b,V b)*(A+3*R):=mul_nonneg hI hT
      have h2 : 0≤|D.j| *(S*(A+3*R)):=mul_nonneg (abs_nonneg _) (mul_nonneg hS hT)
      nlinarith only [h1,h2,hB]
    refine ⟨?_,?_,fun l=>(hp l).mono hZ⟩
    · by_cases ha0:a=0
      · subst a;simpa using hw₀.mono (startedBudget_ge hc hS hB 0)
      · rw [D.startedSource_eq w y (by omega)];exact hw.mono hZ
    · by_cases ha0:a=0
      · subst a;simpa using hy₀.mono (startedBudget_ge hc hS hB 0)
      · rw [D.startedAuxiliary_eq w y (by omega)];exact hf.mono hfC

end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial

namespace LocalConstants
variable (c : LocalConstants)
def startedNormBudget (j : ℝ) (d : ℕ) (B : ℝ) : ℕ→ℝ := startedBudget (recipeCost c.A (c.row d) c.L c.P j d) c.S B
def startedSourceCost (j : ℝ) (d s : ℕ) (B : ℝ) (a : ℕ) : ℝ :=
  (s:ℝ)*(c.C*c.S*c.traceCost d)+(∑b:Fin a,c.C*c.startedNormBudget j d B b*c.traceCost d)+
    (d:ℝ)*(c.startedNormBudget j d B a*c.E)
def startedFieldCost (j : ℝ) (d : ℕ) (B : ℝ) (a : ℕ) : ℝ :=
  (d:ℝ)*(|j| *(c.startedNormBudget j d B a*c.E))+
    |j| *((d:ℝ)*(c.startedNormBudget j d B a*(1+2*c.P))+(∑b:Fin a,3*c.startedNormBudget j d B b*c.row d))
lemma startedNormBudget_nonneg (j : ℝ) (d a : ℕ) {B : ℝ} (hB : 0≤B) : 0≤c.startedNormBudget j d B a :=
  startedBudget_nonneg (recipeCost_nonneg c.A_nonneg (c.row_nonneg d) c.L_nonneg c.P_nonneg) c.S_nonneg hB a
end LocalConstants

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace LocalOrdinaryInput
variable {D : OrdinaryData n ι κ σ} {T : ι→SourceTree (Fin n→ℝ)}
variable {x : Spin n} {N : ℕ} {c : LocalConstants} {w y : VectorFields n} {B : ℝ}
variable (h : LocalOrdinaryInput D T x N c) (hB : 0≤B) (hw₀ : SmallBound w x B) (hy₀ : SmallBound y x B)
include h hB hw₀ hy₀

lemma started_small (a : ℕ) (ha : a≤N) :
    SmallBound (D.startedSource w y a) x (c.startedNormBudget D.j (Fintype.card ι) B a) ∧
    SmallBound (D.startedAuxiliary w y a) x (c.startedNormBudget D.j (Fintype.card ι) B a) ∧
    ∀l,SmallBound (D.startedPartial w y a l) x (c.startedNormBudget D.j (Fintype.card ι) B a) :=
  D.started_evaluation_small w y N x h.dimension c.A_nonneg (c.row_nonneg _) c.L_nonneg c.P_nonneg c.S_nonneg hB hw₀ hy₀
    h.interaction h.seed h.primaryValue h.primaryDerivative h.seed_bound h.aux_bound h.seed_partial_bound h.aux_partial_bound a ha

lemma started_source_control (a : ℕ) (ha : a≤N) :
    TraceControl (D.startedNodeSourceError w y T x a) (c.startedSourceCost D.j (Fintype.card ι) (Fintype.card σ) B a) := by
  let d:=Fintype.card ι
  let W:=c.startedNormBudget D.j d B
  have hn (s : σ) : vectorNorm (D.seed s)≤c.S :=
    (Finset.single_le_sum (fun s _=>vectorNorm_nonneg (D.seed s)) (Finset.mem_univ s)).trans h.seed
  have H:=D.startedNodeSource_control w y T x a c.C_nonneg
    (show 0≤2*(d:ℝ)*c.P by positivity [c.P_nonneg])
    (show 0≤(d:ℝ)*c.P by positivity [c.P_nonneg])
    (show 0≤(d:ℝ)*c.P by positivity [c.P_nonneg]) c.V_nonneg
    (fun b:Fin a=>(h.started_small hB hw₀ hy₀ b (b.isLt.le.trans ha)).2.1) (h.started_small hB hw₀ hy₀ a ha).2.2 h.primaryFieldError
    (h.seedRegular a ha) (h.auxRegular a ha)
    ((parameterIncrement_bound D.θ x).trans h.parameter)
    (primaryIncrement_fourth D.H x c.P_nonneg h.primaryShape)
    (primaryIncrement_row D.H x c.P_nonneg (fun l=>(h.primaryShape l).1))
    (primaryIncrement_diagonal D.H x c.P_nonneg (fun l=>(h.primaryShape l).2.1))
    (show _≤c.traceCost d from add_le_add (add_le_add h.parameter le_rfl) le_rfl)
  apply H.mono
  have hs : (∑s,c.C*vectorNorm (D.seed s)*c.traceCost d)≤(Fintype.card σ:ℝ)*(c.C*c.S*c.traceCost d) :=
    (Finset.sum_le_sum fun s _=>mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hn s) c.C_nonneg) (c.traceCost_nonneg d)).trans_eq (by simp)
  dsimp only [LocalConstants.startedSourceCost]
  have hp : (∑_l:ι,c.startedNormBudget D.j d B a*c.E)=(d:ℝ)*(c.startedNormBudget D.j d B a*c.E) := by simp [d]
  rw [hp]
  exact add_le_add (add_le_add hs le_rfl) le_rfl

lemma started_field_control (a : ℕ) (ha : a≤N) :
    TraceControl (D.startedNodeFieldError w y T x a) (c.startedFieldCost D.j (Fintype.card ι) B a) := by
  have H:=D.startedNodeField_control w y T x a h.dimension c.P_nonneg (c.row_nonneg _)
    (fun b:Fin a=>(h.started_small hB hw₀ hy₀ b (b.isLt.le.trans ha)).1) (h.started_small hB hw₀ hy₀ a ha).2.2 h.primarySourceError
    h.primaryValue h.primaryDerivative (fun b=>(h.aux_bound a ha b).difference)
  simpa only [LocalConstants.startedFieldCost,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using H

end LocalOrdinaryInput
end SKGapCutoff.Recipe

end
end

end OAI
