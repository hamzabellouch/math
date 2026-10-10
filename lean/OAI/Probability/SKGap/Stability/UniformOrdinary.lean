import Mathlib
import OAI.Probability.SKGap.Localization.ResidualMultiplier
import OAI.Probability.SKGap.Matrix.RecipeWordEvent
import OAI.Probability.SKGap.Matrix.PrimaryWordControl

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

theorem uniform_ordinary_control (D : ∀a,OrdinaryData (n a) ι κ σ)
    (T : ∀a,Spin (n a)→ι→SourceTree (Fin (n a)→ℝ))
    (N L : ℕ) (c : LocalConstants) (j : ℝ) (hj : ∀a,(D a).j=j)
    (h : ∀a x,LocalOrdinaryInput (D a) (T a x) x N c)
    {M B Q : ℝ} (hM : 0≤M) (hB : 0≤B) (hQ : 0≤Q)
    (hm : ∀a x l,mass ((T a x l).words j).1≤Q ∧ mass ((T a x l).words j).2≤Q)
    (hT : ∀a x l,PolynomialControl c.A L ((T a x l).words j).1 ∧
      PolynomialControl c.A L ((T a x l).words j).2)
    (hw : ∀a,WordTestBound (D a).J c.A M (2*N+3))
    (hd : ∀a,WordDiagramBound (D a).J j c.A B (L+2*N+2)) :
    ∃C : ℝ,0≤C ∧ ∀a x,
      SmallBound ((D a).source N) x C ∧
      (∀l,SmallBound ((D a).sourcePartial N l) x C) ∧
      (∑i,|derivativeMatrix ((D a).source N) x i i|)≤C := by
  let W:=c.normBudget j (Fintype.card ι)
  let R:=errorBudget (|j| *c.A) (c.sourceCost j (Fintype.card ι) (Fintype.card σ))
      (c.fieldCost j (Fintype.card ι))
  let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|j|)*Q)) (2+|j| *c.A) W
  let C:=|W N|+|V N*B+(R N).1*M|
  have hW : W N≤C := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hR : V N*B+(R N).1*M≤C := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  refine ⟨C,by dsimp [C]; positivity,fun a x=>?_⟩
  have hh:=(D a).ordinary_word_closure (T a x) x N L c (h a x) hM hB hQ
    (by simpa only [hj a] using hm a x) (by simpa only [hj a,PolynomialControl] using hT a x) (hw a)
    (by simpa only [hj a] using hd a) N le_rfl
  rw [hj a] at hh
  have hp:=(h a x).small N le_rfl
  rw [hj a] at hp
  exact ⟨hh.1.mono hW,fun l=>(hp.2.2 l).mono hW,hh.2.2.1.trans hR⟩

theorem uniform_auxiliary_mean (D : ∀a,OrdinaryData (n a) ι κ σ)
    (T : ∀a,Spin (n a)→ι→SourceTree (Fin (n a)→ℝ)) (N : ℕ) (c : LocalConstants)
    (h : ∀a x,LocalOrdinaryInput (D a) (T a x) x N c) (b : Fin N) :
    UniformMultiplier (fun a=>siteMean ((D a).auxCoefficient N b)) := by
  refine ⟨c.A,c.row (Fintype.card ι),c.A_nonneg,c.row_nonneg _,
    fun a x=>(h a x).mean_bound N le_rfl b,fun a x=>?_⟩
  have hm:=coefficient_mean_difference ((D a).auxCoefficient N b) x (c.row_nonneg _)
    ((h a x).aux_bound N le_rfl b).difference
  have hs:=pow_le_pow_left₀ (norm_nonneg _) hm 2
  rw [EuclideanSpace.real_norm_sq_eq] at hs
  exact hs

end SKGapCutoff.Recipe

end
end

end OAI
