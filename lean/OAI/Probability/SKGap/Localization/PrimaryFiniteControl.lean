import Mathlib
import OAI.Probability.SKGap.Localization.RecipePrimaryMass
import OAI.Probability.SKGap.Localization.PrimaryLocalInput

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
universe u
variable {Ω : Type u} {n : Ω→ℕ}

theorem primary_finite_control (j R B : ℝ) (hR : 0≤R) (hB : 0≤B)
    (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (M Nmax : ℕ)
    (hn : ∀a,0<n a) (hJ : ∀a,SKGap.opNorm (J a)≤R)
    (hformal : ∀a x l,l<M → ShapeBound (formalField j (J a) (h a) x l) B)
    (A W D : ℝ) (hA : 1≤A) (hW : 0≤W) (hD : 0≤D)
    (hw : ∀a,WordTestBound (J a) A W (2*Nmax+3))
    (hd : ∀a,WordDiagramBound (J a) j A D ((2*M+1)+2*Nmax+2)) :
    FiniteRecipeControl j J h M Nmax A := by
  let C:=localPrimaryBudget j R B M
  have hC:=localPrimaryBudget_nonneg (j:=j) hR hB M
  let c : LocalConstants:=
    ⟨1,1,C,R,C,(M:ℝ)*(|j| *(C+C)),0,le_rfl,zero_le_one,le_rfl,
      hC,hR,hC,by dsimp [C]; positivity [localPrimaryBudget_nonneg (j:=j) hR hB M],le_rfl⟩
  apply finite_recipe_control (fun a=>emptyRecipe j (J a) (h a) M)
    (emptyRecipe_family j J h M) (fun a x q=>primaryTree j (J a) (h a) x q.val)
    c (fun a x=>primary_local_input (J a) (h a) x (hn a) hR hB (hJ a) M (hformal a x))
    Nmax (2*M+1) A W D ((2+|j|)^M) hA hW hD (by positivity)
  · intro a x q
    have hm:=primaryTree_mass (hn a) j (J a) (h a) x q.val
    have hp : (2+|j|)^q.val≤(2+|j|)^M:=
      pow_le_pow_right₀ (by linarith [abs_nonneg j]) q.isLt.le
    exact ⟨hm.1.trans hp,hm.2.trans hp⟩
  · intro a x q
    have ht:=primaryTree_control j (J a) (h a) x q.val hA
    exact ⟨ht.1.mono (by omega),ht.2.mono (by omega)⟩
  · exact hw
  · exact hd

end SKGapCutoff.Recipe

end
end

end OAI
