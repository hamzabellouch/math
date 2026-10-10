import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.GraphCorrection

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries Matrix
open scoped Classical
variable {R α ι : Type*} [CommRing R] [Fintype ι]

def centeredPart (f : MvPowerSeries α R) : MvPowerSeries α R := f - C (constantCoeff f)

theorem centeredPart_centered [Fintype α] (f : MvPowerSeries α R) :
    constantCoeff (centeredPart f) = 0 := by
  simp [centeredPart]

theorem centeredPart_eq [Fintype α] {f : MvPowerSeries α R} (hf : constantCoeff f = 0) :
    centeredPart f = f := by simp [centeredPart,hf]

theorem centeredPart_jet [Fintype α] {n : ℕ} {f g : MvPowerSeries α R} (h : Jet n f g) :
    Jet n (centeredPart f) (centeredPart g) := by
  by_cases hn : n = 0
  · subst n; exact Vanishes.all _
  · have hc : constantCoeff f = constantCoeff g :=
      Jet.iff_coeff.mp h 0 (by simpa using Nat.pos_of_ne_zero hn)
    rw [centeredPart,centeredPart,hc]
    exact h.sub (Jet.refl _ _)

variable [Fintype α]

theorem quadratic_subst_contracts (H : MvPowerSeries (α ⊕ ι) R) (hH : Vanishes 2 H)
    (f g : ι → MvPowerSeries α R) {n : ℕ}
    (hfg : ∀ i, Jet n (f i) (g i)) :
    Jet (n+1) (subst (Sum.elim X (fun i => centeredPart (f i))) H)
      (subst (Sum.elim X (fun i => centeredPart (g i))) H) := by
  let x : (α ⊕ ι) → MvPowerSeries α R := Sum.elim X (fun i => centeredPart (g i))
  let δ : ι → MvPowerSeries α R := fun i => centeredPart (f i)-centeredPart (g i)
  have hx : ∀ j, constantCoeff (x j) = 0 := by
    intro j; cases j <;> simp [x,centeredPart_centered]
  have hδ : ∀ j, constantCoeff (δ j) = 0 := by
    intro j; simp [δ,centeredPart_centered]
  have hext := extended_centered x δ hx hδ
  let hs := hasSubst_of_constantCoeff_zero hext
  obtain ⟨q,hq,hfact⟩ := exists_first_remainder H
  have hq' : ∀ i, Vanishes 1 (subst (Sum.elim x δ) (q i)) :=
    fun i => (hq 1 hH i).subst _ hext
  have hfact' := congrArg (substAlgHom hs) hfact
  simp only [map_sub,map_sum,map_mul,substAlgHom_apply,subst_X hs,Sum.elim_inr,
    subst_extended_shifted x δ hx hδ,subst_extended_base x δ hx hδ] at hfact'
  have harg : shiftedGraph x δ = Sum.elim X (fun i => centeredPart (f i)) := by
    funext j
    cases j <;> simp [shiftedGraph,x,δ]
  change Vanishes (n+1) _
  rw [← harg]
  change Vanishes (n+1) (subst (shiftedGraph x δ) H-subst x H)
  rw [hfact']
  exact Vanishes.sum _ _ fun i _ => by
    simpa only [Nat.add_comm 1 n] using (hq' i).mul (centeredPart_jet (hfg i))

def implicitOperator (L : ι → MvPowerSeries α R)
    (H : ι → MvPowerSeries (α ⊕ ι) R) (w : ι → MvPowerSeries α R) :
    ι → MvPowerSeries α R := fun i =>
  L i + subst (Sum.elim X (fun j => centeredPart (w j))) (H i)

theorem implicitOperator_contracts (L : ι → MvPowerSeries α R)
    (H : ι → MvPowerSeries (α ⊕ ι) R) (hH : ∀ i, Vanishes 2 (H i)) :
    ∀ n f g, Close n f g → Close (n+1) (implicitOperator L H f) (implicitOperator L H g) := by
  intro n f g h i e he
  have hj := quadratic_subst_contracts (H i) (hH i) f g
    (fun j => Jet.iff_coeff.mpr (h j))
  simpa only [implicitOperator,map_add] using congrArg (fun z => coeff e (L i)+z)
    (Jet.iff_coeff.mp hj e he)

theorem implicitOperator_centered (L : ι → MvPowerSeries α R)
    (H : ι → MvPowerSeries (α ⊕ ι) R)
    (hL : ∀ i, constantCoeff (L i) = 0) (hH : ∀ i, Vanishes 2 (H i))
    (w : ι → MvPowerSeries α R) : ∀ i, constantCoeff (implicitOperator L H w i) = 0 := by
  intro i
  have hargs : ∀ j, constantCoeff (Sum.elim X (fun j => centeredPart (w j)) j) = 0 := by
    intro j; cases j <;> simp [centeredPart_centered]
  have hz := Vanishes.one_iff.mp (((hH i).subst _ hargs).mono (by omega : 1 ≤ 2))
  simpa only [implicitOperator,map_add,hL,zero_add] using hz

theorem centered_implicit_solution (L : ι → MvPowerSeries α R)
    (H : ι → MvPowerSeries (α ⊕ ι) R)
    (hL : ∀ i, constantCoeff (L i) = 0) (hH : ∀ i, Vanishes 2 (H i)) :
    ∃! w : ι → MvPowerSeries α R,
      (∀ i, constantCoeff (w i) = 0) ∧
      (∀ i, w i = L i + subst (Sum.elim X w) (H i)) := by
  let T := implicitOperator L H
  have hT := implicitOperator_contracts L H hH
  have hw : T (fixedPoint T) = fixedPoint T := fixedPoint_eq T hT
  have hcenter : ∀ i, constantCoeff (fixedPoint T i) = 0 := by
    rw [← hw]; exact implicitOperator_centered L H hL hH _
  refine ⟨fixedPoint T,⟨hcenter,?_⟩,?_⟩
  · intro i
    have he := congrFun hw i
    simpa only [T,implicitOperator,centeredPart_eq (hcenter _)] using he.symm
  · intro w ⟨hc,hw⟩
    apply fixedPoint_unique T hT
    funext i
    simpa only [T,implicitOperator,centeredPart_eq (hc _)] using (hw i).symm

end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
