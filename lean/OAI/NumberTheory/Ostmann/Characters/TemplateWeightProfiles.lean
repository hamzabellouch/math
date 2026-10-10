import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationProfiles
import OAI.NumberTheory.Ostmann.Characters.TemplateWeight

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable
open Arithmetic

def conjugateBy (b:Bool) (z:ℂ) : ℂ := if b then conj z else z

abbrev BottomDatum (k:ℕ) := Bool×ℤ×State k 0

def bottomData (k:ℕ) : (j:ℕ)→Bool→ℤ→State k j→HistoryReconstruction.Tree j→List (BottomDatum k)
  | 0,b,s,x,_ => [(b,s,x)]
  | j+1,b,s,x,t =>
      let P := reconstructedPivot k j x s t.1.1 t.1.2
      bottomData k j b t.1.1 (childState k j true x P) t.2.1 ++
        bottomData k j (!b) t.1.2 (childState k j false x P) t.2.2

theorem bottomData_length (k j:ℕ) (b:Bool) (s:ℤ) (x:State k j) (t:HistoryReconstruction.Tree j) :
    (bottomData k j b s x t).length=2^j := by
  induction j generalizing b s with
  | zero => rfl
  | succ j ih => simp only [bottomData,List.length_append,ih,pow_succ]; omega

@[reducible] def WeightSupport (k:ℕ) (mask:(j:ℕ)→ℤ→State k j→Prop) (X Δ W:ℝ) :
    (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop
  | 0,s,x,_ => mask 0 s x ∧
      0<(period k 0 x:ℝ) ∧ Real.log X+Δ-W≤Real.log (period k 0 x:ℝ)
  | j+1,s,x,t => mask (j+1) s x ∧
      WeightSupport k mask X Δ W j t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      WeightSupport k mask X Δ W j t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

def profileValue (k:ℕ) (X:ℝ) (z:BottomDatum k) : ℂ :=
  historyLeafProfile (𝓕 SchwartzCutoff.psi) z.1 (z.2.1:ℝ)
    (Real.log (X/(period k 0 z.2.2:ℝ)))

theorem leafWeight_eq_profile (k:ℕ) (X Δ W:ℝ) (hX:0<X) (b:Bool) (s:ℤ) (x:State k 0)
    (hp:0<(period k 0 x:ℝ)) (hr:Real.log X+Δ-W≤Real.log (period k 0 x:ℝ)) :
    conjugateBy b (leafWeight k X Δ W s x)=profileValue k X (b,s,x) := by
  have he := leafLogProfile_eq_scalar (𝓕 SchwartzCutoff.psi) (s:ℝ) X (period k 0 x:ℝ) hX hp
  have hl : leafWeight k X Δ W s x=
      (Real.sqrt (X/(period k 0 x:ℝ)):ℂ)*𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/(period k 0 x:ℝ)) := by
    unfold leafWeight
    rw [ite_eq_left ⟨hp,hr⟩]
  cases b <;> simp only [conjugateBy,profileValue,historyLeafProfile,
    Bool.false_eq_true,ite_false,ite_true,hl,he]

theorem weight_eq_profile_product (k:ℕ) (mask:(j:ℕ)→ℤ→State k j→Prop)
    (X Δ W:ℝ) (hX:0<X) (j:ℕ) (b:Bool) (s:ℤ) (x:State k j) (t:HistoryReconstruction.Tree j)
    (h:WeightSupport k mask X Δ W j s x t) :
    conjugateBy b (weight k mask X Δ W j s x t)=
      ((bottomData k j b s x t).map (profileValue k X)).prod := by
  induction j generalizing b s with
  | zero =>
    simp only [weight,ite_eq_left h.1,bottomData,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one]
    exact leafWeight_eq_profile k X Δ W hX b s x h.2.1 h.2.2
  | succ j ih =>
    simp only [weight,ite_eq_left h.1,bottomData,List.map_append,List.prod_append]
    cases b with
    | false =>
      simp only [conjugateBy,Bool.false_eq_true,ite_false,Bool.not_false]
      exact congrArg₂ (·*·) (ih false _ _ t.2.1 h.2.1) (ih true _ _ t.2.2 h.2.2)
    | true =>
      simp only [conjugateBy,ite_true,Bool.not_true,map_mul,starRingEnd_self_apply]
      exact congrArg₂ (·*·) (ih true _ _ t.2.1 h.2.1) (ih false _ _ t.2.2 h.2.2)

theorem weight_eq_indexed_profiles (k:ℕ) (mask:(j:ℕ)→ℤ→State k j→Prop)
    (X Δ W:ℝ) (hX:0<X) (j:ℕ) (b:Bool) (s:ℤ) (x:State k j) (t:HistoryReconstruction.Tree j)
    (h:WeightSupport k mask X Δ W j s x t) :
    conjugateBy b (weight k mask X Δ W j s x t)=
      ∏i:Fin (bottomData k j b s x t).length,profileValue k X ((bottomData k j b s x t).get i) := by
  rw [weight_eq_profile_product k mask X Δ W hX j b s x t h]
  exact (Fin.prod_univ_fun_getElem _ _).symm

end Ostmann.Characters.Template

end

end OAI
