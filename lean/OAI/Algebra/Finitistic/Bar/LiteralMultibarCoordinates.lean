import OAI.Algebra.Finitistic.Bar.PatternTensorCoherence
import OAI.Algebra.Finitistic.Bar.MultibarFlattenDerived
import OAI.Algebra.Finitistic.Bar.RecursiveBlockIndex

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar
universe u

/-- The final input degree, separated from all bar lengths. -/
def inputDegree : (r : ℕ) → {n : ℕ} → Index r n → ℕ
  | 0, n, _ => n
  | r+1, _, ⟨_,t⟩ => inputDegree r t

/-- The literal slots from the X bars, ordered outside to inside. -/
def innerPattern : (r : ℕ) → {n : ℕ} → Index r n → List Bool
  | 0, _, _ => []
  | r+1, _, ⟨p,t⟩ => true :: (List.replicate p.val.1 false ++ innerPattern r t)

@[simp] theorem count_innerPattern (r n : ℕ) (t : Index r n) :
    count (innerPattern r t) = r := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    simp [innerPattern, count, ih]

theorem length_innerPattern (r n : ℕ) (t : Index r n) :
    (innerPattern r t).length + inputDegree r t = r+n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    have ht := ih q t
    simp only [innerPattern, inputDegree, List.length_cons, List.length_append,
      List.length_replicate]
    omega

/-- Leading internal D slots; the exterior D coefficient is kept separate. -/
def leadingPattern (r n : ℕ) (t : Index (r+1) n) : List Bool :=
  List.replicate t.1.val.1 false ++ innerPattern r t.2

@[simp] theorem count_leadingPattern (r n : ℕ) (t : Index (r+1) n) :
    count (leadingPattern r n t) = r := by
  simp [leadingPattern]

theorem length_leadingPattern (r n : ℕ) (t : Index (r+1) n) :
    (leadingPattern r n t).length + inputDegree (r+1) t = r+n := by
  rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
  have ht := length_innerPattern r q t
  simp only [leadingPattern, inputDegree, List.length_append, List.length_replicate]
  omega

variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (N : ModuleCat.{u} D) : Module k N := BimoduleTensor.scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (Z : ChainComplex (ModuleCat.{u} D) ℕ)
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "c" => ComplexShape.down ℕ

/-- Every inner summand is isomorphic, D-linearly, to its literal field tensor. -/
def innerSummandIso : (r n : ℕ) → (t : Index r n) →
    summand (fun _ => XB) Z r n t ≅
      ModuleCat.of D (patternTerm k D X (Z.X (inputDegree r t)) (innerPattern r t))
  | 0, _, _ => Iso.refl _
  | r+1, _, ⟨p,t⟩ =>
    (XB ⋙ HomologicalComplex.eval _ c p.val.1).mapIso (innerSummandIso r p.val.2 t) ≪≫
      twoSidedBarPatternIso k D X (Z.X (inputDegree r t)) p.val.1 (innerPattern r t)

/-- The prefix of the leading sequence is exactly the sequence of X bars,
also at the literal summand level. -/
theorem leadingSummand_prefix (r m n : ℕ) (h : m≤r) (t : Index m n) :
    summand (leadingBarSequence k D X r) Z m n t = summand (fun _ => XB) Z m n t := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    change (degreeFunctor (leadingBarSequence k D X r) m i).obj _ = _
    simp only [degreeFunctor, leadingBarSequence, ite_eq_left (show m<r by omega),
      Functor.comp_obj, summand, ih q (by omega) t]

/-- The source tensor D ⊗ D^i₀ ⊗ X ⊗ ... ⊗ D^iᵣ ⊗ Z^q,
with every field scalar action and every exterior D action checked. -/
def leadingSummandIso (r n : ℕ) (t : Index (r+1) n) :
    summand (leadingBarSequence k D X r) Z (r+1) n t ≅
      ModuleCat.of D (D ⊗[k]
        patternTerm k D X (Z.X (inputDegree (r+1) t)) (leadingPattern r n t)) := by
  rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
  simp only [summand, degreeFunctor, leadingBarSequence, lt_self_iff_false, ite_false]
  change ((barFunctor k D ⋙ HomologicalComplex.eval _ c i).obj
      (summand (leadingBarSequence k D X r) Z r q t)) ≅ _
  exact (barFunctor k D ⋙ HomologicalComplex.eval _ c i).mapIso
      (eqToIso (leadingSummand_prefix k D X Z r r q le_rfl t) ≪≫
        innerSummandIso k D X Z r q t) ≪≫
    freeBarPatternIso k D X (Z.X (inputDegree r t)) i (innerPattern r t)
end DerivedBar.RecursiveTotal

end

end OAI
