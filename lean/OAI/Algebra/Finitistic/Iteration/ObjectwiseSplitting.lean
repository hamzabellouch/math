import OAI.Algebra.Finitistic.Iteration.BinomialEvenIteration

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ExternalTensor.Binomial.Objectwise
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
variable {S : Type w}

/-- Exact generic Section 4 statement, assuming only existence of each objectwise split. -/
theorem section4_objectwise (Phi : C ⥤ C) [Phi.Additive] [Phi.CommShift ℤ]
    (M : S → C) (H : S → S)
    (split : ∀ Y, Nonempty (Phi.obj (M Y) ≅ M (H Y) ⊞ (M (H Y))⟦(3 : ℤ)⟧))
    (j : ℕ) (Y : S) :
    Nonempty ((Phi.obj^[j]) (M Y) ≅
      ⨁ fun q : Fin (j+1) => ⨁ fun _ : Fin (Nat.choose j q.val) =>
        (M ((H^[j]) Y))⟦(3 : ℤ)*(q.val : ℤ)⟧) :=
  ⟨section4Iteration Phi M H (fun Y => Classical.choice (split Y)) j Y⟩

/-- Exact generic Section 6 formula, assuming only existence of each two-step split. -/
theorem section6_objectwise (F : C ⥤ C) [F.Additive] [F.CommShift ℤ]
    (M : S → C) (H : S → S) (b : ℤ)
    (split : ∀ Y, Nonempty (F.obj (F.obj (M Y)) ≅
      (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+3⟧))
    (j : ℕ) (Y : S) :
    Nonempty ((F.obj^[2*j]) (M Y) ≅
      ⨁ fun q : Fin (j+1) => ⨁ fun _ : Fin (Nat.choose j q.val) =>
        (M ((H^[j]) Y))⟦(j : ℤ)*b + 3*(q.val : ℤ)⟧) :=
  ⟨evenIteration F M H b (fun Y => Classical.choice (split Y)) j Y⟩

/-- Exact generic zero detection for the two-step formula, with all hypotheses exposed. -/
theorem section6_zero_detection (F : C ⥤ C) [F.Additive] [F.CommShift ℤ]
    (M : S → C) (H : S → S) (b : ℤ)
    (split : ∀ Y, Nonempty (F.obj (F.obj (M Y)) ≅
      (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+3⟧))
    (j : ℕ) (Y : S) :
    IsZero ((F.obj^[2*j]) (M Y)) ↔ IsZero (M ((H^[j]) Y)) :=
  evenIteration_isZero_iff F M H b (fun Y => Classical.choice (split Y)) j Y
end ExternalTensor.Binomial.Objectwise

end

end OAI
