import OAI.NumberTheory.Ostmann.Tree.CutFiberAverage

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators
open Density
local instance horizontalFiberFintype {A B : Type*} [Fintype A] (f : A → B) (y : B) :
    Fintype {x : A // f x=y} := Fintype.ofFinite _

def realFiberAverage {A B : Type*} [Fintype A] (f : A → B) (W : A → ℝ) (y : B) : ℝ :=
  Density.average (fun x : {x : A // f x=y} => W x.val)

theorem real_average_fiberAverage {A B : Type*} [Group A] [Group B]
    [Fintype A] [Fintype B] (f : A →* B) (hf : Function.Surjective f) (W : A → ℝ) :
    Density.average W=Density.average (realFiberAverage f W) := by
  apply Complex.ofReal_injective
  have h := average_fiberAverage f hf (fun x => (W x:ℂ))
  simpa only [Ostmann.Arithmetic.ResidueHaar.average,Density.average,realFiberAverage,
    fiberAverage,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_sum,
    Complex.ofReal_natCast] using h

theorem real_average_surjective {A B : Type*} [Group A] [Group B]
    [Fintype A] [Fintype B] (f : A →* B) (hf : Function.Surjective f) (W : B → ℝ) :
    Density.average (fun x => W (f x))=Density.average W := by
  apply Complex.ofReal_injective
  have h := Ostmann.Arithmetic.GroupHaarImage.average_surjective f hf (fun x => (W x:ℂ))
  simpa only [Ostmann.Arithmetic.ResidueHaar.average,Density.average,
    Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_sum,Complex.ofReal_natCast] using h

theorem real_average_pull_fiberAverage {A B : Type*} [Group A] [Group B]
    [Fintype A] [Fintype B] (f : A →* B) (hf : Function.Surjective f) (W : A → ℝ) :
    Density.average (fun x => realFiberAverage f W (f x))=Density.average W := by
  rw [real_average_surjective f hf,←real_average_fiberAverage f hf]

lemma horizontal_average_fintype_congr {A : Type*} (i j : Fintype A) (f : A → ℝ) :
    @Density.average A i f = @Density.average A j f := by
  cases Subsingleton.elim i j
  rfl

theorem horizontal_fiber_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d k : ℕ} (C : Cut d k) (T : Diagram F d)
    (W : (Leaves d → Fˣ) → ℝ) (H : (Leaves k → Fˣ) → ℝ)
    (hH : ∀ y,0≤H y)
    (hW : ∀ M,realFiberAverage C.project W (C.project M)≤
      integrate H (diagramLevelArguments C T M)) :
    Density.average W≤((2^(2^k-1):ℕ):ℝ)*Density.average H := by
  classical
  have he := real_average_pull_fiberAverage C.projectHom C.project_surjective W
  have hd := diagram_horizontal_domination C T H hH
  simp only [horizontal_average_fintype_congr _ (inferInstance : Fintype (Leaves d → Fˣ)),
    horizontal_average_fintype_congr _ (inferInstance : Fintype (Leaves k → Fˣ))] at hd
  calc
    _ = Density.average (fun M => realFiberAverage C.project W (C.project M)) := he.symm
    _ ≤ Density.average (fun M => integrate H (diagramLevelArguments C T M)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun M _ => hW M)) (by positivity)
    _ ≤ _ := hd

end
end Ostmann.Tree

end OAI
