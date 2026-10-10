import OAI.NumberTheory.Ostmann.Tree.DensityCut
import OAI.NumberTheory.Ostmann.Tree.DensityDomination

namespace OAI

namespace Ostmann.Tree.Density
noncomputable section
open scoped BigOperators

theorem average_surjective {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (f : G →* H) (hf : Function.Surjective f) (w : H → ℝ) :
    average (fun x => w (f x)) = average w := by
  have he := Ostmann.Arithmetic.GroupHaarImage.average_surjective f hf (fun y => (w y : ℂ))
  apply Complex.ofReal_injective
  simpa only [average, Ostmann.Arithmetic.ResidueHaar.average,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum, Complex.ofReal_natCast] using he

variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F

namespace Cut

def arguments {d k : ℕ} (C : Cut d k) (P : Parameters F d) (D Xl Xr c : Fˣ)
    (M : Leaves d → Fˣ) : Option (Leaves k → Fˣ) :=
  reconstruct D (parameters C P) Xl Xr c (project C M)

theorem arguments_stop {d : ℕ} (P : Parameters F d) (D Xl Xr c : Fˣ)
    (M : Leaves d → Fˣ) :
    arguments (.stop d) P D Xl Xr c M = some (fun _ => rootArgument P D Xl Xr c M) := by
  simp only [arguments, parameters, reconstruct, rootArgument,
    Parameters.frequency, project_product]

theorem arguments_split {d k : ℕ} (L R : Cut d k) (s a b u D Xl Xr c : Fˣ)
    (PL PR : Parameters F d) (M : Leaves (d+1) → Fˣ) :
    arguments (.split L R) (.branch s a b u PL PR) D Xl Xr c M =
      if hp : pivot s a b u PL PR Xl Xr M = 0 then none else
        match arguments L PL D (Units.mk0 _ hp) Xl (u*a) (left M),
          arguments R PR D (Units.mk0 _ hp) Xr (u*b) (right M) with
        | some yl, some yr => some (join yl yr)
        | _, _ => none := by
  classical
  simp only [arguments, parameters, reconstruct, project, left_join, right_join,
    pivot, parameters_frequency, project_product]
  rfl

variable [Fintype F]

theorem horizontal_domination {d k : ℕ} (C : Cut d k) (P : Parameters F d)
    (hP : P.consistent) (D Xl Xr c : Fˣ) (hc : P.childConsistent c)
    (H : (Leaves k → Fˣ) → ℝ) (hH : ∀ y, 0 ≤ H y) :
    average (fun M => integrate H (arguments C P D Xl Xr c M)) ≤
      (2^(2^k-1) : ℕ) * average H := by
  have he := average_surjective (projectHom C) (project_surjective C)
    (fun N => integrate H (reconstruct D (parameters C P) Xl Xr c N))
  change average (fun M => integrate H (arguments C P D Xl Xr c M)) = _ at he
  rw [he]
  exact reconstruct_domination (parameters C P) (parameters_consistent C P hP)
    D Xl Xr c (parameters_childConsistent C P c hc) H hH
end Cut

def diagramLevelArguments {d k : ℕ} (C : Cut d k) (T : Diagram F d)
    (M : Leaves d → Fˣ) : Option (Leaves k → Fˣ) :=
  match d, T with
  | 0, T => C.arguments T.parameters 1 1 1 1 M
  | _+1, T => C.arguments T.parameters T.denominator T.rootLeft T.rootRight
    (rootCoefficient T.parameters) M

theorem diagram_horizontal_domination [Fintype F] {d k : ℕ} (C : Cut d k)
    (T : Diagram F d) (H : (Leaves k → Fˣ) → ℝ) (hH : ∀ y, 0 ≤ H y) :
    average (fun M => integrate H (diagramLevelArguments C T M)) ≤
      (2^(2^k-1) : ℕ) * average H := by
  cases d with
  | zero =>
    exact C.horizontal_domination T.parameters T.consistent 1 1 1 1
      (by cases T.parameters; trivial) H hH
  | succ d =>
    exact C.horizontal_domination T.parameters T.consistent T.denominator T.rootLeft T.rootRight
      (rootCoefficient T.parameters) (rootCoefficient_consistent _) H hH

end
end Ostmann.Tree.Density

end OAI
