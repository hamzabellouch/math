import OAI.NumberTheory.Ostmann.Tree.DensityFibers
import OAI.NumberTheory.Ostmann.Tree.DensityValues

namespace OAI

namespace Ostmann.Tree.Density
noncomputable section
open scoped BigOperators

def average {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (Fintype.card A : ℝ)⁻¹ * ∑ x, f x

def integrate {A : Type*} (f : A → ℝ) (x : Option A) : ℝ :=
  match x with | none => 0 | some y => f y

theorem sum_integrate_le {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → Option B) (C : ℕ) (hC : ∀ y, (Finset.univ.filter (fun x => f x = some y)).card ≤ C)
    (H : B → ℝ) (hH : ∀ y, 0 ≤ H y) :
    (∑ x, integrate H (f x)) ≤ (C : ℝ) * ∑ y, H y := by
  classical
  have hp (x : A) : integrate H (f x) = ∑ y, if f x = some y then H y else 0 := by
    cases f x <;> simp [integrate]
  simp_rw [hp]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ x, if f x = some y then H y else 0) =
        ∑ y, ((Finset.univ.filter (fun x => f x = some y)).card : ℝ)*H y := by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y, (C : ℝ)*H y := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC y) (hH y)
    _ = _ := (Finset.mul_sum _ _ _).symm

variable {F : Type*} [Field F] [Fintype F]
local instance : DecidableEq F := Classical.decEq F

theorem reconstruct_domination {d : ℕ} (P : Parameters F d) (hP : P.consistent)
    (D Xl Xr c : Fˣ) (hc : P.childConsistent c)
    (H : (Leaves d → Fˣ) → ℝ) (hH : ∀ y, 0 ≤ H y) :
    average (fun M => integrate H (reconstruct D P Xl Xr c M)) ≤
      (2^(2^d-1) : ℕ) * average H := by
  have hf : ∀ y, (Finset.univ.filter
      (fun M => reconstruct D P Xl Xr c M = some y)).card ≤ 2^(2^d-1) := by
    intro y
    apply reconstruct_fiber_card_bound P hP D Xl Xr c hc _ y
    intro M hM
    exact (Finset.mem_filter.mp hM).2
  unfold average
  calc
    _ ≤ (Fintype.card (Leaves d → Fˣ) : ℝ)⁻¹ * ((2^(2^d-1) : ℕ) * ∑ y, H y) :=
      mul_le_mul_of_nonneg_left (sum_integrate_le _ _ hf H hH) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by ring

omit [Fintype F] in
theorem diagram_fiber_card_bound {d : ℕ} (T : Diagram F d)
    (S : Finset (Leaves d → Fˣ)) (y : Leaves d → Fˣ)
    (hS : ∀ M ∈ S, diagramArguments T M = some y) : S.card ≤ 2^(2^d-1) := by
  cases d with
  | zero =>
    exact reconstruct_fiber_card_bound T.parameters T.consistent 1 1 1 1
      (by cases T.parameters; trivial) S y hS
  | succ d =>
    exact reconstruct_fiber_card_bound T.parameters T.consistent T.denominator T.rootLeft T.rootRight
      (rootCoefficient T.parameters) (rootCoefficient_consistent _) S y hS

theorem diagram_domination {d : ℕ} (T : Diagram F d)
    (H : (Leaves d → Fˣ) → ℝ) (hH : ∀ y, 0 ≤ H y) :
    average (fun M => integrate H (diagramArguments T M)) ≤
      (2^(2^d-1) : ℕ) * average H := by
  cases d with
  | zero =>
    exact reconstruct_domination T.parameters T.consistent 1 1 1 1
      (by cases T.parameters; trivial) H hH
  | succ d =>
    exact reconstruct_domination T.parameters T.consistent T.denominator T.rootLeft T.rootRight
      (rootCoefficient T.parameters) (rootCoefficient_consistent _) H hH

theorem average_weight (d : ℕ) (g : F → ℂ) :
    average (weight (d:=d) g) = (average (fun u : Fˣ => ‖g u‖^2))^(2^d) := by
  classical
  have hc : Fintype.card (Leaves d) = 2^d := by simp [Leaves]
  unfold average weight
  rw [← Fintype.prod_sum (fun (_ : Leaves d) (u : Fˣ) => ‖g u‖^2)]
  simp only [Finset.prod_const, Finset.card_univ, hc, Fintype.card_fun, Nat.cast_pow,
    inv_pow, mul_pow]

end
end Ostmann.Tree.Density

end OAI
