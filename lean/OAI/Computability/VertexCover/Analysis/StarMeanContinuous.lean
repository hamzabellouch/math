import Mathlib
import OAI.Computability.VertexCover.Reduction.SeparatorStarOscillation
import OAI.Computability.VertexCover.Analysis.SeparatorRoundingErrorAe

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover

theorem finiteMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    finiteMean (fun a => f a - g a) = finiteMean f - finiteMean g := by
  simp only [finiteMean, Finset.sum_sub_distrib, sub_div]

theorem finiteMean_abs_le {α : Type*} [Fintype α] (f : α → ℝ) :
    |finiteMean f| ≤ finiteMean (fun a => |f a|) := by
  unfold finiteMean
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card α from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

end VertexCover

namespace VertexCover.LabelCover
open MeasureTheory

def StarKey (Φ : LabelCover) (d : ℕ) :=
  PositionPair d → Option (Fin Φ.M) × Option (Fin Φ.u) × Option (Fin Φ.v)

noncomputable def starKey (Φ : LabelCover) {d : ℕ} (k : Fin d) (seed : Φ.Seeds d) :
    Φ.StarKey d := by
  classical
  exact fun e => (if e.1.1 = k ∨ e.1.2 = k then none else some (seed e),
    if e.1.1 = k then none else some (Φ.left (seed e)),
    if e.1.2 = k then none else some (Φ.right (seed e)))

noncomputable def starFiber (Φ : LabelCover) {d : ℕ} (k : Fin d) (seed : Φ.Seeds d) :
    Finset (Φ.Seeds d) := by
  classical
  exact Finset.univ.filter (fun seed' => Φ.starKey k seed' = Φ.starKey k seed)

theorem mem_starFiber (Φ : LabelCover) {d : ℕ} (k : Fin d) (seed seed' : Φ.Seeds d) :
    seed' ∈ Φ.starFiber k seed ↔ Φ.starKey k seed' = Φ.starKey k seed := by
  classical
  simp [starFiber]

theorem self_mem_starFiber (Φ : LabelCover) {d : ℕ} (k : Fin d) (seed : Φ.Seeds d) :
    seed ∈ Φ.starFiber k seed := (Φ.mem_starFiber k seed seed).mpr rfl

theorem starKey_eq_questions (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed seed' : Φ.Seeds d) (h : Φ.starKey k seed = Φ.starKey k seed') :
    (∀ e : PositionPair d, e.1.1 ≠ k → Φ.left (seed e) = Φ.left (seed' e)) ∧
    (∀ e : PositionPair d, e.1.2 ≠ k → Φ.right (seed e) = Φ.right (seed' e)) := by
  constructor
  · intro e he
    have hh := congrArg (fun key : Φ.StarKey d => (key e).2.1) h
    simpa only [starKey, ite_eq_right he, Option.some.injEq] using hh
  · intro e he
    have hh := congrArg (fun key : Φ.StarKey d => (key e).2.2) h
    simpa only [starKey, ite_eq_right he, Option.some.injEq] using hh

noncomputable def starMean (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : ℝ :=
  VertexCover.finiteMean (fun seed' : Φ.starFiber k seed =>
    Φ.separator A hA (Φ.continuousSum seed'.1 s))

theorem star_residual_abs_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) :
    |Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s| ≤ 2 := by
  classical
  let : Nonempty (Φ.starFiber k seed) := ⟨⟨seed, Φ.self_mem_starFiber k seed⟩⟩
  have heq : Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s =
      VertexCover.finiteMean (fun seed' : Φ.starFiber k seed =>
        Φ.separator A hA (Φ.continuousSum seed s) -
          Φ.separator A hA (Φ.continuousSum seed'.1 s)) := by
    rw [VertexCover.finiteMean_sub, VertexCover.finiteMean_const]
    rfl
  rw [heq]
  apply (VertexCover.finiteMean_abs_le _).trans
  calc
    VertexCover.finiteMean (fun seed' : Φ.starFiber k seed =>
        |Φ.separator A hA (Φ.continuousSum seed s) -
          Φ.separator A hA (Φ.continuousSum seed'.1 s)|) ≤
        VertexCover.finiteMean (fun _ : Φ.starFiber k seed => (2 : ℝ)) := by
      apply VertexCover.finiteMean_mono
      intro seed'
      have hkey := (Φ.mem_starFiber k seed seed'.1).mp seed'.2
      obtain ⟨hL, hR⟩ := Φ.starKey_eq_questions k seed seed'.1 hkey.symm
      exact Φ.separator_star_oscillation A hA seed seed'.1 s hs k hL hR
    _ = 2 := VertexCover.finiteMean_const _

theorem starMean_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) : Continuous (Φ.starMean A hA k seed) := by
  classical
  unfold starMean VertexCover.finiteMean
  exact (continuous_finsetSum _ (fun seed' _ =>
    Φ.separator_continuousSum_continuous A hA seed'.1)).div_const _

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
