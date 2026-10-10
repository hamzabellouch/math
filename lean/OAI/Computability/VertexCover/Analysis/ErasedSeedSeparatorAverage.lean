import Mathlib
import OAI.Computability.VertexCover.Analysis.GraphCompleteness
import OAI.Computability.VertexCover.Analysis.OppositePairSeparatorResidual

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
namespace VertexCover.Average

theorem finiteMean_nested_decomposition {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (fine : α → β) (forget : β → γ) (f : α → ℝ) :
    VertexCover.finiteMean (fun a => (f a)^2) =
      VertexCover.finiteMean (fun a =>
        (fiberAverage (forget ∘ fine) (fun _ => f) (forget (fine a)))^2) +
      VertexCover.finiteMean (fun a =>
        (fiberAverage fine (fun _ => f) (fine a) -
          fiberAverage (forget ∘ fine) (fun _ => f) (forget (fine a)))^2) +
      VertexCover.finiteMean (fun a =>
        (f a - fiberAverage fine (fun _ => f) (fine a))^2) := by
  have h₀ := finiteMean_condition_pythagoras (forget ∘ fine) f (fun _ => 0)
  simp only [sub_zero, Function.comp_apply] at h₀
  have h₁ := finiteMean_condition_pythagoras fine f
    (fun b => fiberAverage (forget ∘ fine) (fun _ => f) (forget b))
  linarith

end VertexCover.Average

namespace VertexCover.LabelCover

theorem oppositePair_three_component_energy (Φ : LabelCover) {d : ℕ}
    (k : Fin d) (e : PositionPair d) (f : Φ.Seeds d → ℝ) :
    let coarse : Φ.Seeds d → Φ.Seeds d :=
      fun seed => Function.update seed e ⟨0, Φ.M_pos⟩
    let fine := Φ.oppositePairKey k e
    VertexCover.finiteMean (fun seed => (f seed)^2) =
      VertexCover.finiteMean (fun seed =>
        (VertexCover.Average.fiberAverage coarse (fun _ => f) (coarse seed))^2) +
      VertexCover.finiteMean (fun seed =>
        (VertexCover.Average.fiberAverage fine (fun _ => f) (fine seed) -
          VertexCover.Average.fiberAverage coarse (fun _ => f) (coarse seed))^2) +
      VertexCover.finiteMean (fun seed =>
        (f seed - VertexCover.Average.fiberAverage fine (fun _ => f) (fine seed))^2) := by
  classical
  exact VertexCover.Average.finiteMean_nested_decomposition
    (Φ.oppositePairKey k e) (fun data : Φ.OppositePairKey d => data.1) f

end VertexCover.LabelCover

namespace VertexCover.LabelCover

noncomputable def erasedSeedFiber (Φ : LabelCover) {d : ℕ}
    (e : PositionPair d) (seed : Φ.Seeds d) : Finset (Φ.Seeds d) := by
  classical
  exact Finset.univ.filter (fun seed' =>
    Function.update seed' e ⟨0, Φ.M_pos⟩ = Function.update seed e ⟨0, Φ.M_pos⟩)

noncomputable def erasedSeedFiberEquiv (Φ : LabelCover) {d : ℕ}
    (e : PositionPair d) (seed : Φ.Seeds d) : Φ.erasedSeedFiber e seed ≃ Fin Φ.M := by
  classical
  exact {
    toFun := fun seed' => seed'.1 e
    invFun := fun c => ⟨Function.update seed e c, by
      simp [erasedSeedFiber, Function.update_idem]⟩
    left_inv := fun seed' => by
      apply Subtype.ext
      funext b
      by_cases hb : b = e
      · subst b
        simp
      · have hh := (Finset.mem_filter.mp seed'.2).2
        have he := congrFun hh b
        simp only [Function.update_of_ne hb] at he ⊢
        exact he.symm
    right_inv := fun c => by simp }

theorem erasedSeed_fiberAverage (Φ : LabelCover) {d : ℕ}
    (e : PositionPair d) (seed : Φ.Seeds d) (f : Φ.Seeds d → ℝ) :
    VertexCover.Average.fiberAverage
      (fun seed' : Φ.Seeds d => Function.update seed' e ⟨0, Φ.M_pos⟩)
      (fun _ => f) (Function.update seed e ⟨0, Φ.M_pos⟩) =
      VertexCover.finiteMean (fun c : Fin Φ.M => f (Function.update seed e c)) := by
  classical
  calc
    _ = VertexCover.finiteMean (fun seed' : Φ.erasedSeedFiber e seed => f seed'.1) := by
      unfold VertexCover.Average.fiberAverage
      simpa only [erasedSeedFiber] using
        (VertexCover.Average.finiteMean_finset (Φ.erasedSeedFiber e seed) f).symm
    _ = _ := (VertexCover.finiteMean_equiv (Φ.erasedSeedFiberEquiv e seed).symm
      (fun seed' : Φ.erasedSeedFiber e seed => f seed'.1)).symm

theorem erasedSeed_separator_average (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (e : PositionPair d) (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    VertexCover.Average.fiberAverage
      (fun seed' : Φ.Seeds d => Function.update seed' e ⟨0, Φ.M_pos⟩)
      (fun _ seed' => Φ.separator A hA (Φ.continuousSum seed' s))
      (Function.update seed e ⟨0, Φ.M_pos⟩) = Φ.seedMean A hA e seed s := by
  exact Φ.erasedSeed_fiberAverage e seed
    (fun seed' => Φ.separator A hA (Φ.continuousSum seed' s))

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
