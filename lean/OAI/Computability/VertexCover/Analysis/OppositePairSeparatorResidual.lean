import Mathlib
import OAI.Computability.VertexCover.Analysis.SeedEnergyBudget

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
namespace VertexCover.LabelCover

def OppositePairKey (Φ : LabelCover) (d : ℕ) :=
  Φ.Seeds d × (Fin Φ.u ⊕ Fin Φ.v)

noncomputable instance oppositePairKeyFintype (Φ : LabelCover) (d : ℕ) :
    Fintype (Φ.OppositePairKey d) := by
  unfold OppositePairKey
  infer_instance

noncomputable def oppositePairKey (Φ : LabelCover) {d : ℕ}
    (k : Fin d) (e : PositionPair d) (seed : Φ.Seeds d) : Φ.OppositePairKey d := by
  classical
  exact (Function.update seed e ⟨0, Φ.M_pos⟩,
    if e.1.1 = k then Sum.inr (Φ.right (seed e)) else Sum.inl (Φ.left (seed e)))

noncomputable def starFromOppositePair (Φ : LabelCover) {d : ℕ}
    (k : Fin d) (e : PositionPair d) (data : Φ.OppositePairKey d) : Φ.StarKey d := by
  classical
  exact fun b => if b = e then
    (none,
      if e.1.1 = k then none else data.2.elim some (fun _ => none),
      if e.1.2 = k then none else data.2.elim (fun _ => none) some)
    else Φ.starKey k data.1 b

theorem starFromOppositePair_key (Φ : LabelCover) {d : ℕ}
    (k : Fin d) (e : PositionPair d) (he : e.1.1 = k ∨ e.1.2 = k)
    (seed : Φ.Seeds d) :
    Φ.starFromOppositePair k e (Φ.oppositePairKey k e seed) = Φ.starKey k seed := by
  classical
  funext b
  by_cases hb : b = e
  · subst b
    rcases he with hL | hR
    · have hR : e.1.2 ≠ k := by
        intro hh
        have hn := ne_of_lt e.2
        exact hn (hL.trans hh.symm)
      simp [starFromOppositePair, oppositePairKey, starKey, hL, hR]
    · have hL : e.1.1 ≠ k := by
        intro hh
        have hn := ne_of_lt e.2
        exact hn (hh.trans hR.symm)
      simp [starFromOppositePair, oppositePairKey, starKey, hL, hR]
  · simp [starFromOppositePair, oppositePairKey, starKey, hb]

theorem oppositePair_residual_le_star (Φ : LabelCover) {d : ℕ}
    (k : Fin d) (e : PositionPair d) (he : e.1.1 = k ∨ e.1.2 = k)
    (f : Φ.Seeds d → ℝ) :
    VertexCover.finiteMean (fun seed =>
      (f seed - VertexCover.Average.fiberAverage (Φ.oppositePairKey k e)
        (fun _ => f) (Φ.oppositePairKey k e seed))^2) ≤
    VertexCover.finiteMean (fun seed =>
      (f seed - VertexCover.Average.fiberAverage (Φ.starKey k)
        (fun _ => f) (Φ.starKey k seed))^2) := by
  have h := VertexCover.Average.finiteMean_condition_best (Φ.oppositePairKey k e) f
    (fun data => VertexCover.Average.fiberAverage (Φ.starKey k) (fun _ => f)
      (Φ.starFromOppositePair k e data))
  simp_rw [Φ.starFromOppositePair_key k e he] at h
  exact h

theorem oppositePair_separator_residual_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (k : Fin d) (e : PositionPair d) (he : e.1.1 = k ∨ e.1.2 = k)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    VertexCover.finiteMean (fun seed =>
      (Φ.separator A hA (Φ.continuousSum seed s) -
        VertexCover.Average.fiberAverage (Φ.oppositePairKey k e)
          (fun _ seed' => Φ.separator A hA (Φ.continuousSum seed' s))
          (Φ.oppositePairKey k e seed))^2) ≤
    VertexCover.finiteMean (fun seed =>
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2) := by
  simp_rw [Φ.starMean_eq_fiberAverage]
  exact Φ.oppositePair_residual_le_star k e he _

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
