import OAI.Geometry.PeriodicTiling.ActivityWord
import OAI.Geometry.PeriodicTiling.SeedSymbols
import OAI.Geometry.PeriodicTiling.WordObstruction

namespace OAI

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem graph_not_fully_periodic_of_activity
    (o : GraphOutputs E) (hdep : HasDependence E o)
    (hwords : ∀ x (w : Word p), (∀ n, Active E o (.inl n) x (w n)) → Allowed p w)
    (hseeds : ∀ (t : Fin 2) (n : Column p) (x : Plane) (j : Symbol p),
      Active E o (.inr t) x () → Active E o (.inl n) x j → j = seedSymbol E t)
    (hordinary : ∀ n x, ∃ j, Active E o (.inl n) x j)
    (hseedactive : ∀ t : Fin 2, ∃ x : Plane, Active E o (.inr t) x ()) :
    ¬ FullyPeriodic (graph o) := by
  intro hper
  obtain ⟨x, hx⟩ := hseedactive 0
  obtain ⟨y, hy⟩ := hseedactive 1
  have hline : LineRule p (selectedWord E o) :=
    selectedWord_lineRule E o hdep hordinary hwords
  have hcolumns : NonconstantColumns (selectedWord E o) :=
    selectedWord_nonconstant_of_forced_letters E o hdep hordinary
      (seedSymbol E 0) (seedSymbol E 1) (seedSymbol_zero_ne_one E) x y
      (fun n j hj => hseeds 0 n x j hx hj)
      (fun n j hj => hseeds 1 n y j hy hj)
  obtain ⟨M, hM, hperiod⟩ := exists_positive_vertical_graph_period E o hper
  exact no_positive_vertical_period E.p_prime E.p_large hline hcolumns
    (Int.natCast_pos.mpr hM) (selectedWord_period_of_graph_period E o (M : ℤ) hperiod)

end PeriodicTilingThree

end OAI
