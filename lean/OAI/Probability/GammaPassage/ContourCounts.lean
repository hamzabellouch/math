import OAI.Probability.FirstPassage.Paths
import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega

namespace OAI

/-! The closedness count in crossings.tex:cr:oriented-paths. A contour need not
be simple at vertices; its zero displacement alone gives the half-length count. -/
namespace PlanarFPP

theorem displacement_counts (ds : List Step) :
    (displacement ds).1=(ds.count Step.east : ℤ)-ds.count Step.west ∧
    (displacement ds).2=(ds.count Step.north : ℤ)-ds.count Step.south ∧
    ds.length=ds.count Step.east+ds.count Step.west+ds.count Step.north+ds.count Step.south := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    cases d <;> simp_all [displacement_cons,Step.delta] <;> omega

/-- Exactly half the edges of a closed square-lattice walk point upward or
leftward, as required before selecting bad sites in the source contour proof. -/
theorem closed_walk_up_left_count (ds : List Step) (h : displacement ds=0) :
    ds.length=2*(ds.count Step.north+ds.count Step.west) := by
  obtain ⟨hx,hy,hl⟩ := displacement_counts ds
  rw [h] at hx hy
  simp only [Prod.fst_zero,Prod.snd_zero] at hx hy
  omega

end PlanarFPP

end OAI
