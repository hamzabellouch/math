import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedProjectiveTower
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # Exactness of cohomology limits for degreewise exact towers -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace IntegralProjectiveTower

theorem cohomology_exact {T U V : IntegralProjectiveTower G} (f : Map T U) (g : Map U V)
    (hzero : ∀ n, f.app n ≫ g.app n = 0)
    (hexact : ∀ n, (ShortComplex.mk (f.app n) (g.app n) (hzero n)).ShortExact)
    (p : ℕ) (x : U.Cohomology p) (hx : g.cohomologyMap p x = 0) :
    ∃ y : T.Cohomology p, f.cohomologyMap p y = x := by
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  rw [Map.cohomologyMap_of] at hx
  obtain ⟨m, hnm, hm⟩ := Module.DirectLimit.of.zero_exact hx
  have hz : g.stageMap p m (U.forward p n m hnm z) = 0 := by
    rw [g.forward_natural]
    exact hm
  let S := ShortComplex.mk (f.app m) (g.app m) (hzero m)
  have h := (ShortComplex.moduleCat_exact_iff _).mp
    (groupCohomology.mapShortComplex₂_exact (hexact m) (m + p))
  obtain ⟨a, ha⟩ := h (U.forward p n m hnm z) hz
  change T.cohomologyStage p m at a
  refine ⟨Module.DirectLimit.of ℤ ℕ _ (T.forward p) m a, ?_⟩
  rw [Map.cohomologyMap_of]
  have ha' : f.stageMap p m a = U.forward p n m hnm z := ha
  rw [ha']
  exact Module.DirectLimit.of_f (R := ℤ) (ι := ℕ) (f := U.forward p) (hij := hnm) (x := z)

end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
