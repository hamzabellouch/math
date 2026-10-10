import OAI.Analysis.Kaplansky.PolynomialTest
import OAI.Geometry.ComplexBundle.Complement

namespace OAI

noncomputable section

/-! Regrouping retained frames and their complement bundles. -/

section
open Bundle
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

namespace ContinuousOrthonormalStageFrame
variable {ι : Type*} [Fintype ι] {K : ι → ℕ} {a b : LineStage K} {d : ℕ}

def congr (f : ContinuousOrthonormalStageFrame a d)
    (e : UnitaryBundleEquiv a.Model b.Model a.Fiber b.Fiber) :
    ContinuousOrthonormalStageFrame b d where
  vector y i := e.fiber y (f.vector y i)
  continuous_vector i := e.continuous_forward.comp (f.continuous_vector i)
  orthonormal y := ((e.fiber y).toLinearIsometry.orthonormal_comp_iff).mpr (f.orthonormal y)
end ContinuousOrthonormalStageFrame

def retainedGroupedStage (m R : ℕ) : LineStage (testProjectiveDimension m R) :=
  ⟨RetainedGroupedSlot m R,inferInstance,fun s => s.1⟩

/-- The polynomial image frame is transported to the actual line-bundle
presentation used in the Chern computation. No characteristic-class
nonvanishing or obstruction is a premise. -/
theorem properlyInfinite_regrouped_frame {m : ℕ} (hm : 0<m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ R : ℕ, 0<R ∧ Nonempty (ContinuousOrthonormalStageFrame (retainedGroupedStage m R)
      (2*m*testRank m R 0)) := by
  obtain ⟨R,hR,⟨f⟩⟩ := properlyInfinite_retained_frame hm hpi
  exact ⟨R,hR,⟨f.congr (retainedRegroupingUnitary m R)⟩⟩

/-- A hypothetical proper-infiniteness witness yields a genuine continuous
frame whose orthogonal complement has rank below the Chern degree on every
fiber. Identifying that Chern class and proving it nonzero remain separate. -/
theorem properlyInfinite_retained_complement {m : ℕ} (hm : 0<m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ (R : ℕ) (_ : 0<R) (f : ContinuousOrthonormalStageFrame (retainedLineStage m R)
      (2*m*testRank m R 0)),
      ∀ y : SmoothTestBase m R,
        Module.finrank ℂ (Submodule.span ℂ (Set.range (f.vector y)))ᗮ <
          ∑ i : Fin R, testProjectiveDimension m R i := by
  obtain ⟨R,hR,⟨f⟩⟩ := properlyInfinite_retained_frame hm hpi
  refine ⟨R,hR,f,fun y => ?_⟩
  exact retained_complement_rank_lt hm y _ (f.image_finrank y).ge

end Kaplansky

end

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem retainedGrouped_complementBundle_rank_lt {m R : ℕ} (hm : 0<m)
    (f : ContinuousOrthonormalStageFrame (retainedGroupedStage m R) (2*m*testRank m R 0))
    (y : SmoothTestBase m R) :
    Module.finrank ℂ (f.ComplementFiber y) < ∑ i : Fin R, testProjectiveDimension m R i := by
  have hr := f.complement_finrank y
  have hc : Fintype.card (retainedGroupedStage m R).Slot = retainedTrivialMultiplicity m R +
      ∑ i : Fin R, testProjectiveDimension m R i := by
    have hd := retainedBundle_rank_decomposition m R y
    change Module.finrank ℂ (EuclideanSpace ℂ (RetainedSlot m R)) = _ at hd
    rw [finrank_euclideanSpace, Fintype.card_congr (retainedGroupingEquiv m R)] at hd
    exact hd
  rw [hc] at hr
  have ht := retainedTrivialMultiplicity_bound (R := R) hm
  change Module.finrank ℂ (Submodule.span ℂ (Set.range (f.vector y)))ᗮ < _
  omega

/-- From a proper-infiniteness witness in the actual matrix algebra, construct
the ordinary complement vector bundle and the actual global bundle splitting.
No characteristic-class hypothesis, bundle realization or norm bound is input. -/
theorem properlyInfinite_retained_bundle_split {m : ℕ} (hm : 0<m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ (R : ℕ) (_ : 0<R)
      (f : ContinuousOrthonormalStageFrame (retainedGroupedStage m R) (2*m*testRank m R 0))
      (H : f.ComplementSplitTotal ≃ₜ
        TotalSpace (retainedGroupedStage m R).Model (retainedGroupedStage m R).Fiber),
      (∀ z, (H z).proj=z.1.proj) ∧
      (∀ y : SmoothTestBase m R, Module.finrank ℂ (f.ComplementFiber y) <
        ∑ i : Fin R, testProjectiveDimension m R i) := by
  obtain ⟨R,hR,⟨f⟩⟩ := properlyInfinite_regrouped_frame hm hpi
  exact ⟨R,hR,f,f.complementSplitHomeomorph,f.complementSplitHomeomorph_base,
    retainedGrouped_complementBundle_rank_lt hm f⟩

end Kaplansky

end

end OAI
