import OAI.GroupTheory.PolycyclicRecognition.Algebra.BilinearCentralGroup
import OAI.GroupTheory.PolycyclicRecognition.Lattices.VectorLatticeModel
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace OAI

/-! # A smooth real Lie model for a bilinear central extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {V W : Type} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℝ V] [NormedSpace ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

variable (B : V →L[ℝ] V →L[ℝ] W)

instance bilinearCentralTopology : TopologicalSpace (BilinearCentralGroup B.toLinearMap₁₂) :=
  inferInstanceAs (TopologicalSpace (V × W))

instance bilinearCentralChartedSpace :
    ChartedSpace (V × W) (BilinearCentralGroup B.toLinearMap₁₂) :=
  inferInstanceAs (ChartedSpace (V × W) (V × W))

instance bilinearCentralLieGroup : LieGroup (𝓘(ℝ, V × W)) ⊤
    (BilinearCentralGroup B.toLinearMap₁₂) :=
    { toIsManifold := by change IsManifold (𝓘(ℝ, V × W)) ⊤ (V × W); infer_instance
      contMDiff_mul := by
        change ContMDiff _ _ ⊤ (fun p : (V × W) × (V × W) =>
          (p.1.1 + p.2.1, p.1.2 + p.2.2 + B p.1.1 p.2.1))
        have hB : ContDiff ℝ ⊤ (fun p : (V × W) × (V × W) => B p.1.1 p.2.1) :=
          (B.contDiff.comp contDiff_fst.fst).clm_apply contDiff_snd.fst
        have hm : ContMDiff ((𝓘(ℝ, V × W)).prod (𝓘(ℝ, V × W)))
            (𝓘(ℝ, V × W)) ⊤ (fun p : (V × W) × (V × W) =>
              (p.1.1 + p.2.1, p.1.2 + p.2.2 + B p.1.1 p.2.1)) := by
          rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
          exact ((contDiff_fst.fst.add contDiff_snd.fst).prodMk
            ((contDiff_fst.snd.add contDiff_snd.snd).add hB)).contMDiff
        exact hm
      contMDiff_inv := by
        change ContMDiff _ _ ⊤ (fun p : V × W => (-p.1, -p.2 + B p.1 p.1))
        have hB : ContDiff ℝ ⊤ (fun p : V × W => B p.1 p.1) :=
          (B.contDiff.comp contDiff_fst).clm_apply contDiff_fst
        exact (contDiff_fst.neg.prodMk (contDiff_snd.neg.add hB)).contMDiff }

def bilinearCentralLieModel : SimplyConnectedSolvableLieModel := by
  let : T2Space (BilinearCentralGroup B.toLinearMap₁₂) := inferInstanceAs (T2Space (V × W))
  let : SecondCountableTopology (BilinearCentralGroup B.toLinearMap₁₂) := inferInstanceAs (SecondCountableTopology (V × W))
  let : SimplyConnectedSpace (BilinearCentralGroup B.toLinearMap₁₂) := inferInstanceAs (SimplyConnectedSpace (V × W))
  exact { modelSpace := V × W, carrier := (BilinearCentralGroup B.toLinearMap₁₂) }

end PolycyclicRecognition

end

end OAI
