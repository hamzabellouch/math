import OAI.NumberTheory.DirichletL.Detector.MellinScaling
import OAI.NumberTheory.DirichletL.Detector.SourceTriple

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma sourceMellinWeight_subset (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q R : ℝ)
    (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hQ : 0<Q) (hR : 0<R)
    (a x w z : ℂ) :
    ((Q^(-(3/2:ℝ)):ℝ):ℂ)*a*sourceMellinWeight W0 W1 (X/Q) (Y/Q) (Z*R) x w z=
      sourceMellinWeight W0 W1 X Y Z x w z*(Q:ℂ)^(z-w-1)*a*(R:ℂ)^(x+z-1) := by
  rw [sourceMellinWeight_marked W0 W1 (X/Q) (Y/Q) Z R hZ hR x w z]
  calc
    _ = a*(R:ℂ)^(x+z-1)*
        (((Q^(-(3/2:ℝ)):ℝ):ℂ)*sourceMellinWeight W0 W1 (X/Q) (Y/Q) Z x w z) := by ring
    _ = _ := by rw [sourceMellinWeight_rescaled W0 W1 X Y Z Q hX hY hQ x w z];ring

lemma tuple_norm_pos {K : ℕ} (p : Fin K→ActualEisensteinCubic.O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) : 0<elementNorm (∏i∈J,p i) := by
  apply elementNorm_pos
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

end SevenEighths.ProbePhysical
end

end OAI
