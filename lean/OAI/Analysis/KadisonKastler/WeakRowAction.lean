import OAI.Analysis.KadisonKastler.WeakMapCompact
import OAI.Analysis.KadisonKastler.FiniteRowOrbit

namespace OAI

/-! Finite row averages act continuously on the compact completely bounded ball. -/

namespace KadisonKastler

noncomputable section

open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance weakRowActionOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance weakRowActionStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem boundedWeakAlgebraCoefficients_injective (M : VonNeumannAlgebra H) (c : ℝ) :
    Function.Injective (boundedWeakAlgebraCoefficients (M := M) (c := c)) := by
  intro F G h
  have hm : F.map = G.map := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_left ℂ
    intro η
    exact congrFun h (a, ξ, η)
  cases F
  cases G
  cases hm
  rfl

instance boundedWeakAlgebraMapT2 (M : VonNeumannAlgebra H) (c : ℝ) :
    T2Space (BoundedWeakAlgebraMap M c) :=
  (boundedWeakAlgebraCoefficients_injective M c).isEmbedding_induced.t2Space

def boundedWeakRowAverage {M : VonNeumannAlgebra H} {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ} (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
    (F : BoundedWeakAlgebraMap M c) : BoundedWeakAlgebraMap M c :=
  ⟨finiteRightAverage r F.map, F.bound.finiteRightAverage hc r hr⟩

theorem boundedWeakRowAverage_coefficient {M : VonNeumannAlgebra H} {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ} (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
    (F : BoundedWeakAlgebraMap M c) (a : Algebra M) (ξ η : H) :
    boundedWeakAlgebraCoefficients (boundedWeakRowAverage hc r hr F) (a, ξ, η) =
      ∑ i, boundedWeakAlgebraCoefficients F (a * r i, (star (r i) : H →L[ℂ] H) ξ, η) := by
  change inner ℂ η ((finiteRightAverage r F.map a : H →L[ℂ] H) ξ) = _
  simp [finiteRightAverage_apply, boundedWeakAlgebraCoefficients]

theorem continuous_boundedWeakRowAverage {M : VonNeumannAlgebra H} {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ} (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1) :
    Continuous (boundedWeakRowAverage hc r hr) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro t
  change Continuous (fun F : BoundedWeakAlgebraMap M c =>
    boundedWeakAlgebraCoefficients (boundedWeakRowAverage hc r hr F) (t.1, t.2.1, t.2.2))
  simp_rw [boundedWeakRowAverage_coefficient]
  apply continuous_finsetSum
  intro i _
  have hcoeff : Continuous (boundedWeakAlgebraCoefficients (M := M) (c := c)) :=
    continuous_induced_dom
  exact (continuous_apply (t.1 * r i, (star (r i) : H →L[ℂ] H) t.2.1, t.2.2)).comp
    hcoeff

end

end KadisonKastler

end OAI
