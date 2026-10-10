import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinInput
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! # The BCH exponential image is a subgroup

Once local exponential coordinates put a neighborhood in the image,
connectedness gives surjectivity. No injectivity is needed for this step.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

def exponentialRangeSubgroup
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hprod : ∀ x y, Exp x * Exp y = Exp (finiteDynkinPolynomial coeff ![x, y])) :
    Subgroup G where
  carrier := range Exp
  one_mem' := ⟨0, hExp.map_zero⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨finiteDynkinPolynomial coeff ![x, y], (hprod x y).symm⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, hExp.map_neg x⟩

theorem exponential_surjective_of_range_mem_nhds [PreconnectedSpace G]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hprod : ∀ x y, Exp x * Exp y = Exp (finiteDynkinPolynomial coeff ![x, y]))
    (hopen : range Exp ∈ 𝓝 (1 : G)) : Function.Surjective Exp := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let H := exponentialRangeSubgroup hExp coeff hprod
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hopen
  have htop : (H : Set G) = univ :=
    (show IsClopen (H : Set G) from ⟨H.isClosed_of_isOpen hH, hH⟩).eq_univ ⟨1, H.one_mem⟩
  intro g
  exact (show g ∈ (H : Set G) from htop ▸ mem_univ g)

end PolycyclicRecognition

end

end OAI
