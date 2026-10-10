import OAI.MeasureTheory.Falconer.Measures.DescriptorProduct
import OAI.MeasureTheory.Falconer.Graphs.DescriptorGraph

namespace OAI

/-! # The retained descriptor product supplies the actual graph tests -/

namespace Falconer
open MeasureTheory
open PlanarFalconer (PolicyDescriptor)
variable {d : ℕ}

theorem descriptorProduct_graph_test (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ c ∈ B, ∀ w : Sphere d,
      ∃ z ∈ S c, dist w z ≤ descriptorMaskRadius N σ c/2)
    {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p) (hpar : .parallel g p ∈ B)
    (X P : List (Fin d → Bool)) (hX : X.length = a) (hP : P.length = p-a)
    {x : Space d} (hx : x ∈ ((Q.descendant X).descendant P).carrier)
    (w : Sphere d) (b : Space d → Sphere d → ℂ)
    (hnz : (descriptorProduct Q ρ m N σ J i B S x w : ℂ)*b x w ≠ 0) :
    DyadicParallelTest (Q.descendant X) ((Q.descendant X).occupiedPaths ρ (p-a))
      (g-a) P w (angularTestWidth N σ J (i+1) p)
      ⌈((2:ℝ)^N)^(PlanarFalconer.height
        (fun n : ℕ => m n-((d:ℝ)/2)*(n:ℝ)/N) g p+1000*((d:ℝ)+1)*σ)⌉₊ := by
  have hp : descriptorProduct Q ρ m N σ J i B S x w ≠ 0 := by
    intro h
    apply hnz
    simp only [h,Complex.ofReal_zero,zero_mul]
  exact descriptorEndpointGood_graph_test Q hQ ρ m N σ J (i+1)
    hag hgp X P hX hP hx w
    (descriptorProduct_support Q ρ m N σ J i B S hcover hp (.parallel g p) hpar)

end Falconer

end OAI
