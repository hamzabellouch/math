import OAI.MeasureTheory.Falconer.Estimates.DescriptorAmbient
import OAI.MeasureTheory.Falconer.Measures.DescriptorProduct

namespace OAI

/-! # Ambient products preserve every original descriptor support -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
variable {d : ℕ}

noncomputable def descriptorAmbientProduct (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x z : Space d) : ℝ :=
  ∏ b ∈ B, descriptorAmbientMask Q ρ m N σ J i b (S b) x z

 theorem descriptorAmbientProduct_sphere (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) (w : Sphere d) :
    descriptorAmbientProduct Q ρ m N σ J i B S x w = descriptorProduct Q ρ m N σ J i B S x w := by
  simp only [descriptorAmbientProduct,descriptorProduct,descriptorAmbientMask_sphere]

 theorem descriptorAmbientProduct_contDiff (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) :
    ContDiff ℝ ∞ (descriptorAmbientProduct Q ρ m N σ J i B S x) :=
  contDiff_prod (fun b _ => descriptorAmbientMask_contDiff Q ρ m N σ J i b (S b) x)

 theorem descriptorAmbientProduct_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorAmbientProduct Q ρ m N σ J i B S)) :=
  Finset.measurable_prod B (fun b _ => descriptorAmbientMask_measurable Q ρ m N σ J i b (S b))

theorem descriptorAmbientProduct_reached_on_cell (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (X : List (Fin d → Bool))
    (hB : ∀ b ∈ B, PlanarFalconer.descriptorAnchor b ≤ X.length)
    {x : Space d} (hx : x ∈ (Q.descendant X).carrier) :
    descriptorAmbientProduct Q ρ m N σ J i B S x =
      descriptorAmbientProduct Q ρ m N σ J i B S (Q.descendant X).center := by
  funext z
  apply Finset.prod_congr rfl
  intro b hb
  let p := X.take (PlanarFalconer.descriptorAnchor b)
  have hp : p.length = PlanarFalconer.descriptorAnchor b := by
    simp only [p,List.length_take,Nat.min_eq_left (hB b hb)]
  have hsub : (Q.descendant X).carrier ⊆ (Q.descendant p).carrier := by
    have he : Q.descendant X = (Q.descendant p).descendant
        (X.drop (PlanarFalconer.descriptorAnchor b)) := by
      rw [← Q.descendant_append]
      simp only [p,List.take_append_drop]
    rw [he]
    exact (Q.descendant p).descendant_subset _
  rw [descriptorAmbientMask_on_cell Q ρ m N σ J i b (S b) p hp (hsub hx),
    descriptorAmbientMask_on_cell Q ρ m N σ J i b (S b) p hp
      (hsub ((Q.descendant X).center_mem (Q.descendant_side_pos hQ X)))]

 theorem descriptorAmbientProduct_tsupport_good (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) (w : Sphere d)
    (hw : (w : Space d) ∈ tsupport (descriptorAmbientProduct Q ρ m N σ J i B S x)) :
    ∀ b ∈ B, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  classical
  intro b hb
  apply descriptorAmbientMask_tsupport_good Q ρ m N σ J i b (S b) x w
  have hs : Function.support (descriptorAmbientProduct Q ρ m N σ J i B S x) ⊆
      Function.support (descriptorAmbientMask Q ρ m N σ J i b (S b) x) := by
    intro z hz
    exact (Finset.prod_ne_zero_iff.mp hz) b hb
  exact closure_mono hs hw

 theorem descriptorAmbientProduct_derivative_good (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) (w : Sphere d)
    (k : ℕ) (hw : iteratedFDeriv ℝ k (descriptorAmbientProduct Q ρ m N σ J i B S x) w ≠ 0) :
    ∀ b ∈ B, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b :=
  descriptorAmbientProduct_tsupport_good Q ρ m N σ J i B S x w
    (support_iteratedFDeriv_subset (𝕜 := ℝ) k hw)

 theorem descriptorAmbientProduct_complex_tsupport_good (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) (w : Sphere d)
    (hw : (w : Space d) ∈ tsupport (fun z => (descriptorAmbientProduct Q ρ m N σ J i B S x z : ℂ))) :
    ∀ b ∈ B, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  apply descriptorAmbientProduct_tsupport_good Q ρ m N σ J i B S x w
  have he : Function.support (fun z => (descriptorAmbientProduct Q ρ m N σ J i B S x z : ℂ)) =
      Function.support (descriptorAmbientProduct Q ρ m N σ J i B S x) := by
    ext z
    simp only [Function.mem_support,ne_eq,Complex.ofReal_eq_zero]
  change (w : Space d) ∈ closure _ at hw ⊢
  rwa [he] at hw

end Falconer

end OAI
