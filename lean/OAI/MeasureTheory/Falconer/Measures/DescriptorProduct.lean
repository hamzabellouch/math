import OAI.MeasureTheory.Falconer.Estimates.DescriptorMasks
import OAI.MeasureTheory.Falconer.Estimates.ReachedMasks

namespace OAI

/-! # Actual descriptor products and their reached angular factors -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def descriptorProduct (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (x : Space d) (w : Sphere d) : ℝ :=
  ∏ b ∈ B, descriptorMask Q ρ m N σ J i b (S b) x w

theorem descriptorProduct_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorProduct Q ρ m N σ J i B S)) :=
  Finset.measurable_prod B (fun b _ => descriptorMask_measurable Q ρ m N σ J i b (S b))

theorem descriptorProduct_bounds (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d, ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (x : Space d) (w : Sphere d) :
    0 ≤ descriptorProduct Q ρ m N σ J i B S x w ∧
      descriptorProduct Q ρ m N σ J i B S x w ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun b hb =>
      (descriptorMask_bounds Q ρ m N σ J i b (S b) (hcover b hb) x w).1)
  · exact Finset.prod_le_one₀ (fun b hb =>
      (descriptorMask_bounds Q ρ m N σ J i b (S b) (hcover b hb) x w).1)
      (fun b hb => (descriptorMask_bounds Q ρ m N σ J i b (S b) (hcover b hb) x w).2)

theorem descriptorProduct_support (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d, ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    {x : Space d} {w : Sphere d} (h : descriptorProduct Q ρ m N σ J i B S x w ≠ 0) :
    ∀ b ∈ B, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  intro b hb
  apply descriptorMask_support Q ρ m N σ J i b (S b) (hcover b hb) w
  exact (Finset.prod_ne_zero_iff.mp h) b hb

theorem uniform_descriptorProduct_core {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (B : Finset PolicyDescriptor), (∀ b ∈ B, descriptorValid N b) →
      ∀ (S : PolicyDescriptor → Finset (Sphere d)),
      (∀ b ∈ B, ∀ w : Sphere d,
        ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (i : ℕ) (x : Space d), x ∈ Q.carrier → ∀ w : Sphere d,
      (∀ b ∈ B, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b) →
      descriptorProduct Q ρ m N σ J i B S x w = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorMask_core (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m B hB S hS i x hx w hw
  apply Finset.prod_eq_one
  intro b hb
  exact h₀ N hN Q hQ ρ m b (hB b hb) (S b) (hS b hb) i x hx w (hw b hb)

theorem descriptorProduct_pair_support (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    {x y : Space d}
    (h : descriptorProduct Q ρ m N σ J i B S x (normalizeToSphere w₀ (x-y)) *
      descriptorProduct Q ρ m N σ J i B S y (normalizeToSphere w₀ (x-y)) ≠ 0) :
    (x,y) ∈ descriptorPairTests w₀ Q ρ m N σ J (i+1) B := by
  intro b hb
  exact ⟨descriptorProduct_support Q ρ m N σ J i B S hcover
      (mul_ne_zero_iff.mp h).1 b hb,
    descriptorProduct_support Q ρ m N σ J i B S hcover (mul_ne_zero_iff.mp h).2 b hb⟩

theorem descriptorMask_reached_on_cell (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (X : List (Fin d → Bool))
    (hb : descriptorAnchor b ≤ X.length) {x : Space d}
    (hx : x ∈ (Q.descendant X).carrier) (w : Sphere d) :
    descriptorMask Q ρ m N σ J i b S x w =
      descriptorMask Q ρ m N σ J i b S (Q.descendant X).center w := by
  let F := fun P => fun w : Sphere d =>
    capCutoffAmbient (descriptorMaskRadius N σ b) (descriptorMaskRadius_pos N σ b) S
      (descriptorGoodDirections Q ρ m N σ J (i+1) P b) w
  have hlen : (X.take (descriptorAnchor b)).length = descriptorAnchor b := by
    simp only [List.length_take,Nat.min_eq_left hb]
  have he (y : Space d) (hy : y ∈ (Q.descendant X).carrier) :
      descriptorMask Q ρ m N σ J i b S y w = F (X.take (descriptorAnchor b)) w := by
    exact anchoredMask_reached Q F (X.take (descriptorAnchor b))
      (X.drop (descriptorAnchor b)) hlen (by simpa only [List.take_append_drop] using hy) w
  exact (he x hx).trans (he _ ((Q.descendant X).center_mem (Q.descendant_side_pos hQ X))).symm

theorem descriptorProduct_reached_split (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (X : List (Fin d → Bool)) {x : Space d} (hx : x ∈ (Q.descendant X).carrier)
    (w : Sphere d) :
    descriptorProduct Q ρ m N σ J i B S x w =
      descriptorProduct Q ρ m N σ J i (B.filter (fun b => descriptorAnchor b ≤ X.length))
        S (Q.descendant X).center w *
      descriptorProduct Q ρ m N σ J i (B.filter (fun b => X.length < descriptorAnchor b))
        S x w := by
  have he := (Finset.prod_filter_mul_prod_filter_not B
    (fun b => descriptorAnchor b ≤ X.length)
    (fun b => descriptorMask Q ρ m N σ J i b (S b) x w)).symm
  rw [show (B.filter (fun b => ¬descriptorAnchor b ≤ X.length)) =
    B.filter (fun b => X.length < descriptorAnchor b) from by ext b; simp] at he
  refine he.trans ?_
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  exact descriptorMask_reached_on_cell Q hQ ρ m N σ J i b (S b) X
    (Finset.mem_filter.mp hb).2 hx w

theorem endpointTransform_descriptorProduct_split (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (X : List (Fin d → Bool)) (μ : Measure (Space d)) (M : ℝ)
    (b : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict (Q.descendant X).carrier) M
      (fun x w => (descriptorProduct Q ρ m N σ J i B S x w:ℂ)*b x w) r w =
    (descriptorProduct Q ρ m N σ J i (B.filter (fun c => descriptorAnchor c ≤ X.length))
      S (Q.descendant X).center w:ℂ) *
      endpointTransform (μ.restrict (Q.descendant X).carrier) M
        (fun x w => (descriptorProduct Q ρ m N σ J i
          (B.filter (fun c => X.length < descriptorAnchor c)) S x w:ℂ)*b x w) r w := by
  rw [← endpointTransform_angular_factor (μ.restrict (Q.descendant X).carrier) M
    (fun x w => (descriptorProduct Q ρ m N σ J i
      (B.filter (fun c => X.length < descriptorAnchor c)) S x w:ℂ)*b x w)
    (fun w => (descriptorProduct Q ρ m N σ J i
      (B.filter (fun c => descriptorAnchor c ≤ X.length)) S (Q.descendant X).center w:ℂ)) r w]
  unfold endpointTransform
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (Q.descendant X).measurable] with x hx
  rw [descriptorProduct_reached_split Q hQ ρ m N σ J i B S X hx w,Complex.ofReal_mul]
  ring

end Falconer

end OAI
