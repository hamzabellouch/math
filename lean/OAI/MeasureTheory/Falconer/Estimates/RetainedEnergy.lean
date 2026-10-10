import OAI.MeasureTheory.Falconer.Graphs.EligibleDyadicGraph
import OAI.MeasureTheory.Falconer.Estimates.EnergySplitting

namespace OAI

/-!
# Integrated estimate for the actual retained dyadic graph

This is the positive Schur step after localization. It uses the two
original restricted laws and retains their endpoint symbols on every
child. Summing the angular partition introduces no cap-count factor.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem retained_dyadic_energy_bound {d n g₁ g₂ L C₁ C₂ : ℕ} {κ : Type*}
    (Q₁ Q₂ : DyadicCube d) (hQ : 0 < Q₁.side) (hside : Q₂.side = Q₁.side)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    (K : Finset κ) (η : κ → Sphere d → ℝ) (center : κ → Sphere d)
    (hη : ∀ k ∈ K, ∀ w, 0 ≤ η k w)
    (hpartition : ∀ w, ∑ k ∈ K, η k w = 1)
    {δ τ W₁ W₂ : ℝ} (hδ : 0 ≤ δ)
    (hcap : ∀ k ∈ K, ∀ w, 0 < η k w → ‖(w : Space d)-center k‖ ≤ δ)
    (hg₁ : g₁ ≤ n) (hg₂ : g₂ ≤ n)
    (hL : 4*τ*((2 : ℝ)^n/Q₁.side) ≤ L)
    (hwidth₁ : 2*τ+2*δ*(Real.sqrt d*(Q₁.side/(2 : ℝ)^g₁)) ≤ W₁)
    (hwidth₂ : 2*τ+2*δ*(Real.sqrt d*(Q₂.side/(2 : ℝ)^g₂)) ≤ W₂)
    (hsupport₁ : ∀ p ∈ Q₁.occupiedPaths μ n,
      ∀ᵐ x ∂μ.restrict (Q₁.descendant p).carrier,
        ∀ w : Sphere d, b x w ≠ 0 →
          DyadicParallelTest Q₁ (Q₁.occupiedPaths μ n) g₁ p (w : Space d) W₁ C₁)
    (hsupport₂ : ∀ p ∈ Q₂.occupiedPaths ν n,
      ∀ᵐ x ∂ν.restrict (Q₂.descendant p).carrier,
        ∀ w : Sphere d, c x w ≠ 0 →
          DyadicParallelTest Q₂ (Q₂.occupiedPaths ν n) g₂ p (w : Space d) W₂ C₂)
    (a p v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    (2 : ℝ)^((d : ℝ)*(v-a)) *
      ‖∫ z, ∑ k ∈ K ×ˢ K, (η k.1 z.2.1 * η k.2 z.2.2) •
        (∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          ∑ col ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          if eligibleDyadicEdge Q₁ Q₂
              (Q₁.eligiblePaths μ n (η k.1) b) (Q₂.eligiblePaths ν n (η k.2) c)
              (center k.1) (center k.2) τ row col then
            dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c row z *
              star (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c col z) else 0)
        ∂angularProductMeasure d v Ψ‖ ≤
    (2 : ℝ)^((d : ℝ)*(p-a)) *
      ((2*L+1)^d * min (C₁*2^(d*g₁)) (C₂*2^(d*g₂)) : ℕ) *
      ∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) M₁ b z.1 z.2)
          (fun z => endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) M₂ c z.1 z.2) := by
  let S := Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n
  let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
    (Q₁.eligiblePaths μ n (η k.1) b) (Q₂.eligiblePaths ν n (η k.2) c)
    (center k.1) (center k.2) τ
  let D : ℕ := (2*L+1)^d * min (C₁*2^(d*g₁)) (C₂*2^(d*g₂))
  have hlen₁ : ∀ q ∈ Q₁.occupiedPaths μ n, q.length = n := by
    intro q hq
    exact (mem_cubePaths d n q).mp (Finset.mem_filter.mp hq).1
  have hlen₂ : ∀ q ∈ Q₂.occupiedPaths ν n, q.length = n := by
    intro q hq
    exact (mem_cubePaths d n q).mp (Finset.mem_filter.mp hq).1
  have hdegree (k : κ × κ) (hk : k ∈ K ×ˢ K)
      (row : List (Fin d → Bool) × List (Fin d → Bool)) :
      (S.filter (G k row)).card ≤ D := by
    obtain ⟨hk₁,hk₂⟩ := Finset.mem_product.mp hk
    apply eligibleDyadic_degree Q₁ Q₂ hQ hside _ _
      (fun q hq => hlen₁ q (Q₁.eligiblePaths_subset μ n (η k.1) b hq))
      (fun q hq => hlen₂ q (Q₂.eligiblePaths_subset ν n (η k.2) c hq))
      hg₁ hg₂ _ _ (sphere_norm _) (sphere_norm _) hδ hL hwidth₁ hwidth₂
    · exact Q₁.eligiblePaths_witnesses μ (η k.1) b (center k.1) δ W₁
        (hη k.1 hk₁) (hcap k.1 hk₁) hsupport₁
    · exact Q₂.eligiblePaths_witnesses ν (η k.2) c (center k.2) δ W₂
        (hη k.2 hk₂) (hcap k.2 hk₂) hsupport₂
  have hcolumn (k : κ × κ) (hk : k ∈ K ×ˢ K)
      (col : List (Fin d → Bool) × List (Fin d → Bool)) :
      (S.filter (fun row => G k row col)).card ≤ D := by
    have he : S.filter (fun row => G k row col) = S.filter (G k col) := by
      apply Finset.filter_congr
      intro row _
      exact eligibleDyadicEdge_symm Q₁ Q₂ _ _ _ _ τ row col
    rw [he]
    exact hdegree k hk col
  let U := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    fun z : ℝ × Sphere d =>
      endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) M₁ b z.1 z.2
  let V := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    fun z : ℝ × Sphere d =>
      endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) M₂ c z.1 z.2
  let bound₁ := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    B * (μ.restrict (Q₁.descendant row.1).carrier).real Set.univ / M₁
  let bound₂ := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    C * (ν.restrict (Q₂.descendant row.2).carrier).real Set.univ / M₂
  have hs := independentAngularEnergy_graph_schur p v Ψ S (K ×ˢ K) G U V
    (fun _ _ => measurable_endpointTransform _ _ _ hb)
    (fun _ _ => measurable_endpointTransform _ _ _ hc)
    bound₁ bound₂ (fun _ _ => by dsimp [bound₁]; positivity)
    (fun _ _ => by dsimp [bound₂]; positivity)
    (fun _ _ z => endpointTransform_norm_le _ hM₁ b hbB z.1 z.2)
    (fun _ _ z => endpointTransform_norm_le _ hM₂ c hcC z.1 z.2)
    (fun k z => η k.1 z.2.1 * η k.2 z.2.2) D
    (fun z k hk => mul_nonneg (hη k.1 (Finset.mem_product.mp hk).1 z.2.1)
      (hη k.2 (Finset.mem_product.mp hk).2 z.2.2))
    (fun z => by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, hpartition, hpartition, one_mul])
    (fun k hk row _ => by exact_mod_cast hdegree k hk row)
    (fun k hk col _ => by exact_mod_cast hcolumn k hk col)
  have hexp : (2 : ℝ)^((d : ℝ)*(v-a)) =
      (2 : ℝ)^((d : ℝ)*(p-a)) * (2 : ℝ)^((d : ℝ)*(v-p)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hexp]
  simpa only [mul_assoc, S, G, U, V, D, dyadicPairTransform, angularProductMeasure] using
    mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg (by norm_num) _)

end Falconer

end OAI
