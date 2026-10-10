import OAI.MeasureTheory.Falconer.Estimates.DyadicCenters
import OAI.MeasureTheory.Falconer.Estimates.EnergySplitting

namespace OAI

/-! # The near part of the independent angular energy

Nearness is imposed on both actual center displacements. Integer grid
packing gives a dimensional degree bound; positive Schur integration then
controls this part by the sum of the original child energies. No angular
localization or separation of the two parent cells is used.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem DyadicCube.neighbor_card {d n L : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (A : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (a : List (Fin d → Bool)) (ha : a.length = n)
    {τ : ℝ} (hL : τ*((2:ℝ)^n/Q.side) ≤ L) :
    (A.filter (fun p => ‖(Q.descendant p).center-(Q.descendant a).center‖ ≤ τ)).card ≤
      (2*L+1)^d := by
  classical
  let T := A.filter (fun p => ‖(Q.descendant p).center-(Q.descendant a).center‖ ≤ τ)
  have hinj : Set.InjOn dyadicCode (↑T : Set (List (Fin d → Bool))) := by
    intro p hp q hq he
    exact dyadicCode_injective_at_depth (hA p (Finset.mem_filter.mp hp).1)
      (hA q (Finset.mem_filter.mp hq).1) he
  rw [← Finset.card_image_of_injOn hinj]
  apply grid_ball_card (show 0 < (2:ℝ)^n/Q.side by positivity) hL _ (dyadicCode a)
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hp,hnear⟩ := Finset.mem_filter.mp hp
  rwa [← Q.center_sub_eq_grid_sub p a (hA p hp) ha]

def nearDyadicEdge {d : ℕ} (Q₁ Q₂ : DyadicCube d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) : Prop :=
  ‖(Q₁.descendant col.1).center-(Q₁.descendant row.1).center‖ ≤ τ ∧
  ‖(Q₂.descendant col.2).center-(Q₂.descendant row.2).center‖ ≤ τ

theorem nearDyadicEdge_symm {d : ℕ} (Q₁ Q₂ : DyadicCube d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    nearDyadicEdge Q₁ Q₂ τ row col ↔ nearDyadicEdge Q₁ Q₂ τ col row := by
  simp only [nearDyadicEdge,norm_sub_rev]

theorem nearDyadic_degree {d n L : ℕ} (Q₁ Q₂ : DyadicCube d)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (A B : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hB : ∀ p ∈ B, p.length = n)
    {τ : ℝ} (hL₁ : τ*((2:ℝ)^n/Q₁.side) ≤ L)
    (hL₂ : τ*((2:ℝ)^n/Q₂.side) ≤ L)
    (row : List (Fin d → Bool) × List (Fin d → Bool)) (hr : row ∈ A ×ˢ B) :
    ((A ×ˢ B).filter (nearDyadicEdge Q₁ Q₂ τ row)).card ≤ (2*L+1)^(2*d) := by
  have heq : (A ×ˢ B).filter (nearDyadicEdge Q₁ Q₂ τ row) =
      (A.filter (fun p => ‖(Q₁.descendant p).center-(Q₁.descendant row.1).center‖ ≤ τ)) ×ˢ
      (B.filter (fun p => ‖(Q₂.descendant p).center-(Q₂.descendant row.2).center‖ ≤ τ)) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_product,nearDyadicEdge]
    tauto
  rw [heq,Finset.card_product]
  calc
    _ ≤ (2*L+1)^d*(2*L+1)^d := Nat.mul_le_mul
      (Q₁.neighbor_card hQ₁ A hA row.1 (hA _ (Finset.mem_product.mp hr).1) hL₁)
      (Q₂.neighbor_card hQ₂ B hB row.2 (hB _ (Finset.mem_product.mp hr).2) hL₂)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- The near contribution after exact model-mass splitting. This is the
analytic near reduction before the profile normalization. -/
theorem dyadic_near_energy_bound {d n L : ℕ} (Q₁ Q₂ : DyadicCube d)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    {τ : ℝ} (hL₁ : τ*((2:ℝ)^n/Q₁.side) ≤ L)
    (hL₂ : τ*((2:ℝ)^n/Q₂.side) ≤ L)
    (a p v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    (2:ℝ)^((d:ℝ)*(v-a)) *
      ‖∫ z, ∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        ∑ col ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          if nearDyadicEdge Q₁ Q₂ τ row col then
            dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c row z *
              star (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c col z) else 0
        ∂angularProductMeasure d v Ψ‖ ≤
    (2:ℝ)^((d:ℝ)*(p-a)) * ((2*L+1)^(2*d):ℕ) *
      ∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) M₁ b z.1 z.2)
          (fun z => endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) M₂ c z.1 z.2) := by
  let S := Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n
  let U := fun row : List (Fin d → Bool) × List (Fin d → Bool) => fun z : ℝ × Sphere d =>
    endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) M₁ b z.1 z.2
  let V := fun row : List (Fin d → Bool) × List (Fin d → Bool) => fun z : ℝ × Sphere d =>
    endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) M₂ c z.1 z.2
  let bound₁ := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    B*(μ.restrict (Q₁.descendant row.1).carrier).real Set.univ/M₁
  let bound₂ := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    C*(ν.restrict (Q₂.descendant row.2).carrier).real Set.univ/M₂
  have hdg (row : List (Fin d → Bool) × List (Fin d → Bool)) (hr : row ∈ S) :
      (S.filter (nearDyadicEdge Q₁ Q₂ τ row)).card ≤ (2*L+1)^(2*d) :=
    nearDyadic_degree Q₁ Q₂ hQ₁ hQ₂ _ _
      (fun q hq => (mem_cubePaths d n q).mp (Finset.mem_filter.mp hq).1)
      (fun q hq => (mem_cubePaths d n q).mp (Finset.mem_filter.mp hq).1) hL₁ hL₂ row hr
  have hcol (col : List (Fin d → Bool) × List (Fin d → Bool)) (hc : col ∈ S) :
      (S.filter (fun row => nearDyadicEdge Q₁ Q₂ τ row col)).card ≤ (2*L+1)^(2*d) := by
    simpa only [nearDyadicEdge_symm Q₁ Q₂ τ _ col] using hdg col hc
  have hs := independentAngularEnergy_graph_schur p v Ψ S ({()} : Finset Unit)
    (fun _ => nearDyadicEdge Q₁ Q₂ τ) U V
    (fun _ _ => measurable_endpointTransform _ _ _ hb)
    (fun _ _ => measurable_endpointTransform _ _ _ hc)
    bound₁ bound₂ (fun _ _ => by dsimp [bound₁]; positivity)
    (fun _ _ => by dsimp [bound₂]; positivity)
    (fun _ _ z => endpointTransform_norm_le _ hM₁ b hbB z.1 z.2)
    (fun _ _ z => endpointTransform_norm_le _ hM₂ c hcC z.1 z.2)
    (fun _ _ => 1) ((2*L+1)^(2*d):ℕ)
    (by intros; norm_num) (by intros; simp)
    (fun _ _ row hr => by exact_mod_cast hdg row hr)
    (fun _ _ col hc => by exact_mod_cast hcol col hc)
  simp only [Finset.sum_singleton,one_smul] at hs
  have hexp : (2:ℝ)^((d:ℝ)*(v-a)) =
      (2:ℝ)^((d:ℝ)*(p-a))*(2:ℝ)^((d:ℝ)*(v-p)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  rw [hexp]
  simpa only [mul_assoc,S,U,V,dyadicPairTransform,angularProductMeasure] using
    mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg (by norm_num) ((d:ℝ)*(p-a)))

end Falconer

end OAI
