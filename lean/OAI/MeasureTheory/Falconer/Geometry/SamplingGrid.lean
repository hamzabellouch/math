import OAI.MeasureTheory.Falconer.Estimates.IidSampling
import OAI.MeasureTheory.Falconer.Incidence.GridCount
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-!
# Finite planar query balls for simultaneous iid estimates

Rounding one point of a ball to the spatial mesh and rounding its radius
up to an integer mesh multiple gives a query ball with radius at most
eight times the original radius. The number of queries is polynomial in
the reciprocal mesh. This is the finite-grid step in `ang:sample-caps`.
-/

namespace Falconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def planarMesh (δ : ℝ) (z : Fin 2 → ℤ) : Space 2 :=
  WithLp.toLp 2 (fun i => δ * (z i : ℝ))

noncomputable def planarGrid (L : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(L : ℤ)) (L : ℤ))

theorem planarGrid_card (L : ℕ) : (planarGrid L).card = (2*L+1)^2 := by
  have hc : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2*L+1 := by
    rw [Int.card_Icc]
    omega
  simp [planarGrid, Fintype.card_piFinset, hc]

theorem planar_mesh_approximation {δ : ℝ} (hδ : 0 < δ) {L : ℕ}
    (hL : δ⁻¹ + 1 ≤ L) (x : Space 2) (hx : ∀ i, |x i| ≤ 1) :
    ∃ z ∈ planarGrid L, dist x (planarMesh δ z) ≤ 2*δ := by
  let z : Fin 2 → ℤ := fun i => ⌊x i / δ⌋
  have hcoord (i : Fin 2) : 0 ≤ x i - δ * (z i : ℝ) ∧
      x i - δ * (z i : ℝ) ≤ δ := by
    have hf := Int.floor_le (x i / δ)
    have hg := Int.lt_floor_add_one (x i / δ)
    have hf' := (le_div_iff₀ hδ).mp hf
    have hg' := (div_lt_iff₀ hδ).mp hg
    change 0 ≤ x i - δ * (⌊x i / δ⌋ : ℝ) ∧ _
    constructor <;> nlinarith
  have hz : z ∈ planarGrid L := by
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hf := Int.floor_le (x i / δ)
    have hg := Int.lt_floor_add_one (x i / δ)
    have hxb := abs_le.mp (hx i)
    have hd := (div_le_div_iff_of_pos_right hδ).mpr hxb.2
    have hd' := (div_le_div_iff_of_pos_right hδ).mpr hxb.1
    have hr : (-(L : ℝ)) ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ L := by
      dsimp [z]
      rw [one_div] at hd
      norm_num only [neg_div, one_div] at hd'
      constructor <;> linarith
    exact_mod_cast hr
  refine ⟨z, hz, ?_⟩
  have hsq (i : Fin 2) : dist (x i) (planarMesh δ z i)^2 ≤ δ^2 := by
    rw [Real.dist_eq, sq_abs]
    change (x i - δ * (z i : ℝ))^2 ≤ δ^2
    exact (sq_le_sq₀ (hcoord i).1 hδ.le).mpr (hcoord i).2
  have hd := EuclideanSpace.dist_sq_eq x (planarMesh δ z)
  simp only [Fin.sum_univ_two] at hd
  nlinarith [hsq 0, hsq 1, dist_nonneg (x := x) (y := planarMesh δ z)]

noncomputable def planarQueries (L H : ℕ) : Finset ((Fin 2 → ℤ) × ℤ) :=
  planarGrid L ×ˢ Finset.Icc 1 (H : ℤ)

theorem planarQueries_card (L H : ℕ) :
    (planarQueries L H).card = (2*L+1)^2 * H := by
  simp [planarQueries, planarGrid_card, Int.card_Icc]

theorem planar_ball_query {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hr : r ≤ 1)
    {L H : ℕ} (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    {X : Type*} (p : X → Space 2) (hp : ∀ x i, |p x i| ≤ 1)
    (c : Space 2) (x₀ : X) (hx₀ : dist (p x₀) c ≤ r) :
    ∃ j ∈ planarQueries L H,
      {x | dist (p x) c ≤ r} ⊆ {x | dist (p x) (planarMesh δ j.1) ≤ 4*(j.2 : ℝ)*δ} ∧
      δ ≤ 4*(j.2 : ℝ)*δ ∧ 4*(j.2 : ℝ)*δ ≤ 8*r := by
  obtain ⟨z, hz, hclose⟩ := planar_mesh_approximation hδ hL (p x₀) (hp x₀)
  let m : ℤ := ⌈r/δ⌉
  have hmlo : (1 : ℤ) ≤ m := by
    have hh : (0 : ℝ) < r/δ := div_pos (hδ.trans_le hδr) hδ
    exact Int.add_one_le_iff.mpr (Int.ceil_pos.mpr hh)
  have hmhi : m ≤ (H : ℤ) := by
    apply Int.ceil_le.mpr
    have hh := (div_le_div_iff_of_pos_right hδ).mpr hr
    rw [one_div] at hh
    exact hh.trans hH
  have hmr : r ≤ (m : ℝ)*δ :=
    (div_le_iff₀ hδ).mp (Int.le_ceil (r/δ))
  have hmr' : (m : ℝ)*δ ≤ 2*r := by
    have hh := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (r/δ)) hδ
    rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at hh
    change (⌈r/δ⌉ : ℝ)*δ ≤ 2*r
    nlinarith
  refine ⟨(z,m), Finset.mem_product.mpr ⟨hz, Finset.mem_Icc.mpr ⟨hmlo,hmhi⟩⟩, ?_, ?_, ?_⟩
  · intro x hx
    change dist (p x) c ≤ r at hx
    have ht := dist_triangle (p x) c (planarMesh δ z)
    have ht' := dist_triangle c (p x₀) (planarMesh δ z)
    rw [dist_comm c (p x₀)] at ht'
    change dist (p x) (planarMesh δ z) ≤ 4*(m : ℝ)*δ
    nlinarith
  · dsimp only
    nlinarith
  · dsimp only
    nlinarith

end Falconer

end OAI
