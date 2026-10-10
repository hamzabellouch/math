import Mathlib

namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach

theorem normalized_embedding_of_finite
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [ProperSpace E]
    (o : X) {A : ℝ} (hA : 0 ≤ A)
    (hfinite : ∀ s : Finset X, ∃ f : s → E, ∀ x y : s,
      dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ A * dist x y) :
    ∃ f : X → E, ∀ x y : X,
      dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ A * dist x y := by
  classical
  let Q : Set (X → E) := {f | ∀ x, f x ∈ closedBall 0 (A * dist o x)}
  have hQ : IsCompact Q := isCompact_pi_infinite fun x => isCompact_closedBall _ _
  let C : X × X → Set (X → E) := fun p => {f |
    dist p.1 p.2 ≤ dist (f p.1) (f p.2) ∧
      dist (f p.1) (f p.2) ≤ A * dist p.1 p.2}
  have hC (p : X × X) : IsClosed (C p) :=
    (isClosed_le continuous_const ((continuous_apply p.1).dist (continuous_apply p.2))).inter
      (isClosed_le ((continuous_apply p.1).dist (continuous_apply p.2)) continuous_const)
  have hFIP (u : Finset (X × X)) : (Q ∩ ⋂ p ∈ u, C p).Nonempty := by
    let s : Finset X := insert o (u.image Prod.fst ∪ u.image Prod.snd)
    have ho : o ∈ s := by simp [s]
    obtain ⟨f, hf⟩ := hfinite s
    let g : X → E := fun x => if hx : x ∈ s then f ⟨x, hx⟩ - f ⟨o, ho⟩ else 0
    refine ⟨g, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ s
      · simp only [g, dite_eq_left hx, mem_closedBall, dist_zero_right]
        simpa only [dist_eq_norm, Subtype.dist_eq, dist_comm o x] using (hf ⟨x, hx⟩ ⟨o, ho⟩).2
      · simp only [g, dite_eq_right hx, mem_closedBall, dist_self]
        exact mul_nonneg hA dist_nonneg
    · simp only [mem_iInter]
      intro p hp
      have hx : p.1 ∈ s := by simp [s, Finset.mem_image_of_mem _ hp]
      have hy : p.2 ∈ s := by simp [s, Finset.mem_image_of_mem _ hp]
      change dist p.1 p.2 ≤ dist (g p.1) (g p.2) ∧
        dist (g p.1) (g p.2) ≤ A * dist p.1 p.2
      simpa only [g, dite_eq_left hx, dite_eq_left hy, dist_sub_right, Subtype.dist_eq] using
        hf ⟨p.1, hx⟩ ⟨p.2, hy⟩
  obtain ⟨f, _, hf⟩ := hQ.inter_iInter_nonempty C hC hFIP
  refine ⟨f, fun x y => ?_⟩
  exact mem_iInter.mp hf (x, y)

                                                                
theorem normalized_embedding_of_scaled
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {a A : ℝ} (ha : 0 < a)
    (hf : ∀ x y, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ A * a * dist x y) :
    ∃ g : X → E, ∀ x y,
      dist x y ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ A * dist x y := by
  let g : X → E := fun x => a⁻¹ • f x
  have hd (x y : X) : dist (g x) (g y) = a⁻¹ * dist (f x) (f y) := by
    simp only [g, dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
  refine ⟨g, fun x y => ?_⟩
  rw [hd]
  constructor
  · calc
      dist x y = a⁻¹ * (a * dist x y) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hf x y).1 (inv_nonneg.mpr ha.le)
  · calc
      a⁻¹ * dist (f x) (f y) ≤ a⁻¹ * (A * a * dist x y) :=
        mul_le_mul_of_nonneg_left (hf x y).2 (inv_nonneg.mpr ha.le)
      _ = A * dist x y := by field_simp

                                                                                 
                                                          
theorem finite_witness_of_no_embedding
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (o : X) {A : ℝ} (hA : 0 ≤ A)
    (hno : ¬ ∃ f : X → E, ∀ x y,
      dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ A * dist x y) :
    ∃ s : Finset X, ¬ ∃ f : s → E, ∃ a : ℝ, 0 < a ∧
      ∀ x y : s, a * dist x y ≤ dist (f x) (f y) ∧
        dist (f x) (f y) ≤ A * a * dist x y := by
  classical
  by_contra! h
  apply hno
  apply normalized_embedding_of_finite o hA
  intro s
  obtain ⟨f, a, ha, hf⟩ := h s
  exact normalized_embedding_of_scaled ha hf

end CompactBanach
end

end OAI
