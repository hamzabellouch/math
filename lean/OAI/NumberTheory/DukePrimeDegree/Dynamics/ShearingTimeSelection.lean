import OAI.NumberTheory.DukePrimeDegree.Geometry.AffineTimeSelection

namespace OAI

/-!
# One time for two points and two shearing scales

The finite bad-window estimate selects the common time in EKL (2006),
Lemma 4.6. For each point and each scale the loss is at most nine times
the original density error. The four losses total at most thirty-six.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree

theorem exists_common_two_scale_time
    {Y : Type*} (Φ : ℝ → Y → Y) (G H : Set Y) (z : Fin 2 → Y)
    (T ε : ℝ) (hT : 0 < T) (hε : 36 * ε < 1)
    (θ η : Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hG : ∀ k, volume.real (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) ≤ ε * T)
    (hH : ∀ k, volume.real (Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}) ≤ ε * (4 * T)) :
    ∃ τ ∈ Ioc 0 T, (∀ k, Φ τ (z k) ∈ G) ∧
      ∀ k q, Φ ((θ q + (2 - η q) * τ) / 2) (z k) ∈ H := by
  let A : Fin 2 → Set ℝ := fun k => Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}
  let E : Fin 2 → Set ℝ := fun k => Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}
  let B : Fin 2 × Fin 2 → Set ℝ := fun p => A p.1 ∪
    (Ioc 0 T ∩ ((fun τ => (θ p.2 + (2 - η p.2) * τ) / 2) ⁻¹' E p.1))
  have hB : ∀ p, B p ⊆ Ioc 0 T := by
    intro p τ hτ
    rcases hτ with hτ | hτ <;> exact hτ.1
  have hbad (p : Fin 2 × Fin 2) : volume.real (B p) ≤ (9 * ε) * T := by
    have hpull := ekl_pullback_bad_time_bound T (θ p.2) (η p.2) ε (hη p.2)
      (E p.1) inter_subset_left (hH p.1)
    have hu := measureReal_union_le (μ := volume) (A p.1)
      (Ioc 0 T ∩ ((fun τ => (θ p.2 + (2 - η p.2) * τ) / 2) ⁻¹' E p.1))
    change volume.real (B p) ≤ volume.real (A p.1) + _ at hu
    have hg : volume.real (A p.1) ≤ ε * T := hG p.1
    linarith
  have hsum : ∑ _p : Fin 2 × Fin 2, (9 * ε) < 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have havoid : ∃ τ ∈ Ioc 0 T, ∀ p : Fin 2 × Fin 2, τ ∉ B p := by
    by_contra h
    have hcover : Ioc 0 T ⊆ ⋃ p, B p := by
      intro τ hτ
      by_contra hn
      apply h
      exact ⟨τ, hτ, fun p hp => hn (mem_iUnion.mpr ⟨p, hp⟩)⟩
    have hsub : (⋃ p, B p) ⊆ Ioc 0 T := iUnion_subset hB
    have hfinite : volume (⋃ p, B p) ≠ ∞ :=
      measure_ne_top_of_subset hsub (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hle := measureReal_mono hcover hfinite
    have hu := measureReal_iUnion_fintype_le (μ := volume) B
    have hb : ∑ p, volume.real (B p) ≤ (∑ _p : Fin 2 × Fin 2, 9 * ε) * T := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun p _ => hbad p
    have hstrict : (∑ _p : Fin 2 × Fin 2, 9 * ε) * T < T := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hsum hT
    rw [Real.volume_real_Ioc_of_le hT.le, sub_zero] at hle
    linarith
  obtain ⟨τ, hτ, hτB⟩ := havoid
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro k
    by_contra hk
    exact hτB (k, 0) (Or.inl ⟨hτ, hk⟩)
  · intro k q
    by_contra hk
    have ht := ekl_affine_time_mem T (θ q) (η q) τ hT (hθlo q) (hθhi q) (hη q) hτ
    exact hτB (k, q) (Or.inr ⟨hτ, ht, hk⟩)

end DukePrimeDegree

end

end OAI
