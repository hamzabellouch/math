import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingTimeCovariance

namespace OAI

/-!
# Four candidate windows for the two annular radii

EKL Lemma 4.6 needs both possible scale regimes at each of two annular
radii. The four windows have total density loss at most `72 * ε` for
two initial points. Null-time exceptions for covariance can be avoided
at all four windows simultaneously.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree

theorem exists_common_four_window_time
    {Y : Type*} (Φ : ℝ → Y → Y) (G H : Set Y) (z : Fin 2 → Y)
    (T ε : ℝ) (hT : 0 < T) (hε : 72 * ε < 1)
    (θ η : Fin 2 × Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hG : ∀ k, volume.real (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) ≤ ε * T)
    (hH : ∀ k, volume.real (Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}) ≤ ε * (4 * T)) :
    ∃ τ ∈ Ioc 0 T, (∀ k, Φ τ (z k) ∈ G) ∧
      ∀ k q, Φ ((θ q + (2 - η q) * τ) / 2) (z k) ∈ H := by
  let A : Fin 2 → Set ℝ := fun k => Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}
  let E : Fin 2 → Set ℝ := fun k => Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}
  let B : Fin 2 × (Fin 2 × Fin 2) → Set ℝ := fun p => A p.1 ∪
    (Ioc 0 T ∩ ((fun τ => (θ p.2 + (2 - η p.2) * τ) / 2) ⁻¹' E p.1))
  have hB : ∀ p, B p ⊆ Ioc 0 T := by
    intro p τ hτ
    rcases hτ with hτ | hτ <;> exact hτ.1
  have hbad (p : Fin 2 × (Fin 2 × Fin 2)) : volume.real (B p) ≤ (9 * ε) * T := by
    have hpull := ekl_pullback_bad_time_bound T (θ p.2) (η p.2) ε (hη p.2)
      (E p.1) inter_subset_left (hH p.1)
    have hu := measureReal_union_le (μ := volume) (A p.1)
      (Ioc 0 T ∩ ((fun τ => (θ p.2 + (2 - η p.2) * τ) / 2) ⁻¹' E p.1))
    change volume.real (B p) ≤ volume.real (A p.1) + _ at hu
    have hg : volume.real (A p.1) ≤ ε * T := hG p.1
    linarith
  have hsum : ∑ _p : Fin 2 × (Fin 2 × Fin 2), (9 * ε) < 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have havoid : ∃ τ ∈ Ioc 0 T, ∀ p : Fin 2 × (Fin 2 × Fin 2), τ ∉ B p := by
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
    have hb : ∑ p, volume.real (B p) ≤ (∑ _p : Fin 2 × (Fin 2 × Fin 2), 9 * ε) * T := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun p _ => hbad p
    have hstrict : (∑ _p : Fin 2 × (Fin 2 × Fin 2), 9 * ε) * T < T := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hsum hT
    rw [Real.volume_real_Ioc_of_le hT.le, sub_zero] at hle
    linarith
  obtain ⟨τ, hτ, hτB⟩ := havoid
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro k
    by_contra hk
    exact hτB (k, (0, 0)) (Or.inl ⟨hτ, hk⟩)
  · intro k q
    by_contra hk
    have ht := ekl_affine_time_mem T (θ q) (η q) τ hT (hθlo q) (hθhi q) (hη q) hτ
    exact hτB (k, q) (Or.inr ⟨hτ, ht, hk⟩)


theorem exists_common_four_window_time_ae
    {Y : Type*} (Φ : ℝ → Y → Y) (G H : Set Y) (z : Fin 2 → Y)
    (T ε : ℝ) (hT : 0 < T) (hε : 72 * ε < 1)
    (θ η : Fin 2 × Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hG : ∀ k, volume.real (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) ≤ ε * T)
    (hH : ∀ k, volume.real (Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}) ≤ ε * (4 * T))
    (P : ℝ → Prop) (hP : ∀ᵐ τ ∂volume, P τ) :
    ∃ τ ∈ Ioc 0 T, P τ ∧ (∀ k, Φ τ (z k) ∈ G) ∧
      ∀ k q, Φ ((θ q + (2 - η q) * τ) / 2) (z k) ∈ H := by
  let Ψ : ℝ → Y × ℝ → Y × ℝ := fun t y => (Φ t y.1, t)
  let G' : Set (Y × ℝ) := {y | y.1 ∈ G ∧ P y.2}
  let H' : Set (Y × ℝ) := {y | y.1 ∈ H}
  have hG' (k : Fin 2) :
      volume.real (Ioc 0 T ∩ {τ | Ψ τ (z k, 0) ∉ G'}) ≤ ε * T := by
    have he : (Ioc 0 T ∩ {τ | Ψ τ (z k, 0) ∉ G'}) =ᵐ[volume]
        (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) := by
      filter_upwards [hP] with τ hτ
      simp only [mem_inter_iff, mem_ofPred_eq, Ψ, G', hτ, and_true]
    have hm := measure_congr he
    simpa only [measureReal_def, hm] using hG k
  obtain ⟨τ, hτ, hg, hh⟩ := exists_common_four_window_time Ψ G' H'
    (fun k => (z k, 0)) T ε hT hε θ η hθlo hθhi hη hG' hH
  exact ⟨τ, hτ, (hg 0).2, fun k => (hg k).1, hh⟩

theorem exists_common_four_window_time_with_covariance
    {Y : Type*} (Φ : ℝ → Y → Y) (G H : Set Y) (z : Fin 2 → Y)
    (T ε : ℝ) (hT : 0 < T) (hε : 72 * ε < 1)
    (θ η : Fin 2 × Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hG : ∀ k, volume.real (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) ≤ ε * T)
    (hH : ∀ k, volume.real (Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}) ≤ ε * (4 * T))
    (Q : Y → ℝ → Prop) (hQ : ∀ k, ∀ᵐ t ∂volume, Q (z k) t) :
    ∃ τ ∈ Ioc 0 T,
      (∀ k, Φ τ (z k) ∈ G ∧ Q (z k) τ) ∧
      ∀ k q, Φ ((θ q + (2 - η q) * τ) / 2) (z k) ∈ H ∧
        Q (z k) ((θ q + (2 - η q) * τ) / 2) := by
  have hfirst : ∀ᵐ τ ∂volume, ∀ k, Q (z k) τ := ae_all_iff.mpr hQ
  have hsecond : ∀ᵐ τ ∂volume, ∀ k q,
      Q (z k) ((θ q + (2 - η q) * τ) / 2) := by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro q
    have ha : (2 - η q) / 2 ≠ 0 := by
      rcases hη q with h | h <;> rw [h] <;> norm_num
    have he (τ : ℝ) : (θ q + (2 - η q) * τ) / 2 =
        θ q / 2 + ((2 - η q) / 2) * τ := by ring
    simp_rw [he]
    exact ae_affine_precompose (hQ k) _ _ ha
  obtain ⟨τ, hτ, hq, hg, hh⟩ := exists_common_four_window_time_ae
    Φ G H z T ε hT hε θ η hθlo hθhi hη hG hH
    (fun τ => (∀ k, Q (z k) τ) ∧
      ∀ k q, Q (z k) ((θ q + (2 - η q) * τ) / 2)) (hfirst.and hsecond)
  exact ⟨τ, hτ, fun k => ⟨hg k, hq.1 k⟩, fun k q => ⟨hh k q, hq.2 k q⟩⟩


end DukePrimeDegree

end

end OAI
