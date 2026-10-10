import OAI.MeasureTheory.Falconer.Fourier.ReachedMaskJets

namespace OAI

/-! # Indexed products of actual normalized descriptor derivatives

The index set distinguishes repeated descriptors. Its total derivative
order controls the norm independently of the number of undifferentiated
masks. Reached factors split off as one angular function on each cell.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

noncomputable def descriptorJetProduct {d : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (x : Space d) (w : Sphere d) : ℂ :=
  ∏ j ∈ F, normalizedDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j w) x w

theorem descriptorJetProduct_reached_split {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (X : List (Fin d → Bool)) {x : Space d} (hx : x ∈ (Q.descendant X).carrier)
    (w : Sphere d) :
    descriptorJetProduct Q ρ m N σ J i F b S k v x w =
      descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun j => descriptorAnchor (b j) ≤ X.length)) b S k v (Q.descendant X).center w *
      descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w := by
  classical
  unfold descriptorJetProduct
  have hsplit := (Finset.prod_filter_mul_prod_filter_not F
    (fun j => descriptorAnchor (b j) ≤ X.length)
    (fun j => normalizedDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j w) x w)).symm
  rw [show F.filter (fun j => ¬descriptorAnchor (b j) ≤ X.length) =
    F.filter (fun j => X.length < descriptorAnchor (b j)) by ext j; simp] at hsplit
  refine hsplit.trans ?_
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact normalizedDescriptorJet_reached Q hQ ρ m N σ J i (b j) (S (b j)) (k j)
    (v j w) X (Finset.mem_filter.mp hj).2 hx w

theorem descriptorJetProduct_support {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ)
    (σ : ℝ) (J i : ℕ) (F : Finset ι) (b : ι → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d) (x : Space d) (w : Sphere d)
    (h : descriptorJetProduct Q ρ m N σ J i F b S k v x w ≠ 0) :
    ∀ j ∈ F, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) (b j) := by
  intro j hj
  apply normalizedDescriptorJet_support Q ρ m N σ J i (b j) (S (b j)) (k j) (v j w) x w
  exact (Finset.prod_ne_zero_iff.mp h) j hj

theorem normalizedDescriptorJet_order_bound (d K : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ k ≤ K, ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x : Space d) (w : Sphere d),
        ‖normalizedDescriptorJet Q ρ m N σ J i b S k v x w‖ ≤ A^k := by
  classical
  choose C hC hbound using fun k => normalizedDescriptorJet_bound d k
  let A := 1+∑ k ∈ Finset.range (K+1), C k
  have hA : 1 ≤ A := by
    have hsum := Finset.sum_nonneg (fun j _ => hC j) (s := Finset.range (K+1))
    dsimp [A]
    linarith
  refine ⟨A,hA,?_⟩
  intro Q ρ m N σ J i b S hsep k hk v hv x w
  cases k with
  | zero =>
    rw [normalizedDescriptorJet_zero,pow_zero,Complex.norm_real,Real.norm_eq_abs]
    have h := descriptorAmbientMask_global_bounds Q ρ m N σ J i b S x w
    exact (abs_of_nonneg h.1).le.trans h.2
  | succ k =>
    have hCA : C (k+1) ≤ A := by
      have hsum := Finset.single_le_sum (fun j _ => hC j)
        (Finset.mem_range.mpr (by omega : k+1 < K+1))
      dsimp [A]
      linarith
    exact (hbound (k+1) Q ρ m N σ J i b S hsep v hv x w).trans
      (hCA.trans (le_self_pow₀ hA (by omega : k+1 ≠ 0)))

theorem descriptorJetProduct_total_order_bound (d K : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {ι : Type*} (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
      (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
      (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d),
      (∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
        descriptorMaskRadius N σ (b j)/2 ≤ dist w z) →
      (∑ j ∈ F, k j) ≤ K →
      (∀ j ∈ F, ∀ w l, ‖v j w l‖ ≤ 1) →
      ∀ x w, ‖descriptorJetProduct Q ρ m N σ J i F b S k v x w‖ ≤ A^K := by
  obtain ⟨A,hA,hbound⟩ := normalizedDescriptorJet_order_bound d K
  refine ⟨A,hA,?_⟩
  intro ι Q ρ m N σ J i F b S k v hsep horder hv x w
  rw [descriptorJetProduct,norm_prod]
  calc
    _ ≤ ∏ j ∈ F, A^(k j) := by
      apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      intro j hj
      exact hbound Q ρ m N σ J i (b j) (S (b j)) (hsep j hj) (k j)
        ((Finset.single_le_sum (fun l _ => Nat.zero_le (k l)) hj).trans horder)
        (v j w) (hv j hj w) x w
    _ = A^(∑ j ∈ F, k j) := Finset.prod_pow_eq_pow_sum F k A
    _ ≤ A^K := pow_le_pow_right₀ hA horder

end Falconer

end OAI
