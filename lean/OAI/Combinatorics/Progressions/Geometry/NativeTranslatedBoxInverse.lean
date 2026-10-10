import OAI.Combinatorics.Progressions.Lattices.NativeIntegerBoxInverse

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

noncomputable def NativeSampleCorrelation.translateInput {σ : Type*} [Fintype σ] [DecidableEq σ]
    {s : ℕ} {p : ℝ} {Q : Finset (σ → ℤ)} {f : (σ → ℤ) → ℂ}
    (a : σ → ℤ) (V : NativeSampleCorrelation (fun _ : σ => 1) s p Q id (fun x => f (a + x))) :
    NativeSampleCorrelation (fun _ : σ => 1) s p (translateSupport a Q) id f where
  L := V.L
  dim := V.dim
  model := V.model
  test := V.test.translate (fun _ => by decide) (-a)
  complexity := V.complexity
  correlation := by
    change Real.exp (-p) ≤ ‖𝔼 x ∈ Q.image (fun y => a + y),
      f x * star ((V.test.translate (fun _ => by decide) (-a)).eval x)‖
    have hinj : Set.InjOn (fun x : σ → ℤ => a + x) (Q : Set (σ → ℤ)) :=
      fun _ _ _ _ h => add_left_cancel h
    rw [Finset.expect_image hinj]
    have heq (x : σ → ℤ) : a + x + -a = x := by abel
    simpa only [RationalFilteredNilmanifold.Niltest.eval_translate, heq, id_eq] using V.correlation

theorem NativeSampleCorrelation.translateInput_norm {σ : Type*} [Fintype σ] [DecidableEq σ]
    {s : ℕ} {p : ℝ} {Q : Finset (σ → ℤ)} {f : (σ → ℤ) → ℂ}
    (a : σ → ℤ) (V : NativeSampleCorrelation (fun _ : σ => 1) s p Q id (fun x => f (a + x))) :
    (V.translateInput a).test.normBound = V.test.normBound := rfl

theorem exists_native_translated_box_inverse (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (a : Fin n → ℤ) (T : Fin n → ℕ) [∀ i, NeZero (T i)]
      {p : ℝ}, 2 ≤ p → ∀ f : (Fin n → ℤ) → ℂ,
      (∀ x ∈ translatedIntegerBox a T, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a T) f →
      ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + n + C) ^ C)
        (translatedIntegerBox a T) id f, V.test.normBound ≤ 1 := by
  obtain ⟨C, hC, hinverse⟩ := exists_native_integer_box_inverse s hs
  refine ⟨C, hC, ?_⟩
  intro n a T _ p hp f hf hGowers
  have hshift : ∀ x ∈ integerBox T, ‖f (a + x)‖ ≤ 1 := by
    intro x hx
    apply hf
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [translatedIntegerBox_norm_eq] at hGowers
  obtain ⟨V, hV⟩ := hinverse T hp (fun x => f (a + x)) hshift hGowers
  exact ⟨V.translateInput a, hV⟩

theorem exists_native_translated_box_inverse_bounded_dimension (s : ℕ) (hs : 1 ≤ s) (D : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (a : Fin n → ℤ) (T : Fin n → ℕ) [∀ i, NeZero (T i)]
      {p : ℝ}, 2 ≤ p → (n : ℝ) ≤ (p + D) ^ D → ∀ f : (Fin n → ℤ) → ℂ,
      (∀ x ∈ translatedIntegerBox a T, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a T) f →
      ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + C) ^ C)
        (translatedIntegerBox a T) id f, V.test.normBound ≤ 1 := by
  obtain ⟨C, hC, hinverse⟩ := exists_native_integer_box_inverse_bounded_dimension s hs D
  refine ⟨C, hC, ?_⟩
  intro n a T _ p hp hn f hf hGowers
  have hshift : ∀ x ∈ integerBox T, ‖f (a + x)‖ ≤ 1 := by
    intro x hx
    apply hf
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [translatedIntegerBox_norm_eq] at hGowers
  obtain ⟨V, hV⟩ := hinverse T hp hn (fun x => f (a + x)) hshift hGowers
  exact ⟨V.translateInput a, hV⟩

end Erdos3

end

end OAI
