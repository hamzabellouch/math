import OAI.Combinatorics.Progressions.Geometry.NativeTranslatedBoxInverse

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_integer_interval_inverse (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (a : ℤ) (L : ℕ) [NeZero L] {p : ℝ}, 2 ≤ p →
      ∀ f : ℤ → ℂ, (∀ x ∈ Finset.Ico a (a + L), ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ finiteSupportGowersNorm (s + 1) (Finset.Ico a (a + L)) f →
      ∃ V : NativeSampleCorrelation (fun _ : Unit => 1) s ((p + C) ^ C)
        (Finset.Ico a (a + L)) (fun x _ => x) f, V.test.normBound ≤ 1 := by
  obtain ⟨C, hC, hbox⟩ := exists_native_translated_box_inverse_bounded_dimension s hs 1
  refine ⟨C, hC, ?_⟩
  intro a L _ p hp f hf hGowers
  have hdim : (1 : ℝ) ≤ (p + (1 : ℕ)) ^ (1 : ℕ) := by norm_num; linarith
  have hcap : ∀ x ∈ translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => L), ‖f (x 0)‖ ≤ 1 := by
    intro x hx
    apply hf
    exact Finset.mem_Ico.mpr ((mem_translatedIntegerBox _ _ _).mp hx 0)
  have hnorm : Real.exp (-p) ≤ finiteSupportGowersNorm (s + 1)
      (translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => L)) (fun x => f (x 0)) := by
    rw [oneDimensionalBox_norm]
    exact hGowers
  obtain ⟨V, hV⟩ := hbox (fun _ : Fin 1 => a) (fun _ => L) hp (by simpa only [Nat.cast_one] using hdim)
    (fun x => f (x 0)) hcap hnorm
  let A : Fin 1 → ((Unit → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x (), map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine ⟨{
    L := V.L
    dim := V.dim
    model := V.model
    test := V.test.linearPullbackHom A
    complexity := V.complexity
    correlation := ?_ }, hV⟩
  have hh := V.correlation
  change Real.exp (-((p + C) ^ C)) ≤ ‖finiteCorrelation
    (translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => L)) (fun x => f (x 0)) V.test.eval‖ at hh
  rw [oneDimensionalBox_correlation] at hh
  simpa only [finiteCorrelation, RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom, A,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hh

end Erdos3

end

end OAI
