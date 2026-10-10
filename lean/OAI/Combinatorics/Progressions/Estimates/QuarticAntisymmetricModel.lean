import OAI.Combinatorics.Progressions.Estimates.QuarticCyclicPositiveCorrelation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

noncomputable def quarticCyclicMain {N : ℕ} [NeZero N] {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (out : Fin 6 → Fin W.outputDim) (h n k l : ZMod N) : ℂ :=
  quarticSixMain W.eval out ![(h.val : ℤ), (n.val : ℤ), (k.val : ℤ), (l.val : ℤ)]

end NativeMultidegreeNilcharacter

theorem exists_quartic_reflected_model_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ (out : Fin 6 → Fin W.outputDim) (z : ZMod N)
          (b : ((ZMod N × ZMod N) × (ZMod N × ZMod N)) → ZMod N → ℂ),
          (∀ t h, ‖b t h‖ ≤ 1) ∧
          let K := fun h n k l => star (W.quarticCyclicMain out h n k l)
          Real.exp (-((p + C) ^ C)) ≤
            (𝔼 t, 𝔼 h, 𝔼 h', quarticReflectionKernel K t h (z - h - h') *
              star (quarticReflectionKernel K t h' (z - h - h')) * b t h * star (b t h')).re := by
  obtain ⟨c, _, hcyclic⟩ := exists_quartic_cyclic_positive_correlation_with_mixed
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (8 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 8 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have height : 8 * q ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, E, out, A, hA, hAind,
    _a, _len, _hlen, _hend, _hshort, _hvol, _hsupport, hpositive⟩ :=
    hcyclic hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let K (h n k l : ZMod N) := star (W.quarticCyclicMain out h n k l)
  let A₀ (n k l : ZMod N) := A 0 ![0, (n.val : ℤ), (k.val : ℤ), (l.val : ℤ)]
  let A₁ (h k l : ZMod N) := A 1 ![(h.val : ℤ), 0, (k.val : ℤ), (l.val : ℤ)]
  let A₂ (h n l : ZMod N) := A 2 ![(h.val : ℤ), (n.val : ℤ), 0, (l.val : ℤ)]
  let A₃ (h n k : ZMod N) := A 3 ![(h.val : ℤ), (n.val : ℤ), (k.val : ℤ), 0]
  have hprod (h n k l : ZMod N) :
      (∏ i, A i ![(h.val : ℤ), (n.val : ℤ), (k.val : ℤ), (l.val : ℤ)]) =
        A₀ n k l * A₁ h k l * A₂ h n l * A₃ h n k := by
    have h₀ : A 0 ![(h.val : ℤ), (n.val : ℤ), (k.val : ℤ), (l.val : ℤ)] = A₀ n k l := by
      apply hAind
      intro j hj
      fin_cases j <;> first | exact (hj rfl).elim | rfl
    have h₁ : A 1 ![(h.val : ℤ), (n.val : ℤ), (k.val : ℤ), (l.val : ℤ)] = A₁ h k l := by
      apply hAind
      intro j hj
      fin_cases j <;> first | exact (hj rfl).elim | rfl
    have h₂ : A 2 ![(h.val : ℤ), (n.val : ℤ), (k.val : ℤ), (l.val : ℤ)] = A₂ h n l := by
      apply hAind
      intro j hj
      fin_cases j <;> first | exact (hj rfl).elim | rfl
    have h₃ : A 3 ![(h.val : ℤ), (n.val : ℤ), (k.val : ℤ), (l.val : ℤ)] = A₃ h n k := by
      apply hAind
      intro j hj
      fin_cases j <;> first | exact (hj rfl).elim | rfl
    rw [Fin.prod_univ_four, h₀, h₁, h₂, h₃]
  have havg :
      (𝔼 l, 𝔼 k, 𝔼 h, 𝔼 n,
        star (f (n + h + k + l)) * K h n k l * A₀ n k l * A₁ h k l * A₂ h n l * A₃ h n k) =
      𝔼 t : (ZMod N × ZMod N) × ZMod N, 𝔼 n : ZMod N,
        star (f (n + t.1.2 + t.1.1 + t.2)) *
          star (quarticSixMain W.eval out
            ![(t.1.2.val : ℤ), (n.val : ℤ), (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
          ∏ i, A i ![(t.1.2.val : ℤ), (n.val : ℤ), (t.1.1.val : ℤ), (t.2.val : ℤ)] := by
    simp_rw [expect_prod_split]
    calc
      _ = 𝔼 k, 𝔼 l, 𝔼 h, 𝔼 n,
          star (f (n + h + k + l)) * K h n k l * A₀ n k l * A₁ h k l * A₂ h n l * A₃ h n k :=
        Finset.expect_comm _ _ _
      _ = 𝔼 k, 𝔼 h, 𝔼 l, 𝔼 n,
          star (f (n + h + k + l)) * K h n k l * A₀ n k l * A₁ h k l * A₂ h n l * A₃ h n k := by
        apply Finset.expect_congr rfl
        intro k _
        exact Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro k _
        apply Finset.expect_congr rfl
        intro h _
        apply Finset.expect_congr rfl
        intro l _
        apply Finset.expect_congr rfl
        intro n _
        rw [hprod]
        dsimp only [K, NativeMultidegreeNilcharacter.quarticCyclicMain]
        ring
  have hinput : Real.exp (-q) ≤
      ‖𝔼 l, 𝔼 k, 𝔼 h, 𝔼 n,
        star (f (n + h + k + l)) * K h n k l * A₀ n k l * A₁ h k l * A₂ h n l * A₃ h n k‖ := by
    rw [havg]
    exact hpositive.trans (Complex.re_le_norm _)
  obtain ⟨z, b, hb, hreflect⟩ := exists_quartic_reflected_correlation K (fun x => star (f x))
    A₀ A₁ A₂ A₃ (fun x => by simpa only [norm_star] using hf x)
    (fun _ _ _ => hA 0 _) (fun _ _ _ => hA 1 _) (fun _ _ _ => hA 2 _) (fun _ _ _ => hA 3 _)
  refine ⟨M.mono hqC, hret.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC, E.mono hqC,
    out, z, b, hb, ?_⟩
  change Real.exp (-((p + C) ^ C)) ≤
    (𝔼 t, 𝔼 h, 𝔼 h', quarticReflectionKernel K t h (z - h - h') *
      star (quarticReflectionKernel K t h' (z - h - h')) * b t h * star (b t h')).re
  calc
    _ ≤ Real.exp (-(8 * q)) := Real.exp_le_exp.mpr (neg_le_neg height)
    _ = (Real.exp (-q)) ^ 8 := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := (pow_le_pow_left₀ (Real.exp_nonneg _) hinput 8).trans hreflect

theorem exists_quartic_reflected_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ (out : Fin 6 → Fin W.outputDim) (z : ZMod N)
          (b : ((ZMod N × ZMod N) × (ZMod N × ZMod N)) → ZMod N → ℂ),
          (∀ t h, ‖b t h‖ ≤ 1) ∧
          let K := fun h n k l => star (W.quarticCyclicMain out h n k l)
          Real.exp (-((p + C) ^ C)) ≤
            (𝔼 t, 𝔼 h, 𝔼 h', quarticReflectionKernel K t h (z - h - h') *
              star (quarticReflectionKernel K t h' (z - h - h')) * b t h * star (b t h')).re := by
  obtain ⟨C, hC, h⟩ := exists_quartic_reflected_model_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def NativeMultidegreeNilcharacter.quarticIntegerReflection
    {N : ℕ} [NeZero N] {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (out : Fin 6 → Fin W.outputDim)
    (t : (ZMod N × ZMod N) × (ZMod N × ZMod N)) (h n : ℤ) : ℂ :=
  quarticReflectionKernel
    (fun h n k l => star (quarticSixMain W.eval out ![h, n, k, l]))
    (((t.1.1.val : ℤ), (t.1.2.val : ℤ)), ((t.2.1.val : ℤ), (t.2.2.val : ℤ))) h n

theorem exists_quartic_unwrapped_reflection_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ (out : Fin 6 → Fin W.outputDim) (z : ZMod N) (carry : Fin 3)
          (A B : ((ZMod N × ZMod N) × (ZMod N × ZMod N)) → ℤ → ℂ),
          (∀ t h, ‖A t h‖ ≤ 1) ∧ (∀ t h, ‖B t h‖ ≤ 1) ∧
          let R := W.quarticIntegerReflection out
          let c : ℤ := z.val + (carry.val : ℤ) * N
          Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 t, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
              R t h.val (c - h.val - h'.val) * star (R t h'.val (c - h.val - h'.val)) *
                A t h.val * B t h'.val‖ := by
  obtain ⟨c, _, hreflection⟩ := exists_quartic_reflected_model_with_mixed
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P + 10)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hcost : 2 * q + 10 ≤ (p + C) ^ C := by
    simpa [P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, E, out, z, b, hb, hreflect⟩ :=
    hreflection hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let R := W.quarticIntegerReflection (N := N) out
  have hR : ∀ t h n, ‖R t h n‖ ≤ 1 := by
    intro t h n
    dsimp only [R, NativeMultidegreeNilcharacter.quarticIntegerReflection, quarticReflectionKernel]
    simp only [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      ((mul_le_of_le_one_left (norm_nonneg _) (W.quarticSixMain_norm _ _)).trans
        (W.quarticSixMain_norm _ _))).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (W.quarticSixMain_norm _ _)).trans
        (W.quarticSixMain_norm _ _))
  have hc : Real.exp (-q) ≤ ‖𝔼 t, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
      R t h.val (z - h - h').val * star (R t h'.val (z - h - h').val) *
        b t h * star (b t h')‖ := by
    simpa only [R, NativeMultidegreeNilcharacter.quarticIntegerReflection,
      NativeMultidegreeNilcharacter.quarticCyclicMain, quarticReflectionKernel]
      using hreflect.trans (Complex.re_le_norm _)
  obtain ⟨carry, A, B, hA, hB, hunwrapped⟩ :=
    exists_unwrapped_family_reflected_correlation hq R R hR hR z b hb hc
  refine ⟨M.mono hqC, hret.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC, E.mono hqC,
    out, z, carry, A, B, hA, hB, ?_⟩
  exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hunwrapped

theorem exists_quartic_unwrapped_reflection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ (out : Fin 6 → Fin W.outputDim) (z : ZMod N) (carry : Fin 3)
          (A B : ((ZMod N × ZMod N) × (ZMod N × ZMod N)) → ℤ → ℂ),
          (∀ t h, ‖A t h‖ ≤ 1) ∧ (∀ t h, ‖B t h‖ ≤ 1) ∧
          let R := W.quarticIntegerReflection out
          let c : ℤ := z.val + (carry.val : ℤ) * N
          Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 t, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
              R t h.val (c - h.val - h'.val) * star (R t h'.val (c - h.val - h'.val)) *
                A t h.val * B t h'.val‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_unwrapped_reflection_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_anchored_reflection_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ (out : Fin 6 → Fin W.outputDim) (z : ZMod N) (carry : Fin 3)
          (A B : (ZMod N × ZMod N) → ℤ → ℂ) (D E : ℤ → ℤ → ℤ → ℂ),
          (∀ t h, ‖A t h‖ ≤ 1) ∧ (∀ t h, ‖B t h‖ ≤ 1) ∧
          (∀ h h' k, ‖D h h' k‖ ≤ 1) ∧ (∀ h h' l, ‖E h h' l‖ ≤ 1) ∧
          let K := fun h n k l => star (quarticSixMain W.eval out ![h, n, k, l])
          let c : ℤ := z.val + (carry.val : ℤ) * N
          Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 t : ZMod N × ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
              K h.val (c - h.val - h'.val) t.1.val t.2.val *
                star (K h'.val (c - h.val - h'.val) t.1.val t.2.val) *
                  A t h.val * B t h'.val * D h.val h'.val t.1.val * E h.val h'.val t.2.val‖ := by
  obtain ⟨C, hC, hunwrap⟩ := exists_quartic_unwrapped_reflection_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, E₀, out, z, carry, A, B, hA, hB, hunwrapped⟩ :=
    hunwrap hp hN f hf hGowers
  let K (h n k l : ℤ) := star (quarticSixMain W.eval out ![h, n, k, l])
  let c : ℤ := z.val + (carry.val : ℤ) * N
  let R (t : (ZMod N × ZMod N) × (ZMod N × ZMod N)) (h n : ℤ) :=
    quarticReflectionKernel K
      (((t.1.1.val : ℤ), (t.1.2.val : ℤ)), ((t.2.1.val : ℤ), (t.2.2.val : ℤ))) h n
  let F (t : (ZMod N × ZMod N) × (ZMod N × ZMod N)) :=
    𝔼 h : ZMod N, 𝔼 h' : ZMod N,
      R t h.val (c - h.val - h'.val) * star (R t h'.val (c - h.val - h'.val)) *
        A t h.val * B t h'.val
  let e : ((ZMod N × ZMod N) × (ZMod N × ZMod N)) ≃
      ((ZMod N × ZMod N) × (ZMod N × ZMod N)) :=
    { toFun := fun t => ((t.2.2, t.1.2), (t.2.1, t.1.1))
      invFun := fun u => ((u.2.2, u.1.2), (u.2.1, u.1.1))
      left_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
      right_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl }
  have hreindex : (𝔼 t, F t) =
      𝔼 u : ZMod N × ZMod N, 𝔼 t : ZMod N × ZMod N, F ((t.2, u.2), (t.1, u.1)) := by
    calc
      _ = 𝔼 u : (ZMod N × ZMod N) × (ZMod N × ZMod N),
          F ((u.2.2, u.1.2), (u.2.1, u.1.1)) := Fintype.expect_equiv e F _ (fun _ => rfl)
      _ = _ := expect_prod_split _
  change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 t, F t‖ at hunwrapped
  rw [hreindex] at hunwrapped
  have hmean : Real.exp (-((p + C) ^ C)) ≤
      𝔼 u : ZMod N × ZMod N, ‖𝔼 t : ZMod N × ZMod N, F ((t.2, u.2), (t.1, u.1))‖ :=
    hunwrapped.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨u, _, hu⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  let A' (t : ZMod N × ZMod N) (h : ℤ) := A ((t.2, u.2), (t.1, u.1)) h
  let B' (t : ZMod N × ZMod N) (h : ℤ) := B ((t.2, u.2), (t.1, u.1)) h
  let D (h h' k : ℤ) :=
    (star (K h (c - h - h') k u.2.val) * K h' (c - h - h') k u.2.val) *
      (K h (c - h - h') u.1.val u.2.val * star (K h' (c - h - h') u.1.val u.2.val))
  let E (h h' l : ℤ) :=
    star (K h (c - h - h') u.1.val l) * K h' (c - h - h') u.1.val l
  have hK (h n k l : ℤ) : ‖K h n k l‖ ≤ 1 := by
    dsimp only [K]
    rw [norm_star]
    exact W.quarticSixMain_norm out _
  have heq : (𝔼 t : ZMod N × ZMod N, F ((t.2, u.2), (t.1, u.1))) =
      𝔼 t : ZMod N × ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        K h.val (c - h.val - h'.val) t.1.val t.2.val *
          star (K h'.val (c - h.val - h'.val) t.1.val t.2.val) *
            A' t h.val * B' t h'.val * D h.val h'.val t.1.val * E h.val h'.val t.2.val := by
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro h _
    apply Finset.expect_congr rfl
    intro h' _
    simp only [R, quarticReflectionKernel, A', B', D, E, star_mul, star_star]
    ring
  refine ⟨M, hret, W, hdim, hsymm, hdiag, E₀, out, z, carry, A', B', D, E,
    (fun _ _ => hA _ _), (fun _ _ => hB _ _), ?_, ?_, ?_⟩
  · intro h h' k
    simp only [D, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      ((mul_le_of_le_one_left (norm_nonneg _) (hK _ _ _ _)).trans (hK _ _ _ _))).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hK _ _ _ _)).trans (hK _ _ _ _))
  · intro h h' l
    simp only [E, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hK _ _ _ _)).trans (hK _ _ _ _)
  · rwa [heq] at hu

theorem exists_quartic_anchored_reflection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ (out : Fin 6 → Fin W.outputDim) (z : ZMod N) (carry : Fin 3)
          (A B : (ZMod N × ZMod N) → ℤ → ℂ) (D E : ℤ → ℤ → ℤ → ℂ),
          (∀ t h, ‖A t h‖ ≤ 1) ∧ (∀ t h, ‖B t h‖ ≤ 1) ∧
          (∀ h h' k, ‖D h h' k‖ ≤ 1) ∧ (∀ h h' l, ‖E h h' l‖ ≤ 1) ∧
          let K := fun h n k l => star (quarticSixMain W.eval out ![h, n, k, l])
          let c : ℤ := z.val + (carry.val : ℤ) * N
          Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 t : ZMod N × ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
              K h.val (c - h.val - h'.val) t.1.val t.2.val *
                star (K h'.val (c - h.val - h'.val) t.1.val t.2.val) *
                  A t h.val * B t h'.val * D h.val h'.val t.1.val * E h.val h'.val t.2.val‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_anchored_reflection_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_antisymmetric_model_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ (i j : Fin (W.outputDim ^ 6)) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 t : (ZMod N × ZMod N) × (ZMod N × ZMod N),
              (W.tensorPower 6).quarticAntisymmetric i j
                ![(t.2.1.val : ℤ), (t.2.2.val : ℤ), (t.1.1.val : ℤ), (t.1.2.val : ℤ)] *
                ∏ k, A k ![(t.2.1.val : ℤ), (t.2.2.val : ℤ), (t.1.1.val : ℤ), (t.1.2.val : ℤ)]‖ := by
  obtain ⟨a, _, hanchor⟩ := exists_quartic_anchored_reflection_with_mixed
  obtain ⟨b, _, htransfer⟩ := exists_quartic_antisymmetric_transfer
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let R := 7 * (Q + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  let r := 7 * (q + 1)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have hr : 0 ≤ r := hq.trans hqr
  have hsum : r + (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqb : 0 ≤ (r + b) ^ b := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hfinal : (r + b) ^ b ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, E₀, out, z, carry, A, B, D, E, hA, hB, hD, hE, hreflection⟩ :=
    hanchor hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let V := W.tensorPower 6
  have hrV : tensorPowerBudget 6 ((p + a) ^ a) = r := by
    norm_num [tensorPowerBudget, r, q]
  let i₀ := tensorIndexEquiv W.outputDim 6 out
  let c : ℤ := z.val + (carry.val : ℤ) * N
  let K (h n k l : ℤ) := star (quarticSixMain W.eval out ![h, n, k, l])
  let L (i : Fin 4) (x : Fin 4 → ℤ) :=
    ![B ((x 2 : ZMod N), (x 3 : ZMod N)) (x 1),
      A ((x 2 : ZMod N), (x 3 : ZMod N)) (x 0),
      E (x 0) (x 1) (x 3), D (x 0) (x 1) (x 2)] i
  have hL : ∀ i x, ‖L i x‖ ≤ 1 := by
    intro i x
    fin_cases i
    · exact hB _ _
    · exact hA _ _
    · exact hE _ _ _
    · exact hD _ _ _
  have hLind : ∀ i x y, (∀ k, k ≠ i → x k = y k) → L i x = L i y := by
    intro i x y hxy
    fin_cases i
    · change B ((x 2 : ZMod N), (x 3 : ZMod N)) (x 1) = B ((y 2 : ZMod N), (y 3 : ZMod N)) (y 1)
      rw [hxy 1 (by decide), hxy 2 (by decide), hxy 3 (by decide)]
    · change A ((x 2 : ZMod N), (x 3 : ZMod N)) (x 0) = A ((y 2 : ZMod N), (y 3 : ZMod N)) (y 0)
      rw [hxy 0 (by decide), hxy 2 (by decide), hxy 3 (by decide)]
    · change E (x 0) (x 1) (x 3) = E (y 0) (y 1) (y 3)
      rw [hxy 0 (by decide), hxy 1 (by decide), hxy 3 (by decide)]
    · change D (x 0) (x 1) (x 2) = D (y 0) (y 1) (y 2)
      rw [hxy 0 (by decide), hxy 1 (by decide), hxy 2 (by decide)]
  let sample (t : (ZMod N × ZMod N) × (ZMod N × ZMod N)) : Fin 4 → ℤ :=
    ![(t.2.1.val : ℤ), (t.2.2.val : ℤ), (t.1.1.val : ℤ), (t.1.2.val : ℤ)]
  have hV (h n k l : ℤ) : V.eval i₀ (quarticInput h ![n, k, l]) =
      quarticSixMain W.eval out ![h, n, k, l] := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      using (W.quarticSixMain_tensorPower out ![h, n, k, l]).symm
  have hsource (x : Fin 4 → ℤ) : star (V.quarticReflectionSource c (i₀, i₀) x) =
      K (x 0) (c - x 0 - x 1) (x 2) (x 3) *
        star (K (x 1) (c - x 0 - x 1) (x 2) (x 3)) := by
    simp only [NativeMultidegreeNilcharacter.quarticReflectionSource, hV, K, star_mul, star_star]
    ring
  have hpoint (t : (ZMod N × ZMod N) × (ZMod N × ZMod N)) :
      star (V.quarticReflectionSource c (i₀, i₀) (sample t)) * ∏ i, L i (sample t) =
        K t.2.1.val (c - t.2.1.val - t.2.2.val) t.1.1.val t.1.2.val *
          star (K t.2.2.val (c - t.2.1.val - t.2.2.val) t.1.1.val t.1.2.val) *
            A t.1 t.2.1.val * B t.1 t.2.2.val * D t.2.1.val t.2.2.val t.1.1.val *
              E t.2.1.val t.2.2.val t.1.2.val := by
    simp only [hsource, sample, L, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  have hinput : Real.exp (-r) ≤ ‖𝔼 t : (ZMod N × ZMod N) × (ZMod N × ZMod N),
      star (V.quarticReflectionSource c (i₀, i₀) (sample t)) * ∏ i, L i (sample t)‖ := by
    have hc := (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans hreflection
    simpa only [hpoint, expect_prod_split, c, K] using hc
  obtain ⟨i, j, L', hL', hL'ind, hc⟩ := htransfer V c i₀ i₀
    (Finset.univ : Finset ((ZMod N × ZMod N) × (ZMod N × ZMod N))) Finset.univ_nonempty
    sample L hL hLind (by simpa only [hrV] using hinput)
  conv_lhs at hc => rw [hrV]
  refine ⟨M.mono hqC, hret.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC, E₀.mono hqC,
    i, j, L', hL', hL'ind, ?_⟩
  change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 t : (ZMod N × ZMod N) × (ZMod N × ZMod N),
    V.quarticAntisymmetric i j (sample t) * ∏ k, L' k (sample t)‖
  exact (Real.exp_le_exp.mpr (neg_le_neg hfinal)).trans hc

theorem exists_quartic_antisymmetric_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ (i j : Fin (W.outputDim ^ 6)) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 t : (ZMod N × ZMod N) × (ZMod N × ZMod N),
              (W.tensorPower 6).quarticAntisymmetric i j
                ![(t.2.1.val : ℤ), (t.2.2.val : ℤ), (t.1.1.val : ℤ), (t.1.2.val : ℤ)] *
                ∏ k, A k ![(t.2.1.val : ℤ), (t.2.2.val : ℤ), (t.1.1.val : ℤ), (t.1.2.val : ℤ)]‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_antisymmetric_model_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

end OAI
