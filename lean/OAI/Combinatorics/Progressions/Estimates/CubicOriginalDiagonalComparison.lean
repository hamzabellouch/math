import OAI.Combinatorics.Progressions.Estimates.CubicDerivativeModel
import OAI.Combinatorics.Progressions.Estimates.CubicPermutedSeven
import OAI.Combinatorics.Progressions.Estimates.CubicRootExchange

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_cubic_original_root_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) p)
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 2 p M.eval (fun k x => W.eval k (fun j => x j.1)) →
      NativeIntegerVectorEquivalence 2 ((p + C) ^ C) M.eval W.cubicRoot.cubicHnnTensor := by
  obtain ⟨A, _, hroot⟩ := exists_explicit_cubic_root_equivalence
  obtain ⟨B, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p M W E
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + A) ^ A + p
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_left (by positivity)
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_right hp
  have hdiag (x : Fin 2 → ℤ) :
      cubicTrilinearInput (x 0) (x 1) (x 1) = fun j : CubicReplicatedIndex => x j.1 := by
    rw [cubicTrilinearInput_diagonal]
    have hx : correlationInput (x 0) (x 1) = x := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
  have F := (hroot W).coordinatePullback (fun j : CubicReplicatedIndex => j.1)
  have hright : (fun a (x : Fin 2 → ℤ) =>
      tensorVector W.cubicRoot.eval 3 a (fun j : CubicReplicatedIndex => x j.1)) =
      W.cubicRoot.cubicHnnTensor := by
    funext a x
    rw [cubicHnnTensor, hdiag]
  have F' : NativeIntegerVectorEquivalence 2 t
      (fun k x => W.eval k (fun j => x j.1)) W.cubicRoot.cubicHnnTensor := by
    rw [← hright]
    exact F.mono hAt
  have H := htrans ht (E.mono hpt) F' (fun x => W.unit_eval _)
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativeCubicPairPartition.finite

theorem NativeMultidegreeNilcharacter.exists_cubic_last_slot_translation_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      {σ : Type*} [Fintype σ] (a b c : σ) (shift : ℤ),
      NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
        (fun out (x : σ → ℤ) => W.eval out (cubicTrilinearInput (x a) (x b) (x c)))
        (fun out x => W.eval out (cubicTrilinearInput (x a) (x b) (x c + shift))) := by
  obtain ⟨C, hC, htranslate⟩ :=
    NativeMultidegreeNilcharacter.exists_cubic_integer_translation_equivalence
  refine ⟨C, hC, ?_⟩
  intro p W σ _ a b c shift
  let π : CubicReplicatedIndex → σ := fun j =>
    if j.1 = 0 then a else if j.2.val = 0 then b else c
  let d : CubicReplicatedIndex → ℤ := fun j =>
    if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift
  have E := (htranslate W 0 d).coordinatePullback π
  have hleft : (fun out (x : σ → ℤ) => W.eval out ((fun j => x (π j)) + 0)) =
      (fun out x => W.eval out (cubicTrilinearInput (x a) (x b) (x c))) := by
    funext out x
    apply congrArg (W.eval out)
    funext j
    rcases j with ⟨j, k⟩
    fin_cases j <;> fin_cases k <;> simp [π, cubicTrilinearInput]
  have hright : (fun out (x : σ → ℤ) => W.eval out ((fun j => x (π j)) + d)) =
      (fun out x => W.eval out (cubicTrilinearInput (x a) (x b) (x c + shift))) := by
    funext out x
    apply congrArg (W.eval out)
    funext j
    rcases j with ⟨j, k⟩
    fin_cases j <;> fin_cases k <;> simp [π, d, Pi.add_apply, cubicTrilinearInput]
  simpa only [hleft, hright] using E

theorem exists_cubic_unshifted_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b δ β : ℝ} {N : ℕ} [NeZero N]
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies) (fun _ : Fin 3 => (N : ℝ)) r}
      (_P : NativeCubicPointwisePartition R b δ β), 0 ≤ b →
      ∃ F : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2
          ((p + b + C) ^ C) (F a c))) ∧
        (∀ a c (x : Fin 2 → ZMod N), ‖F a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
              star (W.eval c (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
            F a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (2 * p) * (2 * (δ + 4 * β))) := by
  obtain ⟨A, _, htranslate⟩ :=
    NativeMultidegreeNilcharacter.exists_cubic_last_slot_translation_equivalence
  obtain ⟨B, _, hexchange⟩ := exists_cubic_diagonal_exchange
  obtain ⟨D, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q r b δ β N _ W i j shift V R P hb
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + b + A) ^ A + (p + b + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (b + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) B
  have hcost : (t + D) ^ D ≤ (p + b + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + b) (add_nonneg hp hb)
  obtain ⟨G, hG, heval, _hcap, herr⟩ := hexchange P hb
  let a := fun out (x : Fin 2 → ℤ) => W.eval out (cubicTrilinearInput (x 0) (x 1) (x 1))
  let b₀ := fun out (x : Fin 2 → ℤ) => W.eval out (cubicTrilinearInput (x 1) (x 0) (x 1))
  let u := fun out (x : Fin 2 → ℤ) => W.eval out (cubicTrilinearInput (x 0) (x 1) (x 1 + shift))
  let v := fun out (x : Fin 2 → ℤ) => W.eval out (cubicTrilinearInput (x 1) (x 0) (x 1 + shift))
  let F := fun ac bc x => complexCrossContraction (a ac x) (b₀ bc x)
    (fun k => u k x) (fun l => v l x) (fun k l => G k l x)
  have hF := hcontract G ht ((htranslate W (0 : Fin 2) 1 1 shift).mono hAt)
    ((htranslate W (1 : Fin 2) 0 1 shift).mono hAt)
    (fun k l => ⟨(Classical.choice (hG k l)).mono hBt⟩)
  refine ⟨F, fun ac bc => ⟨(Classical.choice (hF ac bc)).mono hcost⟩, ?_, ?_⟩
  · intro ac bc x
    have hGeq : (fun k l => G k l (fun z => ((x z).val : ℤ))) =
        (fun k l => ∑ cell, (P.partition.cellWeight cell (cubicDiagonalSample x) : ℂ) *
          (P.partition.cellVector cell 0 k (cubicDiagonalSample x) *
            star (P.partition.cellVector cell 1 l (cubicDiagonalSample x)))) := by
      funext k l
      exact heval k l x
    change ‖complexCrossContraction _ _ _ _ _‖ ≤ 1
    rw [hGeq]
    apply norm_complexCrossContraction_positive_mixture
      _ _ _ _ _ _ _ (W.norm_eval _ _) (W.norm_eval _ _) (W.unit_eval _) (W.unit_eval _)
      (fun cell => P.partition.cellWeight_nonneg cell _) (P.partition.cellWeight_total _)
    · intro cell
      exact R.cubicPairFrozenVector_unit 0 _ _ _
    · intro cell
      exact R.cubicPairFrozenVector_unit 1 _ _ _
  · intro ac bc
    have hcard : (Fintype.card (Fin W.outputDim × Fin W.outputDim) : ℝ) ≤ Real.exp (2 * p) := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      calc
        _ ≤ Real.exp p * Real.exp p :=
          mul_le_mul W.output_bound W.output_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add, two_mul]
    calc
      _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ kl : Fin W.outputDim × Fin W.outputDim,
          ‖u kl.1 (fun z => ((x z).val : ℤ)) * star (v kl.2 (fun z => ((x z).val : ℤ))) -
            G kl.1 kl.2 (fun z => ((x z).val : ℤ))‖ := by
        apply Finset.expect_le_expect
        intro x _
        exact norm_sub_complexCrossContraction_le_sum _ _ _ _ _
          (W.norm_eval _ _) (W.norm_eval _ _) (W.unit_eval _) (W.unit_eval _)
          (fun k => W.norm_eval k _) (fun l => W.norm_eval l _)
      _ = ∑ kl : Fin W.outputDim × Fin W.outputDim, 𝔼 x : Fin 2 → ZMod N,
          ‖u kl.1 (fun z => ((x z).val : ℤ)) * star (v kl.2 (fun z => ((x z).val : ℤ))) -
            G kl.1 kl.2 (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
      _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, 2 * (δ + 4 * β) :=
        Finset.sum_le_sum (fun kl _ => herr kl.1 kl.2)
      _ = (Fintype.card (Fin W.outputDim × Fin W.outputDim) : ℝ) * (2 * (δ + 4 * β)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by
        have hδ := P.error_nonneg
        have hβ := P.density_nonneg
        positivity)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_cubic_permuted_seven_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ), 0 ≤ q → 0 ≤ r →
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (G a b))) →
      (∀ a b c : Fin 2, NativeIntegerVectorEquivalence 2 r
        (fun j (x : Fin 2 → ℤ) => W.eval j (cubicTrilinearInput (x a) (x b) (x c)))
        (fun j x => W.eval j (cubicTrilinearInput (x a) (x c) (x b)))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + r + C) ^ C)
        (W.cubicPermutedSevenProduct G a b)) := by
  obtain ⟨A, _, htranslate⟩ := exists_cubic_last_slot_translation_equivalence
  obtain ⟨B, _, hcontract⟩ := exists_native_cross_contraction
  obtain ⟨D, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget 7
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X
  let S := T + (T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((S + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + r + A) ^ A + (p + q + r)
  let s := t + (t + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hqt : q ≤ t := by
    have he : 0 ≤ (p + q + r + A) ^ A := by positivity
    dsimp [t]; linarith
  have hrt : r ≤ t := by
    have he : 0 ≤ (p + q + r + A) ^ A := by positivity
    dsimp [t]; linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hts : t ≤ s := le_add_of_nonneg_right (by positivity)
  have hBs : (t + B) ^ B ≤ s := le_add_of_nonneg_left ht
  have hself (a b c : Fin 2) : NativeIntegerVectorEquivalence 2 t
      (fun j (x : Fin 2 → ℤ) => W.eval j (cubicTrilinearInput (x a) (x b) (x c)))
      (fun j x => W.eval j (cubicTrilinearInput (x a) (x b) (x c))) := by
    simpa only [add_zero] using (htranslate W a b c 0).mono hAt
  have hleft (i j : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 s
        (W.cubicPermutedExchangeLeft G i j)) := by
    have H := hcontract (fun k l x => star (G l k x)) ht
      ((hperm 1 1 0).mono hrt) (hself 0 1 1)
      (fun k l => ⟨(Classical.choice (hG l k)).conjugate.mono hqt⟩) i j
    exact ⟨(Classical.choice H).mono hBs⟩
  have hright (i j : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 s
        (W.cubicPermutedExchangeRight G i j)) := by
    let f : Fin 2 → ((Fin 2 → ℤ) →+ ℤ) :=
      fun i => ⟨⟨fun x => x i.rev, rfl⟩, fun _ _ => rfl⟩
    have H := hcontract (fun k l x => G k l (cubicExchangeSwap x)) ht
      (hself 1 0 0) ((hperm 0 0 1).mono hrt)
      (fun k l => ⟨((Classical.choice (hG k l)).linearPullbackHom f).mono hqt⟩) i j
    exact ⟨(Classical.choice H).mono hBs⟩
  have hfactor (k : Fin 7) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 s
      (W.cubicPermutedSevenFactor G a b k)) := by
    fin_cases k
    · exact hleft (a 0) (b 0)
    · exact ⟨(Classical.choice (hG (b 1) (a 1))).conjugate.mono (hqt.trans hts)⟩
    · exact hright (a 2) (b 2)
    · exact ((hself 0 1 1).mono hts).expansion (a 3) (b 3)
    · exact ((hperm 0 1 0).mono (hrt.trans hts)).expansion (a 4) (b 4)
    · exact ((hself 0 0 1).mono hts).expansion (a 5) (b 5)
    · exact ((hself 0 0 0).mono hts).expansion (a 6) (b 6)
  obtain ⟨F⟩ := hprod (W.cubicPermutedSevenFactor G a b) hs hfactor
  have hcost : (s + D) ^ D ≤ (p + q + r + C) ^ C := by
    simpa [X, T, S, t, s, Polynomial.eval₂_pow] using hbudget (p + q + r) (by positivity)
  exact ⟨F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_cubic_seven_exchange_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ), 0 ≤ q →
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + C) ^ C)
        (W.cubicSevenExchangeProduct G a b)) := by
  obtain ⟨A, _, htranslate⟩ := exists_cubic_last_slot_translation_equivalence
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget 7
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q W G hq hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + A) ^ A + (p + q)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqt : q ≤ t := by
    have he : 0 ≤ (p + q + A) ^ A := by positivity
    dsimp [t]
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (add_nonneg hp hq))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hself (i j : Fin W.outputDim) (a b c : Fin 2) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 t
        (fun x => W.eval i (cubicTrilinearInput (x a) (x b) (x c)) *
          star (W.eval j (cubicTrilinearInput (x a) (x b) (x c))))) := by
    simpa only [add_zero] using ((htranslate W a b c 0).mono hAt).expansion i j
  have hfactor (k : Fin 7) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 t
      (W.cubicSevenExchangeFactor G a b k)) := by
    fin_cases k
    · exact ⟨(Classical.choice (hG (b 0) (a 0))).conjugate.mono hqt⟩
    · exact ⟨(Classical.choice (hG (b 1) (a 1))).conjugate.mono hqt⟩
    · let f : Fin 2 → ((Fin 2 → ℤ) →+ ℤ) :=
        fun i => ⟨⟨fun x => x i.rev, rfl⟩, fun _ _ => rfl⟩
      exact ⟨((Classical.choice (hG (a 2) (b 2))).linearPullbackHom f).mono hqt⟩
    · exact hself (a 3) (b 3) 0 1 1
    · exact hself (a 4) (b 4) 0 0 1
    · exact hself (a 5) (b 5) 0 0 1
    · exact hself (a 6) (b 6) 0 0 0
  obtain ⟨F⟩ := hprod (W.cubicSevenExchangeFactor G a b) ht hfactor
  have hcost : (t + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicPermutedDiagonalCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (b : Fin 7 → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∑ c : Fin 7 → Fin W.outputDim,
    (W.cubicDiagonalDerivative a x * star (W.cubicMixedSeven c x)) *
      W.cubicPermutedSevenProduct G c b x

theorem cubicPermutedDiagonalCorrection_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (a : Fin W.outputDim × Fin W.outputDim) (b : Fin 7 → Fin W.outputDim)
    (x : Fin 2 → ZMod N) :
    ‖W.cubicPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 7 * ((W.outputDim : ℝ) ^ 2 * B) ^ 7 := by
  unfold cubicPermutedDiagonalCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin 7 → Fin W.outputDim, ((W.outputDim : ℝ) ^ 2 * B) ^ 7 := by
      apply Finset.sum_le_sum
      intro c _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
        (W.cubicPermutedSevenProduct_norm G hB hG c b x)
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.cubicDiagonalDerivative_norm _ _)).trans (W.cubicMixedSeven_norm _ _)
    _ = _ := by simp

theorem cubicPermutedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim) (b : Fin 7 → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        W.cubicPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ 7 * (((W.outputDim : ℝ) ^ 2 * B) ^ 7 * ((2 * (W.outputDim : ℝ) ^ 2 + 1) * ε)) := by
  have hid (x : Fin 2 → ℤ) :
      W.cubicDiagonalDerivative a x * star (W.cubicSymmetricSeven b x) =
        ∑ c : Fin 7 → Fin W.outputDim,
          (W.cubicDiagonalDerivative a x * star (W.cubicMixedSeven c x)) *
            (W.cubicMixedSeven c x * star (W.cubicSymmetricSeven b x)) := by
    calc
      _ = ∑ c, ((W.cubicDiagonalDerivative a x * star (W.cubicSymmetricSeven b x)) *
          star (W.cubicMixedSeven c x)) * W.cubicMixedSeven c x :=
        complex_unit_vector_resolution _ (W.cubicMixedSeven_unit x) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        ring
  have hpoint (x : Fin 2 → ZMod N) :
      ‖W.cubicDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        W.cubicPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      ∑ c : Fin 7 → Fin W.outputDim,
        ‖W.cubicMixedSeven c (fun z => ((x z).val : ℤ)) *
            star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
          W.cubicPermutedSevenProduct G c b (fun z => ((x z).val : ℤ))‖ := by
    rw [hid, cubicPermutedDiagonalCorrection, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c _
    rw [← mul_sub, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (W.cubicDiagonalDerivative_norm _ _)).trans (W.cubicMixedSeven_norm _ _)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ c : Fin 7 → Fin W.outputDim,
        ‖W.cubicMixedSeven c (fun z => ((x z).val : ℤ)) *
            star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
          W.cubicPermutedSevenProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ c : Fin 7 → Fin W.outputDim, 𝔼 x : Fin 2 → ZMod N,
        ‖W.cubicMixedSeven c (fun z => ((x z).val : ℤ)) *
            star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
          W.cubicPermutedSevenProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : Fin 7 → Fin W.outputDim,
        ((W.outputDim : ℝ) ^ 2 * B) ^ 7 * ((2 * (W.outputDim : ℝ) ^ 2 + 1) * ε) :=
      Finset.sum_le_sum (fun c _ => W.cubicPermutedSevenProduct_mean_error G hB hG herr c b)
    _ = _ := by simp

theorem exists_cubic_permuted_diagonal_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ), 0 ≤ q → 0 ≤ r →
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (G a b))) →
      (∀ a b c : Fin 2, NativeIntegerVectorEquivalence 2 r
        (fun j (x : Fin 2 → ℤ) => W.eval j (cubicTrilinearInput (x a) (x b) (x c)))
        (fun j x => W.eval j (cubicTrilinearInput (x a) (x c) (x b)))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + r + C) ^ C)
        (W.cubicPermutedDiagonalCorrection G a b)) := by
  obtain ⟨A, _, hderivative⟩ := exists_cubic_diagonal_derivative_equivalence
  obtain ⟨B, _, hseven⟩ := exists_cubic_permuted_seven_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D + 7 * X)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + r + A) ^ A + (p + q + r + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (p + q + r + B) ^ B ≤ t := le_add_of_nonneg_left (by positivity)
  have hterm (c : Fin 7 → Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((t + D) ^ D)
        (fun x => (W.cubicDiagonalDerivative a x * star (W.cubicMixedSeven c x)) *
          W.cubicPermutedSevenProduct G c b x)) := by
    exact hmul ht (Classical.choice (((hderivative W).mono hAt).expansion a c))
      ((Classical.choice (hseven W G hq hr hG hperm c b)).mono hBt)
  have hdim : (Fintype.card (Fin 7 → Fin W.outputDim) : ℝ) ≤ Real.exp (7 * p) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound 7).trans_eq
      (Real.exp_nat_mul p 7).symm
  have hcoeff : (∑ _ : Fin 7 → Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp (7 * p) := by
    simpa using hdim
  have H := NativeIntegerExpansion.weightedSum (fun c => Classical.choice (hterm c))
    (fun _ => 1) (by positivity : 0 ≤ 7 * p) hdim hcoeff
  have hcost : (t + D) ^ D + 7 * p ≤ (p + q + r + C) ^ C := by
    have hb : (t + D) ^ D + 7 * (p + q + r) ≤ (p + q + r + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q + r) (by positivity)
    linarith
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + r + C) ^ C)
    (fun x => ∑ c : Fin 7 → Fin W.outputDim,
      (W.cubicDiagonalDerivative a x * star (W.cubicMixedSeven c x)) *
        W.cubicPermutedSevenProduct G c b x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicDiagonalCubeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (b : Fin 7 → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∑ c : Fin 7 → Fin W.outputDim,
    (W.cubicDiagonalDerivative a x * star (W.cubicMixedSeven c x)) *
      W.cubicSevenExchangeProduct G c b x

theorem cubicDiagonalCubeCorrection_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1)
    (a : Fin W.outputDim × Fin W.outputDim) (b : Fin 7 → Fin W.outputDim)
    (x : Fin 2 → ZMod N) :
    ‖W.cubicDiagonalCubeCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 7 := by
  unfold cubicDiagonalCubeCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin 7 → Fin W.outputDim, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro c _
      rw [norm_mul, norm_mul, norm_star]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
        (W.cubicSevenExchangeProduct_norm G hG c b x)
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.cubicDiagonalDerivative_norm _ _)).trans (W.cubicMixedSeven_norm _ _)
    _ = _ := by simp

theorem cubicDiagonalCubeCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) i x,
      W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
        W.eval i x)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim) (b : Fin 7 → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        W.cubicDiagonalCubeCorrection G a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ 7 * (3 * ε) := by
  have hid (x : Fin 2 → ℤ) :
      W.cubicDiagonalDerivative a x * star (W.cubicSymmetricSeven b x) =
        ∑ c : Fin 7 → Fin W.outputDim,
          (W.cubicDiagonalDerivative a x * star (W.cubicMixedSeven c x)) *
            (W.cubicMixedSeven c x * star (W.cubicSymmetricSeven b x)) := by
    calc
      _ = ∑ c, ((W.cubicDiagonalDerivative a x * star (W.cubicSymmetricSeven b x)) *
          star (W.cubicMixedSeven c x)) * W.cubicMixedSeven c x :=
        complex_unit_vector_resolution _ (W.cubicMixedSeven_unit x) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        ring
  have hpoint (x : Fin 2 → ZMod N) :
      ‖W.cubicDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        W.cubicDiagonalCubeCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      ∑ c : Fin 7 → Fin W.outputDim,
        ‖W.cubicMixedSeven c (fun z => ((x z).val : ℤ)) *
            star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
          W.cubicSevenExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ := by
    rw [hid, cubicDiagonalCubeCorrection, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c _
    rw [← mul_sub, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (W.cubicDiagonalDerivative_norm _ _)).trans (W.cubicMixedSeven_norm _ _)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ c : Fin 7 → Fin W.outputDim,
        ‖W.cubicMixedSeven c (fun z => ((x z).val : ℤ)) *
            star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
          W.cubicSevenExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ c : Fin 7 → Fin W.outputDim, 𝔼 x : Fin 2 → ZMod N,
        ‖W.cubicMixedSeven c (fun z => ((x z).val : ℤ)) *
            star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
          W.cubicSevenExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : Fin 7 → Fin W.outputDim, 3 * ε :=
      Finset.sum_le_sum (fun c _ => W.cubicSevenExchangeProduct_mean_error hsymm G hG herr c b)
    _ = _ := by simp

theorem exists_cubic_diagonal_cube_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ), 0 ≤ q →
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + C) ^ C)
        (W.cubicDiagonalCubeCorrection G a b)) := by
  obtain ⟨A, _, hderivative⟩ := exists_cubic_diagonal_derivative_equivalence
  obtain ⟨B, _, hseven⟩ := exists_cubic_seven_exchange_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D + 7 * X)
  refine ⟨C, hC, ?_⟩
  intro p q W G hq hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + A) ^ A + (p + q + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (p + q + B) ^ B ≤ t := le_add_of_nonneg_left (by positivity)
  have hterm (c : Fin 7 → Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((t + D) ^ D)
        (fun x => (W.cubicDiagonalDerivative a x * star (W.cubicMixedSeven c x)) *
          W.cubicSevenExchangeProduct G c b x)) := by
    exact hmul ht (Classical.choice (((hderivative W).mono hAt).expansion a c))
      ((Classical.choice (hseven W G hq hG c b)).mono hBt)
  have hdim : (Fintype.card (Fin 7 → Fin W.outputDim) : ℝ) ≤ Real.exp (7 * p) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound 7).trans_eq
      (Real.exp_nat_mul p 7).symm
  have hcoeff : (∑ _ : Fin 7 → Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp (7 * p) := by
    simpa using hdim
  have H := NativeIntegerExpansion.weightedSum (fun c => Classical.choice (hterm c))
    (fun _ => 1) (by positivity : 0 ≤ 7 * p) hdim hcoeff
  have hcost : (t + D) ^ D + 7 * p ≤ (p + q + C) ^ C := by
    have hb : (t + D) ^ D + 7 * (p + q) ≤ (p + q + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
    linarith
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + C) ^ C)
    (fun x => ∑ c : Fin 7 → Fin W.outputDim,
      (W.cubicDiagonalDerivative a x * star (W.cubicMixedSeven c x)) *
        W.cubicSevenExchangeProduct G c b x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicRootSevenCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.cubicRoot.cubicPermutedDiagonalCorrection (W.cubicRootExchangeCorrection G)

theorem cubicRootSevenCorrection_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (a : Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim)
    (b : Fin 7 → Fin W.cubicRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cubicRootSevenCorrection G a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 315 := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ 18 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd 18
  have h := W.cubicRoot.cubicPermutedDiagonalCorrection_norm
    (W.cubicRootExchangeCorrection G) hB (W.cubicRootExchangeCorrection_norm G hG) a b x
  exact h.trans_eq (by
    change (((W.outputDim ^ 9 : ℕ) : ℝ) ^ 7 *
      ((((W.outputDim ^ 9 : ℕ) : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 18) ^ 7)) = _
    rw [Nat.cast_pow]
    ring)

theorem cubicRootSevenCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval j (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim)
    (b : Fin 7 → Fin W.cubicRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicRoot.cubicDiagonalDerivative a (fun k => ((x k).val : ℤ)) *
          star (W.cubicRoot.cubicSymmetricSeven b (fun k => ((x k).val : ℤ))) -
        W.cubicRootSevenCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      81 * (W.outputDim : ℝ) ^ 335 * (2 * (W.outputDim : ℝ) ^ 18 + 1) * ε := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ 18 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd 18
  have h := W.cubicRoot.cubicPermutedDiagonalCorrection_mean_error
    (W.cubicRootExchangeCorrection G) hB (W.cubicRootExchangeCorrection_norm G hG)
    (W.cubicRootExchangeCorrection_mean_error G hG herr) a b
  exact h.trans_eq (by
    change (((W.outputDim ^ 9 : ℕ) : ℝ) ^ 7 *
      (((((W.outputDim ^ 9 : ℕ) : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 18) ^ 7) *
        ((2 * (((W.outputDim ^ 9 : ℕ) : ℝ) ^ 2) + 1) *
          (81 * (W.outputDim : ℝ) ^ 20 * ε)))) = _
    rw [Nat.cast_pow]
    ring)

theorem exists_cubicRootSevenCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p), 0 ≤ q →
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) = W.eval i x) →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + C) ^ C)
        (W.cubicRootSevenCorrection G a b)) := by
  obtain ⟨A, _, hexchange⟩ := exists_cubicRootExchangeCorrection_expansion
  obtain ⟨B, _, hperm⟩ := exists_cubic_root_last_slots_equivalence
  obtain ⟨D, _, hdiagonal⟩ := exists_cubic_permuted_diagonal_expansion
  let X : Polynomial ℕ := Polynomial.X
  let T := 10 * (X + 1) + (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨H⟩ := hdiagonal W.cubicRoot (W.cubicRootExchangeCorrection G)
    (by positivity : 0 ≤ (p + q + A) ^ A) (by positivity : 0 ≤ (p + B) ^ B)
    (hexchange W hq G hG) (hperm W hsymm) a b
  have hcost : (tensorPowerBudget 9 p + (p + q + A) ^ A + (p + B) ^ B + D) ^ D ≤
      (p + q + C) ^ C := by
    have hmono : (p + B) ^ B ≤ (p + q + B) ^ B :=
      pow_le_pow_left₀ (by positivity) (by linarith) B
    have hbound : (10 * (p + q + 1) + (p + q + A) ^ A + (p + q + B) ^ B + D) ^ D ≤
        (p + q + C) ^ C := by
      simpa [X, T, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
    apply le_trans _ hbound
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    norm_num [tensorPowerBudget]
    linarith
  exact ⟨H.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicRootCyclicCorrection (N : ℕ) (δ : ℝ≥0)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.cubicRoot.cubicCyclicDiagonalCorrection N δ (W.cubicRootSevenCorrection G)

theorem cubicRootCyclicCorrection_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval j (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim)
    (b : Fin 7 → Fin W.cubicRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicRoot.cubicCyclicDiagonalDerivative a x *
          star (W.cubicRoot.cubicSymmetricSeven b (fun k => ((x k).val : ℤ))) -
        W.cubicRootCyclicCorrection N δ G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.cubicRoot.outputDim + 1) *
        (81 * (W.outputDim : ℝ) ^ 335 * (2 * (W.outputDim : ℝ) ^ 18 + 1) * ε) +
          12 * (δ : ℝ) + 2 / N :=
  W.cubicRoot.cubicCyclicDiagonalCorrection_mean_error δ hδ (W.cubicRootSevenCorrection G)
    (W.cubicRootSevenCorrection_mean_error G hG herr) a b

theorem exists_cubicRootCyclicCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) (N : ℕ) (δ : ℝ≥0),
      0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) a).symm j)) = W.eval k x) →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + e + C) ^ C)
        (W.cubicRootCyclicCorrection N δ G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_cubicRootSevenCorrection_expansion
  obtain ⟨B, _, hcyclic⟩ := exists_cubicCyclicDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((10 * (X + 1) + (X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : (p + q + A) ^ A ≤ (v + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have hbound : (tensorPowerBudget 9 p + (p + q + A) ^ A + e + B) ^ B ≤
      (p + q + e + C) ^ C := by
    have hh : (10 * (v + 1) + (v + A) ^ A + v + B) ^ B ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    norm_num only [tensorPowerBudget, Nat.cast_ofNat] at *
    dsimp [v] at *
    linarith
  obtain ⟨E⟩ := hcyclic W.cubicRoot N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.cubicRootSevenCorrection G) (hroot W hq hsymm G hG) a b
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) p)
  (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicOriginalDiagonalCorrection
    (F : (Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) →
      (Fin 7 → Fin W.cubicRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) (i : Fin M.outputDim)
    (b : Fin 3 → Fin W.cubicRoot.outputDim) (c : Fin W.cubicRoot.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ d : Fin 3 → Fin W.cubicRoot.outputDim,
    (M.eval i x * star (W.cubicRoot.cubicHnnTensor d x)) * F a (cubicSevenMerge d b c) x

theorem cubicOriginalDiagonalCorrection_pointwise_error {N : ℕ} [NeZero N]
    (F : (Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) →
      (Fin 7 → Fin W.cubicRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) (i : Fin M.outputDim)
    (b : Fin 3 → Fin W.cubicRoot.outputDim) (c : Fin W.cubicRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cubicRoot.cubicCyclicDiagonalDerivative a x *
        (M.eval i (fun k => ((x k).val : ℤ)) *
          (W.cubicRoot.cubicHhnTensor b (fun k => ((x k).val : ℤ)) *
            W.cubicRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
      M.cubicOriginalDiagonalCorrection W F a i b c (fun k => ((x k).val : ℤ))‖ ≤
      ∑ d : Fin 3 → Fin W.cubicRoot.outputDim,
        ‖W.cubicRoot.cubicCyclicDiagonalDerivative a x *
            star (W.cubicRoot.cubicSymmetricSeven (cubicSevenMerge d b c)
              (fun k => ((x k).val : ℤ))) -
          F a (cubicSevenMerge d b c) (fun k => ((x k).val : ℤ))‖ := by
  let z : Fin 2 → ℤ := fun k => ((x k).val : ℤ)
  let R := W.cubicRoot
  let D := R.cubicCyclicDiagonalDerivative a x
  have hres := complex_unit_vector_resolution (fun d => R.cubicHnnTensor d z)
    (R.cubicHnnTensor_unit z) (M.eval i z)
  have heq : D * (M.eval i z * (R.cubicHhnTensor b z * R.eval c (fun _ => z 0))) =
      ∑ d : Fin 3 → Fin R.outputDim,
        (M.eval i z * star (R.cubicHnnTensor d z)) *
          (D * star (R.cubicSymmetricSeven (cubicSevenMerge d b c) z)) := by
    calc
      _ = D * ((∑ d, (M.eval i z * star (R.cubicHnnTensor d z)) * R.cubicHnnTensor d z) *
          (R.cubicHhnTensor b z * R.eval c (fun _ => z 0))) := by rw [← hres]
      _ = _ := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [R.cubicSymmetricSeven_merge]
        ring
  change ‖D * (M.eval i z * (R.cubicHhnTensor b z * R.eval c (fun _ => z 0))) -
    M.cubicOriginalDiagonalCorrection W F a i b c z‖ ≤ _
  rw [heq, cubicOriginalDiagonalCorrection, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [← mul_sub, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (M.norm_eval i z)).trans
    (R.cubicHnnTensor_norm d z)

theorem cubicOriginalDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) →
      (Fin 7 → Fin W.cubicRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicRoot.cubicCyclicDiagonalDerivative a x *
          star (W.cubicRoot.cubicSymmetricSeven b (fun k => ((x k).val : ℤ))) -
        F a b (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) (i : Fin M.outputDim)
    (b : Fin 3 → Fin W.cubicRoot.outputDim) (c : Fin W.cubicRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicRoot.cubicCyclicDiagonalDerivative a x *
          (M.eval i (fun k => ((x k).val : ℤ)) *
            (W.cubicRoot.cubicHhnTensor b (fun k => ((x k).val : ℤ)) *
              W.cubicRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
        M.cubicOriginalDiagonalCorrection W F a i b c (fun k => ((x k).val : ℤ))‖) ≤
      (W.cubicRoot.outputDim : ℝ) ^ 3 * ε := by
  have hm := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => M.cubicOriginalDiagonalCorrection_pointwise_error W F a i b c x)
  rw [Finset.expect_sum_comm] at hm
  apply hm.trans
  calc
    _ ≤ ∑ _ : Fin 3 → Fin W.cubicRoot.outputDim, ε :=
      Finset.sum_le_sum (fun d _ => herr a (cubicSevenMerge d b c))
    _ = _ := by simp

theorem exists_cubicOriginalDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) p)
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p), 0 ≤ q →
      NativeIntegerVectorEquivalence 2 p M.eval (fun k x => W.eval k (fun j => x j.1)) →
      ∀ F : (Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) →
        (Fin 7 → Fin W.cubicRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (F a b))) →
      ∀ a i b c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + C) ^ C)
        (M.cubicOriginalDiagonalCorrection W F a i b c)) := by
  obtain ⟨A, _, hcompare⟩ := exists_cubic_original_root_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C B) ^ B + 30 * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p q M W hq E F hF a i b c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqt : q ≤ t := by
    have hh : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t, v] at *
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    linarith
  have hterm (d : Fin 3 → Fin W.cubicRoot.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((t + B) ^ B)
        (fun x => (M.eval i x * star (W.cubicRoot.cubicHnnTensor d x)) *
          F a (cubicSevenMerge d b c) x)) :=
    hmul ht ((Classical.choice ((hcompare M W E).expansion i d)).mono hAt)
      ((Classical.choice (hF a (cubicSevenMerge d b c))).mono hqt)
  have hcard : (Fintype.card (Fin 3 → Fin W.cubicRoot.outputDim) : ℝ) ≤
      Real.exp (30 * (v + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 9 p) ^ 3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) W.cubicRoot.output_bound _
      _ = Real.exp (3 * tensorPowerBudget 9 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 9 p) 3).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        norm_num [tensorPowerBudget]
        dsimp [v]
        linarith
  have hcoeff : (∑ _ : Fin 3 → Fin W.cubicRoot.outputDim, ‖(1 : ℂ)‖) ≤
      Real.exp (30 * (v + 1)) := by simpa using hcard
  have H := NativeIntegerExpansion.weightedSum (fun d => Classical.choice (hterm d))
    (fun _ => (1 : ℂ)) (by positivity : 0 ≤ 30 * (v + 1)) hcard hcoeff
  have hcost : (t + B) ^ B + 30 * (v + 1) ≤ (p + q + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + C) ^ C)
    (fun x => ∑ d : Fin 3 → Fin W.cubicRoot.outputDim,
      (M.eval i x * star (W.cubicRoot.cubicHnnTensor d x)) * F a (cubicSevenMerge d b c) x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
