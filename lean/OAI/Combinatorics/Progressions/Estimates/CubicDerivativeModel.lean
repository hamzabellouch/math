import OAI.Combinatorics.Progressions.Estimates.QuarticCorrelatingVerticalPair

namespace OAI

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

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}

structure NativeCubicPointwisePartition
    (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
      V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
      (fun _ : Fin 3 => (N : ℝ)) r) (b δ β : ℝ) where
  partition : NativeCubicPairPartition R b (δ + 6 * β)
  error_nonneg : 0 ≤ δ
  density_nonneg : 0 ≤ β
  bad : Finset (ZMod N)
  bad_density : (bad.card : ℝ) / N ≤ β
  pointwise : ∀ a x, (∀ l, x l ∉ bad) → 0 < partition.cellWeight a x →
    ∀ (k : Fin 2) (out : Fin W.outputDim),
      ‖W.eval out (cubicTrilinearInput ((x k.succ).val : ℤ) ((x k.rev.succ).val : ℤ)
          (((x 0).val : ℤ) + shift)) - partition.cellVector a k out x‖ ≤ δ

namespace NativeCubicPointwisePartition

attribute [local instance] NativeCubicPairPartition.finite

variable {b δ β : ℝ} (P : NativeCubicPointwisePartition R b δ β)

noncomputable def mono {b' δ' β' : ℝ} (hb : b ≤ b') (hδ : δ ≤ δ') (hβ : β ≤ β') :
    NativeCubicPointwisePartition R b' δ' β' where
  partition := P.partition.mono hb (by linarith)
  error_nonneg := P.error_nonneg.trans hδ
  density_nonneg := P.density_nonneg.trans hβ
  bad := P.bad
  bad_density := P.bad_density.trans hβ
  pointwise := fun a x hx hax k out => (P.pointwise a x hx hax k out).trans hδ

theorem sampled_error {X : Type*} [Fintype X] [Nonempty X]
    (sample : X → Fin 3 → ZMod N) (E : Finset X)
    (hE : ∀ x, x ∉ E → ∀ l, sample x l ∉ P.bad) (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x, ∑ a, P.partition.cellWeight a (sample x) *
      ‖W.eval out (cubicTrilinearInput ((sample x k.succ).val : ℤ) ((sample x k.rev.succ).val : ℤ)
          (((sample x 0).val : ℤ) + shift)) - P.partition.cellVector a k out (sample x)‖) ≤
      δ + 2 * (E.card : ℝ) / Fintype.card X := by
  exact weighted_partition_mean_error E
    (fun a x => P.partition.cellWeight a (sample x))
    (fun a x => P.partition.cellVector a k out (sample x)) _ P.error_nonneg
    (fun a x => P.partition.cellWeight_nonneg a (sample x))
    (fun x => P.partition.cellWeight_total (sample x))
    (fun a x => P.partition.cellVector_norm a k out (sample x))
    (fun x => W.norm_eval out _) (fun a x hx hax => P.pointwise a (sample x) (hE x hx) hax k out)

theorem sampled_approximation {X : Type*} [Fintype X] [Nonempty X]
    (sample : X → Fin 3 → ZMod N) (E : Finset X)
    (hE : ∀ x, x ∉ E → ∀ l, sample x l ∉ P.bad) (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x, ‖W.eval out (cubicTrilinearInput ((sample x k.succ).val : ℤ) ((sample x k.rev.succ).val : ℤ)
          (((sample x 0).val : ℤ) + shift)) -
      ∑ a, (P.partition.cellWeight a (sample x) : ℂ) * P.partition.cellVector a k out (sample x)‖) ≤
      δ + 2 * (E.card : ℝ) / Fintype.card X := by
  apply le_trans _ (P.sampled_error sample E hE k out)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (sample x))
    (fun a => P.partition.cellVector a k out (sample x)) _
    (fun a => P.partition.cellWeight_nonneg a (sample x)) (P.partition.cellWeight_total (sample x)))

end NativeCubicPointwisePartition
end Erdos3

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

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

theorem select_cubic_pointwise_partition {b c : ℝ}
    (hlocal : R.HasCubicPairLocalApproximation b) (hred : R.HasCubicPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin 3 → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin 3 → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence 2 c
            (R.cubicPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.cubicPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ a x, (∀ l, x l ∉ B) → 0 < A a x →
            ∀ (k : Fin 2) (out : Fin W.outputDim),
              ‖W.eval out (cubicTrilinearInput ((x k.succ).val : ℤ) ((x k.rev.succ).val : ℤ)
                  (((x 0).val : ℤ) + shift)) -
                R.cubicPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
                  (fun l => ((x l).val : ℤ))‖ ≤ Real.exp b * ρ := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin 3 → ZMod N) (i : Fin 3) => ((x i).val : ℤ)
  have hv (x : Fin 3 → ZMod N) (i : Fin 3) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin 3 → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.cubicPairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro a x hx hax k out
  obtain ⟨hy', hAy⟩ := hy a x hx hax
  obtain ⟨hres, hnear⟩ := hcells a x (y a) hx hy' hax hAy
  exact hmodel (v (y a)) (hv (y a)) k out (v x) ρ hρ (hv x) hres
    (by simpa only [v, Int.cast_natCast] using hnear)

end NativePolynomialOrbitFactors

theorem exists_cubic_pointwise_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r),
      R.HasCubicPairLocalApproximation b → R.HasCubicPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      Nonempty (NativeCubicPointwisePartition R ((t + C) ^ C)
        (Real.exp t * ρ) (6 * ρ + 3 / N)) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 60 + 3 * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t W N _ i j shift V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_cubic_pointwise_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨n, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 60 + 3 * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have htC : t ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have hthree : 3 * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  let w := productPartitionWeight (fun _ : Fin 3 => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin 3 => A) i j x :=
    fun _ j x => ((hA j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hcells : ∀ j x y, (∀ i, x i ∉ E) → (∀ i, y i ∉ E) → 0 < w j x → 0 < w j y →
      (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ) := by
    intro j x y hx hy hwx hwy
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j y hwy
    exact ⟨fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).2,
      fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).1⟩
  obtain ⟨y, hequiv, hpoint⟩ := hselect E w hρ.le hw hwSum hcells
  let δ := Real.exp t * ρ
  let β := 6 * ρ + 3 / (N : ℝ)
  have hδ : 0 ≤ δ := mul_nonneg (Real.exp_nonneg _) hρ.le
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hbad : (E.card : ℝ) / N ≤ β := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
  have hcard' : (Fintype.card (Fin 3 → Fin n × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3
      _ = Real.exp (3 * (t + B) ^ B) := (Real.exp_nat_mul _ 3).symm
      _ ≤ _ := Real.exp_le_exp.mpr hthree
  have hpoint' (a) (x) (hx : ∀ l, x l ∉ E) (hax : 0 < w a x) (k : Fin 2) (out : Fin W.outputDim) :
      ‖W.eval out (cubicTrilinearInput ((x k.succ).val : ℤ) ((x k.rev.succ).val : ℤ)
          (((x 0).val : ℤ) + shift)) - R.cubicPairAnchoredVector
        (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖ ≤ δ :=
    (hpoint a x hx hax k out).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbt) hρ.le)
  have herr (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin 3 → ZMod N, ∑ a, w a x *
        ‖W.eval out (cubicTrilinearInput ((x k.succ).val : ℤ) ((x k.rev.succ).val : ℤ)
            (((x 0).val : ℤ) + shift)) - R.cubicPairAnchoredVector
          (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖) ≤ δ + 6 * β := by
    have h := weighted_partition_mean_error (coordinateExceptional E) w
      (fun a x => R.cubicPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
        (fun l => ((x l).val : ℤ))) _ hδ hw hwSum
      (fun a x => R.cubicPairAnchoredVector_norm _ _ _ _)
      (fun x => W.norm_eval out _) (fun a x hx hax =>
        hpoint' a x ((not_mem_coordinateExceptional E x).mp hx) hax k out)
    have hd : ((coordinateExceptional (ι := Fin 3) E).card : ℝ) / Fintype.card (Fin 3 → ZMod N) ≤
        3 * ((E.card : ℝ) / N) := by
      simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] using
        coordinateExceptional_density_le (ι := Fin 3) E
    rw [mul_div_assoc] at h
    linarith
  let core : NativeCubicPairPartition R ((t + C) ^ C) (δ + 6 * β) := {
    I := Fin n × ZMod P
    card_bound := hcard'
    weight := A
    positive := fun j => (hA j).mono le_rfl hcost
    total := hsum
    anchor := y
    equivalence := fun j => (hequiv j).mono (hct.trans htC)
    weighted_approximation := herr }
  exact ⟨{
    partition := core
    error_nonneg := hδ
    density_nonneg := hβ
    bad := E
    bad_density := hbad
    pointwise := hpoint' }⟩

end Erdos3

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

def cubicDiagonalSample {X : Type*} (x : Fin 2 → X) : Fin 3 → X := ![x 1, x 0, x 1]

theorem cubicDiagonalSample_avoids {X : Type*} (B : Set X) (x : Fin 2 → X)
    (hx : ∀ k, x k ∉ B) : ∀ l, cubicDiagonalSample x l ∉ B := by
  intro l
  fin_cases l
  · exact hx 1
  · exact hx 0
  · exact hx 1

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}

namespace NativeCubicPointwisePartition

attribute [local instance] NativeCubicPairPartition.finite

variable {b δ β : ℝ} (P : NativeCubicPointwisePartition R b δ β)

theorem weighted_diagonal_error (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (cubicDiagonalSample x) *
      ‖W.eval out (cubicTrilinearInput ((x 0).val : ℤ) ((x 1).val : ℤ) (((x 1).val : ℤ) + shift)) -
        P.partition.cellVector a 0 out (cubicDiagonalSample x)‖) ≤ δ + 4 * β := by
  let E := coordinateExceptional (ι := Fin 2) P.bad
  have h := P.sampled_error cubicDiagonalSample E (fun x hx =>
    cubicDiagonalSample_avoids (P.bad : Set (ZMod N)) x ((not_mem_coordinateExceptional P.bad x).mp hx)) 0 out
  have hd : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * β := by
    have hD := coordinateExceptional_density_le (ι := Fin 2) P.bad
    simp only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] at hD
    exact hD.trans (mul_le_mul_of_nonneg_left P.bad_density (by norm_num))
  change (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (cubicDiagonalSample x) *
      ‖W.eval out (cubicTrilinearInput ((x 0).val : ℤ) ((x 1).val : ℤ) (((x 1).val : ℤ) + shift)) -
        P.partition.cellVector a 0 out (cubicDiagonalSample x)‖) ≤
    δ + 2 * (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) at h
  rw [mul_div_assoc] at h
  linarith

theorem diagonal_approximation (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out (cubicTrilinearInput ((x 0).val : ℤ) ((x 1).val : ℤ) (((x 1).val : ℤ) + shift)) -
        ∑ a, (P.partition.cellWeight a (cubicDiagonalSample x) : ℂ) *
          P.partition.cellVector a 0 out (cubicDiagonalSample x)‖) ≤ δ + 4 * β := by
  apply le_trans _ (P.weighted_diagonal_error out)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (cubicDiagonalSample x))
    (fun a => P.partition.cellVector a 0 out (cubicDiagonalSample x)) _
    (fun a => P.partition.cellWeight_nonneg a (cubicDiagonalSample x))
    (P.partition.cellWeight_total (cubicDiagonalSample x)))

end NativeCubicPointwisePartition

theorem exists_cubic_diagonal_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r),
      R.HasCubicPairLocalApproximation b → R.HasCubicPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      ∃ δ β : ℝ, ∃ _P : NativeCubicPointwisePartition R ((t + e + C) ^ C) δ β,
        δ + 4 * β ≤ Real.exp (-e) := by
  obtain ⟨A, _, hpartition⟩ := exists_cubic_pointwise_partition 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e W N _ i j shift V R hlocal hred ht he hbt hct hN
  let u := t + e + 100
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsum : (u + A) ^ A + 2 * u ≤ (t + e + C) ^ C := by
    simpa [X, T, u, Polynomial.eval₂_pow] using hbudget (t + e) (add_nonneg ht he)
  have hcost : (u + A) ^ A ≤ (t + e + C) ^ C := by linarith
  have hscale : 2 * u ≤ (t + e + C) ^ C := by
    have : 0 ≤ (u + A) ^ A := by positivity
    linarith
  let ρ := Real.exp (-(2 * u))
  have hρ : 0 < ρ := Real.exp_pos _
  have hprec : 1 / ρ ≤ Real.exp ((u + 2) ^ 2) := by
    dsimp [ρ]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  obtain ⟨P⟩ := hpartition R hlocal hred hu
    (hbt.trans (by dsimp [u]; linarith)) (hct.trans (by dsimp [u]; linarith)) hρ hprec
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using h
  have hρle : ρ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have hthree : (3 : ℝ) / N ≤ 3 * ρ := by
    calc
      _ = 3 * (1 / (N : ℝ)) := by ring
      _ ≤ 3 * ρ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  have hδ : Real.exp u * ρ = Real.exp (-u) := by
    dsimp [ρ]
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨Real.exp u * ρ, 6 * ρ + 3 / N, P.mono hcost le_rfl le_rfl, ?_⟩
  calc
    _ ≤ 37 * Real.exp (-u) := by rw [hδ]; linarith
    _ ≤ Real.exp 100 * Real.exp (-u) := by
      gcongr
      linarith [Real.add_one_le_exp (100 : ℝ)]
    _ = Real.exp (100 - u) := by simp only [← Real.exp_add, sub_eq_add_neg]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [u]; linarith)

end Erdos3

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

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}

attribute [local instance] NativeCubicPairPartition.finite

theorem NativeCubicPointwisePartition.exists_correlating_anchor {b δ β η : ℝ}
    (P : NativeCubicPointwisePartition R b δ β) (out : Fin W.outputDim)
    (f : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N))
    (hf : ∀ h n, ‖f h n‖ ≤ 1) (hη : 0 < η)
    (hmass : η ≤ 𝔼 h : ZMod N, if h ∈ H then
      ‖𝔼 n : ZMod N, f h n * star
        (W.eval out (cubicTrilinearInput h.val n.val ((n.val : ℤ) + shift)))‖ else 0)
    (herror : δ + 4 * β ≤ η / 2) :
    ∃ a : Fin 3 → P.partition.I, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
      η / (4 * Real.exp b) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, η / (4 * Real.exp b) ≤ ‖𝔼 n : ZMod N, f h n * star
        (((P.partition.weight (a 0) n * P.partition.weight (a 2) n : ℝ) : ℂ) *
          P.partition.cellVector a 0 out (cubicDiagonalSample ![h, n]))‖ := by
  classical
  let C := fun (a : Fin 3 → P.partition.I) (h n : ZMod N) =>
    P.partition.cellVector a 0 out (cubicDiagonalSample ![h, n])
  let v := fun (a : Fin 3 → P.partition.I) (h n : ZMod N) =>
    (P.partition.cellWeight a (cubicDiagonalSample ![h, n]) : ℂ) * C a h n
  have hw (i : P.partition.I) (n : ZMod N) : ‖(P.partition.weight i n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((P.partition.positive i).unit_interval n).1]
    exact ((P.partition.positive i).unit_interval n).2
  have hv (a : Fin 3 → P.partition.I) (h n : ZMod N) : ‖v a h n‖ ≤ 1 := by
    have hweight : ‖(P.partition.cellWeight a (cubicDiagonalSample ![h, n]) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (P.partition.cellWeight_nonneg _ _)]
      exact Finset.prod_le_one₀ (fun l _ => ((P.partition.positive (a l)).unit_interval _).1)
        (fun l _ => ((P.partition.positive (a l)).unit_interval _).2)
    exact (norm_mul _ _).trans_le ((mul_le_of_le_one_left (norm_nonneg _) hweight).trans
      (P.partition.cellVector_norm _ _ _ _))
  have herr : (𝔼 h : ZMod N, 𝔼 n : ZMod N,
      ‖W.eval out (cubicTrilinearInput h.val n.val ((n.val : ℤ) + shift)) - ∑ a, v a h n‖) ≤ η / 2 := by
    have h := (P.diagonal_approximation out).trans herror
    rw [expect_fin_two] at h
    exact h
  obtain ⟨a, S, hSH, hS, hsize, hcorr⟩ := exists_dense_row_partition_correlation H f
    (fun h n => W.eval out (cubicTrilinearInput h.val n.val ((n.val : ℤ) + shift)))
    v hη (Real.exp_pos b) P.partition.card_bound hf hv hmass herr
  refine ⟨a, S, hSH, hS, by simpa only [ZMod.card] using hsize, ?_⟩
  intro h hh
  have hrow : (𝔼 n : ZMod N, f h n * star (v a h n)) =
      (P.partition.weight (a 1) h : ℂ) * (𝔼 n : ZMod N, f h n * star
        (((P.partition.weight (a 0) n * P.partition.weight (a 2) n : ℝ) : ℂ) * C a h n)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    have hlast : Matrix.vecHead (Matrix.vecTail ![h, n]) = n := rfl
    simp only [v, NativeCubicPairPartition.cellWeight, cubicDiagonalSample, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal, hlast]
    ring
  apply (hcorr h hh).trans
  rw [hrow, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw _ _)

end Erdos3

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

namespace NativeCubicPointwisePartition

variable {p q r b δ β : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}
  (P : NativeCubicPointwisePartition R b δ β)

theorem weighted_diagonal_error_side (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (cubicDiagonalSample x) *
      ‖W.eval out (cubicTrilinearInput ((x k).val : ℤ) ((x k.rev).val : ℤ)
          (((x 1).val : ℤ) + shift)) - P.partition.cellVector a k out (cubicDiagonalSample x)‖) ≤
      δ + 4 * β := by
  let E := coordinateExceptional (ι := Fin 2) P.bad
  have h := P.sampled_error cubicDiagonalSample E (fun x hx =>
    cubicDiagonalSample_avoids (P.bad : Set (ZMod N)) x ((not_mem_coordinateExceptional P.bad x).mp hx)) k out
  have hd : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * β := by
    have hD := coordinateExceptional_density_le (ι := Fin 2) P.bad
    simp only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] at hD
    exact hD.trans (mul_le_mul_of_nonneg_left P.bad_density (by norm_num))
  have hsample (x : Fin 2 → ZMod N) :
      cubicTrilinearInput ((cubicDiagonalSample x k.succ).val : ℤ)
        ((cubicDiagonalSample x k.rev.succ).val : ℤ)
        (((cubicDiagonalSample x 0).val : ℤ) + shift) =
      cubicTrilinearInput ((x k).val : ℤ) ((x k.rev).val : ℤ) (((x 1).val : ℤ) + shift) := by
    fin_cases k <;> rfl
  simp only [hsample] at h
  rw [mul_div_assoc] at h
  linarith

theorem weighted_diagonal_exchange_error (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (cubicDiagonalSample x) *
      ‖W.eval out₀ (cubicTrilinearInput (x 0).val (x 1).val (((x 1).val : ℤ) + shift)) *
          star (W.eval out₁ (cubicTrilinearInput (x 1).val (x 0).val (((x 1).val : ℤ) + shift))) -
        P.partition.cellVector a 0 out₀ (cubicDiagonalSample x) *
          star (P.partition.cellVector a 1 out₁ (cubicDiagonalSample x))‖) ≤ 2 * (δ + 4 * β) := by
  let err := fun (k : Fin 2) (out : Fin W.outputDim) (a : Fin 3 → P.partition.I)
      (x : Fin 2 → ZMod N) =>
    ‖W.eval out (cubicTrilinearInput (x k).val (x k.rev).val (((x 1).val : ℤ) + shift)) -
      P.partition.cellVector a k out (cubicDiagonalSample x)‖
  have hbound (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (cubicDiagonalSample x) * err k out a x) ≤
        δ + 4 * β := P.weighted_diagonal_error_side k out
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (cubicDiagonalSample x) *
        (err 0 out₀ a x + err 1 out₁ a x) := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (P.partition.cellWeight_nonneg _ _)
      exact norm_mul_star_sub_mul_star_le_of_le_one (W.norm_eval out₁ _)
        (P.partition.cellVector_norm a 0 out₀ _)
    _ = (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (cubicDiagonalSample x) * err 0 out₀ a x) +
        (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (cubicDiagonalSample x) * err 1 out₁ a x) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.expect_add_distrib]
    _ ≤ _ := by linarith [hbound 0 out₀, hbound 1 out₁]

theorem diagonal_exchange_approximation (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out₀ (cubicTrilinearInput (x 0).val (x 1).val (((x 1).val : ℤ) + shift)) *
          star (W.eval out₁ (cubicTrilinearInput (x 1).val (x 0).val (((x 1).val : ℤ) + shift))) -
        ∑ a, (P.partition.cellWeight a (cubicDiagonalSample x) : ℂ) *
          (P.partition.cellVector a 0 out₀ (cubicDiagonalSample x) *
            star (P.partition.cellVector a 1 out₁ (cubicDiagonalSample x)))‖) ≤ 2 * (δ + 4 * β) := by
  apply le_trans _ (P.weighted_diagonal_exchange_error out₀ out₁)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (cubicDiagonalSample x))
    (fun a => P.partition.cellVector a 0 out₀ (cubicDiagonalSample x) *
      star (P.partition.cellVector a 1 out₁ (cubicDiagonalSample x))) _
    (fun a => P.partition.cellWeight_nonneg a _) (P.partition.cellWeight_total _))

end NativeCubicPointwisePartition
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {N : ℕ} [NeZero N]

noncomputable def normalizedDerivativeRow (T : D.Niltest (fun _ : Fin 2 => 1)) (p : ℝ)
    (f : ZMod N → ℂ) (χ : ZMod N → AddChar (ZMod N) ℂ) (h n : ZMod N) : ℂ :=
  multiplicativeDerivative f h n * star (χ h n) *
    star ((T.expNormalize p).eval (correlationInput (h.val : ℤ) (n.val : ℤ)))

theorem normalizedDerivativeRow_norm (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}
    (hT : T.ComplexityLE p) (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (χ : ZMod N → AddChar (ZMod N) ℂ) (h n : ZMod N) :
    ‖T.normalizedDerivativeRow p f χ h n‖ ≤ 1 := by
  unfold normalizedDerivativeRow
  rw [norm_mul, norm_mul, norm_star, norm_star, AddChar.norm_apply, mul_one]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (multiplicativeDerivative_norm_le_one f hf h n)).trans
  apply ((T.expNormalize p).norm_eval_le _).trans
  exact_mod_cast T.expNormalize_norm hT

end RationalFilteredNilmanifold.Niltest

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativeCubicPairPartition.finite

theorem exists_fixed_cubic_shifted_correlation {m p u a : ℝ} {N : ℕ} [NeZero N]
    {M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) m}
    {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {shift : ℤ}
    (E : NativeIntegerVectorEquivalence 2 u M.eval
      (fun out x => W.eval out (cubicTrilinearInput (x 0) (x 1) (x 1 + shift))))
    (out : Fin M.outputDim) (H : Finset (ZMod N)) (hH : H.Nonempty)
    (hsize : Real.exp (-a) * N ≤ (H.card : ℝ))
    (f : ZMod N → ℂ) (χ : ZMod N → AddChar (ZMod N) ℂ)
    (hcorr : ∀ h ∈ H, Real.exp (-a) ≤ ‖finiteFourierCoeff
      (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖) :
    ∃ (k : Fin W.outputDim) (l : Fin (E.selectedExpansion out k).count)
      (S : Finset (ZMod N)), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-(a + 2 * u)) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, Real.exp (-(a + 3 * u)) ≤
        ‖𝔼 n : ZMod N, ((E.selectedExpansion out k).test l).normalizedDerivativeRow u f χ h n *
          star (W.eval k (cubicTrilinearInput h.val n.val ((n.val : ℤ) + shift)))‖ := by
  classical
  let I := Σ k : Fin W.outputDim, Fin (E.selectedExpansion out k).count
  let g := fun (h n : ZMod N) => multiplicativeDerivative f h n * star (χ h n)
  let rel := fun (h : ZMod N) (_ : Unit) (c : I) =>
    Real.exp (-(a + 2 * u)) ≤ ‖𝔼 n : ZMod N, g h n *
      star (W.eval c.1 (cubicTrilinearInput h.val n.val ((n.val : ℤ) + shift))) *
      star (((E.selectedExpansion out c.1).test c.2).eval (correlationInput (h.val : ℤ) (n.val : ℤ)))‖
  have hchoice : ∀ h ∈ H, ∀ z : Unit, ∃ c : I, rel h z c := by
    intro h hh _
    have hc : Real.exp (-a) ≤ ‖𝔼 n : ZMod N, g h n *
        star (M.eval out (correlationInput (h.val : ℤ) (n.val : ℤ)))‖ := by
      have heval (n : ZMod N) : M.eval out (correlationInput (h.val : ℤ) (n.val : ℤ)) =
          M.evalCyclic N out (correlationInput h n) := by
        apply congrArg (M.eval out)
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      have heq : (𝔼 n : ZMod N, g h n * star (M.eval out (correlationInput (h.val : ℤ) (n.val : ℤ)))) =
          finiteFourierCoeff (fun n => multiplicativeDerivative f h n *
            star (M.evalCyclic N out (correlationInput h n))) (χ h) := by
        unfold finiteFourierCoeff
        apply Finset.expect_congr rfl
        intro n _
        change (multiplicativeDerivative f h n * star (χ h n)) *
            star (M.eval out (correlationInput (h.val : ℤ) (n.val : ℤ))) =
          (multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) * star (χ h n)
        rw [← heval n]
        ring
      rw [heq]
      exact hcorr h hh
    obtain ⟨k, l, hkl⟩ := E.transfer_sample_correlation Finset.univ
      (fun n : ZMod N => correlationInput (h.val : ℤ) (n.val : ℤ)) out (g h)
      (fun n _ => W.unit_eval _) hc
    exact ⟨⟨k, l⟩, hkl⟩
  have hcount : (Fintype.card I : ℝ) ≤ Real.exp (2 * u) := by
    simp only [I, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      _ ≤ ∑ _k : Fin W.outputDim, Real.exp u :=
        Finset.sum_le_sum (fun k _ => (E.selectedExpansion out k).count_bound)
      _ = (Fintype.card (Fin W.outputDim) : ℝ) * Real.exp u := by simp
      _ ≤ Real.exp u * Real.exp u := mul_le_mul_of_nonneg_right E.right_dimension (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨c, S, hSH, hS, hSsize, hfixed⟩ := exists_large_fixed_choices H hH rel hchoice hcount
  have hSsize' : Real.exp (-(2 * u)) * (H.card : ℝ) ≤ (S.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSsize
  refine ⟨(c ()).1, (c ()).2, S, hSH, hS, ?_, ?_⟩
  · calc
      _ = Real.exp (-(2 * u)) * (Real.exp (-a) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(2 * u)) * (H.card : ℝ) := mul_le_mul_of_nonneg_left hsize (Real.exp_nonneg _)
      _ ≤ _ := hSsize'
  · intro h hh
    let T := (E.selectedExpansion out (c ()).1).test (c ()).2
    have hraw := hfixed h hh ()
    have heq : (𝔼 n : ZMod N, T.normalizedDerivativeRow u f χ h n *
        star (W.eval (c ()).1 (cubicTrilinearInput h.val n.val ((n.val : ℤ) + shift)))) =
        (Real.exp (-u) : ℂ) * (𝔼 n : ZMod N, g h n *
          star (W.eval (c ()).1 (cubicTrilinearInput h.val n.val ((n.val : ℤ) + shift))) *
          star (T.eval (correlationInput (h.val : ℤ) (n.val : ℤ)))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      simp only [Niltest.normalizedDerivativeRow, Niltest.expNormalize_eval, g,
        star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    change Real.exp (-(a + 3 * u)) ≤ ‖𝔼 n : ZMod N, T.normalizedDerivativeRow u f χ h n *
      star (W.eval (c ()).1 (cubicTrilinearInput h.val n.val ((n.val : ℤ) + shift)))‖
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ = Real.exp (-u) * Real.exp (-(a + 2 * u)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hraw (Real.exp_nonneg _)

theorem NativeCubicPointwisePartition.exists_shifted_derivative_anchor
    {p q r m u a b δ β : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
    {M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) m}
    {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
    {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
      Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
    {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
      V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies) (fun _ : Fin 3 => (N : ℝ)) r}
    (P : NativeCubicPointwisePartition R b δ β)
    (E : NativeIntegerVectorEquivalence 2 u M.eval
      (fun out x => W.eval out (cubicTrilinearInput (x 0) (x 1) (x 1 + shift))))
    (out : Fin M.outputDim) (H : Finset (ZMod N)) (hH : H.Nonempty)
    (hsize : Real.exp (-a) * N ≤ (H.card : ℝ))
    (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (χ : ZMod N → AddChar (ZMod N) ℂ)
    (hcorr : ∀ h ∈ H, Real.exp (-a) ≤ ‖finiteFourierCoeff
      (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖)
    (herror : δ + 4 * β ≤ Real.exp (-(2 * a + 5 * u)) / 2) :
    ∃ (k : Fin W.outputDim) (l : Fin (E.selectedExpansion out k).count)
      (cell : Fin 3 → P.partition.I) (S : Finset (ZMod N)), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-(2 * a + 5 * u)) / (4 * Real.exp b) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, Real.exp (-(2 * a + 5 * u)) / (4 * Real.exp b) ≤
        ‖𝔼 n : ZMod N, ((E.selectedExpansion out k).test l).normalizedDerivativeRow u f χ h n *
          star (((P.partition.weight (cell 0) n * P.partition.weight (cell 2) n : ℝ) : ℂ) *
            P.partition.cellVector cell 0 k (cubicDiagonalSample ![h, n]))‖ := by
  classical
  obtain ⟨k, l, H', hH'H, hH', hH'size, hH'corr⟩ :=
    exists_fixed_cubic_shifted_correlation E out H hH hsize f χ hcorr
  let T := (E.selectedExpansion out k).test l
  let row := T.normalizedDerivativeRow u f χ
  have hrow : ∀ h n, ‖row h n‖ ≤ 1 :=
    T.normalizedDerivativeRow_norm ((E.selectedExpansion out k).complexity l) f hf χ
  have hmass : Real.exp (-(2 * a + 5 * u)) ≤ 𝔼 h : ZMod N, if h ∈ H' then
      ‖𝔼 n : ZMod N, row h n * star
        (W.eval k (cubicTrilinearInput h.val n.val ((n.val : ℤ) + shift)))‖ else 0 := by
    have hind : (𝔼 h : ZMod N, if h ∈ H' then Real.exp (-(a + 3 * u)) else 0) =
        (H'.card : ℝ) * Real.exp (-(a + 3 * u)) / N := by
      rw [Fintype.expect_eq_sum_div_card]
      simp only [ZMod.card]
      simp
    calc
      _ = Real.exp (-(a + 2 * u)) * Real.exp (-(a + 3 * u)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ (H'.card : ℝ) * Real.exp (-(a + 3 * u)) / N := by
        apply (le_div_iff₀ (Nat.cast_pos.mpr (NeZero.pos N))).mpr
        nlinarith [mul_le_mul_of_nonneg_right hH'size (Real.exp_nonneg (-(a + 3 * u)))]
      _ = _ := hind.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hH'corr h hh
        · exact le_rfl
  obtain ⟨cell, S, hSH', hS, hSsize, hScorr⟩ :=
    P.exists_correlating_anchor k row H' hrow (Real.exp_pos _) hmass herror
  exact ⟨k, l, cell, S, hSH'.trans hH'H, hS, hSsize, hScorr⟩

end Erdos3

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

theorem exists_cubic_diagonal_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b δ β : ℝ} {N : ℕ} [NeZero N]
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies) (fun _ : Fin 3 => (N : ℝ)) r}
      (P : NativeCubicPointwisePartition R b δ β), 0 ≤ b →
      ∃ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((b + C) ^ C) (G a c))) ∧
        (∀ a c (x : Fin 2 → ZMod N), G a c (fun z => ((x z).val : ℤ)) =
          ∑ cell, (P.partition.cellWeight cell (cubicDiagonalSample x) : ℂ) *
            (P.partition.cellVector cell 0 a (cubicDiagonalSample x) *
              star (P.partition.cellVector cell 1 c (cubicDiagonalSample x)))) ∧
        (∀ a c (x : Fin 2 → ZMod N), ‖G a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (((x 1).val : ℤ) + shift)) *
              star (W.eval c (cubicTrilinearInput (x 1).val (x 0).val (((x 1).val : ℤ) + shift))) -
            G a c (fun z => ((x z).val : ℤ))‖) ≤ 2 * (δ + 4 * β)) := by
  obtain ⟨A, _, hpartition⟩ := exists_positive_partition_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + 3 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r b δ β N _ W i j shift V R P hb
  classical
  let t := b + 3
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hbt : b ≤ t := by dsimp [t]; linarith
  have hσ : (Fintype.card (Fin 3) : ℝ) ≤ t := by norm_num; dsimp [t]; linarith
  let v := fun (cell : Fin 3 → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim)
      (x : Fin 3 → ℤ) =>
    R.cubicPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 0 ac.1 x *
      star (R.cubicPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 1 ac.2 x)
  have hv (cell : Fin 3 → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 t (v cell ac)) :=
    ((P.partition.equivalence cell).mono hbt).expansion ac.1 ac.2
  obtain ⟨F, hF, hFeval⟩ := hpartition ht hσ
    (P.partition.card_bound.trans (Real.exp_le_exp.mpr hbt))
    (fun cell k => P.partition.weight (cell k)) v
    (fun cell k => (P.partition.positive (cell k)).mono (by decide) hbt) hv
  let G := fun (a c : Fin W.outputDim) (x : Fin 2 → ℤ) => F (a, c) (cubicDiagonalSample x)
  have hcost : (t + A) ^ A ≤ (b + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget b hb
  have hexp (a c : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((b + C) ^ C) (G a c)) := by
    let π : Fin 3 → Fin 2 := ![1, 0, 1]
    let f : Fin 3 → ((Fin 2 → ℤ) →+ ℤ) :=
      fun k => ⟨⟨fun x => x (π k), rfl⟩, fun _ _ => rfl⟩
    have he (x : Fin 2 → ℤ) : (fun k => f k x) = cubicDiagonalSample x := by
      funext k
      fin_cases k <;> rfl
    exact ⟨by simpa only [he] using
      (((Classical.choice (hF (a, c))).linearPullbackHom f).mono hcost)⟩
  have heval (a c : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      G a c (fun z => ((x z).val : ℤ)) =
        ∑ cell, (P.partition.cellWeight cell (cubicDiagonalSample x) : ℂ) *
          (P.partition.cellVector cell 0 a (cubicDiagonalSample x) *
            star (P.partition.cellVector cell 1 c (cubicDiagonalSample x))) := by
    have he : cubicDiagonalSample (fun z => ((x z).val : ℤ)) =
        fun k => ((cubicDiagonalSample x k).val : ℤ) := by
      funext k
      fin_cases k <;> rfl
    change F (a, c) (cubicDiagonalSample (fun z => ((x z).val : ℤ))) = _
    rw [he]
    exact hFeval (a, c) (cubicDiagonalSample x)
  refine ⟨G, hexp, heval, ?_, ?_⟩
  · intro a c x
    rw [heval]
    apply norm_positive_partition_sum_le_one
      (fun cell => P.partition.cellWeight cell (cubicDiagonalSample x))
      (fun cell => P.partition.cellVector cell 0 a (cubicDiagonalSample x) *
        star (P.partition.cellVector cell 1 c (cubicDiagonalSample x)))
      (fun cell => P.partition.cellWeight_nonneg cell _) (P.partition.cellWeight_total _)
    intro cell
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (P.partition.cellVector_norm cell 0 a _)).trans (P.partition.cellVector_norm cell 1 c _)
  · intro a c
    simpa only [heval] using P.diagonal_exchange_approximation a c

end Erdos3

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

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}

namespace NativePolynomialOrbitFactors

def HasCubicCorrelatingAnchor (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r) (row : ZMod N → ZMod N → ℂ)
    (H : Finset (ZMod N)) (out : Fin W.outputDim) (b : ℝ) : Prop :=
  ∃ y : Fin 3 → ZMod N, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
    Real.exp (-b) * N ≤ (S.card : ℝ) ∧ ∃ w : ZMod N → ℝ,
      PositiveCyclicNiltest.{0} 1 N b w ∧
      NativeIntegerVectorEquivalence 2 b
        (R.cubicPairAnchoredVector (fun k => ((y k).val : ℤ)) 0)
        (R.cubicPairAnchoredVector (fun k => ((y k).val : ℤ)) 1) ∧
      ∀ h ∈ S, Real.exp (-b) ≤ ‖𝔼 n : ZMod N, row h n *
        star ((w n : ℂ) * R.cubicPairAnchoredVector (fun k => ((y k).val : ℤ))
          0 out ![(n.val : ℤ), (h.val : ℤ), (n.val : ℤ)])‖

theorem hasCubicCorrelatingAnchor_mono {row : ZMod N → ZMod N → ℂ}
    {H : Finset (ZMod N)} {out : Fin W.outputDim} {a b : ℝ}
    (h : R.HasCubicCorrelatingAnchor row H out a) (hab : a ≤ b) :
    R.HasCubicCorrelatingAnchor row H out b := by
  obtain ⟨y, S, hSH, hS, hsize, w, hw, hequiv, hcorr⟩ := h
  have he : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (neg_le_neg hab)
  exact ⟨y, S, hSH, hS, (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)).trans hsize,
    w, hw.mono le_rfl hab, hequiv.mono hab, fun h hh => he.trans (hcorr h hh)⟩

end NativePolynomialOrbitFactors

theorem NativeCubicPairPartition.correlatingAnchor_of_cell {a b ε t : ℝ}
    (P : NativeCubicPairPartition R b ε) (hb : 0 ≤ b) (hbt : b ≤ t)
    (hprod : productNiltestBudget (raisedNiltestBudget b) ≤ t) (hloss : a + b + 4 ≤ t)
    (row : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N)) (out : Fin W.outputDim)
    (cell : Fin 3 → P.I) (S : Finset (ZMod N)) (hSH : S ⊆ H) (hS : S.Nonempty)
    (hsize : Real.exp (-a) / (4 * Real.exp b) * N ≤ (S.card : ℝ))
    (hcorr : ∀ h ∈ S, Real.exp (-a) / (4 * Real.exp b) ≤
      ‖𝔼 n : ZMod N, row h n * star
        (((P.weight (cell 0) n * P.weight (cell 2) n : ℝ) : ℂ) *
          P.cellVector cell 0 out (cubicDiagonalSample ![h, n]))‖) :
    R.HasCubicCorrelatingAnchor row H out t := by
  have hlower : Real.exp (-t) ≤ Real.exp (-a) / (4 * Real.exp b) := by
    have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.exp b)).mpr
    calc
      _ ≤ Real.exp (-t) * (Real.exp 4 * Real.exp b) := by gcongr
      _ = Real.exp (-t + (4 + b)) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have heval (h n : ZMod N) : (fun k => ((cubicDiagonalSample ![h, n] k).val : ℤ)) =
      ![(n.val : ℤ), (h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  refine ⟨P.anchor cell, S, hSH, hS,
    (mul_le_mul_of_nonneg_right hlower (Nat.cast_nonneg N)).trans hsize,
    fun n => P.weight (cell 0) n * P.weight (cell 2) n,
    ((P.positive (cell 0)).mul (P.positive (cell 2)) hb).mono le_rfl hprod,
    (P.equivalence cell).mono hbt, ?_⟩
  intro h hh
  apply hlower.trans
  simpa only [NativeCubicPairPartition.cellVector, heval] using hcorr h hh

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]

def HasCubicVerticalCorrelatingAnchor (row : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N))
    (out : Fin W.outputDim) (b : ℝ) : Prop :=
  ∃ y : Fin 3 → ZMod N, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
    Real.exp (-b) * N ≤ (S.card : ℝ) ∧ ∃ w : ZMod N → ℝ,
      PositiveCyclicNiltest.{0} 1 N b w ∧
      ∃ M : R.FrozenMiddleRealization
          (R.slowValue (fun k => ((y k).val : ℤ)))
          (R.rationalValue (fun k => ((y k).val : ℤ))) b,
        ∃ U : Fin 2 → M.model.UnitVerticalObservable
            (M.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
            (Fin W.outputDim) b,
          (∀ k, (U k).frequency = R.cubicPairMiddleFrequency) ∧
          (∀ k l x, (U k).observable l (QuotientGroup.mk
            (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M.orbit)) =
              R.cubicPairAnchoredVector (fun k => ((y k).val : ℤ)) k l x) ∧
          NativeIntegerVectorEquivalence 2 b
            (R.cubicPairAnchoredVector (fun k => ((y k).val : ℤ)) 0)
            (R.cubicPairAnchoredVector (fun k => ((y k).val : ℤ)) 1) ∧
          ∀ h ∈ S, Real.exp (-b) ≤
            ‖𝔼 n : ZMod N, row h n *
              star ((w n : ℂ) * (U 0).observable out (QuotientGroup.mk
                (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1)
                  ![(n.val : ℤ), (h.val : ℤ), (n.val : ℤ)] M.orbit)))‖

theorem hasCubicVerticalCorrelatingAnchor_mono
    {row : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)} {out : Fin W.outputDim}
    {a b : ℝ} (h : R.HasCubicVerticalCorrelatingAnchor row H out a) (hab : a ≤ b) :
    R.HasCubicVerticalCorrelatingAnchor row H out b := by
  obtain ⟨y, S, hSH, hS, hsize, w, hw, M, U, hfreq, heval, hequiv, hcorr⟩ := h
  have he : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (neg_le_neg hab)
  exact ⟨y, S, hSH, hS, (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)).trans hsize,
    w, hw.mono le_rfl hab, M.mono hab, fun k => (U k).mono hab, hfreq, heval,
    hequiv.mono hab, fun h hh => he.trans (hcorr h hh)⟩

end NativePolynomialOrbitFactors

theorem exists_cubic_correlating_vertical_pair :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ]
        (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ]
        (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ]
        (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [T2Space (ℝ ⊗[ℚ]
        (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)],
      0 ≤ r → 0 ≤ b → R.HasCubicPairFrozenReduction b →
      ∀ (row : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N)) (out : Fin W.outputDim),
        R.HasCubicCorrelatingAnchor row H out b →
        R.HasCubicVerticalCorrelatingAnchor row H out ((p + q + r + b + C) ^ C) := by
  obtain ⟨A, _, hmodel⟩ := exists_cubic_pair_middle_model
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let D := (X + Polynomial.C A) ^ A
  let P := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + D + (P + D + 4 + (X + D + 2) ^ 4))
  refine ⟨C, hC, ?_⟩
  intro p q r b W N _ i j shift V R _ _ _ _ _ _ _ _ hr hb hred row H out hanchor
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + b
  let B₀ := 4 * (v + 1) + raisedNiltestBudget v + 6
  let d := (v + A) ^ A
  let z := productNiltestBudget B₀ + d + 4 + (v + d + 2) ^ 4
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hB : 0 ≤ B₀ := by dsimp [B₀, raisedNiltestBudget]; positivity
  have hz : 0 ≤ z := by
    dsimp [z]
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hsum : v + d + z ≤ (p + q + r + b + C) ^ C := by
    simpa [X, B, D, P, v, B₀, d, z, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have hbC : b ≤ (p + q + r + b + C) ^ C := by dsimp [v] at hsum; linarith
  have hdC : d ≤ (p + q + r + b + C) ^ C := by linarith
  have hzC : z ≤ (p + q + r + b + C) ^ C := by linarith
  obtain ⟨u, hu, hub, houter, _hfreeze⟩ := hred
  obtain ⟨y, S, hSH, hS, hdensity, w, hw, hequiv, hcorr⟩ := hanchor
  have hy : ∀ k : Fin 3, |(((y k).val : ℤ) : ℝ)| ≤ (N : ℝ) := by
    intro k
    change |((y k).val : ℝ)| ≤ (N : ℝ)
    rw [abs_of_nonneg (Nat.cast_nonneg ((y k).val))]
    exact Nat.cast_le.mpr (y k).val_lt.le
  obtain ⟨M, _hMc, _hMe⟩ := hmodel R hr hu houter (fun k => ((y k).val : ℤ)) hy
  let c := (p + q + r + u + A) ^ A
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcd : c ≤ d := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hpv : p ≤ v := by dsimp [v]; linarith
  have hpair : cubicPairBudget p q ≤ B₀ := by
    dsimp [cubicPairBudget, B₀, raisedNiltestBudget]
    gcongr
  have hpair0 : 0 ≤ cubicPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le
  have hprod : productNiltestBudget (cubicPairBudget p q) ≤ productNiltestBudget B₀ := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have hvcost : cubicPairMiddleVerticalBudget p q c ≤ z := by
    dsimp [cubicPairMiddleVerticalBudget, z]
    gcongr
  let M' := M.mono (hcd.trans hdC)
  let U : Fin 2 → M'.model.UnitVerticalObservable
      (M'.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
      (Fin W.outputDim) ((p + q + r + b + C) ^ C) :=
    fun k => (M.cubicPairMiddleVertical hc k).mono (hvcost.trans hzC)
  have heval (k l x) : (U k).observable l (QuotientGroup.mk
      (M'.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M'.orbit)) =
      R.cubicPairAnchoredVector (fun k => ((y k).val : ℤ)) k l x :=
    M.cubicPairMiddleVertical_eval hc k l x
  have hexp : Real.exp (-((p + q + r + b + C) ^ C)) ≤ Real.exp (-b) :=
    Real.exp_le_exp.mpr (neg_le_neg hbC)
  refine ⟨y, S, hSH, hS, (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg N)).trans hdensity,
    w, hw.mono le_rfl hbC, M', U, fun _ => rfl, heval, hequiv.mono hbC, ?_⟩
  intro h hh
  apply hexp.trans
  simpa only [heval] using hcorr h hh

end Erdos3

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
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_cubic_derivative_anchor :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r m a u b c t : ℝ} {N : ℕ} [NeZero N]
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) m}
      {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies) (fun _ : Fin 3 => (N : ℝ)) r)
      (E : NativeIntegerVectorEquivalence 2 u M.eval
        (fun out x => W.eval out (cubicTrilinearInput (x 0) (x 1) (x 1 + shift)))),
      R.HasCubicPairLocalApproximation b → R.HasCubicPairFrozenReduction c →
      0 ≤ t → a ≤ t → u ≤ t → b ≤ t → c ≤ t → Real.exp ((t + C) ^ C) ≤ (N : ℝ) →
      ∀ (f : ZMod N → ℂ) (χ : ZMod N → AddChar (ZMod N) ℂ)
        (H : Finset (ZMod N)) (out : Fin M.outputDim),
        (∀ n, ‖f n‖ ≤ 1) → H.Nonempty → Real.exp (-a) * N ≤ (H.card : ℝ) →
        (∀ h ∈ H, Real.exp (-a) ≤ ‖finiteFourierCoeff
          (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖) →
        ∃ (k : Fin W.outputDim) (l : Fin (E.selectedExpansion out k).count),
          R.HasCubicCorrelatingAnchor (((E.selectedExpansion out k).test l).normalizedDerivativeRow u f χ)
            H k ((t + C) ^ C) := by
  obtain ⟨A, _, hpartition⟩ := exists_cubic_diagonal_partition
  let X : Polynomial ℕ := Polynomial.X
  let D := (8 * X + 1 + Polynomial.C A) ^ A
  let B := D + (D + 2) ^ 2 + 3
  let Q := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (D + Q + 7 * X + 4)
  refine ⟨C, hC, ?_⟩
  intro p q r m a u b c t N _ W M i j shift V R E hlocal hred ht hat hut hbt hct hN
    f χ H out hf hH hsize hcorr
  let d := (8 * t + 1 + A) ^ A
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hQ : 0 ≤ productNiltestBudget (raisedNiltestBudget d) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have htotal : d + productNiltestBudget (raisedNiltestBudget d) + 7 * t + 4 ≤ (t + C) ^ C := by
    simpa [X, D, B, Q, d, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget t ht
  have hdC : d ≤ (t + C) ^ C := by linarith
  have hprod : productNiltestBudget (raisedNiltestBudget d) ≤ (t + C) ^ C := by linarith
  have hsum : 2 * a + 5 * u + d + 4 ≤ (t + C) ^ C := by linarith
  have heq : t + (7 * t + 1) + (A : ℝ) = 8 * t + 1 + A := by ring
  obtain ⟨δ, β, P, herror⟩ := hpartition R hlocal hred ht
    (by linarith : 0 ≤ 7 * t + 1) hbt hct
    (by simpa only [heq] using (Real.exp_le_exp.mpr hdC).trans hN)
  have hP : NativeCubicPointwisePartition R d δ β := by simpa only [heq] using P
  have herr : δ + 4 * β ≤ Real.exp (-(2 * a + 5 * u)) / 2 := by
    apply herror.trans
    apply (Real.exp_le_exp.mpr (show -(7 * t + 1) ≤ -(2 * a + 5 * u) - 1 by linarith)).trans
    exact exp_sub_one_le_half_exp _
  obtain ⟨k, l, cell, S, hSH, hS, hSsize, hScorr⟩ :=
    hP.exists_shifted_derivative_anchor E out H hH hsize f hf χ hcorr herr
  exact ⟨k, l, hP.partition.correlatingAnchor_of_cell hd hdC hprod hsum
    _ H k cell S hSH hS hSsize hScorr⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_cubic_derivative_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) q,
        ∃ W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q,
          W.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              W.eval k x) ∧
          NativeIntegerVectorEquivalence 2 q
            M.eval (fun k x => W.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 q M.cubicMixedDerivative W.cubicTrilinearTriple ∧
          ∃ out : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-q) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i j : Fin W.outputDim × Fin W.outputDim),
              ∃ V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
                Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
                (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val
                  (((z 0).val : ℤ) + -(if branch then (N : ℤ) else 0))),
                ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
                ∃ R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
                  V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
                  (fun _ : Fin 3 => (N : ℝ)) r,
                  R.HasCubicPairFrozenReduction ((p + C) ^ C) ∧
                  ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
                  ∃ E : NativeIntegerVectorEquivalence 2 u M.eval
                    (fun k x => W.eval k (cubicTrilinearInput (x 0) (x 1)
                      (x 1 + -(if branch then (N : ℤ) else 0)))),
                    ∃ (k : Fin W.outputDim) (l : Fin (E.selectedExpansion out k).count),
                      R.HasCubicCorrelatingAnchor
                        (((E.selectedExpansion out k).test l).normalizedDerivativeRow u f χ)
                        H k ((p + C) ^ C) := by
  obtain ⟨A, _, hmodel⟩ := exists_cubic_pair_factored_model
  obtain ⟨B, _, hshift⟩ := NativeMultidegreeNilcharacter.exists_cubic_mixed_shifted_equivalence
  obtain ⟨D, _, hlocal⟩ := exists_cubic_pair_local_approximation
  obtain ⟨F, _, hfrozen⟩ := exists_cubic_pair_frozen_reduction
  obtain ⟨G, _, hanchor⟩ := exists_cubic_derivative_anchor
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let U := (2 * Q + Polynomial.C B) ^ B
  let L := (3 * Q + Polynomial.C D) ^ D
  let J := (3 * Q + Polynomial.C F) ^ F
  let T := Q + U + L + J
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C G) ^ G)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let r := (p + A) ^ A
  let u := (2 * r + B) ^ B
  let b := (3 * r + D) ^ D
  let c := (3 * r + F) ^ F
  let t := r + u + b + c
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htotal : t + (t + G) ^ G ≤ (p + C) ^ C := by
    simpa [X, Q, U, L, J, T, t, r, u, b, c, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hrC : r ≤ (p + C) ^ C := (by dsimp [t] at htC; linarith)
  have huC : u ≤ (p + C) ^ C := (by dsimp [t] at htC; linarith)
  have hcC : c ≤ (p + C) ^ C := (by dsimp [t] at htC; linarith)
  have hcost : (t + G) ^ G ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans htotal
  obtain ⟨q, hq, hqr, H, hH, hHdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, branch, i, j, V, ⟨R⟩⟩ :=
    hmodel hp ((Real.exp_le_exp.mpr hrC).trans hN) f hf hGowers
  have hqr' : q ≤ r := hqr
  have hshiftcost : (q + q + B) ^ B ≤ u := by
    change (q + q + B) ^ B ≤ (2 * r + B) ^ B
    apply pow_le_pow_left₀ (by positivity)
    linarith
  let E := (hshift M W hq hdiag (-(if branch then (N : ℤ) else 0))).mono hshiftcost
  have hlocalcost : (q + q + r + D) ^ D ≤ b := by
    change (q + q + r + D) ^ D ≤ (3 * r + D) ^ D
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hfrozencost : (q + q + r + F) ^ F ≤ c := by
    change (q + q + r + F) ^ F ≤ (3 * r + F) ^ F
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hlocal' := R.hasCubicPairLocalApproximation_mono (hlocal R hr) hlocalcost
  have hfrozen' := R.hasCubicPairFrozenReduction_mono (hfrozen R hr) hfrozencost
  obtain ⟨k, l, hkl⟩ := hanchor R E hlocal' hfrozen' ht
    (by dsimp [t]; linarith : q ≤ t) (by dsimp [t]; linarith : u ≤ t)
    (by dsimp [t]; linarith : b ≤ t) (by dsimp [t]; linarith : c ≤ t)
    ((Real.exp_le_exp.mpr hcost).trans hN) f χ H out hf hH hHdense hcorr
  exact ⟨q, hq, hqr'.trans hrC, H, hH, hHdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, branch, i, j, V, r, hr, hrC, R,
    R.hasCubicPairFrozenReduction_mono hfrozen' hcC, u, hu, huC, E, k, l,
    R.hasCubicCorrelatingAnchor_mono hkl hcost⟩

theorem exists_cubic_vertical_derivative_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) q,
        ∃ W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q,
          W.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              W.eval k x) ∧
          NativeIntegerVectorEquivalence 2 q
            M.eval (fun k x => W.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 q M.cubicMixedDerivative W.cubicTrilinearTriple ∧
          ∃ out : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-q) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i j : Fin W.outputDim × Fin W.outputDim),
              ∃ V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
                Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
                (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val
                  (((z 0).val : ℤ) + -(if branch then (N : ℤ) else 0))),
                ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
                ∃ R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
                  V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
                  (fun _ : Fin 3 => (N : ℝ)) r,
                  R.HasCubicPairFrozenReduction ((p + C) ^ C) ∧
                  ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
                  ∃ E : NativeIntegerVectorEquivalence 2 u M.eval
                    (fun k x => W.eval k (cubicTrilinearInput (x 0) (x 1)
                      (x 1 + -(if branch then (N : ℤ) else 0)))),
                    ∃ (k : Fin W.outputDim) (l : Fin (E.selectedExpansion out k).count),
                      R.HasCubicCorrelatingAnchor
                        (((E.selectedExpansion out k).test l).normalizedDerivativeRow u f χ)
                        H k ((p + C) ^ C) ∧
                      ∀ [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
                        [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
                        [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
                        [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
                        [TopologicalSpace (ℝ ⊗[ℚ]
                          (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
                        [IsTopologicalAddGroup (ℝ ⊗[ℚ]
                          (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
                        [ContinuousSMul ℝ (ℝ ⊗[ℚ]
                          (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
                        [T2Space (ℝ ⊗[ℚ]
                          (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)],
                        R.HasCubicVerticalCorrelatingAnchor
                          (((E.selectedExpansion out k).test l).normalizedDerivativeRow u f χ)
                          H k ((p + C) ^ C) := by
  obtain ⟨A, _, hmodel⟩ := exists_cubic_derivative_model
  obtain ⟨B, _, hvertical⟩ := exists_cubic_correlating_vertical_pair
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (4 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htotal : t + (4 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hBC : (4 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans htotal
  obtain ⟨q, hq, hqt, H, hH, hHdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, branch, i, j, V, r, hr, hrt, R, hred, u, hu, hut, E, k, l, hanchor⟩ :=
    hmodel hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hGowers
  have hcost : (q + q + r + t + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    change q + q + r + t + B ≤ 4 * t + B
    linarith
  refine ⟨q, hq, hqt.trans htC, H, hH, hHdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, branch, i, j, V, r, hr, hrt.trans htC, R,
    R.hasCubicPairFrozenReduction_mono hred htC, u, hu, hut.trans htC, E, k, l,
    R.hasCubicCorrelatingAnchor_mono hanchor htC, ?_⟩
  intro _ _ _ _ _ _ _ _
  have h := hvertical R hr ht hred
    (((E.selectedExpansion out k).test l).normalizedDerivativeRow u f χ) H k hanchor
  exact R.hasCubicVerticalCorrelatingAnchor_mono h hcost

end Erdos3

end

end OAI
