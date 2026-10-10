import OAI.Combinatorics.Progressions.Linear.MixedPairPartitionKernel

namespace OAI

universe u

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
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}

structure NativeQuarticPointwisePartition
    (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
      V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
      (fun _ : Fin 4 => (N : ℝ)) r) (b δ β : ℝ) where
  partition : NativeQuarticPairPartition R b (δ + 8 * β)
  error_nonneg : 0 ≤ δ
  density_nonneg : 0 ≤ β
  bad : Finset (ZMod N)
  bad_density : (bad.card : ℝ) / N ≤ β
  pointwise : ∀ a x, (∀ l, x l ∉ bad) → 0 < partition.cellWeight a x →
    ∀ (k : Fin 2) (out : Fin W.outputDim),
      ‖W.eval out (quarticInput ((x (![0, 1] k)).val : ℤ) ![((x (![1, 0] k)).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)]) - partition.cellVector a k out x‖ ≤ δ

namespace NativeQuarticPointwisePartition

attribute [local instance] NativeQuarticPairPartition.finite

variable {b δ β : ℝ} (P : NativeQuarticPointwisePartition R b δ β)

noncomputable def mono {b' δ' β' : ℝ} (hb : b ≤ b') (hδ : δ ≤ δ') (hβ : β ≤ β') :
    NativeQuarticPointwisePartition R b' δ' β' where
  partition := P.partition.mono hb (by linarith)
  error_nonneg := P.error_nonneg.trans hδ
  density_nonneg := P.density_nonneg.trans hβ
  bad := P.bad
  bad_density := P.bad_density.trans hβ
  pointwise := fun a x hx hax k out => (P.pointwise a x hx hax k out).trans hδ

theorem sampled_error {X : Type*} [Fintype X] [Nonempty X]
    (sample : X → Fin 4 → ZMod N) (E : Finset X)
    (hE : ∀ x, x ∉ E → ∀ l, sample x l ∉ P.bad) (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x, ∑ a, P.partition.cellWeight a (sample x) *
      ‖W.eval out (quarticInput ((sample x (![0, 1] k)).val : ℤ) ![((sample x (![1, 0] k)).val : ℤ), ((sample x 2).val : ℤ), ((sample x 3).val : ℤ)]) - P.partition.cellVector a k out (sample x)‖) ≤
      δ + 2 * (E.card : ℝ) / Fintype.card X := by
  exact weighted_partition_mean_error E
    (fun a x => P.partition.cellWeight a (sample x))
    (fun a x => P.partition.cellVector a k out (sample x)) _ P.error_nonneg
    (fun a x => P.partition.cellWeight_nonneg a (sample x))
    (fun x => P.partition.cellWeight_total (sample x))
    (fun a x => P.partition.cellVector_norm a k out (sample x))
    (fun x => W.norm_eval out _) (fun a x hx hax => P.pointwise a (sample x) (hE x hx) hax k out)

theorem sampled_approximation {X : Type*} [Fintype X] [Nonempty X]
    (sample : X → Fin 4 → ZMod N) (E : Finset X)
    (hE : ∀ x, x ∉ E → ∀ l, sample x l ∉ P.bad) (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x, ‖W.eval out (quarticInput ((sample x (![0, 1] k)).val : ℤ) ![((sample x (![1, 0] k)).val : ℤ), ((sample x 2).val : ℤ), ((sample x 3).val : ℤ)]) -
      ∑ a, (P.partition.cellWeight a (sample x) : ℂ) * P.partition.cellVector a k out (sample x)‖) ≤
      δ + 2 * (E.card : ℝ) / Fintype.card X := by
  apply le_trans _ (P.sampled_error sample E hE k out)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (sample x))
    (fun a => P.partition.cellVector a k out (sample x)) _
    (fun a => P.partition.cellWeight_nonneg a (sample x)) (P.partition.cellWeight_total (sample x)))

end NativeQuarticPointwisePartition
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
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)

theorem select_quartic_pointwise_partition {b c : ℝ}
    (hlocal : R.HasQuarticPairLocalApproximation b) (hred : R.HasQuarticPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin 4 → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin 4 → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence 3 c
            (R.quarticPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.quarticPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ a x, (∀ l, x l ∉ B) → 0 < A a x →
            ∀ (k : Fin 2) (out : Fin W.outputDim),
              ‖W.eval out (quarticInput ((x (![0, 1] k)).val : ℤ) ![((x (![1, 0] k)).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)]) -
                R.quarticPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
                  (fun l => ((x l).val : ℤ))‖ ≤ Real.exp b * ρ := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin 4 → ZMod N) (i : Fin 4) => ((x i).val : ℤ)
  have hv (x : Fin 4 → ZMod N) (i : Fin 4) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin 4 → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.quarticPairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro a x hx hax k out
  obtain ⟨hy', hAy⟩ := hy a x hx hax
  obtain ⟨hres, hnear⟩ := hcells a x (y a) hx hy' hax hAy
  exact hmodel (v (y a)) (hv (y a)) k out (v x) ρ hρ (hv x) hres
    (by simpa only [v, Int.cast_natCast] using hnear)

end NativePolynomialOrbitFactors

theorem exists_quartic_pointwise_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r),
      R.HasQuarticPairLocalApproximation b → R.HasQuarticPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      Nonempty (NativeQuarticPointwisePartition R ((t + C) ^ C)
        (Real.exp t * ρ) (6 * ρ + 3 / N)) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 60 + 4 * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t W N _ i j V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_quartic_pointwise_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨n, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 60 + 4 * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have htC : t ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have hfour : 4 * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  let w := productPartitionWeight (fun _ : Fin 4 => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin 4 => A) i j x :=
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
  have hcard' : (Fintype.card (Fin 4 → Fin n × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 4
      _ = Real.exp (4 * (t + B) ^ B) := (Real.exp_nat_mul _ 4).symm
      _ ≤ _ := Real.exp_le_exp.mpr hfour
  have hpoint' (a) (x) (hx : ∀ l, x l ∉ E) (hax : 0 < w a x) (k : Fin 2) (out : Fin W.outputDim) :
      ‖W.eval out (quarticInput ((x (![0, 1] k)).val : ℤ) ![((x (![1, 0] k)).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)]) - R.quarticPairAnchoredVector
        (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖ ≤ δ :=
    (hpoint a x hx hax k out).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbt) hρ.le)
  have herr (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin 4 → ZMod N, ∑ a, w a x *
        ‖W.eval out (quarticInput ((x (![0, 1] k)).val : ℤ) ![((x (![1, 0] k)).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)]) - R.quarticPairAnchoredVector
          (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖) ≤ δ + 8 * β := by
    have h := weighted_partition_mean_error (coordinateExceptional E) w
      (fun a x => R.quarticPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
        (fun l => ((x l).val : ℤ))) _ hδ hw hwSum
      (fun a x => R.quarticPairAnchoredVector_norm _ _ _ _)
      (fun x => W.norm_eval out _) (fun a x hx hax =>
        hpoint' a x ((not_mem_coordinateExceptional E x).mp hx) hax k out)
    have hd : ((coordinateExceptional (ι := Fin 4) E).card : ℝ) / Fintype.card (Fin 4 → ZMod N) ≤
        4 * ((E.card : ℝ) / N) := by
      simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] using
        coordinateExceptional_density_le (ι := Fin 4) E
    rw [mul_div_assoc] at h
    linarith
  let core : NativeQuarticPairPartition R ((t + C) ^ C) (δ + 8 * β) := {
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

def quarticDiagonalSample {X : Type*} (x : Fin 2 → X) : Fin 4 → X := ![x 0, x 1, x 1, x 1]

theorem quarticDiagonalSample_avoids {X : Type*} (B : Set X) (x : Fin 2 → X)
    (hx : ∀ k, x k ∉ B) : ∀ l, quarticDiagonalSample x l ∉ B := by
  intro l
  fin_cases l
  · exact hx 0
  · exact hx 1
  · exact hx 1
  · exact hx 1

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}

namespace NativeQuarticPointwisePartition

attribute [local instance] NativeQuarticPairPartition.finite

variable {b δ β : ℝ} (P : NativeQuarticPointwisePartition R b δ β)

theorem weighted_diagonal_error (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (quarticDiagonalSample x) *
      ‖W.eval out (quarticInput ((x 0).val : ℤ) ![((x 1).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)]) -
        P.partition.cellVector a 0 out (quarticDiagonalSample x)‖) ≤ δ + 4 * β := by
  let E := coordinateExceptional (ι := Fin 2) P.bad
  have h := P.sampled_error quarticDiagonalSample E (fun x hx =>
    quarticDiagonalSample_avoids (P.bad : Set (ZMod N)) x ((not_mem_coordinateExceptional P.bad x).mp hx)) 0 out
  have hd : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * β := by
    have hD := coordinateExceptional_density_le (ι := Fin 2) P.bad
    simp only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] at hD
    exact hD.trans (mul_le_mul_of_nonneg_left P.bad_density (by norm_num))
  change (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (quarticDiagonalSample x) *
      ‖W.eval out (quarticInput ((x 0).val : ℤ) ![((x 1).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)]) -
        P.partition.cellVector a 0 out (quarticDiagonalSample x)‖) ≤
    δ + 2 * (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) at h
  rw [mul_div_assoc] at h
  linarith

theorem diagonal_approximation (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out (quarticInput ((x 0).val : ℤ) ![((x 1).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)]) -
        ∑ a, (P.partition.cellWeight a (quarticDiagonalSample x) : ℂ) *
          P.partition.cellVector a 0 out (quarticDiagonalSample x)‖) ≤ δ + 4 * β := by
  apply le_trans _ (P.weighted_diagonal_error out)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (quarticDiagonalSample x))
    (fun a => P.partition.cellVector a 0 out (quarticDiagonalSample x)) _
    (fun a => P.partition.cellWeight_nonneg a (quarticDiagonalSample x))
    (P.partition.cellWeight_total (quarticDiagonalSample x)))

end NativeQuarticPointwisePartition

theorem exists_quartic_diagonal_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r),
      R.HasQuarticPairLocalApproximation b → R.HasQuarticPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      ∃ δ β : ℝ, ∃ _P : NativeQuarticPointwisePartition R ((t + e + C) ^ C) δ β,
        δ + 4 * β ≤ Real.exp (-e) := by
  obtain ⟨A, _, hpartition⟩ := exists_quartic_pointwise_partition 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e W N _ i j V R hlocal hred ht he hbt hct hN
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
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}

attribute [local instance] NativeQuarticPairPartition.finite

theorem NativeQuarticPointwisePartition.exists_correlating_anchor {b δ β η : ℝ}
    (P : NativeQuarticPointwisePartition R b δ β) (out : Fin W.outputDim)
    (f : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N))
    (hf : ∀ h n, ‖f h n‖ ≤ 1) (hη : 0 < η)
    (hmass : η ≤ 𝔼 h : ZMod N, if h ∈ H then
      ‖𝔼 n : ZMod N, f h n * star
        (W.eval out (quarticInput h.val ![(n.val : ℤ), (n.val : ℤ), (n.val : ℤ)]))‖ else 0)
    (herror : δ + 4 * β ≤ η / 2) :
    ∃ a : Fin 4 → P.partition.I, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
      η / (4 * Real.exp b) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, η / (4 * Real.exp b) ≤ ‖𝔼 n : ZMod N, f h n * star
        (((P.partition.weight (a 1) n * P.partition.weight (a 2) n * P.partition.weight (a 3) n : ℝ) : ℂ) *
          P.partition.cellVector a 0 out (quarticDiagonalSample ![h, n]))‖ := by
  classical
  let C := fun (a : Fin 4 → P.partition.I) (h n : ZMod N) =>
    P.partition.cellVector a 0 out (quarticDiagonalSample ![h, n])
  let v := fun (a : Fin 4 → P.partition.I) (h n : ZMod N) =>
    (P.partition.cellWeight a (quarticDiagonalSample ![h, n]) : ℂ) * C a h n
  have hw (i : P.partition.I) (n : ZMod N) : ‖(P.partition.weight i n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((P.partition.positive i).unit_interval n).1]
    exact ((P.partition.positive i).unit_interval n).2
  have hv (a : Fin 4 → P.partition.I) (h n : ZMod N) : ‖v a h n‖ ≤ 1 := by
    have hweight : ‖(P.partition.cellWeight a (quarticDiagonalSample ![h, n]) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (P.partition.cellWeight_nonneg _ _)]
      exact Finset.prod_le_one₀ (fun l _ => ((P.partition.positive (a l)).unit_interval _).1)
        (fun l _ => ((P.partition.positive (a l)).unit_interval _).2)
    exact (norm_mul _ _).trans_le
      ((mul_le_of_le_one_left (norm_nonneg _) hweight).trans
        (P.partition.cellVector_norm _ _ _ _))
  have herr : (𝔼 h : ZMod N, 𝔼 n : ZMod N,
      ‖W.eval out (quarticInput h.val ![(n.val : ℤ), (n.val : ℤ), (n.val : ℤ)]) - ∑ a, v a h n‖) ≤ η / 2 := by
    have h := (P.diagonal_approximation out).trans herror
    rw [expect_fin_two] at h
    exact h
  obtain ⟨a, S, hSH, hS, hsize, hcorr⟩ := exists_dense_row_partition_correlation H f
    (fun h n => W.eval out (quarticInput h.val ![(n.val : ℤ), (n.val : ℤ), (n.val : ℤ)]))
    v hη (Real.exp_pos b) P.partition.card_bound hf hv hmass herr
  refine ⟨a, S, hSH, hS, by simpa only [ZMod.card] using hsize, ?_⟩
  intro h hh
  have hrow : (𝔼 n : ZMod N, f h n * star (v a h n)) =
      (P.partition.weight (a 0) h : ℂ) * (𝔼 n : ZMod N, f h n * star
        (((P.partition.weight (a 1) n * P.partition.weight (a 2) n * P.partition.weight (a 3) n : ℝ) : ℂ) * C a h n)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    have h0 : quarticDiagonalSample ![h, n] 0 = h := rfl
    have h1 : quarticDiagonalSample ![h, n] 1 = n := rfl
    have h2 : quarticDiagonalSample ![h, n] 2 = n := rfl
    have h3 : quarticDiagonalSample ![h, n] 3 = n := rfl
    simp only [v, NativeQuarticPairPartition.cellWeight, Fin.prod_univ_four,
      h0, h1, h2, h3, Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
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
  NativeQuarticPairPartition.finite

namespace NativeQuarticPointwisePartition

variable {p q r b δ β : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}
  (P : NativeQuarticPointwisePartition R b δ β)

theorem weighted_diagonal_error_side (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (quarticDiagonalSample x) *
      ‖W.eval out (quarticInput ((x k).val : ℤ) ![((x k.rev).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)]) - P.partition.cellVector a k out (quarticDiagonalSample x)‖) ≤
      δ + 4 * β := by
  let E := coordinateExceptional (ι := Fin 2) P.bad
  have h := P.sampled_error quarticDiagonalSample E (fun x hx =>
    quarticDiagonalSample_avoids (P.bad : Set (ZMod N)) x ((not_mem_coordinateExceptional P.bad x).mp hx)) k out
  have hd : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * β := by
    have hD := coordinateExceptional_density_le (ι := Fin 2) P.bad
    simp only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] at hD
    exact hD.trans (mul_le_mul_of_nonneg_left P.bad_density (by norm_num))
  have hsample (x : Fin 2 → ZMod N) :
      quarticInput ((quarticDiagonalSample x (![0, 1] k)).val : ℤ)
        ![((quarticDiagonalSample x (![1, 0] k)).val : ℤ),
          ((quarticDiagonalSample x 2).val : ℤ), ((quarticDiagonalSample x 3).val : ℤ)] =
      quarticInput ((x k).val : ℤ) ![((x k.rev).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)] := by
    fin_cases k <;> rfl
  simp only [hsample] at h
  rw [mul_div_assoc] at h
  linarith

theorem weighted_diagonal_exchange_error (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (quarticDiagonalSample x) *
      ‖W.eval out₀ (quarticInput ((x 0).val : ℤ) ![((x 1).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)]) *
          star (W.eval out₁ (quarticInput ((x 1).val : ℤ) ![((x 0).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)])) -
        P.partition.cellVector a 0 out₀ (quarticDiagonalSample x) *
          star (P.partition.cellVector a 1 out₁ (quarticDiagonalSample x))‖) ≤ 2 * (δ + 4 * β) := by
  let err := fun (k : Fin 2) (out : Fin W.outputDim) (a : Fin 4 → P.partition.I)
      (x : Fin 2 → ZMod N) =>
    ‖W.eval out (quarticInput ((x k).val : ℤ) ![((x k.rev).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)]) -
      P.partition.cellVector a k out (quarticDiagonalSample x)‖
  have hbound (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (quarticDiagonalSample x) * err k out a x) ≤
        δ + 4 * β := P.weighted_diagonal_error_side k out
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (quarticDiagonalSample x) *
        (err 0 out₀ a x + err 1 out₁ a x) := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (P.partition.cellWeight_nonneg _ _)
      exact norm_mul_star_sub_mul_star_le_of_le_one (W.norm_eval out₁ _)
        (P.partition.cellVector_norm a 0 out₀ _)
    _ = (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (quarticDiagonalSample x) * err 0 out₀ a x) +
        (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (quarticDiagonalSample x) * err 1 out₁ a x) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.expect_add_distrib]
    _ ≤ _ := by linarith [hbound 0 out₀, hbound 1 out₁]

theorem diagonal_exchange_approximation (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out₀ (quarticInput ((x 0).val : ℤ) ![((x 1).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)]) *
          star (W.eval out₁ (quarticInput ((x 1).val : ℤ) ![((x 0).val : ℤ), ((x 1).val : ℤ), ((x 1).val : ℤ)])) -
        ∑ a, (P.partition.cellWeight a (quarticDiagonalSample x) : ℂ) *
          (P.partition.cellVector a 0 out₀ (quarticDiagonalSample x) *
            star (P.partition.cellVector a 1 out₁ (quarticDiagonalSample x)))‖) ≤ 2 * (δ + 4 * β) := by
  apply le_trans _ (P.weighted_diagonal_exchange_error out₀ out₁)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (quarticDiagonalSample x))
    (fun a => P.partition.cellVector a 0 out₀ (quarticDiagonalSample x) *
      star (P.partition.cellVector a 1 out₁ (quarticDiagonalSample x))) _
    (fun a => P.partition.cellWeight_nonneg a _) (P.partition.cellWeight_total _))

end NativeQuarticPointwisePartition
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
  NativeQuarticPairPartition.finite

namespace NativeQuarticPointwisePartition

variable {p q r b δ β : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}
  (P : NativeQuarticPointwisePartition R b δ β)

theorem weighted_two_variable_error (π : Fin 4 → Fin 2)
    (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
      ‖W.eval out (quarticInput ((x (π (![0, 1] k))).val : ℤ)
          ![((x (π (![1, 0] k))).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)]) -
        P.partition.cellVector a k out (fun l => x (π l))‖) ≤ δ + 4 * β := by
  let E := coordinateExceptional (ι := Fin 2) P.bad
  have h := P.sampled_error (fun x l => x (π l)) E
    (fun x hx l => (not_mem_coordinateExceptional P.bad x).mp hx (π l)) k out
  have hd : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * β := by
    have hD := coordinateExceptional_density_le (ι := Fin 2) P.bad
    simp only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] at hD
    exact hD.trans (mul_le_mul_of_nonneg_left P.bad_density (by norm_num))
  rw [mul_div_assoc] at h
  linarith

theorem weighted_two_variable_exchange_error (π : Fin 4 → Fin 2) (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
      ‖W.eval out₀ (quarticInput ((x (π 0)).val : ℤ) ![((x (π 1)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)]) *
          star (W.eval out₁ (quarticInput ((x (π 1)).val : ℤ) ![((x (π 0)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)])) -
        P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
          star (P.partition.cellVector a 1 out₁ (fun l => x (π l)))‖) ≤ 2 * (δ + 4 * β) := by
  let err := fun (k : Fin 2) (out : Fin W.outputDim) (a : Fin 4 → P.partition.I)
      (x : Fin 2 → ZMod N) =>
    ‖W.eval out (quarticInput ((x (π (![0, 1] k))).val : ℤ) ![((x (π (![1, 0] k))).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)]) -
      P.partition.cellVector a k out (fun l => x (π l))‖
  have hbound (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err k out a x) ≤
        δ + 4 * β := P.weighted_two_variable_error π k out
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
        (err 0 out₀ a x + err 1 out₁ a x) := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (P.partition.cellWeight_nonneg _ _)
      exact norm_mul_star_sub_mul_star_le_of_le_one (W.norm_eval out₁ _)
        (P.partition.cellVector_norm a 0 out₀ _)
    _ = (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err 0 out₀ a x) +
        (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err 1 out₁ a x) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.expect_add_distrib]
    _ ≤ _ := by linarith [hbound 0 out₀, hbound 1 out₁]

theorem two_variable_exchange_approximation (π : Fin 4 → Fin 2) (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out₀ (quarticInput ((x (π 0)).val : ℤ) ![((x (π 1)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)]) *
          star (W.eval out₁ (quarticInput ((x (π 1)).val : ℤ) ![((x (π 0)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)])) -
        ∑ a, (P.partition.cellWeight a (fun l => x (π l)) : ℂ) *
          (P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
            star (P.partition.cellVector a 1 out₁ (fun l => x (π l))))‖) ≤ 2 * (δ + 4 * β) := by
  apply le_trans _ (P.weighted_two_variable_exchange_error π out₀ out₁)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (fun l => x (π l)))
    (fun a => P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
      star (P.partition.cellVector a 1 out₁ (fun l => x (π l)))) _
    (fun a => P.partition.cellWeight_nonneg a _) (P.partition.cellWeight_total _))

end NativeQuarticPointwisePartition
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
  NativeQuarticPairPartition.finite

def positiveCyclicTripleBudget (p : ℝ) : ℝ :=
  productNiltestBudget (raisedNiltestBudget (productNiltestBudget (raisedNiltestBudget p)))

theorem PositiveCyclicNiltest.mul_three {degree N : ℕ} [NeZero N] {p : ℝ}
    {f g h : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} degree N p f)
    (hg : PositiveCyclicNiltest.{u} degree N p g) (hh : PositiveCyclicNiltest.{u} degree N p h)
    (hp : 0 ≤ p) : PositiveCyclicNiltest.{u} degree N (positiveCyclicTripleBudget p)
      (fun x => f x * g x * h x) := by
  have hpq : p ≤ productNiltestBudget (raisedNiltestBudget p) :=
    (le_raisedNiltestBudget p).trans (le_productNiltestBudget (hp.trans (le_raisedNiltestBudget p)))
  exact (hf.mul hg hp).mul (hh.mono le_rfl hpq) (hp.trans hpq)

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}

namespace NativePolynomialOrbitFactors

def HasQuarticCorrelatingAnchor (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r) (row : ZMod N → ZMod N → ℂ)
    (H : Finset (ZMod N)) (out : Fin W.outputDim) (b : ℝ) : Prop :=
  ∃ y : Fin 4 → ZMod N, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
    Real.exp (-b) * N ≤ (S.card : ℝ) ∧ ∃ w : ZMod N → ℝ,
      PositiveCyclicNiltest.{0} 1 N b w ∧
      NativeIntegerVectorEquivalence 3 b
        (R.quarticPairAnchoredVector (fun k => ((y k).val : ℤ)) 0)
        (R.quarticPairAnchoredVector (fun k => ((y k).val : ℤ)) 1) ∧
      ∀ h ∈ S, Real.exp (-b) ≤ ‖𝔼 n : ZMod N, row h n *
        star ((w n : ℂ) * R.quarticPairAnchoredVector (fun k => ((y k).val : ℤ))
          0 out ![(h.val : ℤ), (n.val : ℤ), (n.val : ℤ), (n.val : ℤ)])‖

theorem hasQuarticCorrelatingAnchor_mono {row : ZMod N → ZMod N → ℂ}
    {H : Finset (ZMod N)} {out : Fin W.outputDim} {a b : ℝ}
    (h : R.HasQuarticCorrelatingAnchor row H out a) (hab : a ≤ b) :
    R.HasQuarticCorrelatingAnchor row H out b := by
  obtain ⟨y, S, hSH, hS, hsize, w, hw, hequiv, hcorr⟩ := h
  have he : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (neg_le_neg hab)
  exact ⟨y, S, hSH, hS, (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)).trans hsize,
    w, hw.mono le_rfl hab, hequiv.mono hab, fun h hh => he.trans (hcorr h hh)⟩

end NativePolynomialOrbitFactors

theorem NativeQuarticPairPartition.correlatingAnchor_of_cell {a b ε t : ℝ}
    (P : NativeQuarticPairPartition R b ε) (hb : 0 ≤ b) (hbt : b ≤ t)
    (hprod : positiveCyclicTripleBudget b ≤ t) (hloss : a + b + 4 ≤ t)
    (row : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N)) (out : Fin W.outputDim)
    (cell : Fin 4 → P.I) (S : Finset (ZMod N)) (hSH : S ⊆ H) (hS : S.Nonempty)
    (hsize : Real.exp (-a) / (4 * Real.exp b) * N ≤ (S.card : ℝ))
    (hcorr : ∀ h ∈ S, Real.exp (-a) / (4 * Real.exp b) ≤
      ‖𝔼 n : ZMod N, row h n * star
        (((P.weight (cell 1) n * P.weight (cell 2) n * P.weight (cell 3) n : ℝ) : ℂ) *
          P.cellVector cell 0 out (quarticDiagonalSample ![h, n]))‖) :
    R.HasQuarticCorrelatingAnchor row H out t := by
  have hlower : Real.exp (-t) ≤ Real.exp (-a) / (4 * Real.exp b) := by
    have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.exp b)).mpr
    calc
      _ ≤ Real.exp (-t) * (Real.exp 4 * Real.exp b) := by gcongr
      _ = Real.exp (-t + (4 + b)) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have heval (h n : ZMod N) : (fun k => ((quarticDiagonalSample ![h, n] k).val : ℤ)) =
      ![(h.val : ℤ), (n.val : ℤ), (n.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  refine ⟨P.anchor cell, S, hSH, hS,
    (mul_le_mul_of_nonneg_right hlower (Nat.cast_nonneg N)).trans hsize,
    fun n => P.weight (cell 1) n * P.weight (cell 2) n * P.weight (cell 3) n,
    ((P.positive (cell 1)).mul_three (P.positive (cell 2)) (P.positive (cell 3)) hb).mono le_rfl hprod,
    (P.equivalence cell).mono hbt, ?_⟩
  intro h hh
  apply hlower.trans
  simpa only [NativeQuarticPairPartition.cellVector, heval] using hcorr h hh

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
  NativeQuarticPairPartition.finite

theorem exists_quartic_sampled_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b δ β : ℝ} {N : ℕ} [NeZero N]
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r}
      (P : NativeQuarticPointwisePartition R b δ β), 0 ≤ b →
      ∃ G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3
          ((b + C) ^ C) (G π a c))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), G π a c (fun z => ((x z).val : ℤ)) =
          ∑ cell, (P.partition.cellWeight cell (fun l => x (π l)) : ℂ) *
            (P.partition.cellVector cell 0 a (fun l => x (π l)) *
              star (P.partition.cellVector cell 1 c (fun l => x (π l))))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (quarticInput ((x (π 0)).val : ℤ)
              ![((x (π 1)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)]) *
              star (W.eval c (quarticInput ((x (π 1)).val : ℤ)
                ![((x (π 0)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)])) -
            G π a c (fun z => ((x z).val : ℤ))‖) ≤ 2 * (δ + 4 * β)) := by
  obtain ⟨A, _, hpartition⟩ := exists_positive_partition_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + 4 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r b δ β N _ W i j V R P hb
  classical
  let t := b + 4
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hbt : b ≤ t := by dsimp [t]; linarith
  have hσ : (Fintype.card (Fin 4) : ℝ) ≤ t := by norm_num; dsimp [t]; linarith
  let v := fun (cell : Fin 4 → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim)
      (x : Fin 4 → ℤ) =>
    R.quarticPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 0 ac.1 x *
      star (R.quarticPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 1 ac.2 x)
  have hv (cell : Fin 4 → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 t (v cell ac)) :=
    ((P.partition.equivalence cell).mono hbt).expansion ac.1 ac.2
  obtain ⟨F, hF, hFeval⟩ := hpartition ht hσ
    (P.partition.card_bound.trans (Real.exp_le_exp.mpr hbt))
    (fun cell k => P.partition.weight (cell k)) v
    (fun cell k => (P.partition.positive (cell k)).mono (by decide) hbt) hv
  let G := fun (π : Fin 4 → Fin 2) (a c : Fin W.outputDim) (x : Fin 2 → ℤ) =>
    F (a, c) (fun l => x (π l))
  have hcost : (t + A) ^ A ≤ (b + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget b hb
  have hexp (π : Fin 4 → Fin 2) (a c : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((b + C) ^ C) (G π a c)) := by
    let f : Fin 4 → ((Fin 2 → ℤ) →+ ℤ) :=
      fun k => ⟨⟨fun x => x (π k), rfl⟩, fun _ _ => rfl⟩
    exact ⟨((Classical.choice (hF (a, c))).linearPullbackHom f).mono hcost⟩
  have heval (π : Fin 4 → Fin 2) (a c : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      G π a c (fun z => ((x z).val : ℤ)) =
        ∑ cell, (P.partition.cellWeight cell (fun l => x (π l)) : ℂ) *
          (P.partition.cellVector cell 0 a (fun l => x (π l)) *
            star (P.partition.cellVector cell 1 c (fun l => x (π l)))) :=
    hFeval (a, c) (fun l => x (π l))
  refine ⟨G, hexp, heval, ?_, ?_⟩
  · intro π a c x
    rw [heval]
    apply norm_positive_partition_sum_le_one
      (fun cell => P.partition.cellWeight cell (fun l => x (π l)))
      (fun cell => P.partition.cellVector cell 0 a (fun l => x (π l)) *
        star (P.partition.cellVector cell 1 c (fun l => x (π l))))
      (fun cell => P.partition.cellWeight_nonneg cell _) (P.partition.cellWeight_total _)
    intro cell
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (P.partition.cellVector_norm cell 0 a _)).trans
        (P.partition.cellVector_norm cell 1 c _)
  · intro π a c
    simpa only [heval] using P.two_variable_exchange_approximation π a c

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

theorem exists_quartic_precise_sampled_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (_R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ e → Real.exp ((tensorPowerBudget 6 p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3
          ((tensorPowerBudget 6 p + q + r + e + C) ^ C) (G π a c))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (quarticInput ((x (π 0)).val : ℤ)
              ![((x (π 1)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)]) *
              star (W.eval c (quarticInput ((x (π 1)).val : ℤ)
                ![((x (π 0)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)])) -
            G π a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hlocal⟩ := exists_quartic_pair_local_approximation
  obtain ⟨b, _, hfrozen⟩ := exists_quartic_pair_frozen_reduction
  obtain ⟨d, _, hpartition⟩ := exists_quartic_diagonal_partition
  obtain ⟨c, _, hexchange⟩ := exists_quartic_sampled_exchange
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b
  let Z := (T + X + 1 + Polynomial.C d) ^ d
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z + (Z + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hk : 0 ≤ tensorPowerBudget 6 p := hp.trans (tensorPowerBudget_bounds 6 hp).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget 6 p + q + r + e
  let t := (v + a) ^ a + (v + b) ^ b
  let z := (t + (e + 1) + d) ^ d
  let zmax := (t + v + 1 + d) ^ d
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzm : 0 ≤ zmax := by dsimp [zmax]; positivity
  have hzz : z ≤ zmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hsum : zmax + (zmax + c) ^ c ≤ (v + C) ^ C := by
    simpa [X, T, Z, zmax, t, Polynomial.eval₂_pow] using hbudget v hv
  have hzC : z ≤ (v + C) ^ C :=
    hzz.trans ((le_add_of_nonneg_right (by positivity)).trans hsum)
  have hcost : (z + c) ^ c ≤ (v + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (by linarith : z + c ≤ zmax + c) c).trans
      ((le_add_of_nonneg_left hzm).trans hsum)
  have ha : (tensorPowerBudget 6 p + q + r + a) ^ a ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hb : (tensorPowerBudget 6 p + q + r + b) ^ b ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  obtain ⟨δ, β, P, herr⟩ := hpartition R (hlocal (W := W) R hr) (hfrozen (W := W) R hr)
    ht (by positivity : 0 ≤ e + 1) ha hb ((Real.exp_le_exp.mpr hzC).trans hN)
  obtain ⟨G, hG, _, hcap, herror⟩ := hexchange P hz
  refine ⟨G, fun π a c => ⟨(Classical.choice (hG π a c)).mono hcost⟩, hcap, ?_⟩
  intro π a c
  apply (herror π a c).trans
  have hhalf := exp_sub_one_le_half_exp (-e)
  have hid : -(e + 1) = -e - 1 := by ring
  rw [← hid] at hhalf
  linarith

end Erdos3

end

end OAI
