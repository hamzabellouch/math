import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussianDistance

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

def ProofFamily.atomTotal (f : ProofFamily Name I) (σ η θ : ℝ) : EdgeStatistic Name I :=
  fun U h pos => atomProbability (m := m) (n := n) (f.second (secondQuestion U h pos)) σ η θ

def ProofFamily.fourthTotal (f : ProofFamily Name I) (σ η : ℝ) : EdgeStatistic Name I :=
  fun U h pos => fourthError (m := m) (n := n) (projection U h pos)
    (f.first U) (f.second (secondQuestion U h pos)) σ η

lemma ProofFamily.atomTotal_mean (f : ProofFamily Name I) (equations : S → Equation Name)
    (k : ℕ) (σ η θ : ℝ) :
    (𝔼 x : Point m n, 𝔼 i : Fin m,edgeMean equations k (f.atomAt σ η θ x i)) =
      edgeMean equations k (f.atomTotal (m := m) (n := n) σ η θ) := by
  simp_rw [edgeMean_expect]
  rfl

lemma ProofFamily.distanceTotal_bound (f : ProofFamily Name I) (equations : S → Equation Name)
    (k : ℕ) (hm : 0 < m) (hn : 0 < n) {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    (𝔼 x : Point m n, 𝔼 i : Fin m,edgeMean equations k (f.distanceAt σ η x i)) ≤
      (4*σ⁻¹^2)*edgeMean equations k (f.fourthTotal (m := m) (n := n) σ η) := by
  simp_rw [edgeMean_expect]
  rw [← edgeMean_mul]
  apply edgeMean_mono
  intro U h pos
  change (𝔼 x : Point m n, 𝔼 i : Fin m,
    𝔼 D, ∫ c, rowDistance (projection U h pos)
      (comparisonRow (f.first U) σ η c x ⟨i,face x i⟩ (fun t => formPullback (projection U h pos) (D t)))
      (comparisonRow (f.second (secondQuestion U h pos)) σ η c x ⟨i,face x i⟩ D) ∂gauss (Point m n)) ≤ _
  rw [comparisonRow_distance_total _ _ _ hm hσ]
  exact averaged_comparison _ _ _ hn hσ η

theorem ProofFamily.atomTotal_bound [Fintype Name] [Nonempty I] [Nonempty S]
    (f : ProofFamily Name I) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s≤3/4)
    {k : ℕ} (hk : k≤Fintype.card I) (hm : 0 < m) (hn : 0 < n)
    {σ u θ : ℝ} (hσ : 0<σ) (hu : 0<u) (hθ : 0<θ) (η : ℝ) :
    edgeMean equations k (f.atomTotal (m := m) (n := n) σ η θ) ≤
      listTerm (Real.sqrt (n^m:ℕ)/σ) u θ (Fintype.card (Row m n)-1) k +
      (64/(θ^2*σ^2))*edgeMean equations k (f.fourthTotal (m := m) (n := n) σ η) +
      remainderTerm (Real.sqrt (n^m:ℕ)/σ) u θ (Fintype.card (Row m n)-1) k (Fintype.card I) := by
  let : NeZero m := ⟨hm.ne'⟩
  let : NeZero n := ⟨hn.ne'⟩
  have h := Finset.expect_le_expect (s := Finset.univ) (fun (x : Point m n) _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun i _ => f.row_soundness equations hsound hk hσ hu hθ η x i))
  rw [f.atomTotal_mean] at h
  simp only [Finset.expect_add_distrib,Fintype.expect_const,← Finset.mul_expect] at h
  have hd := f.distanceTotal_bound equations k hm hn hσ.ne' η
  have hd' := mul_le_mul_of_nonneg_left hd (by positivity : 0≤16/θ^2)
  have hc : (16/θ^2)*(4*σ⁻¹^2) = 64/(θ^2*σ^2) := by ring
  rw [← mul_assoc,hc] at hd'
  linarith
end MinUncut.Outer

open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient oddAtom rowAtom pairSlice pairAtomMean
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

lemma weighted_row_secondMoment (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {σ θ p : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (hn : 0 < n) (i : Fin m)
    (hp : (∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) σ η θ) ≤ p) :
    (∑ ξ, w ξ*(𝔼 x : Point m n, 𝔼 D, ∫ c, (rowAtom (f ξ) σ η x i D c)^2 ∂γpi (Point m n))) ≤
      θ^2 + (m:ℝ)*p*(n^m:ℕ)/σ^2 := by
  have : NeZero n := ⟨by omega⟩
  have hcap : (0:ℝ) ≤ (n^m:ℕ)/σ^2 := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hξ (ξ : Ξ) : (𝔼 x : Point m n, 𝔼 D, ∫ c, (rowAtom (f ξ) σ η x i D c)^2 ∂γpi (Point m n)) ≤
      θ^2 + (n^m:ℕ)/σ^2*((m:ℝ)*atomProbability (m := m) (n := n) (f ξ) σ η θ) := by
    calc
      _ ≤ (𝔼 x : Point m n, (θ^2 + (n^m:ℕ)/σ^2*rowEventProbability (f ξ) σ η θ x i)) :=
        Finset.expect_le_expect (fun x _ => rowAtom_secondMoment (f ξ) hσ hθ η x i)
      _ = θ^2+(n^m:ℕ)/σ^2*(𝔼 x : Point m n, rowEventProbability (f ξ) σ η θ x i) := by
        rw [Finset.expect_add_distrib,Fintype.expect_const,← Finset.mul_expect]
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (fixed_row_probability_le (f ξ) σ η θ i) hcap) _
  calc
    _ ≤ ∑ ξ, w ξ*(θ^2 + (n^m:ℕ)/σ^2*((m:ℝ)*atomProbability (m := m) (n := n) (f ξ) σ η θ)) :=
      Finset.sum_le_sum (fun ξ _ => mul_le_mul_of_nonneg_left (hξ ξ) (hw ξ))
    _ = θ^2+(n^m:ℕ)/σ^2*(m:ℝ)*(∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) σ η θ) := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
      rw [hw1,one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    _ ≤ θ^2+(n^m:ℕ)/σ^2*(m:ℝ)*p :=
      add_le_add_right (mul_le_mul_of_nonneg_left hp (mul_nonneg hcap hm0)) _
    _ = _ := by ring

lemma weighted_pairAtomMean (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {σ θ p : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (hn : 0 < n) {k s : ℕ} (hk : k ≤ n-1) (r : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, GaussianHermite.degree j.2 ≤ s)
    (hp : (∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) σ η θ) ≤ p) :
    (∑ ξ, w ξ*(𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean (f ξ) σ η x Y r J)) ≤
      (4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)*
        Real.sqrt (θ^2+(m:ℝ)*p*(n^m:ℕ)/σ^2) := by
  have : NeZero n := ⟨by omega⟩
  have (x : Point m n) (i : Fin m) : Nonempty (OuterSmoothness.FixedSets (Away (x i)) k) :=
    OuterSmoothness.fixedSets_nonempty (by simpa [card_away] using hk)
  let C := (4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)
  let E (ξ : Ξ) (x : Point m n) := 𝔼 D, ∫ c, (rowAtom (f ξ) σ η x r.val.1 D c)^2 ∂γpi (Point m n)
  have hE ξ x : 0 ≤ E ξ x := Finset.expect_nonneg (fun D _ => integral_nonneg (fun c => sq_nonneg _))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hξ (ξ : Ξ) : (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean (f ξ) σ η x Y r J) ≤
      C*Real.sqrt (𝔼 x : Point m n, E ξ x) := by
    calc
      _ ≤ 𝔼 x : Point m n, 𝔼 _Y : PointedBox x k, C*Real.sqrt (E ξ x) := by
        apply Finset.expect_le_expect
        intro x _
        apply Finset.expect_le_expect
        intro Y _
        unfold E C rowAtom
        exact pairAtomMean_uniform_le (f ξ) hσ.ne' η x Y r J hJ
      _ = C*(𝔼 x : Point m n, Real.sqrt (E ξ x)) := by
        simp only [Fintype.expect_const,← Finset.mul_expect]
      _ ≤ _ := mul_le_mul_of_nonneg_left (expect_sqrt_le _ (hE ξ)) hC
  calc
    _ ≤ ∑ ξ, w ξ*(C*Real.sqrt (𝔼 x : Point m n, E ξ x)) :=
      Finset.sum_le_sum (fun ξ _ => mul_le_mul_of_nonneg_left (hξ ξ) (hw ξ))
    _ = C*(∑ ξ, w ξ*Real.sqrt (𝔼 x : Point m n, E ξ x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    _ ≤ C*Real.sqrt (∑ ξ, w ξ*(𝔼 x : Point m n, E ξ x)) :=
      mul_le_mul_of_nonneg_left (Average.weighted_sqrt _ _ hw hw1 (fun ξ => Finset.expect_nonneg (fun x _ => hE ξ x))) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (weighted_row_secondMoment V A w hw hw1 f hσ hθ η hn r.val.1 hp)) hC
end MinUncut.Inner

end

end OAI
