import OAI.Combinatorics.SparsestCut.Replication
import OAI.Combinatorics.SparsestCut.PositiveKernels

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.UniformReplication
open scoped BigOperators RealInnerProductSpace
noncomputable section
lemma negative_pullback {V : Type u1} {H : Type u2} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Z : V → H) (htri : ∀ v w z, ‖Z v-Z z‖^2 ≤ ‖Z v-Z w‖^2+‖Z w-Z z‖^2)
    {n : ℕ} (r : Fin n → V) : NegativeType (fun i j => ‖Z (r i)-Z (r j)‖^2) := by
  classical
  obtain ⟨Y,hY⟩ := TriangleRepair.exists_gram (TriangleRepair.gram_posSemidef (fun i => Z (r i)))
  refine ⟨⟨Y,?_⟩,fun i j k => htri (r i) (r j) (r k)⟩
  intro i j
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, hY, Matrix.of_apply]

variable {V : Type u3} {H : Type u4} [Fintype V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma estimates (M : ℕ) (hM : 0<M) (w : V → ℝ) (hw : ∀ v, 0≤w v) (hws : (∑ v,w v)=1)
    (Z : V → H) (htri : ∀ v w z, ‖Z v-Z z‖^2 ≤ ‖Z v-Z w‖^2+‖Z w-Z z‖^2)
    {D a b : ℝ} (hD : 0≤D) (hdiam : ∀ v z, ‖Z v-Z z‖^2≤D)
    (havg : a≤∑ v, ∑ z, w v*w z*‖Z v-Z z‖^2)
    (hcon : ∀ (A : Type) [Fintype A] (F : V → A → ℝ),
      (∀ v z, (∑ k, |F v k-F z k|)≤‖Z v-Z z‖^2) →
      (∑ v, ∑ z, w v*w z*(∑ k, |F v k-F z k|))≤b) :
    let n := Replication.n M w
    let d := fun i j : Fin n => ‖Z (Replication.rep M w i)-Z (Replication.rep M w j)‖^2
    let ε := 4*D*(Fintype.card V:ℝ)/M
    NegativeType d ∧ (n:ℝ)^2*(a-ε)≤∑ i, ∑ j,d i j ∧
      ∀ (A : Type) [Fintype A] (F : Fin n → A → ℝ),
        (∀ i j, (∑ k, |F i k-F j k|)≤d i j) →
        (∑ i, ∑ j, ∑ k, |F i k-F j k|)≤(n:ℝ)^2*(b+ε) := by
  dsimp only
  have hn : 0<Replication.n M w := hM.trans_le (Replication.n_bounds M w hw hws).1
  refine ⟨negative_pullback Z htri _,?_,?_⟩
  · rw [Replication.ordered_sum M w hn (fun v z => ‖Z v-Z z‖^2)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have he := Replication.expectation_error M hM w hw hws
      (fun v z => ‖Z v-Z z‖^2) hD (fun v z => by rw [abs_of_nonneg (sq_nonneg _)]; exact hdiam v z)
    linarith [(abs_le.mp he).1]
  · intro A hA F hF
    let G : V → A → ℝ := fun v k => F (Replication.representative M w v) k
    have hG : ∀ v z, (∑ k, |G v k-G z k|)≤‖Z v-Z z‖^2 :=
      Replication.descend_contraction M w _ F hF
    have he : (∑ i, ∑ j, ∑ k, |F i k-F j k|)=
        ∑ i, ∑ j, ∑ k, |G (Replication.rep M w i) k-G (Replication.rep M w j) k| := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      have h1 := Replication.collapse M w (fun v z => ‖Z v-Z z‖^2) (by simp) F hF i k
      have h2 := Replication.collapse M w (fun v z => ‖Z v-Z z‖^2) (by simp) F hF j k
      change |F i k-F j k|=|F (Replication.representative M w (Replication.rep M w i)) k-
        F (Replication.representative M w (Replication.rep M w j)) k|
      rw [h1,h2]
    rw [he,Replication.ordered_sum M w hn (fun v z => ∑ k, |G v k-G z k|)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have herr := Replication.expectation_error M hM w hw hws
      (fun v z => ∑ k, |G v k-G z k|) hD (fun v z => by
        rw [abs_of_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg _))]
        exact (hG v z).trans (hdiam v z))
    have hbound := hcon A G hG
    linarith [(abs_le.mp herr).2]
end
end UniformSparsestCut.UniformReplication

end

end OAI
