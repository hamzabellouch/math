import OAI.Probability.SignedSweeps.WeightedGraph

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma finite_sum_le_of_injective {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (g : I → ℝ) (h : J → ℝ)
    (hg : ∀ i, g i ≤ h (f i)) (hh : ∀ j, 0 ≤ h j) :
    (∑ i, g i) ≤ ∑ j, h j := by
  classical
  calc
    _ ≤ ∑ i, h (f i) := Finset.sum_le_sum (fun i _ => hg i)
    _ = ∑ j ∈ Finset.univ.image f, h j := (Finset.sum_image (fun _ _ _ _ he => hf he)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hh j)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]

def NoIsolatedVertex (G : SimpleGraph A) (S : Finset A) : Prop :=
  ∀ x ∈ S, ∃ y ∈ S, G.Adj x y

def noIsolatesWeight (G : SimpleGraph A) (w : A → ℝ) : ℝ :=
  ∑ S : {S : Finset A // NoIsolatedVertex G S}, ∏ x ∈ S.1, w x

lemma matching_univ {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hm : DisjointEdgeMatching G S M) : DisjointEdgeMatching G Finset.univ M :=
  ⟨fun e he => ⟨(hm.1 e he).1, Finset.mem_univ _, Finset.mem_univ _⟩, hm.2⟩

lemma noIsolatesWeight_le_matching_sum (G : SimpleGraph A) (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    noIsolatesWeight G w ≤ ∑ M : Finset (A × A),
      if DisjointEdgeMatching G Finset.univ M then
        (∏ e ∈ M, w e.1 * w e.2) *
          ∏ y ∈ neighborUnion G (matchingVertices M), (1 + w y)
      else 0 := by
  classical
  let I := {S : Finset A // NoIsolatedVertex G S}
  let m (S : I) := (exists_dominating_matching G S.1 S.2).choose
  have hm (S : I) := (exists_dominating_matching G S.1 S.2).choose_spec
  let phi (S : I) : Finset (A × A) × Finset A := (m S, S.1 \ matchingVertices (m S))
  have hsub (S : I) : matchingVertices (m S) ⊆ S.1 := matching_vertices_sub (hm S).1
  have hu (S : I) : matchingVertices (phi S).1 ∪ (phi S).2 = S.1 :=
    Finset.union_sdiff_of_subset (hsub S)
  have hinj : Function.Injective phi := by
    intro S T h
    apply Subtype.ext
    rw [← hu S, ← hu T, h]
  let W (z : Finset (A × A) × Finset A) : ℝ :=
    if DisjointEdgeMatching G Finset.univ z.1 ∧ z.2 ⊆ neighborUnion G (matchingVertices z.1) then
      (∏ x ∈ matchingVertices z.1, w x) * ∏ y ∈ z.2, w y
    else 0
  have hW (z) : 0 ≤ W z := by
    dsimp [W]
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg (fun x _ => hw x)) (Finset.prod_nonneg (fun x _ => hw x))
    · exact le_rfl
  have hp (S : I) : (∏ x ∈ S.1, w x) ≤ W (phi S) := by
    dsimp only [W, phi]
    rw [ite_eq_left ⟨matching_univ (hm S).1, (hm S).2⟩]
    rw [← Finset.prod_union (Finset.disjoint_left.mpr (fun x hx hx' =>
      (Finset.mem_sdiff.mp hx').2 hx))]
    exact le_of_eq (congrArg (fun U : Finset A => ∏ x ∈ U, w x) (hu S).symm)
  have h := finite_sum_le_of_injective phi hinj (fun S => ∏ x ∈ S.1, w x) W hp hW
  change noIsolatesWeight G w ≤ _ at h
  apply h.trans_eq
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro M _
  dsimp only [W]
  by_cases hM : DisjointEdgeMatching G Finset.univ M
  · simp only [hM, true_and, ↓reduceIte]
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have he : (Finset.univ.filter (fun T => T ⊆ neighborUnion G (matchingVertices M))) =
        (neighborUnion G (matchingVertices M)).powerset := by ext T; simp
    rw [he, ← Finset.prod_one_add, matching_weight_factorization hM]
  · simp [hM]

omit [Fintype A] [DecidableEq A] in
lemma product_one_add_le_exp_sum [Fintype A] [DecidableEq A]
    (S : Finset A) (w : A → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∏ x ∈ S, (1 + w x)) ≤ Real.exp (∑ x ∈ S, w x) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun x _ => by linarith [hw x])
    (fun x _ => by simpa [add_comm] using Real.add_one_le_exp (w x))

lemma noIsolatesWeight_bound (G : SimpleGraph A) (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) {Δ : ℝ}
    (hdeg : ∀ x, (∑ y ∈ Finset.univ.filter (G.Adj x), w y) ≤ Δ) :
    noIsolatesWeight G w ≤ Real.exp (Real.exp (2 * Δ) * (∑ x, w x) * Δ) := by
  classical
  let eWeight (e : A × A) : ℝ := if G.Adj e.1 e.2 then Real.exp (2 * Δ) * (w e.1 * w e.2) else 0
  have hepos (e) : 0 ≤ eWeight e := by
    dsimp [eWeight]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hw _) (hw _))
    · exact le_rfl
  calc
    _ ≤ ∑ M : Finset (A × A), if DisjointEdgeMatching G Finset.univ M then
        (∏ e ∈ M, w e.1 * w e.2) * ∏ y ∈ neighborUnion G (matchingVertices M), (1 + w y)
        else 0 := noIsolatesWeight_le_matching_sum G w hw
    _ ≤ ∑ M : Finset (A × A), ∏ e ∈ M, eWeight e := by
      apply Finset.sum_le_sum
      intro M _
      by_cases hM : DisjointEdgeMatching G Finset.univ M
      · rw [ite_eq_left hM]
        calc
          _ ≤ (∏ e ∈ M, w e.1 * w e.2) *
              Real.exp ((matchingVertices M).card * Δ) := by
            apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun e _ => mul_nonneg (hw _) (hw _)))
            exact (product_one_add_le_exp_sum _ w hw).trans
              (Real.exp_le_exp.mpr (neighborUnion_weight_bound G _ w hw hdeg))
          _ = _ := by
            rw [matching_vertices_card hM]
            rw [Nat.cast_mul, Nat.cast_ofNat]
            have hh : Real.exp ((2 : ℝ) * M.card * Δ) = ∏ e ∈ M, Real.exp (2 * Δ) := by
              rw [← Real.exp_sum]
              simp only [Finset.sum_const, nsmul_eq_mul]
              congr 1
              ring
            rw [hh, ← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro e he
            simp only [eWeight, ite_eq_left (hM.1 e he).1]
            ring
      · rw [ite_eq_right hM]
        exact Finset.prod_nonneg (fun e _ => hepos e)
    _ = ∏ e : A × A, (1 + eWeight e) := by
      rw [Finset.prod_one_add]
      have he : (Finset.univ : Finset (A × A)).powerset = Finset.univ := by ext; simp
      rw [he]
    _ ≤ Real.exp (∑ e, eWeight e) := product_one_add_le_exp_sum _ _ hepos
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [Fintype.sum_prod_type]
      calc
        (∑ u, ∑ v, eWeight (u,v)) = Real.exp (2 * Δ) * ∑ u, w u *
            (∑ v ∈ Finset.univ.filter (G.Adj u), w v) := by
          simp only [eWeight, Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro v _
          split_ifs <;> ring
        _ ≤ Real.exp (2 * Δ) * ∑ u, w u * Δ := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hdeg u) (hw u))
        _ = _ := by rw [← Finset.sum_mul]; ring

def fixedNoIsolatesWeight (G : SimpleGraph A) (w : A → ℝ) (k : ℕ) : ℝ :=
  ∑ S : {S : Finset A // NoIsolatedVertex G S ∧ S.card = k}, ∏ x ∈ S.1, w x

omit [Fintype A] [DecidableEq A] in
lemma fixedNoIsolatesWeight_le [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (w : A → ℝ) (k : ℕ)
    (hw : ∀ x, 0 ≤ w x) : fixedNoIsolatesWeight G w k ≤ noIsolatesWeight G w := by
  classical
  let f : {S : Finset A // NoIsolatedVertex G S ∧ S.card = k} →
      {S : Finset A // NoIsolatedVertex G S} := fun S => ⟨S.1, S.2.1⟩
  have hf : Function.Injective f := fun S T h => Subtype.ext (congrArg (fun U : {S : Finset A // NoIsolatedVertex G S} => U.1) h)
  exact finite_sum_le_of_injective f hf _ _ (fun _ => le_rfl)
    (fun S => Finset.prod_nonneg (fun x _ => hw x))

omit [Fintype A] [DecidableEq A] in
lemma fixedNoIsolatesWeight_smul [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (w : A → ℝ) (k : ℕ) (t : ℝ) :
    fixedNoIsolatesWeight G (fun x => t * w x) k = t ^ k * fixedNoIsolatesWeight G w k := by
  classical
  unfold fixedNoIsolatesWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib]
  simp [S.2.2]

lemma weighted_noIsolates_fixed_card (G : SimpleGraph A) (w : A → ℝ) (k : ℕ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (∑ x, w x) = k) {Δ : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hdeg : ∀ x, (∑ y ∈ Finset.univ.filter (G.Adj x), w y) ≤ Δ) :
    fixedNoIsolatesWeight G w k ≤ (Real.sqrt Δ) ^ k * Real.exp (Real.exp 2 * k) := by
  classical
  let t := Real.sqrt Δ
  have ht : 0 < t := Real.sqrt_pos.2 hΔ
  have ht0 := ht.ne'
  have htt : t * t = Δ := Real.mul_self_sqrt hΔ.le
  have ht1 : t ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hΔ1
  have hw' (x) : 0 ≤ w x / t := div_nonneg (hw x) ht.le
  have hdeg' (x) : (∑ y ∈ Finset.univ.filter (G.Adj x), w y / t) ≤ t := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ ht).2
    rw [htt]
    exact hdeg x
  have htotal' : (∑ x, w x / t) = (k : ℝ) / t := by rw [← Finset.sum_div, htotal]
  have hb := (fixedNoIsolatesWeight_le G (fun x => w x / t) k hw').trans
    (noIsolatesWeight_bound G _ hw' hdeg')
  have hh : (fun x => t * (w x / t)) = w := by ext x; field_simp
  calc
    fixedNoIsolatesWeight G w k = t ^ k * fixedNoIsolatesWeight G (fun x => w x / t) k := by
      rw [← fixedNoIsolatesWeight_smul, hh]
    _ ≤ t ^ k * Real.exp (Real.exp (2 * t) * (∑ x, w x / t) * t) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg ht.le _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.le _)
      apply Real.exp_le_exp.mpr
      rw [htotal', mul_assoc, div_mul_cancel₀ _ ht0]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg k)

theorem noIsolates_probability_bound (G : SimpleGraph A) (w : A → ℝ) (k : ℕ)
    (μ : Finset A → ℝ) (hμ : ∀ S, 0 ≤ μ S)
    (hcard : ∀ S, S.card ≠ k → μ S = 0)
    (hw : ∀ x, 0 ≤ w x) (htotal : (∑ x, w x) = k) {Δ : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hdeg : ∀ x, (∑ y ∈ Finset.univ.filter (G.Adj x), w y) ≤ Δ)
    (hinc : ∀ T, (∑ S : Finset A, if T ⊆ S then μ S else 0) ≤ ∏ x ∈ T, w x) :
    (∑ S : {S : Finset A // NoIsolatedVertex G S}, μ S.1) ≤
      (Real.sqrt Δ) ^ k * Real.exp (Real.exp 2 * k) := by
  classical
  have hexact (S : Finset A) : μ S ≤ ∏ x ∈ S, w x := by
    apply le_trans _ (hinc S)
    calc
      μ S = if S ⊆ S then μ S else 0 := by simp
      _ ≤ ∑ T : Finset A, if S ⊆ T then μ T else 0 :=
        Finset.single_le_sum (f := fun T => if S ⊆ T then μ T else 0) (fun T _ => by split_ifs; exact hμ T; exact le_rfl) (Finset.mem_univ S)
  have he : (∑ S : {S : Finset A // NoIsolatedVertex G S}, μ S.1) =
      ∑ S : {S : Finset A // NoIsolatedVertex G S ∧ S.card = k}, μ S.1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (NoIsolatedVertex G)) (by simp) μ,
      ← Finset.sum_subtype (Finset.univ.filter (fun S => NoIsolatedVertex G S ∧ S.card = k)) (by simp) μ]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hp : NoIsolatedVertex G S <;> by_cases hc : S.card = k <;>
      simp [hp, hc, hcard S]
  rw [he]
  apply le_trans _ (weighted_noIsolates_fixed_card G w k hw htotal hΔ hΔ1 hdeg)
  exact Finset.sum_le_sum (fun S _ => hexact S.1)

end SignedSweeps
end

end OAI
