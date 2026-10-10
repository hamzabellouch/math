import Mathlib

namespace OAI

/-! Polynomial separators, finite-point isolation and elementary bounds for distinct Euclidean distances. -/

noncomputable section

open scoped BigOperators Topology

namespace ErdosDistinctDistances

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def distances {d : ℕ} (P : Finset (Point d)) : Finset ℝ := by
  classical
  exact P.offDiag.image (fun pq => dist pq.1 pq.2)

variable {d : ℕ} {P Q : Finset (Point d)}

@[simp] theorem mem_distances {r : ℝ} :
    r ∈ distances P ↔ ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ dist p q = r := by
  classical
  simp only [distances, Finset.mem_image, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨p, q⟩, ⟨hp, hq, hpq⟩, hr⟩
    exact ⟨p, hp, q, hq, hpq, hr⟩
  · rintro ⟨p, hp, q, hq, hpq, hr⟩
    exact ⟨(p, q), ⟨hp, hq, hpq⟩, hr⟩

theorem coe_distances (P : Finset (Point d)) :
    (distances P : Set ℝ) =
      {r | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ ‖p - q‖ = r} := by
  ext r
  simp [mem_distances, dist_eq_norm]

theorem distance_pos {r : ℝ} (hr : r ∈ distances P) : 0 < r := by
  obtain ⟨p, _, q, _, hpq, rfl⟩ := mem_distances.mp hr
  exact dist_pos.mpr hpq

@[simp] theorem zero_not_mem_distances (P : Finset (Point d)) :
    (0 : ℝ) ∉ distances P := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (distance_pos h)

theorem distances_mono (h : P ⊆ Q) : distances P ⊆ distances Q := by
  intro r hr
  obtain ⟨p, hp, q, hq, hpq, rfl⟩ := mem_distances.mp hr
  exact mem_distances.mpr ⟨p, h hp, q, h hq, hpq, rfl⟩

theorem distances_nonempty (hP : 2 ≤ P.card) : (distances P).Nonempty := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hP
  exact ⟨dist p q, mem_distances.mpr ⟨p, hp, q, hq, hpq, rfl⟩⟩

theorem one_le_card_distances (hP : 2 ≤ P.card) : 1 ≤ (distances P).card :=
  (distances_nonempty hP).card_pos

theorem failure_gives_regime (hd : 3 ≤ d)
    (hfail : ¬ ∃ c : ℝ, 0 < c ∧
      ∀ P : Finset (Point d), 2 ≤ P.card →
        c * (P.card : ℝ) ^ (2 / (d : ℝ)) ≤ (distances P).card) :
    ∃ P : ℕ → Finset (Point d),
      (∀ k, 2 ≤ (P k).card) ∧
      Filter.Tendsto (fun k => (P k).card) Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun k => (1 + ((distances (P k)).card : ℝ)) /
          ((P k).card : ℝ) ^ (2 / (d : ℝ)))
        Filter.atTop (𝓝 0) := by
  classical
  have hf : ∀ c : ℝ, 0 < c → ∃ P : Finset (Point d),
      2 ≤ P.card ∧ (distances P).card < c * (P.card : ℝ) ^ (2 / (d : ℝ)) := by
    push Not at hfail
    exact hfail
  have hchoice : ∀ k : ℕ, ∃ P : Finset (Point d), 2 ≤ P.card ∧
      (distances P).card < (1 / ((k : ℝ) + 1)) *
        (P.card : ℝ) ^ (2 / (d : ℝ)) := by
    intro k
    exact hf _ (by positivity)
  choose P hP hm using hchoice
  have hn (k : ℕ) : (2 : ℝ) ≤ (P k).card := by exact_mod_cast hP k
  have hA (k : ℕ) : 0 < ((P k).card : ℝ) ^ (2 / (d : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith [hn k]) _
  have hM (k : ℕ) : (1 : ℝ) ≤ (distances (P k)).card := by
    exact_mod_cast one_le_card_distances (hP k)
  have he : 2 / (d : ℝ) ≤ 1 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    apply (div_le_one (by linarith : (0 : ℝ) < d)).mpr
    linarith
  have hkA (k : ℕ) : (k : ℝ) + 1 < ((P k).card : ℝ) ^ (2 / (d : ℝ)) := by
    have h : (1 : ℝ) < ((P k).card : ℝ) ^ (2 / (d : ℝ)) / ((k : ℝ) + 1) := by
      simpa [div_eq_mul_inv, mul_comm] using lt_of_le_of_lt (hM k) (hm k)
    simpa using (lt_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mp h
  have hkn (k : ℕ) : k ≤ (P k).card := by
    have hpow := Real.rpow_le_self_of_one_le (by linarith [hn k] : (1 : ℝ) ≤ (P k).card) he
    have : (k : ℝ) ≤ (P k).card := by linarith [hkA k]
    exact_mod_cast this
  refine ⟨P, hP, Filter.tendsto_atTop_mono hkn Filter.tendsto_id, ?_⟩
  apply squeeze_zero
  · intro k
    exact div_nonneg (by positivity) (hA k).le
  · intro k
    apply le_of_lt
    apply (div_lt_iff₀ (hA k)).mpr
    calc
      1 + ((distances (P k)).card : ℝ) ≤ 2 * (distances (P k)).card := by
        linarith [hM k]
      _ < 2 * ((1 / ((k : ℝ) + 1)) * ((P k).card : ℝ) ^ (2 / (d : ℝ))) :=
        mul_lt_mul_of_pos_left (hm k) (by norm_num)
      _ = (2 / ((k : ℝ) + 1)) * ((P k).card : ℝ) ^ (2 / (d : ℝ)) := by ring
  · convert tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ) using 1 <;>
      simp [div_eq_mul_inv]

theorem regime_precludes_bound (P : ℕ → Finset (Point d))
    (hP : ∀ k, 2 ≤ (P k).card)
    (hlim : Filter.Tendsto
      (fun k => (1 + ((distances (P k)).card : ℝ)) /
        ((P k).card : ℝ) ^ (2 / (d : ℝ))) Filter.atTop (𝓝 0)) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ Q : Finset (Point d), 2 ≤ Q.card →
        c * (Q.card : ℝ) ^ (2 / (d : ℝ)) ≤ (distances Q).card := by
  rintro ⟨c, hc, hb⟩
  have hcle : c ≤ 0 := ge_of_tendsto' hlim fun k => by
    have hn : (0 : ℝ) < (P k).card := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (hP k)
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hn _)).mpr
    linarith [hb (P k) (hP k)]
  exact (not_le_of_gt hc) hcle

def complexPoint (p : Point d) : Fin d → ℂ := fun i => (p i : ℂ)

def squaredDistancePolynomial (p : Point d) : MvPolynomial (Fin d) ℂ :=
  ∑ i : Fin d, (MvPolynomial.X i - MvPolynomial.C ((p i : ℝ) : ℂ)) ^ 2

theorem eval_squaredDistancePolynomial (p q : Point d) :
    MvPolynomial.eval (complexPoint q) (squaredDistancePolynomial p) =
      (dist p q : ℂ) ^ 2 := by
  simp only [squaredDistancePolynomial, map_sum, map_pow, map_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C, complexPoint]
  norm_cast
  simp [EuclideanSpace.dist_sq_eq, Real.dist_eq, sub_sq_comm]

theorem degree_squaredDistancePolynomial (p : Point d) :
    (squaredDistancePolynomial p).totalDegree ≤ 2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  have h : (MvPolynomial.X i - MvPolynomial.C ((p i : ℝ) : ℂ)).totalDegree ≤ 1 := by
    simpa using MvPolynomial.totalDegree_sub
      (MvPolynomial.X i) (MvPolynomial.C ((p i : ℝ) : ℂ))
  calc
    _ ≤ 2 * (MvPolynomial.X i - MvPolynomial.C ((p i : ℝ) : ℂ)).totalDegree :=
      MvPolynomial.totalDegree_pow _ _
    _ ≤ 2 * 1 := Nat.mul_le_mul_left _ h
    _ = 2 := rfl

def separatorFactor (p : Point d) (r : ℝ) : MvPolynomial (Fin d) ℂ :=
  (squaredDistancePolynomial p - MvPolynomial.C ((r : ℂ) ^ 2)) *
    MvPolynomial.C ((-((r : ℂ) ^ 2))⁻¹)

def physicalSeparator (P : Finset (Point d)) (p : Point d) : MvPolynomial (Fin d) ℂ :=
  ∏ r ∈ distances P, separatorFactor p r

theorem degree_separatorFactor (p : Point d) (r : ℝ) :
    (separatorFactor p r).totalDegree ≤ 2 := by
  have h := MvPolynomial.totalDegree_sub (squaredDistancePolynomial p)
    (MvPolynomial.C ((r : ℂ) ^ 2))
  simp only [MvPolynomial.totalDegree_C, max_eq_left (Nat.zero_le _)] at h
  calc
    _ ≤ (squaredDistancePolynomial p - MvPolynomial.C ((r : ℂ) ^ 2)).totalDegree +
      (MvPolynomial.C ((-((r : ℂ) ^ 2))⁻¹)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (squaredDistancePolynomial p - MvPolynomial.C ((r : ℂ) ^ 2)).totalDegree := by
      simp
    _ ≤ (squaredDistancePolynomial p).totalDegree := h
    _ ≤ 2 := degree_squaredDistancePolynomial p

theorem degree_physicalSeparator (P : Finset (Point d)) (p : Point d) :
    (physicalSeparator P p).totalDegree ≤ 2 * (distances P).card := by
  calc
    _ ≤ ∑ r ∈ distances P, (separatorFactor p r).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _ ∈ distances P, 2 := Finset.sum_le_sum fun r _ => degree_separatorFactor p r
    _ = 2 * (distances P).card := by simp [Nat.mul_comm]

theorem eval_physicalSeparator_self (P : Finset (Point d)) (p : Point d) :
    MvPolynomial.eval (complexPoint p) (physicalSeparator P p) = 1 := by
  classical
  rw [physicalSeparator, map_prod]
  apply Finset.prod_eq_one
  intro r hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (distance_pos hr)
  simp [separatorFactor, eval_squaredDistancePolynomial, hr0]

theorem eval_physicalSeparator_ne {p q : Point d} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    MvPolynomial.eval (complexPoint q) (physicalSeparator P p) = 0 := by
  classical
  rw [physicalSeparator, map_prod]
  apply Finset.prod_eq_zero (mem_distances.mpr ⟨p, hp, q, hq, hpq, rfl⟩)
  simp [separatorFactor, eval_squaredDistancePolynomial]

theorem eval_physicalSeparator {p q : Point d} (hp : p ∈ P) (hq : q ∈ P) :
    MvPolynomial.eval (complexPoint q) (physicalSeparator P p) = if p = q then 1 else 0 := by
  classical
  by_cases h : p = q
  · subst q
    simp [eval_physicalSeparator_self]
  · simp [h, eval_physicalSeparator_ne hp hq h]

def isolationPolynomials (P : Finset (Point d)) : Finset (MvPolynomial (Fin d) ℂ) := by
  classical
  exact insert (1 - ∑ p ∈ P, physicalSeparator P p)
    ((P.product Finset.univ).image (fun pj =>
      (MvPolynomial.X pj.2 - MvPolynomial.C (complexPoint pj.1 pj.2)) *
        physicalSeparator P pj.1))

theorem degree_isolationPolynomials {f : MvPolynomial (Fin d) ℂ}
    (hf : f ∈ isolationPolynomials P) :
    f.totalDegree ≤ 2 * (distances P).card + 1 := by
  classical
  rcases Finset.mem_insert.mp hf with rfl | hf
  · have hs : (∑ p ∈ P, physicalSeparator P p).totalDegree ≤ 2 * (distances P).card :=
      MvPolynomial.totalDegree_finsetSum_le fun p _ => degree_physicalSeparator P p
    have ht := MvPolynomial.totalDegree_sub (1 : MvPolynomial (Fin d) ℂ)
      (∑ p ∈ P, physicalSeparator P p)
    simp only [MvPolynomial.totalDegree_one, zero_le, max_eq_right] at ht
    exact (ht.trans hs).trans (Nat.le_add_right _ _)
  · obtain ⟨⟨p, j⟩, _, rfl⟩ := Finset.mem_image.mp hf
    have hl : (MvPolynomial.X j - MvPolynomial.C (complexPoint p j)).totalDegree ≤ 1 := by
      simpa using MvPolynomial.totalDegree_sub (MvPolynomial.X j)
        (MvPolynomial.C (complexPoint p j))
    calc
      _ ≤ (MvPolynomial.X j - MvPolynomial.C (complexPoint p j)).totalDegree +
          (physicalSeparator P p).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 + 2 * (distances P).card := Nat.add_le_add hl (degree_physicalSeparator P p)
      _ = 2 * (distances P).card + 1 := Nat.add_comm _ _

theorem isolation_zero_iff (P : Finset (Point d)) (z : Fin d → ℂ) :
    (∀ f ∈ isolationPolynomials P, MvPolynomial.eval z f = 0) ↔
      ∃ p ∈ P, complexPoint p = z := by
  classical
  constructor
  · intro hzero
    have hsum : ∑ p ∈ P, MvPolynomial.eval z (physicalSeparator P p) = 1 := by
      have hz := hzero _ (Finset.mem_insert_self _ _)
      simp only [map_sub, map_one, map_sum] at hz
      exact (sub_eq_zero.mp hz).symm
    have hsum0 : ∑ p ∈ P, MvPolynomial.eval z (physicalSeparator P p) ≠ 0 := by
      rw [hsum]
      exact one_ne_zero
    obtain ⟨p, hp, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum0
    refine ⟨p, hp, ?_⟩
    funext j
    have hj : (MvPolynomial.X j - MvPolynomial.C (complexPoint p j)) *
        physicalSeparator P p ∈ isolationPolynomials P := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨(p, j), Finset.mem_product.mpr ⟨hp, Finset.mem_univ j⟩, rfl⟩
    have hz := hzero _ hj
    simp only [map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at hz
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hs)).symm
  · rintro ⟨p, hp, rfl⟩ f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rw [map_sub, map_one, map_sum]
      have hsum : ∑ q ∈ P, MvPolynomial.eval (complexPoint p) (physicalSeparator P q) = 1 := by
        rw [Finset.sum_eq_single p]
        · exact eval_physicalSeparator_self P p
        · intro q hq hqp
          exact eval_physicalSeparator_ne hq hp hqp
        · exact fun h => (h hp).elim
      simp [hsum]
    · obtain ⟨⟨q, j⟩, hqj, rfl⟩ := Finset.mem_image.mp hf
      have hq : q ∈ P := (Finset.mem_product.mp hqj).1
      by_cases hqp : q = p
      · subst q
        simp
      · simp [eval_physicalSeparator_ne hq hp hqp]

theorem linearIndependent_physicalSeparator (P : Finset (Point d)) :
    LinearIndependent ℂ (fun p : P => physicalSeparator P p) := by
  classical
  rw [linearIndependent_iff']
  intro s a hs p hp
  have h := congrArg (MvPolynomial.eval (complexPoint (p : Point d))) hs
  simp only [map_sum, MvPolynomial.smul_eval, map_zero] at h
  have heq : ∑ q ∈ s, a q *
      MvPolynomial.eval (complexPoint (p : Point d)) (physicalSeparator P q) = a p := by
    rw [Finset.sum_eq_single p]
    · simp [eval_physicalSeparator_self]
    · intro q _ hqp
      have hqp' : (q : Point d) ≠ (p : Point d) := fun h => hqp (Subtype.ext h)
      simp [eval_physicalSeparator_ne q.property p.property hqp']
    · exact fun h => (h hp).elim
  exact heq.symm.trans h

theorem finrank_restrictDegree (d L : ℕ) :
    Module.finrank ℂ (MvPolynomial.restrictDegree (Fin d) ℂ L) = (L + 1) ^ d := by
  classical
  let e : {n : Fin d →₀ ℕ // ∀ i, n i ≤ L} ≃ (Fin d → Fin (L + 1)) :=
    { toFun := fun n i => ⟨n.1 i, Nat.lt_succ_iff.mpr (n.2 i)⟩
      invFun := fun n => ⟨Finsupp.equivFunOnFinite.symm (fun i => (n i).val),
        fun i => by simpa using Nat.lt_succ_iff.mp (n i).isLt⟩
      left_inv := fun n => by
        apply Subtype.ext
        ext i
        simp
      right_inv := fun n => by
        funext i
        apply Fin.ext
        simp }
  let : Fintype {n : Fin d →₀ ℕ // ∀ i, n i ≤ L} := Fintype.ofEquiv _ e.symm
  calc
    _ = Fintype.card {n : Fin d →₀ ℕ // ∀ i, n i ≤ L} :=
      Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℂ _)
    _ = Fintype.card (Fin d → Fin (L + 1)) := Fintype.card_congr e
    _ = (L + 1) ^ d := by simp

theorem elementary_card_bound (P : Finset (Point d)) :
    P.card ≤ (2 * (distances P).card + 1) ^ d := by
  classical
  let V := MvPolynomial.restrictDegree (Fin d) ℂ (2 * (distances P).card)
  have hv (p : P) : physicalSeparator P p ∈ V :=
    MvPolynomial.restrictTotalDegree_le_restrictDegree _ _ _
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr (degree_physicalSeparator P p))
  let v : P → V := fun p => ⟨physicalSeparator P p, hv p⟩
  have hlin : LinearIndependent ℂ v :=
    LinearIndependent.of_comp V.subtype (linearIndependent_physicalSeparator P)
  have hcard := hlin.fintype_card_le_finrank
  simpa [V, finrank_restrictDegree] using hcard

def lengthFiber (S : Finset (Point d × Point d)) (r : ℝ) : Finset (Point d × Point d) := by
  classical
  exact S.filter (fun pq => dist pq.1 pq.2 = r)

def equalLengthPairs (S : Finset (Point d × Point d)) :
    Finset ((Point d × Point d) × (Point d × Point d)) := by
  classical
  exact (S.product S).filter (fun ab => dist ab.1.1 ab.1.2 = dist ab.2.1 ab.2.2)

theorem sum_lengthFiber_card (S : Finset (Point d × Point d)) (hS : S ⊆ P.offDiag) :
    ∑ r ∈ distances P, (lengthFiber S r).card = S.card := by
  classical
  change ∑ r ∈ distances P, (S.filter (fun pq => dist pq.1 pq.2 = r)).card = S.card
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro pq hpq
  exact Finset.mem_image.mpr ⟨pq, hS hpq, rfl⟩

theorem equalLengthPairs_card (S : Finset (Point d × Point d)) (hS : S ⊆ P.offDiag) :
    (equalLengthPairs S).card = ∑ r ∈ distances P, (lengthFiber S r).card ^ 2 := by
  classical
  have hfib (r : ℝ) :
      ((equalLengthPairs S).filter (fun ab => dist ab.1.1 ab.1.2 = r)) =
        (lengthFiber S r).product (lengthFiber S r) := by
    ext ab
    simp only [equalLengthPairs, lengthFiber, Finset.mem_filter]
    aesop
  have hcover : ((equalLengthPairs S).filter
      (fun ab => dist ab.1.1 ab.1.2 ∈ distances P)) = equalLengthPairs S := by
    apply Finset.filter_eq_self.mpr
    intro ab hab
    have ha : ab.1 ∈ S := (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1
    exact Finset.mem_image.mpr ⟨ab.1, hS ha, rfl⟩
  have hsum := Finset.sum_card_fiberwise_eq_card_filter (equalLengthPairs S)
    (distances P) (fun ab => dist ab.1.1 ab.1.2)
  rw [hcover] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro r _
  rw [hfib r]
  exact (Finset.card_product _ _).trans (pow_two _).symm

theorem equalLengthPairs_lower_bound (S : Finset (Point d × Point d)) (hS : S ⊆ P.offDiag) :
    S.card ^ 2 ≤ (distances P).card * (equalLengthPairs S).card := by
  classical
  have h := Finset.sum_mul_sq_le_sq_mul_sq (distances P)
    (fun _ => (1 : ℕ)) (fun r => (lengthFiber S r).card)
  simpa only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one,
    sum_lengthFiber_card S hS, ← equalLengthPairs_card S hS] using h

theorem equalLengthPairs_lower_bound_real (S : Finset (Point d × Point d)) (hS : S ⊆ P.offDiag) :
    (S.card : ℝ) ^ 2 / (1 + ((distances P).card : ℝ)) ≤ (equalLengthPairs S).card := by
  have h : (S.card : ℝ) ^ 2 ≤ (distances P).card * (equalLengthPairs S).card := by
    exact_mod_cast equalLengthPairs_lower_bound S hS
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + ((distances P).card : ℝ))).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) (equalLengthPairs S).card]

end ErdosDistinctDistances

end

end OAI
