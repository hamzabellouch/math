import OAI.InformationTheory.QuantumCircuit.Spectral

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

section NormAlgebra
variable {A : Type*} [CStarAlgebra A]

lemma norm_unitary_conjugate {U : A} (hU : U ∈ unitary A) (B : A) :
    ‖U * B * star U‖ = ‖B‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU), CStarRing.norm_mem_unitary_mul _ hU]

lemma conjugate_projection {U B : A} (hU : U ∈ unitary A) (hB : IsStarProjection B) :
    IsStarProjection (U * B * star U) := by
  rw [isStarProjection_iff']
  constructor
  · calc
      _ = U * (B * B) * star U := by
        simp only [mul_assoc, ← mul_assoc (star U) U, Unitary.star_mul_self_of_mem hU, one_mul]
      _ = _ := by rw [hB.isIdempotentElem.eq]
  · simp only [star_mul, star_star, hB.isSelfAdjoint.star_eq, mul_assoc]

lemma projection_transition_square (H P Q X : A)
    (hH : IsStarProjection H) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ‖H * Q * P‖^2 ≤ ‖H * X * P‖ + ‖(Q-X) * P * Q‖ := by
  have hid : (H*Q*P) * star (H*Q*P) = H*Q*P*Q*H := by
    simp only [star_mul, hH.isSelfAdjoint.star_eq, hP.isSelfAdjoint.star_eq,
      hQ.isSelfAdjoint.star_eq]
    calc
      _ = H * Q * (P*P) * Q * H := by simp only [mul_assoc]
      _ = _ := by rw [hP.isIdempotentElem.eq]
  have heq : H*Q*P*Q*H = (H*X*P)*Q*H + H*((Q-X)*P*Q)*H := by noncomm_ring
  calc
    ‖H*Q*P‖^2 = ‖(H*Q*P) * star (H*Q*P)‖ := by rw [CStarRing.norm_self_mul_star]; ring
    _ = ‖(H*X*P)*Q*H + H*((Q-X)*P*Q)*H‖ := by rw [hid,heq]
    _ ≤ ‖(H*X*P)*Q*H‖ + ‖H*((Q-X)*P*Q)*H‖ := norm_add_le _ _
    _ ≤ _ := by
      apply add_le_add
      · exact (norm_mul_le_left _ _ (IsStarProjection.norm_le _ hH)).trans
          (norm_mul_le_left _ _ (IsStarProjection.norm_le _ hQ))
      · exact (norm_mul_le_left _ _ (IsStarProjection.norm_le _ hH)).trans
          (norm_mul_le_right _ _ (IsStarProjection.norm_le _ hH))

lemma norm_split_bound (E W P Q : A) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖E*P*Q‖ ≤ ‖E*(1-W)‖ + ‖E‖*‖W*P*Q‖ := by
  have heq : E*P*Q = E*(1-W)*P*Q + E*(W*P*Q) := by noncomm_ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_mul_le_left _ _ hQ).trans (norm_mul_le_left _ _ hP)) (norm_mul_le _ _))
end NormAlgebra


lemma sum_powers_bound (N K : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range K, N^k ≤ (N+1)^K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hpow : N^K ≤ (N+1)^K := Nat.pow_le_pow_left (by omega) _
    have hmul : (N+1)^K ≤ (N+1)^K*N := by
      simpa only [mul_one] using Nat.mul_le_mul_left ((N+1)^K) hN
    nlinarith only [ih, hpow, hmul]

lemma low_patterns_card {N : ℕ} (S : Finset (Fin N)) {r : ℝ} (hN : 1 ≤ N) :
    (S.powerset.filter (fun F => (F.card:ℝ) < r)).card ≤ (N+1)^(⌈r⌉₊+1) := by
  classical
  have hsub : S.powerset.filter (fun F => (F.card:ℝ) < r) ⊆
      (Finset.range (⌈r⌉₊+1)).biUnion (fun k => S.powersetCard k) := by
    intro F hF
    obtain ⟨hFS, hFr⟩ := Finset.mem_filter.mp hF
    refine Finset.mem_biUnion.mpr ⟨F.card, ?_, Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hFS,rfl⟩⟩
    rw [Finset.mem_range]
    have h : (F.card:ℝ) ≤ ⌈r⌉₊ := hFr.le.trans (Nat.le_ceil r)
    have : F.card ≤ ⌈r⌉₊ := by exact_mod_cast h
    omega
  calc
    _ ≤ ((Finset.range (⌈r⌉₊+1)).biUnion (fun k => S.powersetCard k)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (⌈r⌉₊+1), (S.powersetCard k).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (⌈r⌉₊+1), N^k := by
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by simpa using Finset.card_le_univ S) _)
    _ ≤ _ := sum_powers_bound N _ hN

lemma list_disjoint_hits_length {ι κ : Type*} [DecidableEq κ]
    (f : ι → Finset κ) (l : List ι) (hl : l.Pairwise (fun a b => Disjoint (f a) (f b)))
    (S : Finset κ) (hS : ∀ a ∈ l, (f a ∩ S).Nonempty) : l.length ≤ S.card := by
  induction l generalizing S with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    obtain ⟨i,hi⟩ := hS a (List.mem_cons_self ..)
    obtain ⟨hia,hiS⟩ := Finset.mem_inter.mp hi
    have hh : ∀ b ∈ l, (f b ∩ S.erase i).Nonempty := by
      intro b hb
      obtain ⟨j,hj⟩ := hS b (List.mem_cons_of_mem _ hb)
      obtain ⟨hjb,hjS⟩ := Finset.mem_inter.mp hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact Finset.disjoint_left.mp (ha b hb) hia hjb
      exact ⟨j,Finset.mem_inter.mpr ⟨hjb,Finset.mem_erase.mpr ⟨hji,hjS⟩⟩⟩
    have h := ih hl (S.erase i) hh
    simp only [List.length_cons]
    have hc := Finset.card_erase_add_one hiS
    omega

/-- Scalar list estimates retain multiplicities, including the ordered monomials. -/
lemma norm_list_smul_sum {ι A : Type*} [SeminormedAddCommGroup A] [NormedSpace ℝ A]
    (l : List ι) (c : ι → ℝ) (f : ι → A) (δ : ℝ) (hf : ∀ i ∈ l, ‖f i‖ ≤ δ) :
    ‖(l.map (fun i => c i • f i)).sum‖ ≤ (l.map (fun i => |c i|)).sum * δ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf i (List.mem_cons_self ..)) (abs_nonneg _)
    · exact ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))


lemma Count.low_propagation_bound {N : ℕ} (M : Count N) (B : Operator N)
    {r q R δ : ℝ} (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hrq : q + r ≤ R)
    (hB : ∀ K : Count N, ‖K.high q * B * K.zero‖ ≤ δ) :
    ‖M.high R * B * M.low r‖ ≤ (N+1:ℝ)^(⌈r⌉₊+1) * δ := by
  classical
  rw [M.low_eq_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ F ∈ M.support.powerset.filter (fun F => (F.card:ℝ) < r), δ := by
      apply Finset.sum_le_sum
      intro F hF
      obtain ⟨hFs, hFr⟩ := Finset.mem_filter.mp hF
      exact (M.high_flip_norm F (Finset.mem_powerset.mp hFs)
        (by linarith) B).trans (hB (M.flip F))
    _ = ((M.support.powerset.filter (fun F => (F.card:ℝ) < r)).card:ℝ)*δ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast low_patterns_card M.support (r:=r) hN) hδ

lemma norm_mul_le_one {A : Type*} [NormedRing A] {x y : A}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x*y‖ ≤ 1 :=
  (norm_mul_le_left _ _ hy).trans hx

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

lemma three_factor_transition (H P H₁ H₂ B₁ B₂ B₃ : A) {δ : ℝ}
    (hH : ‖H‖ ≤ 1) (hP : ‖P‖ ≤ 1)
    (hE₁ : ‖1-H₁‖ ≤ 1)
    (hB₁ : ‖B₁‖ ≤ 1) (hB₂ : ‖B₂‖ ≤ 1) (hB₃ : ‖B₃‖ ≤ 1)
    (h₁ : ‖H₁*B₃*P‖ ≤ δ) (h₂ : ‖H₂*B₂*(1-H₁)‖ ≤ δ)
    (h₃ : ‖H*B₁*(1-H₂)‖ ≤ δ) : ‖H*B₁*B₂*B₃*P‖ ≤ 3*δ := by
  have heq : H*B₁*B₂*B₃*P = (H*B₁*B₂)*(H₁*B₃*P) +
      (H*B₁)*(H₂*B₂*(1-H₁))*(B₃*P) +
      (H*B₁*(1-H₂))*(B₂*(1-H₁)*B₃*P) := by noncomm_ring
  have ht₁ : ‖(H*B₁*B₂)*(H₁*B₃*P)‖ ≤ δ :=
    (norm_mul_le_right _ _ (norm_mul_le_one (norm_mul_le_one hH hB₁) hB₂)).trans h₁
  have ht₂ : ‖(H*B₁)*(H₂*B₂*(1-H₁))*(B₃*P)‖ ≤ δ :=
    ((norm_mul_le_left _ _ (norm_mul_le_one hB₃ hP)).trans
      (norm_mul_le_right _ _ (norm_mul_le_one hH hB₁))).trans h₂
  have ht₃ : ‖(H*B₁*(1-H₂))*(B₂*(1-H₁)*B₃*P)‖ ≤ δ :=
    (norm_mul_le_left _ _ (norm_mul_le_one (norm_mul_le_one
      (norm_mul_le_one hB₂ hE₁) hB₃) hP)).trans h₃
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    (by linarith only [ht₁,ht₂,ht₃]))
end ThreeFactors


section Conjugation
variable {A : Type*} [CStarAlgebra A]

def conjugate (U B : A) : A := U*B*star U

lemma conjugate_comp (U V B : A) : conjugate (U*V) B = conjugate U (conjugate V B) := by
  simp only [conjugate,star_mul,mul_assoc]

lemma conjugate_mul {U : A} (hU : U ∈ unitary A) (B C : A) :
    conjugate U (B*C) = conjugate U B * conjugate U C := by
  simp only [conjugate,mul_assoc,← mul_assoc (star U) U,Unitary.star_mul_self_of_mem hU,one_mul]

lemma conjugate_star (U B : A) : conjugate U (star B) = star (conjugate U B) := by
  simp only [conjugate,star_mul,star_star,mul_assoc]

lemma conjugate_sub (U B C : A) : conjugate U (B-C) = conjugate U B - conjugate U C := by
  simp only [conjugate,mul_sub,sub_mul]

lemma conjugate_one {U : A} (hU : U ∈ unitary A) : conjugate U 1 = 1 := by
  simp only [conjugate,mul_one,Unitary.mul_star_self_of_mem hU]

lemma conjugate_smul (U B : A) (r : ℝ) : conjugate U (r • B) = r • conjugate U B := by
  simp only [conjugate,mul_smul_comm,smul_mul_assoc]

lemma conjugate_list_sum {ι : Type*} (U : A) (l : List ι) (f : ι → A) :
    conjugate U (l.map f).sum = (l.map (fun i => conjugate U (f i))).sum := by
  simp only [conjugate,← List.sum_map_mul_left,← List.sum_map_mul_right]

lemma conjugate_fixed {U B : A} (hU : U ∈ unitary A) (h : Commute U B) :
    conjugate U B = B := by
  rw [conjugate,h.eq,mul_assoc,Unitary.mul_star_self_of_mem hU,mul_one]

lemma list_conjugate_filter {ι : Type*} (f : ι → A) (l : List ι) (p : ι → Bool) (B : A)
    (hl : l.Pairwise (fun a b => Commute (f a) (f b)))
    (hu : ∀ a ∈ l, f a ∈ unitary A)
    (hd : ∀ a ∈ l, p a = false → Commute (f a) B) :
    conjugate (l.map f).prod B = conjugate ((l.filter p).map f).prod B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    have hu' : ∀ b ∈ l, f b ∈ unitary A := fun b hb => hu b (List.mem_cons_of_mem _ hb)
    have hd' : ∀ b ∈ l, p b = false → Commute (f b) B := fun b hb => hd b (List.mem_cons_of_mem _ hb)
    have hc : Commute (f a) (l.map f).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
      exact ha b hb
    cases hpa : p a with
    | false =>
      simp only [List.map_cons,List.prod_cons,List.filter_cons,hpa,Bool.false_eq_true,ite_false]
      rw [hc.eq,conjugate_comp,conjugate_fixed (hu a (List.mem_cons_self ..))
        (hd a (List.mem_cons_self ..) hpa)]
      exact ih hl hu' hd'
    | true =>
      simp only [List.map_cons,List.prod_cons,List.filter_cons,hpa,ite_true,List.map_cons,List.prod_cons]
      rw [conjugate_comp,conjugate_comp,ih hl hu' hd']
end Conjugation

end QAC

end

end OAI
