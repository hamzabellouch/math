import OAI.NumberTheory.JointDickman.Arithmetic.PrimePairAllCutoffs

namespace OAI

/-! # Prime-pair correlations grouped by their difference -/
namespace JointDickman
open Finset

lemma even_kernel_pair_sum (P : Finset ℕ) (K : ℤ → ℝ)
    (hK : ∀ h, K (-h) = K h) :
    (∑ p ∈ P, ∑ r ∈ P, K ((r:ℤ)-p)) =
      (P.card:ℝ)*K 0 + 2*(∑ p ∈ P, ∑ r ∈ P, if p < r then K ((r:ℤ)-p) else 0) := by
  classical
  have hpoint (p r : ℕ) : K ((r:ℤ)-p) =
      (if p = r then K 0 else 0) +
      (if p < r then K ((r:ℤ)-p) else 0) +
      (if r < p then K ((r:ℤ)-p) else 0) := by
    rcases lt_trichotomy p r with h | h | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le]
    · subst r
      simp
    · simp [h,ne_of_gt h,not_lt_of_ge h.le]
  have hsym : (∑ p ∈ P, ∑ r ∈ P, if r < p then K ((r:ℤ)-p) else 0) =
      ∑ p ∈ P, ∑ r ∈ P, if p < r then K ((r:ℤ)-p) else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro r hr
    rw [show (p:ℤ)-r = -((r:ℤ)-p) by ring,hK]
  calc
    _ = ∑ p ∈ P, ∑ r ∈ P,
        ((if p = r then K 0 else 0) +
        (if p < r then K ((r:ℤ)-p) else 0) +
        (if r < p then K ((r:ℤ)-p) else 0)) := by
      exact sum_congr rfl (fun p _ => sum_congr rfl (fun r _ => hpoint p r))
    _ = _ := by
      simp only [sum_add_distrib]
      rw [hsym]
      simp
      ring

lemma prime_positive_difference_sum_le (P : Finset ℕ) (Q X : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (hspan : ∀ p ∈ P, ∀ r ∈ P, r-p ≤ X) (K : ℕ → ℝ) (hK : ∀ h, 0 ≤ K h) :
    (∑ p ∈ P, ∑ r ∈ P, if p < r then K (r-p) else 0) ≤
      ∑ h ∈ Icc 1 X, (primePairCount Q h:ℝ)*K h := by
  classical
  let T := (P ×ˢ P).filter (fun pr => pr.1 < pr.2)
  let e := fun pr : ℕ × ℕ => (pr.2-pr.1,pr.1)
  let g := fun hp : ℕ × ℕ => if hp.2.Prime ∧ (hp.2+hp.1).Prime then K hp.1 else 0
  have hT : (∑ p ∈ P, ∑ r ∈ P, if p < r then K (r-p) else 0) =
      ∑ pr ∈ T, K (pr.2-pr.1) := by
    simp only [T,sum_filter,sum_product]
  have hi : Set.InjOn e T := by
    intro pr hpr qr hqr he
    change pr ∈ T at hpr
    change qr ∈ T at hqr
    obtain ⟨hp,hr,hlt⟩ := by simpa only [T,mem_filter,mem_product,and_assoc] using hpr
    obtain ⟨hq,hs,hlt'⟩ := by simpa only [T,mem_filter,mem_product,and_assoc] using hqr
    dsimp [e] at he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    exact Prod.ext h2 (by omega)
  have himage : T.image e ⊆ (Icc 1 X) ×ˢ (Ico 0 (Q+1)) := by
    intro hp hhp
    obtain ⟨⟨p,r⟩,hpr,rfl⟩ := mem_image.mp hhp
    obtain ⟨hp,hr,hlt⟩ := by simpa only [T,mem_filter,mem_product,and_assoc] using hpr
    obtain ⟨_,hpQ⟩ := hP p hp
    obtain ⟨_,hrQ⟩ := hP r hr
    have hd := hspan p hp r hr
    simp only [e,mem_product,mem_Icc,mem_Ico]
    omega
  have hterm (pr : ℕ × ℕ) (hpr : pr ∈ T) : K (pr.2-pr.1) ≤ g (e pr) := by
    obtain ⟨hp,hr,hlt⟩ := by simpa only [T,mem_filter,mem_product,and_assoc] using hpr
    have heq : pr.1+(pr.2-pr.1) = pr.2 := Nat.add_sub_of_le hlt.le
    simp [g,e,heq,(hP _ hp).1,(hP _ hr).1]
  rw [hT]
  apply (sum_le_sum_of_injOn e hi himage hterm (fun hp _ _ => by
    dsimp [g]; split_ifs <;> simp_all)).trans_eq
  rw [sum_product]
  apply sum_congr rfl
  intro h hh
  change (∑ p ∈ Ico 0 (Q+1), if p.Prime ∧ (p+h).Prime then K h else 0) = _
  rw [←sum_filter]
  simp [primePairCount]

/-- An even nonnegative prime correlation kernel is bounded by its diagonal
and the explicit totient-weighted sum over positive differences. -/
theorem prime_even_kernel_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (Q X : ℕ) (P : Finset ℕ), 2 ≤ Q →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) →
    (∀ p ∈ P, ∀ r ∈ P, r-p ≤ X) → ∀ K : ℤ → ℝ,
    (∀ h, 0 ≤ K h) → (∀ h, K (-h) = K h) →
    (∑ p ∈ P, ∑ r ∈ P, K ((r:ℤ)-p)) ≤
      (P.card:ℝ)*K 0 + 2*C*(Q:ℝ)/(Real.log Q)^2 *
        ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h := by
  obtain ⟨C,hC,hbound⟩ := primePair_upper_sieve
  refine ⟨C,hC,?_⟩
  intro Q X P hQ hP hspan K hK hsym
  rw [even_kernel_pair_sum P K hsym]
  have hcast (p r : ℕ) (h : p < r) : ((r-p:ℕ):ℤ) = (r:ℤ)-p :=
    Int.ofNat_sub h.le
  have hupper := prime_positive_difference_sum_le P Q X hP hspan
    (fun h => K h) (fun h => hK h)
  have heq : (∑ p ∈ P, ∑ r ∈ P, if p < r then K ((r-p:ℕ):ℤ) else 0) =
      ∑ p ∈ P, ∑ r ∈ P, if p < r then K ((r:ℤ)-p) else 0 := by
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro r hr
    split_ifs with h
    · rw [hcast p r h]
    · rfl
  rw [heq] at hupper
  have hweighted : (∑ h ∈ Icc 1 X, (primePairCount Q h:ℝ)*K h) ≤
      C*(Q:ℝ)/(Real.log Q)^2 * ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h := by
    rw [mul_sum]
    apply sum_le_sum
    intro h hh
    have hhpos : 0 < h := (mem_Icc.mp hh).1
    have hb := mul_le_mul_of_nonneg_right (hbound Q h hQ hhpos) (hK h)
    convert hb using 1
    ring
  have hs := hupper.trans hweighted
  calc
    _ ≤ (P.card:ℝ)*K 0 + 2*(C*(Q:ℝ)/(Real.log Q)^2 *
        ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2))
    _ = _ := by ring

end JointDickman

end OAI
