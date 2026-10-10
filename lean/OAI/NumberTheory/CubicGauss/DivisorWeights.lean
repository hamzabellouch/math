import Mathlib
import OAI.NumberTheory.CubicGauss.Cutoffs

namespace OAI

/-! Squarefree divisors and Möbius-weighted coprimality decompositions. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma primary_prime_prod_coprime (S T : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (hT : ∀ q ∈ T, primaryPrime q)
    (hd : Disjoint S T) : IsCoprime (∏ p ∈ S,p) (∏ q ∈ T,q) := by
  apply IsCoprime.prod_left
  intro p hp
  apply IsCoprime.prod_right
  intro q hq
  exact primaryPrimes_isCoprime (hS p hp) (hT q hq)
    (fun he => (Finset.disjoint_left.mp hd hp) (he ▸ hq))

lemma primary_prime_prod_dvd_iff (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (m : Eisenstein) :
    (∏ p ∈ S,p) ∣ m ↔ ∀ p ∈ S,p ∣ m := by
  refine ⟨fun h p hp => dvd_trans (Finset.dvd_prod_of_mem _ hp) h,?_⟩
  apply Finset.prod_dvd_of_coprime
  intro p hp q hq hpq
  exact primaryPrimes_isCoprime (hS p hp) (hS q hq) hpq

lemma common_squarefree_split {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b) :
    ∃ k x y : Eisenstein, primary k ∧ primary x ∧ primary y ∧
      Squarefree k ∧ Squarefree x ∧ Squarefree y ∧
      IsCoprime k x ∧ IsCoprime k y ∧ IsCoprime x y ∧ a=k*x ∧ b=k*y := by
  let S := primaryPrimeFactors a
  let T := primaryPrimeFactors b
  let k := ∏ p ∈ S ∩ T,p
  let x := ∏ p ∈ S \ T,p
  let y := ∏ p ∈ T \ S,p
  have hS : ∀ p ∈ S,primaryPrime p := fun _ hp => (primaryPrimeFactor_spec ha hp).1
  have hT : ∀ p ∈ T,primaryPrime p := fun _ hp => (primaryPrimeFactor_spec hb hp).1
  have hK : ∀ p ∈ S ∩ T,primaryPrime p := fun _ hp => hS _ (Finset.mem_inter.mp hp).1
  have hX : ∀ p ∈ S \ T,primaryPrime p := fun _ hp => hS _ (Finset.mem_sdiff.mp hp).1
  have hY : ∀ p ∈ T \ S,primaryPrime p := fun _ hp => hT _ (Finset.mem_sdiff.mp hp).1
  have hek : a=k*x := by
    rw [← primaryPrimeFactors_prod ha hsa]
    exact (Finset.prod_inter_mul_prod_sdiff S T (fun p => p)).symm
  have heb : b=k*y := by
    rw [← primaryPrimeFactors_prod hb hsb]
    dsimp only [k,y]
    rw [Finset.inter_comm]
    exact (Finset.prod_inter_mul_prod_sdiff T S (fun p => p)).symm
  have hsa' : Squarefree (k*x) := hek ▸ hsa
  have hsb' : Squarefree (k*y) := heb ▸ hsb
  refine ⟨k,x,y,primary_finset_prod _ _ (fun _ hp => (hK _ hp).1),
    primary_finset_prod _ _ (fun _ hp => (hX _ hp).1),
    primary_finset_prod _ _ (fun _ hp => (hY _ hp).1),hsa'.of_mul_left,hsa'.of_mul_right,
    hsb'.of_mul_right,isRelPrime_iff_isCoprime.mp (IsRelPrime.of_squarefree_mul hsa'),
    isRelPrime_iff_isCoprime.mp (IsRelPrime.of_squarefree_mul hsb'),?_,hek,heb⟩
  apply primary_prime_prod_coprime _ _ hX hY
  exact Finset.disjoint_left.mpr (fun p hp hq => (Finset.mem_sdiff.mp hp).2
    (Finset.mem_sdiff.mp hq).1)

lemma coprime_indicator_prod {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (m : Eisenstein) :
    (if IsCoprime n m then (1:ℂ) else 0) =
      ∏ p ∈ primaryPrimeFactors n, (1 - if p ∣ m then (1:ℂ) else 0) := by
  have he : IsCoprime n m ↔ ∀ p ∈ primaryPrimeFactors n,¬p ∣ m := by
    conv_lhs => rw [← primaryPrimeFactors_prod hn hs]
    rw [IsCoprime.prod_left_iff]
    exact forall₂_congr (fun p hp => (primaryPrimeFactor_spec hn hp).1.2.coprime_iff_not_dvd)
  by_cases h : IsCoprime n m
  · rw [ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro p hp
    rw [ite_eq_right ((he.mp h) p hp),sub_zero]
  · rw [ite_eq_right h]
    obtain ⟨p,hp,hd⟩ := by simpa only [not_forall,not_not,exists_prop] using (not_congr he).mp h
    symm
    apply Finset.prod_eq_zero hp
    simp [hd]

lemma dvd_indicator_prod (S : Finset Eisenstein) (hS : ∀ p ∈ S,primaryPrime p)
    (m : Eisenstein) :
    (∏ p ∈ S,if p ∣ m then (1:ℂ) else 0) =
      if (∏ p ∈ S,p) ∣ m then 1 else 0 := by
  rw [primary_prime_prod_dvd_iff S hS]
  split_ifs with h
  · exact Finset.prod_eq_one (fun p hp => ite_eq_left (h p hp))
  · obtain ⟨p,hp,hd⟩ := by simpa only [not_forall,exists_prop] using h
    exact Finset.prod_eq_zero hp (ite_eq_right hd)

theorem coprime_indicator_moebius {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (m : Eisenstein) :
    (if IsCoprime n m then (1:ℂ) else 0) =
      ∑ S ∈ (primaryPrimeFactors n).powerset,
        (idealMoebius (∏ p ∈ S,p) : ℂ) *
          (if (∏ p ∈ S,p) ∣ m then 1 else 0) := by
  rw [coprime_indicator_prod hn hs]
  have he := Finset.prod_add (fun p : Eisenstein => -(if p ∣ m then (1:ℂ) else 0))
    (fun _ => (1:ℂ)) (primaryPrimeFactors n)
  simp only [Finset.prod_const_one,mul_one,← sub_eq_neg_add] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro S hS
  have hSp : ∀ p ∈ S,primaryPrime p := fun p hp =>
    (primaryPrimeFactor_spec hn ((Finset.mem_powerset.mp hS) hp)).1
  rw [Finset.prod_neg,dvd_indicator_prod S hSp,idealMoebius_prod_primaryPrimes S hSp]
  push_cast
  rfl

lemma mem_primaryPrimeFactors_iff {n p : Eisenstein} (hn : primary n) :
    p ∈ primaryPrimeFactors n ↔ primaryPrime p ∧ p ∣ n := by
  refine ⟨primaryPrimeFactor_spec hn, fun ⟨hp,hd⟩ => ?_⟩
  obtain ⟨q,hq,hqp⟩ := exists_mem_normalizedFactors_of_dvd (primary_ne_zero hn) hp.2.irreducible hd
  apply Finset.mem_image.mpr
  refine ⟨q,Multiset.mem_toFinset.mpr hq,?_⟩
  apply primary_associated_eq
    (primaryNormalize_primary (unit_residue_of_dvd_primary hn (dvd_of_mem_normalizedFactors hq)))
    hp.1
  exact (primaryNormalize_associated q).symm.trans hqp.symm

def primaryDivisors (n : Eisenstein) : Finset Eisenstein :=
  (nonzeroNormBall (norm n)).filter (fun d => primary d ∧ d ∣ n)

lemma mem_primaryDivisors {n d : Eisenstein} (hn : n ≠ 0) :
    d ∈ primaryDivisors n ↔ primary d ∧ d ∣ n := by
  simp only [primaryDivisors,Finset.mem_filter,mem_nonzeroNormBall]
  exact ⟨fun h => h.2,fun h => ⟨⟨norm_le_of_dvd hn h.2,primary_ne_zero h.1⟩,h⟩⟩

lemma primaryDivisors_subset_products {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    primaryDivisors n ⊆ (primaryPrimeFactors n).powerset.image (fun s => ∏ p ∈ s, p) := by
  intro d hd
  obtain ⟨hdp,hdd⟩ := (mem_primaryDivisors (primary_ne_zero hn)).mp hd
  apply Finset.mem_image.mpr
  refine ⟨primaryPrimeFactors d,Finset.mem_powerset.mpr ?_,
    primaryPrimeFactors_prod hdp (hs.squarefree_of_dvd hdd)⟩
  intro p hp
  have hp := (mem_primaryPrimeFactors_iff hdp).mp hp
  exact (mem_primaryPrimeFactors_iff hn).mpr ⟨hp.1,dvd_trans hp.2 hdd⟩

lemma primaryDivisors_card_le {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    (primaryDivisors n).card ≤ 2^(primaryPrimeFactors n).card := by
  exact (Finset.card_le_card (primaryDivisors_subset_products hn hs)).trans
    (Finset.card_image_le.trans (by rw [Finset.card_powerset]))

lemma norm_prod_rpow {ι : Type*} (s : Finset ι) (f : ι → Eisenstein) (ε : ℝ) :
    ∏ i ∈ s, (norm (f i))^ε = (norm (∏ i ∈ s,f i))^ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, norm_mul_eq,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ih]

theorem squarefree_divisor_power_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : Eisenstein, primary n → Squarefree n →
      (2:ℝ)^(primaryPrimeFactors n).card ≤ C * (norm n)^ε := by
  let small := nonzeroNormBall ((2:ℝ)^ε⁻¹)
  refine ⟨(2:ℝ)^small.card,by positivity,?_⟩
  intro n hn hs
  let S := primaryPrimeFactors n
  have hfactor (p : Eisenstein) (hp : p ∈ S) :
      (2:ℝ) ≤ (if p ∈ small then 2 else 1) * (norm p)^ε := by
    have hp0 := (primaryPrimeFactor_spec hn hp).1.2.ne_zero
    by_cases hps : p ∈ small
    · rw [ite_eq_left hps]
      have hh : 1 ≤ (norm p)^ε := Real.one_le_rpow (one_le_norm hp0) hε.le
      linarith
    · rw [ite_eq_right hps,one_mul]
      apply (Real.rpow_inv_le_iff_of_pos (by norm_num) (norm_nonneg p) hε).mp
      have hpn : ¬norm p ≤ (2:ℝ)^ε⁻¹ := by
        intro h
        exact hps (mem_nonzeroNormBall.mpr ⟨h,hp0⟩)
      exact (lt_of_not_ge hpn).le
  have hprod := Finset.prod_le_prod₀ (fun _ _ => by norm_num : ∀ a ∈ S, (0:ℝ) ≤ 2) hfactor
  rw [Finset.prod_const,Finset.prod_mul_distrib,norm_prod_rpow,
    primaryPrimeFactors_prod hn hs] at hprod
  have hc : (∏ p ∈ S, if p ∈ small then (2:ℝ) else 1) ≤ (2:ℝ)^small.card := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num)
    exact Finset.card_le_card (by intro p hp; exact (Finset.mem_filter.mp hp).2)
  exact hprod.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (norm_nonneg n) ε))

lemma primary_prime_dvd_prod_iff {p : Eisenstein} (hp : primaryPrime p)
    (S : Finset Eisenstein) (hS : ∀ q ∈ S,primaryPrime q) :
    p ∣ ∏ q ∈ S,q ↔ p ∈ S := by
  rw [hp.2.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q,hq,hd⟩
    have he : p=q := primary_associated_eq hp.1 (hS q hq).1
      ((hp.2.dvd_prime_iff_associated (hS q hq).2).mp hd)
    exact he ▸ hq
  · intro h; exact ⟨p,h,dvd_refl p⟩

lemma primaryPrimeFactors_prime_prod (S : Finset Eisenstein)
    (hS : ∀ p ∈ S,primaryPrime p) : primaryPrimeFactors (∏ p ∈ S,p) = S := by
  have hp : primary (∏ p ∈ S,p) := primary_finset_prod _ _ (fun p hp => (hS p hp).1)
  ext p
  rw [mem_primaryPrimeFactors_iff hp]
  exact ⟨fun h => (primary_prime_dvd_prod_iff h.1 S hS).mp h.2,
    fun h => ⟨hS p h,Finset.dvd_prod_of_mem _ h⟩⟩

lemma primaryDivisors_eq_products {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    primaryDivisors n = (primaryPrimeFactors n).powerset.image (fun S => ∏ p ∈ S,p) := by
  apply Finset.Subset.antisymm (primaryDivisors_subset_products hn hs)
  intro d hd
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hd
  apply (mem_primaryDivisors (primary_ne_zero hn)).mpr
  refine ⟨primary_finset_prod _ _ (fun p hp =>
    (primaryPrimeFactor_spec hn ((Finset.mem_powerset.mp hS) hp)).1.1),?_⟩
  rw [← primaryPrimeFactors_prod hn hs]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp hS)

lemma sum_primaryDivisors {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (f : Eisenstein → ℂ) :
    ∑ d ∈ primaryDivisors n,f d =
      ∑ S ∈ (primaryPrimeFactors n).powerset,f (∏ p ∈ S,p) := by
  rw [primaryDivisors_eq_products hn hs,Finset.sum_image]
  intro S hS T hT he
  have hSp : ∀ p ∈ S,primaryPrime p := fun p hp =>
    (primaryPrimeFactor_spec hn ((Finset.mem_powerset.mp hS) hp)).1
  have hTp : ∀ p ∈ T,primaryPrime p := fun p hp =>
    (primaryPrimeFactor_spec hn ((Finset.mem_powerset.mp hT) hp)).1
  rw [← primaryPrimeFactors_prime_prod S hSp,← primaryPrimeFactors_prime_prod T hTp]
  exact congrArg primaryPrimeFactors he

lemma coprime_indicator_divisors {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (m : Eisenstein) :
    (if IsCoprime n m then (1:ℂ) else 0) =
      ∑ d ∈ primaryDivisors n, (idealMoebius d : ℂ) * (if d ∣ m then 1 else 0) := by
  rw [sum_primaryDivisors hn hs,coprime_indicator_moebius hn hs]

lemma coprime_indicator_ball {n : Eisenstein} {N : ℝ}
    (hn : n ∈ squarefreePrimaryBall N) (m : Eisenstein) :
    (if IsCoprime n m then (1:ℂ) else 0) =
      ∑ d ∈ squarefreePrimaryBall N,
        (idealMoebius d : ℂ) * (if d ∣ n ∧ d ∣ m then 1 else 0) := by
  obtain ⟨hp,hs,hN⟩ := mem_squarefreePrimaryBall.mp hn
  rw [coprime_indicator_divisors hp hs]
  have hsub : primaryDivisors n ⊆ squarefreePrimaryBall N := by
    intro d hd
    obtain ⟨hdp,hdd⟩ := (mem_primaryDivisors (primary_ne_zero hp)).mp hd
    exact mem_squarefreePrimaryBall.mpr ⟨hdp,hs.squarefree_of_dvd hdd,
      (norm_le_of_dvd (primary_ne_zero hp) hdd).trans hN⟩
  apply Finset.sum_subset_zero_on_sdiff hsub
  · intro d hd
    obtain ⟨hd,hd'⟩ := Finset.mem_sdiff.mp hd
    have hdp := (mem_squarefreePrimaryBall.mp hd).1
    have hdn : ¬ d ∣ n := fun h => hd' ((mem_primaryDivisors (primary_ne_zero hp)).mpr ⟨hdp,h⟩)
    simp [hdn]
  · intro d hd
    have hdn := ((mem_primaryDivisors (primary_ne_zero hp)).mp hd).2
    simp [hdn]

theorem coprime_pair_sum_moebius {N : ℝ} (S : Finset Eisenstein)
    (hS : S ⊆ squarefreePrimaryBall N) (f : Eisenstein → Eisenstein → ℂ) :
    (∑ a ∈ S, ∑ b ∈ S, (if IsCoprime a b then (1:ℂ) else 0) * f a b) =
      ∑ d ∈ squarefreePrimaryBall N, (idealMoebius d : ℂ) *
        ∑ a ∈ S.filter (d ∣ ·), ∑ b ∈ S.filter (d ∣ ·), f a b := by
  have he (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) :
      (if IsCoprime a b then (1:ℂ) else 0) * f a b =
        ∑ d ∈ squarefreePrimaryBall N, (idealMoebius d : ℂ) *
          (if d ∣ a ∧ d ∣ b then f a b else 0) := by
    rw [coprime_indicator_ball (hS ha),Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b _ => he a ha b))]
  simp_rw [Finset.sum_comm (s := S) (t := squarefreePrimaryBall N)]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hda : d ∣ a <;> simp [hda,Finset.mul_sum]

end CubicFirstMoment
end

end OAI
