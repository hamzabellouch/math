import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius

namespace OAI

/-! The exact square-divisor Möbius identity on primary elements.
This is the arithmetic inversion used by the low-height angular model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primarySquarePrimeFactors (a : Eisenstein) : Finset Eisenstein :=
  (primaryPrimeFactors a).filter (fun p => p^2 ∣ a)

lemma primary_subset_square_dvd {a : Eisenstein} (ha : primary a)
    {s : Finset Eisenstein} (hs : s ⊆ primaryPrimeFactors a) :
    (∏ p ∈ s, p)^2 ∣ a ↔ ∀ p ∈ s, p^2 ∣ a := by
  constructor
  · intro h p hp
    exact (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp) 2).trans h
  · intro h
    rw [←Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact (primaryPrimes_isCoprime (primaryPrimeFactor_spec ha (hs hp)).1
        (primaryPrimeFactor_spec ha (hs hq)).1 hpq).pow
    · exact h

lemma primarySquarePrimeFactors_empty_iff {a : Eisenstein} (ha : primary a) :
    primarySquarePrimeFactors a = ∅ ↔ Squarefree a := by
  constructor
  · intro he
    by_contra hs
    obtain ⟨p,hp,hpa⟩ := exists_primary_prime_square_dvd ha hs
    have hd : p ∣ a := (dvd_mul_right p p).trans hpa
    have hm : p ∈ primarySquarePrimeFactors a := by
      exact Finset.mem_filter.mpr ⟨(primaryPrime_mem_factors_iff ha).mpr ⟨hp,hd⟩,
        by simpa only [pow_two] using hpa⟩
    simp only [he,Finset.notMem_empty] at hm
  · intro hs
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh := Finset.mem_filter.mp hp
    have hu : IsUnit p := hs p (by simpa only [pow_two] using hh.2)
    exact (primaryPrimeFactor_spec ha hh.1).1.2.not_isUnit hu

lemma primary_square_divisors_image (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {a : Eisenstein} (ha : primary a)
    (hcomplete : ∀ c, primary c → Squarefree c → c^2 ∣ a → c ∈ C) :
    C.filter (fun c => c^2 ∣ a) =
      (primarySquarePrimeFactors a).powerset.image (fun s => ∏ p ∈ s, p) := by
  ext c
  constructor
  · intro hc
    obtain ⟨hc,hd⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_image.mpr ⟨primaryPrimeFactors c,Finset.mem_powerset.mpr ?_,
      primaryPrimeFactors_prod (hC c hc).1 (hC c hc).2⟩
    intro p hp
    have hpc := (primaryPrimeFactor_spec (hC c hc).1 hp).2
    have hpa := (pow_dvd_pow_of_dvd hpc 2).trans hd
    exact Finset.mem_filter.mpr
      ⟨(primaryPrime_mem_factors_iff ha).mpr
        ⟨(primaryPrimeFactor_spec (hC c hc).1 hp).1,
          (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hpa⟩,hpa⟩
  · intro hc
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hc
    have hsub := Finset.mem_powerset.mp hs
    have hpr : ∀ p ∈ s, primaryPrime p := fun p hp =>
      (primaryPrimeFactor_spec ha (Finset.mem_filter.mp (hsub hp)).1).1
    have hprim := primary_finset_prod s (fun p : Eisenstein => p) (fun p hp => (hpr p hp).1)
    have hsq := primaryPrime_product_squarefree s hpr
    have hd : (∏ p ∈ s, p)^2 ∣ a :=
      (primary_subset_square_dvd ha (fun p hp => (Finset.mem_filter.mp (hsub hp)).1)).mpr
        (fun p hp => (Finset.mem_filter.mp (hsub hp)).2)
    exact Finset.mem_filter.mpr ⟨hcomplete _ hprim hsq hd,hd⟩

lemma sum_powerset_sign (P : Finset Eisenstein) :
    (∑ s ∈ P.powerset, (-1:ℝ)^s.card) = if P = ∅ then 1 else 0 := by
  have he := Finset.prod_add (fun _ : Eisenstein => (-1:ℝ)) (fun _ => (1:ℝ)) P
  simp only [Finset.prod_const_one,mul_one,Finset.prod_const,neg_add_cancel] at he
  rw [←he]
  by_cases hP : P = ∅
  · simp [hP]
  · simp [hP,Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hP)]

/-- Every square divisor is included, so the actual truncated coefficient
equals the squarefree indicator; no error term occurs. -/
theorem primary_square_moebius_inversion (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {a : Eisenstein} (ha : primary a)
    (hcomplete : ∀ c, primary c → Squarefree c → c^2 ∣ a → c ∈ C) :
    (∑ c ∈ C, if c^2 ∣ a then (idealMoebius c:ℝ) else 0) =
      (idealMoebius a:ℝ)^2 := by
  rw [←Finset.sum_filter,primary_square_divisors_image C hC ha hcomplete]
  have hinj : Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s, p)
      (↑(primarySquarePrimeFactors a).powerset : Set (Finset Eisenstein)) :=
    primaryPrimeFactors_prod_injective (fun p hp =>
      (primaryPrimeFactor_spec ha (Finset.mem_filter.mp hp).1).1)
  rw [Finset.sum_image hinj]
  have he : (∑ s ∈ (primarySquarePrimeFactors a).powerset,
      (idealMoebius (∏ p ∈ s, p):ℝ)) =
      ∑ s ∈ (primarySquarePrimeFactors a).powerset,(-1:ℝ)^s.card := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [idealMoebius_prod_primaryPrimes s (fun p hp =>
      (primaryPrimeFactor_spec ha (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).1).1)]
    push_cast
    rfl
  rw [he,sum_powerset_sign,idealMoebius_sq]
  simp only [primarySquarePrimeFactors_empty_iff ha]

lemma squarefreeDivisorTruncation_complete {a : Eisenstein} (ha : primary a)
    {X : ℝ} (hX : norm a ≤ X) {c : Eisenstein} (hc : primary c)
    (hsc : Squarefree c) (hd : c^2 ∣ a) :
    c ∈ squarefreeDivisorTruncation (Real.sqrt X) := by
  apply mem_squarefreeDivisorTruncation.mpr
  refine ⟨hc,hsc,Real.le_sqrt_of_sq_le ?_⟩
  have hn := (norm_le_of_dvd_nonzero (primary_ne_zero ha) hd).trans hX
  simpa only [pow_two,norm_mul_eq] using hn

theorem primary_square_moebius_truncation {a : Eisenstein} (ha : primary a)
    {X : ℝ} (hX : norm a ≤ X) :
    (∑ c ∈ squarefreeDivisorTruncation (Real.sqrt X),
      if c^2 ∣ a then (idealMoebius c:ℝ) else 0) = (idealMoebius a:ℝ)^2 := by
  exact primary_square_moebius_inversion _
    (fun c hc => ⟨(mem_squarefreeDivisorTruncation.mp hc).1,
      (mem_squarefreeDivisorTruncation.mp hc).2.1⟩) ha
    (fun c hc hs hd => squarefreeDivisorTruncation_complete ha hX hc hs hd)

end CubicFirstMoment

end

end OAI
