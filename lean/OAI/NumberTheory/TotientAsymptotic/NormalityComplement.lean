import OAI.NumberTheory.TotientAsymptotic.NormalitySmoothCount

namespace OAI

/-! The complementary primes are counted by their smooth predecessors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def normalitySmallFactorPrimes (S : ℝ) (N : ℕ) : Finset ℕ :=
  (nonNormalPrimes S N).filter (fun p => ¬normalityPrimeCutoff N ≤ largestPrimeFactor (p-1))

lemma normality_complement_count : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, ∀ N : ℕ,
    Real.exp 2 ≤ N → 1 ≤ B N → 1 ≤ Real.log N/(200*B N) →
    ((normalitySmallFactorPrimes S N).card:ℝ) ≤ C*N/(Real.log N)^2 := by
  classical
  obtain ⟨C,hC,hsmooth⟩ := normality_smooth_count
  refine ⟨C,hC,?_⟩
  intro S N hN hB hL
  let P := normalitySmallFactorPrimes S N
  let Q := P.image (fun p => p-1)
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp r hr he
    change p-1=r-1 at he
    have hp2 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2.two_le
    have hr2 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).2.two_le
    omega
  have hcard : Q.card=P.card := Finset.card_image_iff.mpr hinj
  rw [← hcard]
  apply hsmooth N hN hB hL Q
  intro n hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hcut⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpN,hprime⟩ := Nat.mem_primesLE.mp hp
  exact ⟨by have := hprime.two_le; omega,by omega,(le_of_not_ge hcut)⟩

lemma nonNormalPrimes_card_split (S : ℝ) (N : ℕ) :
    (nonNormalPrimes S N).card =
      (normalityLargeFactorPrimes S N).card+(normalitySmallFactorPrimes S N).card := by
  classical
  exact (Finset.card_filter_add_card_filter_not (s:=nonNormalPrimes S N)
    (p:=fun p => normalityPrimeCutoff N ≤ largestPrimeFactor (p-1))).symm

lemma normality_middle_scale {S : ℝ} (hS : 1 < S) {N : ℕ} (hB : 1 ≤ B N)
    (hlogN : 0 < Real.log N) (hSupper : Real.log S ≤ (Real.log N)^6) :
    (N:ℝ)/(Real.log N)^2 ≤ N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  have hroot : (Real.log S)^(1/6:ℝ) ≤ Real.log N := by
    calc
      _ ≤ ((Real.log N)^6)^(1/6:ℝ) :=
        Real.rpow_le_rpow (Real.log_pos hS).le hSupper (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hlogN.le]
        norm_num
  have hinv : (Real.log N)⁻¹ ≤ (Real.log S)^(-1/6:ℝ) := by
    rw [show (-1/6:ℝ) = -(1/6:ℝ) by norm_num,Real.rpow_neg (Real.log_pos hS).le]
    exact (inv_le_inv₀ hlogN (Real.rpow_pos_of_pos (Real.log_pos hS) _)).mpr hroot
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  have hpow : 1 ≤ (B N)^5 := one_le_pow₀ hB
  calc
    _ = (N/Real.log N)*(Real.log N)⁻¹ := by ring
    _ ≤ (N/Real.log N)*(Real.log S)^(-1/6:ℝ) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ N/Real.log N*(Real.log S)^(-1/6:ℝ) by positivity)
      nlinarith

 theorem normality_middle_parameter : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ,
    2 < S → 4 ≤ B S → ∀ N : ℕ, Real.exp 2 ≤ N → 1 ≤ B N →
    1 ≤ Real.log N/(200*B N) → Real.log S ≤ (Real.log N)^6 →
    ((nonNormalPrimes S N).card:ℝ) ≤
      C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,hC,hlarge⟩ := normality_large_factor_count
  obtain ⟨D,hD,hsmall⟩ := normality_complement_count
  refine ⟨C+D,by positivity,?_⟩
  intro S hS hBS N hN hB hL hupper
  have hlog : 0 < Real.log N := by
    have hn0 := (Real.exp_pos 2).trans_le hN
    have hh := (Real.le_log_iff_exp_le hn0).mpr hN
    linarith
  have hscale := mul_le_mul_of_nonneg_left
    (normality_middle_scale (by linarith : 1 < S) hB hlog hupper) hD.le
  have hs : ((normalitySmallFactorPrimes S N).card:ℝ) ≤
      D*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
    calc
      _ ≤ D*N/(Real.log N)^2 := hsmall S N hN hB hL
      _ = D*(N/(Real.log N)^2) := by ring
      _ ≤ D*(N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ)) := hscale
      _ = _ := by ring
  have he : ((nonNormalPrimes S N).card:ℝ) =
      ((normalityLargeFactorPrimes S N).card:ℝ)+((normalitySmallFactorPrimes S N).card:ℝ) := by
    exact_mod_cast nonNormalPrimes_card_split S N
  rw [he]
  have hl := hlarge S hS hBS N hN hB hL
  calc
    _ ≤ C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ)+
        D*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := add_le_add hl hs
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
