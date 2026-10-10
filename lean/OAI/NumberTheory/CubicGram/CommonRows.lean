import Mathlib
import OAI.NumberTheory.CubicGram.DyadicRecurrence

namespace OAI

/-! Exact common-factor row reindexing and matrix decomposition. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def residualRows (S : Finset Eisenstein) (k : Eisenstein) : Finset Eisenstein :=
  if hk : k ≠ 0 then S.preimage (k*·) (mul_right_injective₀ hk).injOn else ∅

lemma mem_residualRows {S : Finset Eisenstein} {k a : Eisenstein} (hk : k ≠ 0) :
    a ∈ residualRows S k ↔ k*a ∈ S := by
  simp [residualRows,hk]

lemma residualRows_primary {S : Finset Eisenstein} {k : Eisenstein} (hk : primary k)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) :
    ∀ a ∈ residualRows S k, primary a ∧ Squarefree a := by
  intro a ha
  have hn := hS (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
  exact ⟨primary_of_mul hk hn.1,hn.2.of_mul_right⟩

lemma primaryPrimeFactors_coprime_overlap {k a b : Eisenstein}
    (hk : primary k) (ha : primary a) (hb : primary b) (hab : IsCoprime a b) :
    primaryPrimeFactors (k*a) ∩ primaryPrimeFactors (k*b) = primaryPrimeFactors k := by
  ext p
  rw [Finset.mem_inter, primaryPrime_mem_factors_iff (primary_mul hk ha),
    primaryPrime_mem_factors_iff (primary_mul hk hb), primaryPrime_mem_factors_iff hk]
  constructor
  · rintro ⟨⟨hp,hpa⟩,⟨_,hpb⟩⟩
    refine ⟨hp,?_⟩
    rcases hp.2.dvd_mul.mp hpa with hd | hd
    · exact hd
    rcases hp.2.dvd_mul.mp hpb with hd' | hd'
    · exact hd'
    exact (hp.2.not_isUnit (hab.isUnit_of_dvd' hd hd')).elim
  · rintro ⟨hp,hd⟩
    exact ⟨⟨hp,hd.trans (dvd_mul_right k a)⟩,⟨hp,hd.trans (dvd_mul_right k b)⟩⟩

def primaryCommonFactor (p q : Eisenstein) : Eisenstein :=
  ∏ r ∈ primaryPrimeFactors p ∩ primaryPrimeFactors q, r

lemma primaryCommonFactor_mul {k a b : Eisenstein}
    (hk : primary k) (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) : primaryCommonFactor (k*a) (k*b) = k := by
  unfold primaryCommonFactor
  rw [primaryPrimeFactors_coprime_overlap hk ha hb hab,primaryPrimeFactors_prod hk hsk]

lemma primaryCommonFactor_decomposition {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q) :
    ∃ a b : Eisenstein, primary a ∧ primary b ∧ Squarefree a ∧ Squarefree b ∧
      IsCoprime a b ∧ p = primaryCommonFactor p q*a ∧ q = primaryCommonFactor p q*b := by
  obtain ⟨k,a,b,hk,ha,hb,hsk,hsa,hsb,hab,_,_,hpa,hqb⟩ :=
    primarySquarefree_common_decomposition hp hq hsp hsq
  have he : primaryCommonFactor p q = k := hpa ▸ hqb ▸ primaryCommonFactor_mul hk hsk ha hb hab
  exact ⟨a,b,ha,hb,hsa,hsb,hab,by simpa [he] using hpa,by simpa [he] using hqb⟩

lemma primaryCommonFactor_spec {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q) :
    primary (primaryCommonFactor p q) ∧ Squarefree (primaryCommonFactor p q) ∧
      primaryCommonFactor p q ∣ p ∧ primaryCommonFactor p q ∣ q := by
  obtain ⟨k,a,b,hk,ha,hb,hsk,hsa,hsb,hab,_,_,hpa,hqb⟩ :=
    primarySquarefree_common_decomposition hp hq hsp hsq
  have he : primaryCommonFactor p q = k := hpa ▸ hqb ▸ primaryCommonFactor_mul hk hsk ha hb hab
  rw [he,hpa,hqb]
  exact ⟨hk,hsk,dvd_mul_right k a,dvd_mul_right k b⟩

def commonRowFactors (S : Finset Eisenstein) : Finset Eisenstein :=
  (S ×ˢ S).image (fun pq => primaryCommonFactor pq.1 pq.2)

lemma mem_commonRowFactors {S : Finset Eisenstein} {p q : Eisenstein}
    (hp : p ∈ S) (hq : q ∈ S) : primaryCommonFactor p q ∈ commonRowFactors S :=
  Finset.mem_image.mpr ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,rfl⟩

lemma commonRowFactors_spec {S : Finset Eisenstein}
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) {k : Eisenstein}
    (hk : k ∈ commonRowFactors S) : primary k ∧ Squarefree k := by
  obtain ⟨⟨p,q⟩,hpq,rfl⟩ := Finset.mem_image.mp hk
  have hp := hS p (Finset.mem_product.mp hpq).1
  have hq := hS q (Finset.mem_product.mp hpq).2
  exact ⟨(primaryCommonFactor_spec hp.1 hq.1 hp.2 hq.2).1,
    (primaryCommonFactor_spec hp.1 hq.1 hp.2 hq.2).2.1⟩

lemma residualRows_image {S : Finset Eisenstein} {k : Eisenstein} (hk : k ≠ 0) :
    (residualRows S k).image (k*·) = S.filter (fun p => k ∣ p) := by
  ext p
  simp only [Finset.mem_image,mem_residualRows hk,Finset.mem_filter]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,dvd_mul_right k a⟩
  · rintro ⟨hp,a,rfl⟩
    exact ⟨a,hp,rfl⟩

lemma commonFactor_eq_iff_coprime {k a b : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (hsa : Squarefree (k*a)) (hsb : Squarefree (k*b)) :
    primaryCommonFactor (k*a) (k*b) = k ↔ IsCoprime a b := by
  constructor
  · intro he
    obtain ⟨a',b',_,_,_,_,hab,hpa,hqb⟩ := primaryCommonFactor_decomposition
      (primary_mul hk ha) (primary_mul hk hb) hsa hsb
    rw [he] at hpa hqb
    have hea := mul_left_cancel₀ (primary_ne_zero hk) hpa
    have heb := mul_left_cancel₀ (primary_ne_zero hk) hqb
    simpa only [← hea,← heb] using hab
  · exact primaryCommonFactor_mul hk hsk ha hb

lemma sum_residualRows {S : Finset Eisenstein} {k : Eisenstein} (hk : k ≠ 0)
    (f : Eisenstein → ℂ) :
    (∑ a ∈ residualRows S k, f (k*a)) = ∑ p ∈ S.filter (fun p => k ∣ p), f p := by
  rw [← residualRows_image hk,Finset.sum_image]
  intro a ha b hb he
  exact mul_left_cancel₀ hk he

lemma common_factor_block_reindex (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    {k : Eisenstein} (hk : primary k) (hsk : Squarefree k)
    (F : Eisenstein → Eisenstein → ℂ) :
    (∑ p ∈ S, ∑ q ∈ S, if primaryCommonFactor p q = k then F p q else 0) =
      ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        if IsCoprime a b then F (k*a) (k*b) else 0 := by
  have hn := primary_ne_zero hk
  have hp := residualRows_primary hk hS
  have hrhs : (∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        if IsCoprime a b then F (k*a) (k*b) else 0) =
      ∑ p ∈ S.filter (fun p => k ∣ p), ∑ q ∈ S.filter (fun q => k ∣ q),
        if primaryCommonFactor p q = k then F p q else 0 := by
    calc
      _ = ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
          if primaryCommonFactor (k*a) (k*b) = k then F (k*a) (k*b) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        simp only [commonFactor_eq_iff_coprime hk hsk (hp a ha).1 (hp b hb).1
          (hS (k*a) ((mem_residualRows hn).mp ha)).2
          (hS (k*b) ((mem_residualRows hn).mp hb)).2]
      _ = ∑ a ∈ residualRows S k, ∑ q ∈ S.filter (fun q => k ∣ q),
          if primaryCommonFactor (k*a) q = k then F (k*a) q else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact sum_residualRows (S := S) hn
          (fun q => if primaryCommonFactor (k*a) q = k then F (k*a) q else 0)
      _ = _ := sum_residualRows (S := S) hn
        (fun p => ∑ q ∈ S.filter (fun q => k ∣ q), if primaryCommonFactor p q = k then F p q else 0)
  rw [hrhs]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hpS
  by_cases hpk : k ∣ p
  · simp only [ite_eq_left hpk]
    apply Finset.sum_congr rfl
    intro q hqS
    by_cases hqk : k ∣ q
    · simp [hqk]
    · have he : primaryCommonFactor p q ≠ k := by
        intro he
        exact hqk (he ▸ (primaryCommonFactor_spec (hS p hpS).1 (hS q hqS).1
          (hS p hpS).2 (hS q hqS).2).2.2.2)
      simp [hqk,he]
  · simp only [ite_eq_right hpk]
    apply Finset.sum_eq_zero
    intro q hqS
    have he : primaryCommonFactor p q ≠ k := by
      intro he
      exact hpk (he ▸ (primaryCommonFactor_spec (hS p hpS).1 (hS q hqS).1
        (hS p hpS).2 (hS q hqS).2).2.2.1)
    simp [he]

theorem common_factor_matrix_decomposition (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (F : Eisenstein → Eisenstein → ℂ) :
    (∑ p ∈ S, ∑ q ∈ S, F p q) =
      ∑ k ∈ commonRowFactors S, ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        if IsCoprime a b then F (k*a) (k*b) else 0 := by
  calc
    _ = ∑ p ∈ S, ∑ q ∈ S, ∑ k ∈ commonRowFactors S,
        if primaryCommonFactor p q = k then F p q else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      simp [mem_commonRowFactors hp hq]
    _ = ∑ k ∈ commonRowFactors S, ∑ p ∈ S, ∑ q ∈ S,
        if primaryCommonFactor p q = k then F p q else 0 := by
      simp_rw [Finset.sum_comm (s := S) (t := commonRowFactors S)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact common_factor_block_reindex S hS (commonRowFactors_spec hS hk).1
        (commonRowFactors_spec hS hk).2 F

def commonBlockCoefficient (u : Eisenstein → ℂ) (k m a : Eisenstein) : ℂ :=
  u (k*a) * cubicSymbol a m

lemma commonBlockCoefficient_norm_le (u : Eisenstein → ℂ) (k m : Eisenstein)
    {a : Eisenstein} (ha : primary a) :
    ‖commonBlockCoefficient u k m a‖ ≤ ‖u (k*a)‖ := by
  unfold commonBlockCoefficient
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left (norm_cubicSymbol_le_one ha m) (_root_.norm_nonneg _)

theorem primarySmoothedSieveMass_common_blocks (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    primarySmoothedSieveMass S u W Z =
      ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        let m := ∏ p ∈ s, p
        (idealMoebius m : ℂ) *
          coprimeGramForm (residualRows S k) (commonBlockCoefficient u k m) W (Z/norm m) := by
  rw [primarySmoothedSieveMass_gram S (fun a ha => (hS a ha).1) u W hW hW' hZ,
    common_factor_matrix_decomposition S hS]
  apply Finset.sum_congr rfl
  intro k hkS
  have hk := commonRowFactors_spec hS hkS
  have hr := residualRows_primary hk.1 hS
  calc
    _ = ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k,
        ∑ s ∈ (primaryPrimeFactors k).powerset,
          let m := ∏ p ∈ s, p
          (idealMoebius m : ℂ) *
            (if IsCoprime a b then commonBlockCoefficient u k m a *
              star (commonBlockCoefficient u k m b) * primaryCharacterGram a b W (Z/norm m) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab : IsCoprime a b
      · simp only [ite_eq_left hab]
        rw [primaryCharacterGram_common_factor hk.1 hk.2 (hr a ha).1 (hr b hb).1 W hW hW' hZ]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        simp only [commonBlockCoefficient,mixedSymbol,star_mul]
        ring
      · simp [hab]
    _ = _ := by
      simp_rw [Finset.sum_comm (s := residualRows S k) (t := (primaryPrimeFactors k).powerset)]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [coprimeGramForm,Finset.mul_sum]

end CubicFirstMoment
end
end

end OAI
