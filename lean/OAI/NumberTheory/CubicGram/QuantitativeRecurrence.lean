import Mathlib
import OAI.NumberTheory.CubicGram.PoissonBounds

namespace OAI

/-! Uniform quantitative recurrence and exponent monotonicity. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def sieveRecurrenceShape (ξ M N : ℝ) : ℝ :=
  M+(M*N)^(2/3 : ℝ)+N+M^(1-ξ)*N^(2*ξ-1)

lemma sieveRecurrenceShape_nonneg {ξ M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    0 ≤ sieveRecurrenceShape ξ M N := by unfold sieveRecurrenceShape; positivity

lemma scaled_poisson_error_le {ξ M N m k : ℝ} (hξ : 1 ≤ ξ)
    (hM : 0 < M) (hN : 0 < N) (hm : 1 ≤ m) (hk : m ≤ k) :
    (M/m)^(1-ξ)*(N/k)^(2*ξ-1) ≤ M^(1-ξ)*N^(2*ξ-1) := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hk0 : 0 < k := hm0.trans_le hk
  have hk1 : 1 ≤ k := hm.trans hk
  have hp : m^(ξ-1) ≤ k^(2*ξ-1) := by
    calc
      _ ≤ k^(ξ-1) := Real.rpow_le_rpow hm0.le hk (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  have hden : 1 ≤ m^(1-ξ)*k^(2*ξ-1) := by
    rw [show (1 : ℝ)-ξ = -(ξ-1) by ring,Real.rpow_neg hm0.le]
    rw [inv_mul_eq_div]
    exact (one_le_div (by positivity)).mpr hp
  rw [Real.div_rpow hM.le hm0.le,Real.div_rpow hN.le hk0.le,← mul_div_mul_comm]
  exact div_le_self (by positivity) hden

lemma SieveExponent.common_cost_bound {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (M N : ℝ), 1 ≤ N → N ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ∀ k ∈ commonRowFactors S, ∀ s ∈ (primaryPrimeFactors k).powerset,
      commonBlockCost S cubicSieveCutoff M N 8 k (∏ p ∈ s, p) ≤
        C*(M*N)^δ*sieveRecurrenceShape ξ M N := by
  obtain ⟨D,hD,hdual⟩ := hExp.dual_bound hξ hξ2 hδ hδ1
  obtain ⟨E,hE,hdiag⟩ := primaryCharacterGram_one_one_bound cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth.continuous
  let C : ℝ := 54000*D+E
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : 54000*D ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro S M N hN hNM hS k hkS s hs
  let m := ∏ p ∈ s, p
  have hS' : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hk := commonRowFactors_spec hS' hkS
  have hm : primary m := primary_finset_prod _ _
    (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).1.1)
  have hmk : m ∣ k := (primary_subsets_prod_dvd hk.1 (Finset.mem_powerset.mp hs) k).mpr
    (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).2)
  have hnk1 : 1 ≤ norm k := one_le_norm (primary_ne_zero hk.1)
  have hnm1 : 1 ≤ norm m := one_le_norm (primary_ne_zero hm)
  have hnk : 0 < norm k := zero_lt_one.trans_le hnk1
  have hnm : 0 < norm m := zero_lt_one.trans_le hnm1
  have hmkN : norm m ≤ norm k := norm_le_of_dvd (primary_ne_zero hk.1) hmk
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := hN0.trans_le hNM
  have hM1 : 1 ≤ M := hN.trans hNM
  have hMN1 : 1 ≤ M*N := one_le_mul_of_one_le_of_one_le hM1 hN
  have hpow1 : 1 ≤ (M*N)^δ := Real.one_le_rpow hMN1 hδ.le
  have hshape := sieveRecurrenceShape_nonneg (ξ := ξ) hM0.le hN0.le
  have hMshape : M ≤ sieveRecurrenceShape ξ M N := by
    unfold sieveRecurrenceShape
    have hh : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
    have hh' : 0 ≤ M^(1-ξ)*N^(2*ξ-1) := by positivity
    linarith
  change commonBlockCost S cubicSieveCutoff M N 8 k m ≤ _
  unfold commonBlockCost
  split_ifs with hkN
  · let n : ℝ := N/norm k
    let z : ℝ := M/norm m
    have hn : 1 ≤ n := by dsimp [n]; exact (one_le_div hnk).mpr hkN.le
    have hn0 : 0 < n := zero_lt_one.trans_le hn
    have hnz : n ≤ z := by
      dsimp [n,z]
      apply (div_le_div_iff₀ hnk hnm).mpr
      nlinarith [mul_le_mul hNM hmkN (norm_nonneg m) hM0.le]
    have hz : 0 < z := hn0.trans_le hnz
    have hnN : n ≤ N := div_le_self hN0.le hnk1
    have hzM : z ≤ M := div_le_self hM0.le hnm1
    have hzn : z*n ≤ M*N := mul_le_mul hzM hnN hn0.le hM0.le
    have hres : ∀ a ∈ residualRows S k, primary a ∧ Squarefree a ∧ norm a ≤ 2*n := by
      intro a ha
      have hh := residualRows_primary hk.1 hS' a ha
      refine ⟨hh.1,hh.2,?_⟩
      have hnorm := (residualRows_norm hk.1 (fun p hp => (hS p hp).2.2) a ha).2
      have hsqrt : Real.sqrt 2 ≤ 2 := by norm_num
      exact hnorm.trans (mul_le_mul_of_nonneg_right hsqrt hn0.le)
    have hbound := hdual (residualRows S k) (2*n) (z/(27*n^2)) (by linarith) (by positivity) hres
    have hnum := poisson_dual_numerical hξ hξ2 hδ hδ1 hn hnz
    have herr : z^(1-ξ)*n^(2*ξ-1) ≤ M^(1-ξ)*N^(2*ξ-1) :=
      scaled_poisson_error_le hξ hM0 hN0 hnm1 hmkN
    have hbracket : (z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1) ≤ sieveRecurrenceShape ξ M N := by
      have hh : (z*n)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := Real.rpow_le_rpow (by positivity) hzn (by norm_num)
      unfold sieveRecurrenceShape
      linarith
    calc
      _ ≤ (z/n)*(D*(2*n)^δ*
        ((2*n)*(z/(27*n^2))^(-(δ+1/3 : ℝ))+(2*n)^(2/3 : ℝ)*(z/(27*n^2))^(-(δ+2/3 : ℝ))+
        (z/(27*n^2))^(-(δ+ξ))+(z/(27*n^2))^(-(δ+1)))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = D*((z/n)*(2*n)^δ*
        ((2*n)*(z/(27*n^2))^(-(δ+1/3 : ℝ))+(2*n)^(2/3 : ℝ)*(z/(27*n^2))^(-(δ+2/3 : ℝ))+
        (z/(27*n^2))^(-(δ+ξ))+(z/(27*n^2))^(-(δ+1)))) := by ring
      _ ≤ D*(54000*(z*n)^δ*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1))) :=
        mul_le_mul_of_nonneg_left hnum hD.le
      _ = (54000*D)*(z*n)^δ*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1)) := by ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ E*(M/norm m) := hdiag _ (div_pos hM0 hnm)
      _ ≤ C*M := mul_le_mul hEC (div_le_self hM0.le hnm1) (by positivity) hC.le
      _ ≤ C*((M*N)^δ*sieveRecurrenceShape ξ M N) := mul_le_mul_of_nonneg_left
        (hMshape.trans (le_mul_of_one_le_left hshape hpow1)) hC.le
      _ = _ := by ring

lemma SieveExponent.thin_recurrence {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ N → N ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N := by
  obtain ⟨C₀,hC₀,hrec⟩ := primarySmoothedSieveMass_norm_recurrence cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth 8 (by norm_num)
  obtain ⟨D,hD,hcost⟩ := hExp.common_cost_bound hξ hξ2 hδ hδ1
  obtain ⟨E,hE,henergy⟩ := common_energy_small_power δ hδ
  refine ⟨C₀*D*E*(Real.sqrt 2)^δ,by positivity,?_⟩
  intro S H M N hN hNM hS hH
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := hN0.trans_le hNM
  have hM1 : 1 ≤ M := hN.trans hNM
  have hS' : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hshape := sieveRecurrenceShape_nonneg (ξ := ξ) hM0.le hN0.le
  have hpow : (M*N)^δ*N^δ ≤ (M*N)^(2*δ) := by
    rw [show 2*δ = δ+δ by ring,Real.rpow_add (by positivity)]
    gcongr
    exact le_mul_of_one_le_left hN0.le hM1
  apply (finiteCubicBound_le_iff _ _ (by positivity)).mpr
  intro u
  have hb := hrec S hS' u M N hM0 hN0 (fun a ha => (hS a ha).2.2)
  have hsum : (∑ k ∈ commonRowFactors S,
       (∑ s ∈ (primaryPrimeFactors k).powerset,
         commonBlockCost S cubicSieveCutoff M N 8 k (∏ p ∈ s, p))*commonBlockEnergy S u k) ≤
      (D*(M*N)^δ*sieveRecurrenceShape ξ M N)*
        ∑ k ∈ commonRowFactors S, (2 : ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S u k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro k hk
    have hh := Finset.sum_le_card_nsmul _ _ _ (hcost S M N hN hNM hS k hk)
    simp only [Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
    exact (mul_le_mul_of_nonneg_right hh (commonBlockEnergy_nonneg _ _ _)).trans_eq (by ring)
  have he := henergy S u (Real.sqrt 2*N)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)
  calc
    _ ≤ ‖primarySmoothedSieveMass S u cubicSieveCutoff M‖ :=
      finiteCubicMass_le_smoothed S H (fun x hx => (hH x hx).1) u hM0 (fun x hx => (hH x hx).2)
    _ ≤ C₀*((D*(M*N)^δ*sieveRecurrenceShape ξ M N)*(E*(Real.sqrt 2*N)^δ*∑ a ∈ S, ‖u a‖^2)) :=
      hb.trans (mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left he (by positivity))) hC₀.le)
    _ = (C₀*D*E*(Real.sqrt 2)^δ)*((M*N)^δ*N^δ)*sieveRecurrenceShape ξ M N*∑ a ∈ S, ‖u a‖^2 := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) hN0.le]; ring
    _ ≤ _ := by gcongr

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sieveRecurrenceShape_mono_right {ξ M n N : ℝ} (hξ : 1 ≤ ξ)
    (hM : 0 ≤ M) (hn : 0 ≤ n) (hnN : n ≤ N) :
    sieveRecurrenceShape ξ M n ≤ sieveRecurrenceShape ξ M N := by
  unfold sieveRecurrenceShape
  gcongr
  linarith

lemma SieveExponent.recurrence {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ N → N ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^ε*sieveRecurrenceShape ξ M N := by
  let δ : ℝ := min (ε/3) (1/3)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδε : 3*δ ≤ ε := by have := min_le_left (ε/3) (1/3 : ℝ); change δ ≤ ε/3 at this; linarith
  obtain ⟨D,hD,hthin⟩ := hExp.thin_recurrence hξ hξ2 hδ hδ1
  obtain ⟨E,hE,hlog⟩ := cutoff_log_small_power hδ
  refine ⟨2*E*D,by positivity,?_⟩
  intro S H M N hN hNM hS hH
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := hN0.trans_le hNM
  have hM1 : 1 ≤ M := hN.trans hNM
  have hshape := sieveRecurrenceShape_nonneg (ξ := ξ) hM0.le hN0.le
  have hlocal : ∀ R : Finset Eisenstein, R ⊆ S → ∀ n : ℝ, 1 ≤ n → n ≤ N →
      (∀ a ∈ R, n ≤ norm a ∧ norm a ≤ Real.sqrt 2*n) →
      finiteCubicBound R H ≤ D*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N := by
    intro R hRS n hn hnN hR
    have hh := hthin R H M n hn (hnN.trans hNM)
      (fun a ha => ⟨(hS a (hRS ha)).1,(hS a (hRS ha)).2.1,hR a ha⟩) hH
    have hs := sieveRecurrenceShape_mono_right hξ hM0.le (zero_lt_one.trans_le hn).le hnN
    exact hh.trans (mul_le_mul (by gcongr) hs (sieveRecurrenceShape_nonneg hM0.le (by linarith)) (by positivity))
  have hb := finiteCubicBound_local_to_global S H N
    (D*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N) hN (by positivity)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩) (fun x hx => (hH x hx).1) hlocal
  have hp : N^δ*(M*N)^(2*δ) ≤ (M*N)^ε := by
    calc
      _ ≤ (M*N)^δ*(M*N)^(2*δ) := by gcongr; exact le_mul_of_one_le_left hN0.le hM1
      _ = (M*N)^(3*δ) := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le hM1 hN) hδε
  calc
    _ ≤ 2*((Nat.log 2 ⌊N⌋₊ : ℝ)+1)*(D*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N) := hb
    _ ≤ 2*(E*N^δ)*(D*(M*N)^(2*δ)*sieveRecurrenceShape ξ M N) := by gcongr; exact hlog N hN
    _ = (2*E*D)*(N^δ*(M*N)^(2*δ))*sieveRecurrenceShape ξ M N := by ring
    _ ≤ _ := by gcongr

lemma SieveExponent.mono {ξ ζ : ℝ} (hξ : SieveExponent ξ) (h : ξ ≤ ζ) : SieveExponent ζ := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := hξ ε hε
  refine ⟨C,hC,?_⟩
  intro S H M N hM hN hS hH
  exact (hbound S H M N hM hN hS hH).trans (by
    gcongr)

end CubicFirstMoment
end
end

end OAI
