import Mathlib
import OAI.NumberTheory.CubicGauss.InitialBounds

namespace OAI

/-! Smoothed sieve inequalities and dyadic coefficient bins. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma cubicRowEnergy_card_bound (S : Finset Eisenstein) (hS : ∀ a ∈ S,primary a)
    (u : Eisenstein → ℂ) (m : Eisenstein) :
    cubicRowEnergy S u m ≤ (S.card:ℝ)*∑ a ∈ S,‖u a‖^2 := by
  have h := SieveOperator.sum_mul_norm_sq S u (fun a => cubicSymbol a m)
  have hc : ∑ a ∈ S,‖cubicSymbol a m‖^2 ≤ (S.card:ℝ) := by
    calc
      _ ≤ ∑ _a ∈ S,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS a ha) m) 2
      _ = _ := by simp
  apply h.trans
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc
    (Finset.sum_nonneg fun a _ => sq_nonneg ‖u a‖)

lemma cubicRowEnergy_gaussian_summable (S : Finset Eisenstein) (hS : ∀ a ∈ S,primary a)
    (u : Eisenstein → ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : Eisenstein => Real.exp (-Real.pi*t*norm m)*cubicRowEnergy S u m) := by
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (Real.exp_pos _).le (cubicRowEnergy_nonneg S u m))
    (fun m => mul_le_mul_of_nonneg_left (cubicRowEnergy_card_bound S hS u m) (Real.exp_pos _).le)
  simpa only [neg_mul] using (real_gaussian_summable (Real.pi*t) (mul_pos Real.pi_pos ht)).mul_right
    ((S.card:ℝ)*∑ a ∈ S,‖u a‖^2)

lemma cubic_gaussian_norm_eq (S : Finset Eisenstein) (u : Eisenstein → ℂ) (t : ℝ) :
    ‖∑' m : Eisenstein,(cubicRowEnergy S u m:ℂ)*Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ))‖ =
      ∑' m : Eisenstein,Real.exp (-Real.pi*t*norm m)*cubicRowEnergy S u m := by
  have he (m : Eisenstein) : (cubicRowEnergy S u m:ℂ)*Complex.exp (-(Real.pi:ℂ)*t*(norm m:ℂ)) =
      ((Real.exp (-Real.pi*t*norm m)*cubicRowEnergy S u m:ℝ):ℂ) := by
    rw [Complex.ofReal_mul,Complex.ofReal_exp]
    push_cast
    ring
  simp_rw [he]
  rw [← Complex.ofReal_tsum,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  exact tsum_nonneg (fun m => mul_nonneg (Real.exp_pos _).le (cubicRowEnergy_nonneg S u m))

 

lemma cubic_cutoff_le_gaussian {M : ℝ} (hM : 0 < M)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S,primary a) (u : Eisenstein → ℂ) :
    ∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m ≤
      Real.exp Real.pi * ‖∑' m : Eisenstein,(cubicRowEnergy S u m:ℂ)*
        Complex.exp (-(Real.pi:ℂ)*((1/M:ℝ):ℂ)*(norm m:ℂ))‖ := by
  rw [cubic_gaussian_norm_eq]
  calc
    _ ≤ ∑ m ∈ squarefreePrimaryBall M, Real.exp Real.pi *
        (Real.exp (-Real.pi*(1/M)*norm m)*cubicRowEnergy S u m) := by
      apply Finset.sum_le_sum
      intro m hm
      have hn := (mem_squarefreePrimaryBall.mp hm).2.2
      have hp : Real.pi*(1/M)*norm m ≤ Real.pi := by
        have := mul_le_mul_of_nonneg_left hn (show 0 ≤ Real.pi/M by positivity)
        simpa [div_eq_mul_inv,mul_assoc,ne_of_gt hM] using this
      have hex : 1 ≤ Real.exp Real.pi * Real.exp (-Real.pi*(1/M)*norm m) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right hex (cubicRowEnergy_nonneg S u m)]
    _ = Real.exp Real.pi*∑ m ∈ squarefreePrimaryBall M,
        Real.exp (-Real.pi*(1/M)*norm m)*cubicRowEnergy S u m := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum _ (fun m _ => mul_nonneg (Real.exp_pos _).le (cubicRowEnergy_nonneg S u m))
        (cubicRowEnergy_gaussian_summable S hS u (one_div_pos.mpr hM))) (Real.exp_pos _).le

lemma initial_positive_factor {N t k d : ℝ} (hN : 1 ≤ N) (ht : 0 < t)
    (hk : 1 ≤ k) (hkN : k ≤ N) (hd : 1 ≤ d) :
    (2/(Real.sqrt 3*t*d)) *
      (7*(1+648*(N/k)/(4*Real.pi/(3*(t*d)*((9/10:ℝ)*N/k)^2)))/((9/10:ℝ)*N/k)) ≤
      10000*(1/t+N^2) := by
  have hk0 : 0 < k := by linarith
  have hd0 : 0 < d := by linarith
  have hN0 : 0 < N := by linarith
  have hs := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)
  have hs1 : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  have hp1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have he : (2/(Real.sqrt 3*t*d)) *
      (7*(1+648*(N/k)/(4*Real.pi/(3*(t*d)*((9/10:ℝ)*N/k)^2)))/((9/10:ℝ)*N/k)) =
      (140/9:ℝ)*k/(Real.sqrt 3*t*d*N)+(30618/5:ℝ)*N^2/(Real.sqrt 3*Real.pi*k^2) := by
    field_simp
    ring
  rw [he]
  have h1 : k/(Real.sqrt 3*t*d*N) ≤ 1/t := by
    apply (div_le_div_iff₀ (by positivity) ht).mpr
    have hh : k ≤ Real.sqrt 3*d*N := by
      calc
        k ≤ N := hkN
        _ ≤ Real.sqrt 3*d*N := le_mul_of_one_le_left hN0.le (one_le_mul_of_one_le_of_one_le hs1 hd)
    nlinarith
  have h2 : N^2/(Real.sqrt 3*Real.pi*k^2) ≤ N^2 := by
    exact div_le_self (sq_nonneg _) (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hs1 hp1) (one_le_pow₀ hk))
  have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ)≤140/9)
  have h2' := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ)≤30618/5)
  have ht0 : 0 ≤ 1/t := by positivity
  have hn0 := sq_nonneg N
  calc
    _ = (140/9:ℝ)*(k/(Real.sqrt 3*t*d*N))+(30618/5:ℝ)*(N^2/(Real.sqrt 3*Real.pi*k^2)) := by ring
    _ ≤ _ := by linarith

 
theorem cubic_sieve_thin_initial (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (M N : ℝ) (S : Finset Eisenstein) (u : Eisenstein → ℂ),
      1 ≤ M → 1 ≤ N → S ⊆ squarefreePrimaryBall N →
      (∀ b ∈ S,(9/10:ℝ)*N ≤ norm b) →
      ∑ m ∈ squarefreePrimaryBall M,cubicRowEnergy S u m ≤
        C*N^ε*(M+N^2)*∑ b ∈ S,‖u b‖^2 := by
  obtain ⟨C,hC,hCbound⟩ := sieve_divisor_power_bound ε hε
  refine ⟨Real.exp Real.pi*10000*C,by positivity,?_⟩
  intro M N S u hM hN hS hthin
  have hM0 : 0 < M := by linarith
  have ht : 0 < 1/M := by positivity
  have hb := cubic_gaussian_positive_bound (show 0<N by linarith) S hS hthin u (1/M) ht
    _ initial_cubicGaussianBound
  have hs : ∀ a ∈ S,primary a := fun a ha => (mem_squarefreePrimaryBall.mp (hS ha)).1
  apply (cubic_cutoff_le_gaussian hM0 S hs u).trans
  apply (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans
  have hh : (∑ k ∈ squarefreePrimaryBall N, ∑ d ∈ primaryDivisors k,
        (2/((Real.sqrt 3)*(1/M)*norm d)) *
        (7*(1+648*(N/norm k)/(4*Real.pi/(3*((1/M)*norm d)*((9/10:ℝ)*N/norm k)^2))) /
          ((9/10:ℝ)*N/norm k)) *
        ∑ l ∈ squarefreePrimaryBall (N/norm k),
          ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·), ‖u (k*a)‖^2) ≤
      10000*(M+N^2)*(C*N^ε*∑ b ∈ S,‖u b‖^2) := by
    calc
      _ ≤ ∑ k ∈ squarefreePrimaryBall N, ∑ _d ∈ primaryDivisors k,
          (10000*(M+N^2))*∑ l ∈ squarefreePrimaryBall (N/norm k),
            ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·),‖u (k*a)‖^2 := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hkp,hks,hkn⟩ := mem_squarefreePrimaryBall.mp hk
        apply Finset.sum_le_sum
        intro d hd
        have hdp := ((mem_primaryDivisors (primary_ne_zero hkp)).mp hd).1
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun a _ => sq_nonneg _)
        simpa using initial_positive_factor hN ht (one_le_norm (primary_ne_zero hkp)) hkn
          (one_le_norm (primary_ne_zero hdp))
      _ = (10000*(M+N^2))*(∑ k ∈ squarefreePrimaryBall N, ∑ _d ∈ primaryDivisors k,
          ∑ l ∈ squarefreePrimaryBall (N/norm k),
            ∑ a ∈ (sieveFiber N S k).filter (l ∣ ·),‖u (k*a)‖^2) := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hCbound N S u hN hS) (by positivity)
  apply (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans_eq
  ring



def sieveBin (S : Finset Eisenstein) (j : ℕ) : Finset Eisenstein :=
  S.filter fun b => (10/9:ℝ)^j ≤ norm b ∧ norm b < (10/9:ℝ)^(j+1)

lemma sieveBin_range {N : ℝ} (_ : 1 ≤ N) {J : ℕ}
    (hJ : (10/9:ℝ)^J ≤ N ∧ N < (10/9:ℝ)^(J+1))
    {S : Finset Eisenstein} (hS : S ⊆ squarefreePrimaryBall N)
    {b : Eisenstein} (hb : b ∈ S) :
    ∃ j ∈ Finset.range (J+1), b ∈ sieveBin S j := by
  obtain ⟨hp,hs,hn⟩ := mem_squarefreePrimaryBall.mp (hS hb)
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near (one_le_norm (primary_ne_zero hp))
    (by norm_num : (1:ℝ)<10/9)
  refine ⟨j,Finset.mem_range.mpr ?_,Finset.mem_filter.mpr ⟨hb,hj,hj'⟩⟩
  by_contra h
  have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤10/9) (show J+1 ≤ j by omega)
  linarith

lemma sieveBin_unique {S : Finset Eisenstein} {i j : ℕ} {b : Eisenstein}
    (hi : b ∈ sieveBin S i) (hj : b ∈ sieveBin S j) : i=j := by
  obtain ⟨_,hilo,hihi⟩ := Finset.mem_filter.mp hi
  obtain ⟨_,hjlo,hjhi⟩ := Finset.mem_filter.mp hj
  rcases lt_trichotomy i j with h|h|h
  · have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤10/9) (show i+1 ≤ j by omega)
    linarith
  · exact h
  · have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤10/9) (show j+1 ≤ i by omega)
    linarith

lemma sieveBin_sum {A : Type*} [AddCommMonoid A] {N : ℝ} (hN : 1 ≤ N) {J : ℕ}
    (hJ : (10/9:ℝ)^J ≤ N ∧ N < (10/9:ℝ)^(J+1))
    (S : Finset Eisenstein) (hS : S ⊆ squarefreePrimaryBall N) (f : Eisenstein → A) :
    ∑ j ∈ Finset.range (J+1),∑ b ∈ sieveBin S j,f b = ∑ b ∈ S,f b := by
  simp only [sieveBin,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨j,hj,hbj⟩ := sieveBin_range hN hJ hS hb
  rw [Finset.sum_eq_single j]
  · exact ite_eq_left (Finset.mem_filter.mp hbj).2
  · intro i hi hij
    apply ite_eq_right
    intro hbi
    exact hij (sieveBin_unique (Finset.mem_filter.mpr ⟨hb,hbi⟩) hbj)
  · exact fun h => (h hj).elim

lemma sieveBin_subset {N : ℝ} {S : Finset Eisenstein}
    (hS : S ⊆ squarefreePrimaryBall N) (j : ℕ) :
    sieveBin S j ⊆ squarefreePrimaryBall ((10/9:ℝ)^(j+1)) := by
  intro b hb
  obtain ⟨hb,hn,hn'⟩ := Finset.mem_filter.mp hb
  obtain ⟨hp,hs,_⟩ := mem_squarefreePrimaryBall.mp (hS hb)
  exact mem_squarefreePrimaryBall.mpr ⟨hp,hs,hn'.le⟩

lemma sieveBin_thin (S : Finset Eisenstein) (j : ℕ) {b : Eisenstein}
    (hb : b ∈ sieveBin S j) : (9/10:ℝ)*(10/9:ℝ)^(j+1) ≤ norm b := by
  convert (Finset.mem_filter.mp hb).2.1 using 1
  rw [pow_succ]
  ring

lemma sieveBin_top {N : ℝ} {J j : ℕ} (hJ : (10/9:ℝ)^J ≤ N)
    (hj : j ∈ Finset.range (J+1)) : (10/9:ℝ)^(j+1) ≤ (10/9:ℝ)*N := by
  have hjJ : j ≤ J := by have := Finset.mem_range.mp hj; omega
  have hp := (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤10/9) hjJ).trans hJ
  rw [pow_succ,mul_comm]
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

lemma sieveBin_count_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℝ) (J : ℕ),1≤N → (10/9:ℝ)^J ≤ N →
      (J+1:ℝ) ≤ C*N^ε := by
  let r : ℝ := (10/9:ℝ)^ε
  have hr : 1<r := Real.one_lt_rpow (by norm_num) hε
  refine ⟨r/(r-1),by positivity,?_⟩
  intro N J hN hJ
  have hB := one_add_mul_sub_le_pow (show (-1:ℝ)≤r by linarith) J
  have hpow : r^J ≤ N^ε := by
    have he : r^J = ((10/9:ℝ)^J)^ε := by
      dsimp only [r]
      simp_rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤10/9)]
      rw [mul_comm]
    rw [he]
    exact Real.rpow_le_rpow (by positivity) hJ hε.le
  have hrJ : 1 ≤ r^J := one_le_pow₀ hr.le
  have hR : (J+1:ℝ)*(r-1) ≤ r*r^J := by nlinarith
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (show 0<r-1 by linarith)).mpr
    (hR.trans (mul_le_mul_of_nonneg_left hpow (by linarith)))

lemma cubic_bin_operator_bound {N : ℝ} (hN : 1≤N) {J : ℕ}
    (hJ : (10/9:ℝ)^J ≤ N ∧ N < (10/9:ℝ)^(J+1))
    (S H : Finset Eisenstein) (hS : S ⊆ squarefreePrimaryBall N)
    (u : Eisenstein → ℂ) {K : ℝ}
    (hK : ∀ j ∈ Finset.range (J+1),
      ∑ m ∈ H,‖∑ b ∈ sieveBin S j,u b*cubicSymbol b m‖^2 ≤ K*∑ b ∈ sieveBin S j,‖u b‖^2) :
    ∑ m ∈ H,‖∑ b ∈ S,u b*cubicSymbol b m‖^2 ≤
      (J+1:ℝ)*K*∑ b ∈ S,‖u b‖^2 := by
  calc
    _ ≤ ∑ m ∈ H,(J+1:ℝ)*∑ j ∈ Finset.range (J+1),
        ‖∑ b ∈ sieveBin S j,u b*cubicSymbol b m‖^2 := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← sieveBin_sum hN hJ S hS]
      have hb := SieveOperator.sum_mul_norm_sq (Finset.range (J+1))
        (fun j => ∑ b ∈ sieveBin S j,u b*cubicSymbol b m) (fun _ => (1:ℂ))
      simpa [mul_comm] using hb
    _ = (J+1:ℝ)*∑ j ∈ Finset.range (J+1),∑ m ∈ H,
        ‖∑ b ∈ sieveBin S j,u b*cubicSymbol b m‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ (J+1:ℝ)*∑ j ∈ Finset.range (J+1),K*∑ b ∈ sieveBin S j,‖u b‖^2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hK)
      positivity
    _ = _ := by rw [← Finset.mul_sum,sieveBin_sum hN hJ S hS]; ring

 

theorem cubic_thin_to_full (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ,0<D ∧ ∀ (N : ℝ) (S H : Finset Eisenstein) (u : Eisenstein → ℂ)
      (K : ℝ → ℝ),
      1≤N → S ⊆ squarefreePrimaryBall N →
      (∀ X,1≤X → 0≤K X) → MonotoneOn K (Set.Ici 1) →
      (∀ (X : ℝ) (T : Finset Eisenstein),1≤X → T ⊆ squarefreePrimaryBall X →
        (∀ b ∈ T,(9/10:ℝ)*X ≤ norm b) →
        ∑ m ∈ H,‖∑ b ∈ T,u b*cubicSymbol b m‖^2 ≤ K X*∑ b ∈ T,‖u b‖^2) →
      ∑ m ∈ H,‖∑ b ∈ S,u b*cubicSymbol b m‖^2 ≤
        D*N^ε*K ((10/9:ℝ)*N)*∑ b ∈ S,‖u b‖^2 := by
  obtain ⟨D,hD,hcount⟩ := sieveBin_count_power ε hε
  refine ⟨D,hD,?_⟩
  intro N S H u K hN hS hK hmono hthin
  obtain ⟨J,hJ⟩ := exists_nat_pow_near hN (by norm_num : (1:ℝ)<10/9)
  have htop : 1 ≤ (10/9:ℝ)*N := by nlinarith
  have hb := cubic_bin_operator_bound hN hJ S H hS u (K := K ((10/9:ℝ)*N)) (by
    intro j hj
    have hj1 : 1 ≤ (10/9:ℝ)^(j+1) := one_le_pow₀ (by norm_num)
    apply (hthin _ (sieveBin S j) hj1 (sieveBin_subset hS j)
      (fun b hb => sieveBin_thin S j hb)).trans
    exact mul_le_mul_of_nonneg_right
      (hmono hj1 htop (sieveBin_top hJ.1 hj))
      (Finset.sum_nonneg fun b _ => sq_nonneg _))
  apply hb.trans
  have he := mul_le_mul_of_nonneg_right (hcount N J hN hJ.1)
    (mul_nonneg (hK _ htop) (Finset.sum_nonneg fun b (_ : b ∈ S) => sq_nonneg ‖u b‖))
  simpa only [mul_assoc] using he

end CubicFirstMoment
end

end OAI
