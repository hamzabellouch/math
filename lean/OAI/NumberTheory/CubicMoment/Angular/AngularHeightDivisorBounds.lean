import OAI.NumberTheory.CubicMoment.Angular.AngularHeightCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.CommonOuterLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.LargeDivisorLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.MellinSignedIntegration

namespace OAI

/-! The actual angular common-divisor mass: exact empty row, rough-divisor
split, and shortened outer-sieve bound. The constants do not depend on the
angular index, since its coefficient factors have modulus one. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def angular_fullPrimeDivisorMellinMass (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (H : Finset Eisenstein) (u N : ℝ) (f : Eisenstein) (t : ℝ) : ℝ :=
  ((∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a))*
        star (gramMellinPhase t (norm a/N))*star (cubicSymbol a h)‖^2)+
   (∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a))*
        gramMellinPhase t (norm a/N)*star (cubicSymbol a h)‖^2))/2

lemma angular_fullPrimeDivisorMellinMass_one (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (H : Finset Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    angular_fullPrimeDivisorMellinMass ℓ R W X e H u N 1 t =
      (fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
        fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2 := by
  simp only [angular_fullPrimeDivisorMellinMass,one_dvd,Finset.filter_true,
    fullStructuredHeightMass,angular_fullStructuredPrimeRow_norm ℓ R W X _ e u t hN,
    angular_fullStructuredPrimeRow_reverse_norm ℓ R W X _ e u t hN,
    add_comm (2*Real.pi*t) u,sub_eq_add_neg,add_comm (-(2*Real.pi*t)) u]


lemma angular_fullPrimeDivisorMellinMass_small {R D : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) (hrough : ∀ i, D < X i)
    (s : Finset Eisenstein) (hs : ∀ p ∈ s, primaryPrime p) (hsne : s.Nonempty)
    (hsmall : norm (∏ p ∈ s, p) ≤ D) (e : Eisenstein) (H : Finset Eisenstein)
    (u N t : ℝ) :
    angular_fullPrimeDivisorMellinMass ℓ R W X e H u N (∏ p ∈ s, p) t = 0 := by
  have hempty : (fullSquarefreePrimeSupport R W X e).filter
      (fun a => (∏ p ∈ s, p) ∣ a) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha,hsd⟩ := Finset.mem_filter.mp ha
    have hh := fullPrime_nonempty_divisor_large W X hX hlo hhi hrough s hs hsne
      (Finset.mem_filter.mp ha).1 hsd
    exact (not_lt_of_ge hsmall) hh
  simp only [angular_fullPrimeDivisorMellinMass,hempty,Finset.sum_empty,norm_zero,zero_pow
    (by decide : (2:ℕ) ≠ 0),Finset.sum_const_zero,zero_add,zero_div]

lemma angular_fullPrime_coprime_mass_split {R D : ℝ} (hD : 1 ≤ D)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) (H U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    coprimeMellinMass (fullSquarefreePrimeSupport R W X e) H U
      (fun a => star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a)))
      (fun a => star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a)))
      (fun a => norm a/N) t =
    (fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2+
    ∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
      angular_fullPrimeDivisorMellinMass ℓ R W X e H u N (∏ p ∈ s, p) t := by
  let F := fun s : Finset Eisenstein =>
    angular_fullPrimeDivisorMellinMass ℓ R W X e H u N (∏ p ∈ s, p) t
  have hsmall : (∑ s ∈ U.powerset.filter (fun s => norm (∏ p ∈ s, p) ≤ D), F s) = F ∅ := by
    apply Finset.sum_eq_single ∅
    · intro s hs hsne
      obtain ⟨hsU,hsmall⟩ := Finset.mem_filter.mp hs
      exact angular_fullPrimeDivisorMellinMass_small ℓ W X hX hlo hhi hrough s
        (fun p hp => hU p (Finset.mem_powerset.mp hsU hp))
        (Finset.nonempty_iff_ne_empty.mpr hsne) hsmall e H u N t
    · intro hn
      exact (hn (by simpa only [Finset.mem_filter,Finset.mem_powerset,Finset.empty_subset,
        true_and,Finset.prod_empty] using (show norm (1:Eisenstein) ≤ D by simpa [norm] using hD))).elim
  have hsplit := Finset.sum_filter_add_sum_filter_not U.powerset
    (fun s => norm (∏ p ∈ s, p) ≤ D) F
  rw [hsmall] at hsplit
  change (∑ s ∈ U.powerset, F s) = _
  rw [← hsplit]
  simp only [not_le] 
  congr 1
  exact angular_fullPrimeDivisorMellinMass_one ℓ R W X e H u t hN

lemma angular_fullPrimeDivisorMellinMass_le {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e : Eisenstein) (H : Finset Eisenstein) (u t : ℝ) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    angular_fullPrimeDivisorMellinMass ℓ R W X e H u N₀ f t ≤
      ((∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h 1 ℓ (u+2*Real.pi*t)‖^2)+
       (∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h 1 ℓ (u-2*Real.pi*t)‖^2))/2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
  apply add_le_add
  · exact Finset.sum_le_sum (fun h _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
      (angular_fullPrimeSliceRow_norm_le ℓ W X hX hlo hhi hf e h u t hN₀) 2)
  · exact Finset.sum_le_sum (fun h _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
      (angular_fullPrimeSliceRow_reverse_norm_le ℓ W X hX hlo hhi hf e h u t hN₀) 2)

theorem angular_fullPrime_divisor_outer_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
      (f e : Eisenstein) (H : Finset Eisenstein) (u t N₀ B N : ℝ),
      (∀ i, 0 < X i) → (∀ i x, x < 1 → W i x = 0) →
      (∀ i x, R < x → W i x = 0) → primary f → 0 < N₀ →
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ fullPrimeSliceSupport R W X f e, norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      angular_fullPrimeDivisorMellinMass ℓ R W X e H u N₀ f t ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
  obtain ⟨C,hC,houter⟩ := all_frequency_outer_sieve hε
  refine ⟨C,hC,?_⟩
  intro R W X f e H u t N₀ B N hX hlo hhi hf hN₀ hB hN hS hH
  have hbound (v : ℝ) :
      (∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h 1 ℓ v‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
    let β := fun n => fullPrimeCoefficient R W X (f*n)*theta ℓ n*mellinPhase v (norm n)
    have hp : ∀ n ∈ fullPrimeSliceSupport R W X f e,
        primary n ∧ Squarefree n ∧ norm n ≤ N := by
      intro n hn
      have hh := fullPrimeSliceSupport_bounds R W X f e hn
      exact ⟨hh.1,hh.2.1,hS n hn⟩
    have hh := houter (fullPrimeSliceSupport R W X f e) H B N hB hN hp hH β
    have he : (∑ n ∈ fullPrimeSliceSupport R W X f e, ‖β n‖^2) =
        ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [β,norm_mul,mellinPhase_norm,
        norm_theta (primary_ne_zero (fullPrimeSliceSupport_bounds R W X f e hn).1),mul_one]
    rw [he] at hh
    simpa only [fullPrimeSliceSum,one_mul,β] using hh
  apply (angular_fullPrimeDivisorMellinMass_le ℓ W X hX hlo hhi hf e H u t hN₀).trans
  have hp := hbound (u+2*Real.pi*t)
  have hn := hbound (u-2*Real.pi*t)
  linarith


theorem angular_fullPrime_large_divisor_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
      (e : Eisenstein) (H U : Finset Eisenstein) (u t N₀ B D : ℝ),
      1 ≤ R → (∀ i, 0 < X i) → (∀ i x, x < 1 → W i x = 0) →
      (∀ i x, R < x → W i x = 0) → (∀ p ∈ U, primaryPrime p) →
      0 < N₀ → 1 ≤ B → 1 ≤ D → D ≤ ∏ i, X i →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      let N := R^Fintype.card ι*(∏ i, X i)/D
      (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
        angular_fullPrimeDivisorMellinMass ℓ R W X e H u N₀ (∏ p ∈ s, p) t) ≤
      C*(2^Fintype.card ι:ℝ)*(2*B*N)^ε*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
        ∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2 := by
  obtain ⟨C,hC,hbound⟩ := angular_fullPrime_divisor_outer_mass ℓ (ι := ι) hε
  refine ⟨C,hC,?_⟩
  intro R W X e H U u t N₀ B D hR hX hlo hhi hU hN₀ hB hD hDL hH
  dsimp only
  let L := ∏ i, X i
  let N := R^Fintype.card ι*L/D
  let A := C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)
  have hL : 0 < L := Finset.prod_pos (fun i _ => hX i)
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hN : 1 ≤ N := by
    apply (le_div_iff₀ hD0).mpr
    have hRp : 1 ≤ R^Fintype.card ι := one_le_pow₀ hR
    simpa only [one_mul] using hDL.trans (le_mul_of_one_le_left hL.le hRp)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrow (s : Finset Eisenstein)
      (hs : s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p))) :
      angular_fullPrimeDivisorMellinMass ℓ R W X e H u N₀ (∏ p ∈ s, p) t ≤
        A*∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
          ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2 := by
    obtain ⟨hsU,hfD⟩ := Finset.mem_filter.mp hs
    have hf := primary_finset_prod s (fun p : Eisenstein => p)
      (fun p hp => (hU p (Finset.mem_powerset.mp hsU hp)).1)
    apply hbound R W X (∏ p ∈ s, p) e H u t N₀ B N hX hlo hhi hf hN₀ hB hN _ hH
    intro n hn
    apply (fullPrimeSliceSupport_bounds R W X _ e hn).2.2.2.trans
    exact div_le_div_of_nonneg_left (mul_nonneg (by positivity) hL.le) hD0 hfD.le
  have he := fullPrime_summed_slice_energy W X hX hlo hhi e U hU
  have hesub : (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
      ∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
        ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2) ≤
      (2^Fintype.card ι:ℝ)*∑ b ∈ fullSquarefreePrimeSupport R W X e,
        ‖fullPrimeCoefficient R W X b‖^2 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans he
  calc
    _ ≤ ∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
        A*∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
          ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2 := Finset.sum_le_sum hrow
    _ = A*(∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
        ∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
          ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((2^Fintype.card ι:ℝ)*∑ b ∈ fullSquarefreePrimeSupport R W X e,
        ‖fullPrimeCoefficient R W X b‖^2) := mul_le_mul_of_nonneg_left hesub hA
    _ = _ := by dsimp [A,N,L]; ring


theorem angular_fullPrime_large_divisor_log_saving {R δ : ℝ} (hR : 1 ≤ R)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (e : Eisenstein) (H U : Finset Eisenstein) (u t N₀ : ℝ),
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      1 ≤ B → B ≤ (L r)^(1+δ/4) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ p ∈ U, primaryPrime p) → 0 < N₀ →
      (∑ s ∈ U.powerset.filter (fun s => (L r)^δ < norm (∏ p ∈ s, p)),
        angular_fullPrimeDivisorMellinMass ℓ R (W r) X e H u N₀ (∏ p ∈ s, p) t) ≤
      K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,hC,hbound⟩ := angular_fullPrime_large_divisor_mass ℓ (ι := ι)
    (show 0 < δ/100 by positivity)
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  let A := R^Fintype.card ι
  let D := (2*A)^(δ/100)*(1+A^(2/3:ℝ)+A)
  have hA : 1 ≤ A := one_le_pow₀ hR
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (show 0 < δ/20 by positivity) (a+k))
  refine ⟨C*(2^Fintype.card ι:ℝ)*(E+1)*D,T₀,by positivity,?_⟩
  intro r X B e H U u t N₀ hT₀ hL hX hprod hB hBL hH hU hN₀
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hDel : 1 ≤ (L r)^δ := Real.one_le_rpow hL hδ.le
  have hDL : (L r)^δ ≤ L r := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL hδ₁
  let N := A*L r/(L r)^δ
  have hNeq : N = A*(L r)^(1-δ) := by
    dsimp [N]
    rw [Real.rpow_sub hLp,Real.rpow_one]
    ring
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hm := hbound R (W r) X e H U u t N₀ B ((L r)^δ) hR
    (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) hU hN₀ hB hDel
    (by simpa only [hprod] using hDL) hH
  rw [hprod] at hm
  have he : (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      ‖fullPrimeCoefficient R (W r) X b‖^2) ≤
      (E+1)*L r*(1+Real.log (L r))^a := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans
    apply (henergy r X hL hX hprod).trans
    nlinarith [mul_nonneg hLp.le (pow_nonneg hz.le a)]
  have hn := shortened_outer_power_saving hL (zero_lt_one.trans_le hB) hN hA hδ hδ₁
    (show δ/4 ≤ 1/4 by linarith) le_rfl hBL hNeq.le
  have hlog : (1+Real.log (L r))^a*(L r)^(-δ/20) ≤ 1/(1+Real.log (L r))^k := by
    rw [show -δ/20 = -(δ/20) by ring]
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  calc
    _ ≤ C*(2^Fintype.card ι:ℝ)*(2*B*N)^(δ/100)*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*((E+1)*L r*(1+Real.log (L r))^a) :=
      hm.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ = (C*(2^Fintype.card ι:ℝ)*(E+1)*(1+Real.log (L r))^a)*
        ((2*B*N)^(δ/100)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*L r) := by ring
    _ ≤ (C*(2^Fintype.card ι:ℝ)*(E+1)*(1+Real.log (L r))^a)*
        (D*(L r)^2*B^(1/3:ℝ)*(L r)^(-δ/20)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (C*(2^Fintype.card ι:ℝ)*(E+1)*D)*(L r)^2*B^(1/3:ℝ)*
        ((1+Real.log (L r))^a*(L r)^(-δ/20)) := by ring
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hlog
        (show 0 ≤ (C*(2^Fintype.card ι:ℝ)*(E+1)*D)*(L r)^2*B^(1/3:ℝ) by positivity)

theorem angular_fullPrime_coprime_mass_integral_le {R D : ℝ} (hD : 1 ≤ D)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) (H U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (u : ℝ) {N : ℝ} (hN : 0 < N)
    {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ t, 0 ≤ f t) {A : ℝ}
    (hlarge : ∀ t, (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
      angular_fullPrimeDivisorMellinMass ℓ R W X e H u N (∏ p ∈ s, p) t) ≤ A) :
    (∫ t : ℝ, f t * coprimeMellinMass (fullSquarefreePrimeSupport R W X e) H U
      (fun a => star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a)))
      (fun a => star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a)))
      (fun a => norm a/N) t) ≤
    (∫ t : ℝ, f t*((fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2)) + A*(∫ t : ℝ, f t) := by
  have hp := integrable_scaled_height_mass hf R H 1 e ℓ u W X (2*Real.pi)
  have hn := integrable_scaled_height_mass hf R H 1 e ℓ u W X (-(2*Real.pi))
  simp only [neg_mul] at hn
  have hs : Integrable (fun t : ℝ => f t*((fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2)) := by
    convert (hp.add hn).div_const 2 using 1
    ext t
    dsimp only [Pi.add_apply]
    ring
  calc
    _ ≤ ∫ t : ℝ, f t*((fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
        fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2)+A*f t := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall (fun t => mul_nonneg (hf0 t) (coprimeMellinMass_nonneg _ _ _ _ _ _ t)))
        (hs.add (hf.const_mul A))
      filter_upwards with t
      rw [angular_fullPrime_coprime_mass_split ℓ hD W X hX hlo hhi hrough e H U hU u t hN]
      calc
        _ ≤ f t*((fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
            fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2+A) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl (hlarge t)) (hf0 t)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = _ := by rw [integral_add hs (hf.const_mul A),integral_const_mul]

theorem angular_fullPrime_divisor_noncoprime_log_saving {R c η : ℝ} (hR : 1 ≤ R)
    (hc : 0 < c) (hc1 : c ≤ 1) (hηc : η ≤ c)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (d e : Eisenstein) (u : ℝ), T₀ ≤ L r → 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → (∀ i, (L r)^c < X i) →
      primary d → norm d ≤ L r → (L r)^(1-η) ≤ A →
      A ≤ (L r)^2/(1+Real.log (L r))^G →
      ‖divisorDispersionVariance d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A-
        divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,hC,hbound⟩ := fullPrime_divisor_noncoprime_outer (ι := ι)
    (show 0 < c/100 by positivity) (show c/100 ≤ 1 by linarith) hR V hV hV'
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (show 0 < c/4 by positivity) (a+k))
  let B := R^Fintype.card ι
  let F := (2:ℝ)^(3*Fintype.card ι)
  let K₀ := ‖normProfileFourier V 0‖/9
  let K₁ := K₀*F*(E+1)+3*C*B^(c/100)*F*(E+1)+1
  refine ⟨3*(a+k),K₁,T₀,by dsimp [K₁,K₀,F,B]; positivity,?_⟩
  intro r X A d e u hT₀ hL hX hprod hrough hd hdL hAlo hAhi
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hz1 : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hz : 0 < 1+Real.log (L r) := zero_lt_one.trans_le hz1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hh := hbound (W r) X (L r) ((L r)^c) A e d
    (angularHeightPrimeCoefficient ℓ R (W r) X) u (fun i => zero_lt_one.trans_le (hX i)) hprod hL
    (Real.one_le_rpow hL hc.le) hA hd (hlo r) (hhi r) hrough
  have hcost := commonOuterCost_power_saving V hC.le hB (norm_nonneg d) hdL
    hL hA hc hc1 hηc hAlo
  have he : (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      ‖angularHeightPrimeCoefficient ℓ R (W r) X b‖^2) ≤ (E+1)*L r*(1+Real.log (L r))^a := by
    rw [angularHeightPrimeCoefficient_energy]
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans
    apply (henergy r X hL hX hprod).trans
    nlinarith [mul_nonneg hLp.le (pow_nonneg hz.le a)]
  have hlattice := cube_lattice_error_scale hA hLp hz a k hAhi
  have hlog : (1+Real.log (L r))^a*(L r)^(-c/4) ≤ 1/(1+Real.log (L r))^k := by
    rw [show -c/4 = -(c/4) by ring]
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  have hpower : (L r)^(2/3:ℝ)*L r = (L r)^(5/3:ℝ) := by
    calc
      _ = (L r)^(2/3:ℝ)*(L r)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hLp]; norm_num
  have hsplit : ((K₀*A+3*C*B^(c/100)*A^(2/3:ℝ)*(L r)^(2/3:ℝ)*(L r)^(-c/4))*F)*
      ((E+1)*L r*(1+Real.log (L r))^a) =
      (K₀*F*(E+1))*(A*L r*(1+Real.log (L r))^a)+
      (3*C*B^(c/100)*F*(E+1))*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
        ((1+Real.log (L r))^a*(L r)^(-c/4)) := by
    rw [← hpower]
    ring
  apply (hh.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost (by positivity))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left he (by positivity)))).trans
  change ((K₀*A+3*C*B^(c/100)*A^(2/3:ℝ)*(L r)^(2/3:ℝ)*(L r)^(-c/4))*F)*
    ((E+1)*L r*(1+Real.log (L r))^a) ≤ _
  rw [hsplit]
  calc
    _ ≤ (K₀*F*(E+1))*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k)+
        (3*C*B^(c/100)*F*(E+1))*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
          (1/(1+Real.log (L r))^k) := add_le_add
      (mul_le_mul_of_nonneg_left hlattice (by dsimp [K₀,F]; positivity))
      (mul_le_mul_of_nonneg_left hlog (by dsimp [F,B]; positivity))
    _ = (K₀*F*(E+1)+3*C*B^(c/100)*F*(E+1))*
        (A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ K₁*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [K₁]
      linarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
