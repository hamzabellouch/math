import OAI.NumberTheory.PrimeGaps.LevelMoments

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem integral_eq_orthant_integral {j : ℕ} {f : (Fin j → ℝ) → ℝ}
    (hf : Function.support f ⊆ {t | ∀ i, 0 < t i}) :
    (∫ t, f t) = ∫ t in {t : Fin j → ℝ | ∀ i, 0 ≤ t i}, f t := by
  have hm : MeasurableSet {t : Fin j → ℝ | ∀ i, 0 ≤ t i} := by
    have heq : {t : Fin j → ℝ | ∀ i, 0 ≤ t i} =
        ⋂ i : Fin j, {t : Fin j → ℝ | 0 ≤ t i} := by ext t; simp
    rw [heq]
    exact MeasurableSet.iInter (fun i : Fin j =>
      (isClosed_le continuous_const (continuous_apply i)).measurableSet)
  rw [← integral_indicator hm]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ {t : Fin j → ℝ | ∀ i, 0 ≤ t i}
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    by_contra hn
    exact ht (fun i => (hf hn i).le)

theorem l2Mass_eq_orthant_integral {j : ℕ} {f : (Fin j → ℝ) → ℝ}
    (hf : Function.support f ⊆ {t | ∀ i, 0 < t i}) :
    l2Mass f = ∫ t in {t : Fin j → ℝ | ∀ i, 0 ≤ t i}, f t^2 := by
  apply integral_eq_orthant_integral
  intro t ht
  apply hf
  exact fun h => ht (by simp only [h, zero_pow (by decide : 2 ≠ 0)])

theorem deleteCoordinate_eq_orthant_integral {j : ℕ} {f : (Fin (j+1) → ℝ) → ℝ}
    (hf : Function.support f ⊆ {t | ∀ i, 0 < t i}) (t : Fin j → ℝ) :
    deleteCoordinate f t = ∫ u in Ici (0:ℝ), f (Fin.snoc t u) := by
  unfold deleteCoordinate
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Ici (0:ℝ)
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu]
    by_contra hn
    apply hu
    change 0 ≤ u
    simpa only [Fin.snoc_last] using (hf hn (Fin.last j)).le

def squareDimension (m : ℕ) : ℕ := (m+1)^2

theorem squareDimension_pos (m : ℕ) : 0 < squareDimension m := by
  unfold squareDimension
  positivity

theorem active_length_le_squareDimension (m : ℕ) : m+1 ≤ squareDimension m := by
  unfold squareDimension
  nlinarith [Nat.zero_le m]

theorem squareDimension_strictMono : StrictMono squareDimension := by
  intro m n hmn
  unfold squareDimension
  nlinarith

theorem tendsto_squareDimension : Tendsto squareDimension atTop atTop :=
  squareDimension_strictMono.tendsto_atTop

theorem tendsto_inverse_squareDimension :
    Tendsto (fun m : ℕ => ((squareDimension m:ℕ):ℝ)⁻¹) atTop (nhds 0) :=
  (tendsto_natCast_atTop_atTop.comp tendsto_squareDimension).inv_tendsto_atTop

theorem tendsto_inverse_active_length :
    Tendsto (fun m : ℕ => (((m+1):ℕ):ℝ)⁻¹) atTop (nhds 0) :=
  (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop

theorem rectangle_error_tendsto_zero (v d : ℝ) :
    Tendsto (fun m : ℕ => v/((squareDimension m:ℝ)*d^2)) atTop (nhds 0) := by
  have h := tendsto_inverse_squareDimension.const_mul (v/(d^2))
  simpa only [mul_zero, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm (d^2)⁻¹] using h

theorem square_ratio_eq_inverse (m : ℕ) :
    ((m+1:ℕ):ℝ)/(squareDimension m:ℝ) = ((m+1:ℕ):ℝ)⁻¹ := by
  have hm : ((m+1:ℕ):ℝ) ≠ 0 := by positivity
  unfold squareDimension
  rw [Nat.cast_pow]
  field_simp

theorem cancellation_bound_tendsto_zero (lambda v d : ℝ) :
    Tendsto (fun m : ℕ => lambda * (2/((m+1:ℕ):ℝ) +
      (((m+1:ℕ):ℝ)/(squareDimension m:ℝ))^2 +
      4*v/((squareDimension m:ℝ)*d^2))) atTop (nhds 0) := by
  have h1 := tendsto_inverse_active_length.const_mul 2
  have h2 := tendsto_inverse_active_length.pow 2
  have h3 := rectangle_error_tendsto_zero (4*v) d
  have h := ((h1.add h2).add h3).const_mul lambda
  simp only [square_ratio_eq_inverse]
  simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_add, div_eq_mul_inv] using h

theorem cancellationFamily_W_tendsto {g chi : ℝ → ℝ} {lambda beta : ℝ}
    (hlambda : 0 < lambda) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hg2 : (∫ u, g u^2) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta) :
    Tendsto (fun m => familyW lambda (squareDimension m)
      (cancellationFamily g chi lambda (squareDimension m) (m+1))) atTop (nhds 1) := by
  let d := beta - ∫ u, u*g u^2
  let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
  have hlo := (rectangle_error_tendsto_zero v d).const_sub 1
  simp only [sub_zero] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
  · intro m
    exact (cancellationFamily_W_bounds hlambda (Nat.succ_pos m)
      (active_length_le_squareDimension m) hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu).1
  · intro m
    exact (cancellationFamily_W_bounds hlambda (Nat.succ_pos m)
      (active_length_le_squareDimension m) hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu).2

theorem cancellationFamily_V_tendsto {g chi : ℝ → ℝ} {lambda beta B : ℝ}
    (hlambda : 0 < lambda) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hgn : ∀ u, 0 ≤ g u)
    (hg2 : (∫ u, g u^2) = 1) (hg1 : (∫ u, g u) = Real.sqrt lambda)
    (hB : ∀ u ∈ Function.support g, u ≤ B) (hB0 : 0 ≤ B)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta) :
    Tendsto (fun m => familyV lambda (squareDimension m)
      (cancellationFamily g chi lambda (squareDimension m) (m+1))) atTop (nhds 0) := by
  let d := beta - ∫ u, u*g u^2
  let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
  have hBdiv : Tendsto (fun m => B/(squareDimension m:ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inverse_squareDimension.const_mul B
  have hBk : ∀ᶠ m in atTop, B/(squareDimension m:ℝ) ≤ d/2 := by
    exact ((tendsto_order.mp hBdiv).2 (d/2) (by dsimp only [d]; linarith)).mono (fun _ h => h.le)
  apply squeeze_zero' (Eventually.of_forall fun m => familyV_nonneg hlambda _ _)
    _ (cancellation_bound_tendsto_zero lambda v d)
  filter_upwards [hBk] with m hm
  exact cancellationFamily_V_bound hlambda (Nat.succ_pos m)
    (active_length_le_squareDimension m) hg hgc hgs hgn hg2 hg1 hB hB0 hchi hchi0 hchi1 hflat hmu hm

def AdmissibleFamily (tau : ℝ) (k : ℕ) (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : Prop :=
  0 < k ∧
  (∀ j, j ≤ k → ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
    tsupport (f j) ⊆ positiveSimplex j tau ∧ SymmetricFunction (f j)) ∧
  (∀ j, k < j → f j = 0)

theorem exists_canceling_families {lambda tau : ℝ} (hlambda : 0 < lambda) (htau : 0 < tau) :
    ∃ f : (m j : ℕ) → (Fin j → ℝ) → ℝ,
      (∀ m, AdmissibleFamily tau (squareDimension m) (f m) ∧ f m 0 = 0) ∧
      Tendsto (fun m => familyW lambda (squareDimension m) (f m)) atTop (nhds 1) ∧
      Tendsto (fun m => familyV lambda (squareDimension m) (f m)) atTop (nhds 0) := by
  let beta := tau/3
  let gamma := 2*tau/3
  have hb : 0 < beta := by dsimp only [beta]; positivity
  have hbg : beta < gamma := by dsimp only [beta, gamma]; linarith
  have hgt : gamma < tau := by dsimp only [gamma]; linarith
  obtain ⟨g, hgsmooth, hgc, hgs, hgn, hg2, hg1, hmu⟩ := exists_small_first_moment_profile hlambda hb
  let chi := simplexCutoff beta gamma
  have hchi : ContDiff ℝ ∞ chi := simplexCutoff_smooth beta gamma
  have hc0 : ∀ s, 0 ≤ chi s := simplexCutoff_nonneg beta gamma
  have hc1 : ∀ s, chi s ≤ 1 := simplexCutoff_le_one beta gamma
  have hcflat : ∀ s ≤ beta, chi s = 1 := fun _ hs => simplexCutoff_eq_one hbg hs
  have hcz : ∀ s, gamma ≤ s → chi s = 0 := fun _ hs => simplexCutoff_eq_zero hbg hs
  obtain ⟨b, hbnd⟩ := hgc.bddAbove
  let B := max b 0
  have hB : ∀ u ∈ Function.support g, u ≤ B := fun u hu =>
    (hbnd (subset_closure hu)).trans (le_max_left b 0)
  have hB0 : 0 ≤ B := le_max_right b 0
  have hsupport : Function.support g ⊆ Ioi 0 := fun _ hu => hgs (subset_closure hu)
  refine ⟨fun m => cancellationFamily g chi lambda (squareDimension m) (m+1), ?_, ?_, ?_⟩
  · intro m
    refine ⟨⟨squareDimension_pos m, ?_, ?_⟩, cancellationFamily_zero _ _ _ _ _⟩
    · intro j _
      exact cancellationFamily_properties (squareDimension_pos m) hgsmooth hgc hgs hchi hgt hcz j
    · intro j hj
      exact cancellationFamily_above _ _ _ _ _ hj
  · exact cancellationFamily_W_tendsto hlambda hgsmooth.continuous hgc hsupport hg2
      hchi.continuous hc0 hc1 hcflat hmu
  · exact cancellationFamily_V_tendsto hlambda hgsmooth.continuous hgc hsupport hgn hg2 hg1
      hB hB0 hchi.continuous hc0 hc1 hcflat hmu

theorem exists_family_small_marked_ratio {lambda tau epsilon : ℝ}
    (hlambda : 0 < lambda) (htau : 0 < tau) (hepsilon : 0 < epsilon) :
    ∃ k : ℕ, ∃ f : (j : ℕ) → (Fin j → ℝ) → ℝ,
      AdmissibleFamily tau k f ∧ f 0 = 0 ∧
      0 < familyW lambda k f ∧ familyV lambda k f / familyW lambda k f ≤ epsilon := by
  obtain ⟨f, hf, hW, hV⟩ := exists_canceling_families hlambda htau
  have hWpos : ∀ᶠ m in atTop, 0 < familyW lambda (squareDimension m) (f m) :=
    (tendsto_order.mp hW).1 0 (by norm_num)
  have hratio : Tendsto (fun m => familyV lambda (squareDimension m) (f m) /
      familyW lambda (squareDimension m) (f m)) atTop (nhds 0) := by
    have hdiv := hV.div hW (by norm_num : (1:ℝ) ≠ 0)
    rw [zero_div] at hdiv
    exact hdiv
  have hsmall := (tendsto_order.mp hratio).2 epsilon hepsilon
  obtain ⟨m, hmW, hmV⟩ := (hWpos.and hsmall).exists
  exact ⟨squareDimension m, f m, (hf m).1, (hf m).2, hmW, hmV.le⟩

def divisorMultiplicity (k n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k) n

theorem divisorMultiplicity_one (k : ℕ) : divisorMultiplicity k 1 = 1 := by
  exact (ArithmeticFunction.isMultiplicative_zeta.pow).1

theorem divisorMultiplicity_succ (k n : ℕ) :
    divisorMultiplicity (k+1) n = ∑ d ∈ n.divisors, divisorMultiplicity k d := by
  simp only [divisorMultiplicity, pow_succ, ArithmeticFunction.mul_zeta_apply]

theorem divisorMultiplicity_prime (k : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    divisorMultiplicity k p = k := by
  induction k with
  | zero => simp [divisorMultiplicity, hp.ne_one]
  | succ k ih =>
    rw [divisorMultiplicity_succ, hp.divisors]
    simp [hp.ne_one.symm, divisorMultiplicity_one, ih, Nat.add_comm]

theorem divisorMultiplicity_squarefree (k : ℕ) {q : ℕ} (hq : Squarefree q) :
    divisorMultiplicity k q = k ^ q.primeFactors.card := by
  rw [divisorMultiplicity, ← ArithmeticFunction.IsMultiplicative.prod_primeFactors
    (ArithmeticFunction.isMultiplicative_zeta.pow) hq]
  calc
    _ = ∏ p ∈ q.primeFactors, k := Finset.prod_congr rfl fun p hp =>
      divisorMultiplicity_prime k (Nat.prime_of_mem_primeFactors hp)
    _ = _ := by simp

theorem reciprocal_divisor_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d : ℝ)) * (harmonic Q : ℝ) := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1/x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q,d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq,hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q/d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
    obtain ⟨hq,hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq',hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q/d = q'/d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) =
      ∑ x ∈ s, f (e x).1 / (e x).1 / (e x).2 := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    dsimp only [e]
    rw [div_div, ← Nat.cast_mul, Nat.mul_div_cancel' hdq]
  rw [hsum]
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [t, Finset.sum_product, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
        harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.sum_comm]

theorem sum_divisorMultiplicity_reciprocal_le (k Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (divisorMultiplicity k q : ℝ) / (q : ℝ)) ≤
      (harmonic Q : ℝ) ^ k := by
  induction k with
  | zero =>
    by_cases hQ : Q = 0
    · subst Q; simp
    · have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
      simp [divisorMultiplicity, ArithmeticFunction.one_apply, ite_div, hQ1]
  | succ k ih =>
    have h := reciprocal_divisor_sum_le (fun n => (divisorMultiplicity k n : ℝ))
      (fun n => Nat.cast_nonneg _) Q
    simp only [divisorMultiplicity_succ, Nat.cast_sum] at ⊢
    apply h.trans
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right ih (by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem squarefree_reciprocal_weight_bound (T Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, if Squarefree q then (T : ℝ)^q.primeFactors.card / q else 0) ≤
      (harmonic Q : ℝ)^T := by
  classical
  apply (Finset.sum_le_sum (g := fun q => (divisorMultiplicity T q : ℝ)/(q:ℝ)) ?_).trans
    (sum_divisorMultiplicity_reciprocal_le T Q)
  intro q _
  split_ifs with hq
  · rw [divisorMultiplicity_squarefree T hq, Nat.cast_pow]
  · positivity

theorem squarefree_totient_lower {q : ℕ} (hq : Squarefree q) :
    q ≤ 2 ^ q.primeFactors.card * q.totient := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hq,
    Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero), one_mul]
  calc
    q = ∏ p ∈ q.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hq).symm
    _ ≤ ∏ p ∈ q.primeFactors, 2 * (p-1) := by
      apply Finset.prod_le_prod
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem weighted_error_square_bound (K Q : ℕ) (E : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    {X L : ℝ} (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hb : ∀ q ∈ Finset.Icc 1 Q, Squarefree q →
      E q ≤ X/(q:ℝ) * (L + 2^q.primeFactors.card)) :
    (∑ q ∈ Finset.Icc 1 Q, if Squarefree q then (K:ℝ)^q.primeFactors.card * E q else 0)^2 ≤
      (∑ q ∈ Finset.Icc 1 Q, E q) * X *
        (L * (harmonic Q : ℝ)^(K^2) + (harmonic Q : ℝ)^(2*K^2)) := by
  classical
  let s := Finset.Icc 1 Q
  let w : ℕ → ℝ := fun q => if Squarefree q then (K:ℝ)^q.primeFactors.card else 0
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun q => Real.sqrt (E q))
    (fun q => w q * Real.sqrt (E q))
  have heq1 : ∀ q, Real.sqrt (E q) * (w q * Real.sqrt (E q)) = w q * E q := by
    intro q
    calc
      _ = w q * (Real.sqrt (E q))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hE q)]
  simp only [heq1, mul_pow, Real.sq_sqrt (hE _)] at hcs
  have hsecond : (∑ q ∈ s, w q ^ 2 * E q) ≤
      X * (L * (harmonic Q : ℝ)^(K^2) + (harmonic Q : ℝ)^(2*K^2)) := by
    have hterm : ∀ q ∈ s, w q^2 * E q ≤
        X * (L * (if Squarefree q then ((K^2:ℕ):ℝ)^q.primeFactors.card / q else 0) +
          (if Squarefree q then ((2*K^2:ℕ):ℝ)^q.primeFactors.card / q else 0)) := by
      intro q hq
      have hqR : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
      by_cases hsq : Squarefree q
      · simp only [w, ite_eq_left hsq]
        calc
          _ ≤ ((K:ℝ)^q.primeFactors.card)^2 * (X/(q:ℝ) * (L+2^q.primeFactors.card)) :=
            mul_le_mul_of_nonneg_left (hb q hq hsq) (sq_nonneg _)
          _ = _ := by
            rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_pow, ← pow_mul, Nat.mul_comm,
              pow_mul]
            ring
      · simp [w, hsq]
    calc
      _ ≤ ∑ q ∈ s, X * (L *
          (if Squarefree q then ((K^2:ℕ):ℝ)^q.primeFactors.card / q else 0) +
          (if Squarefree q then ((2*K^2:ℕ):ℝ)^q.primeFactors.card / q else 0)) :=
        Finset.sum_le_sum hterm
      _ = X * (L * (∑ q ∈ s, if Squarefree q then ((K^2:ℕ):ℝ)^q.primeFactors.card/q else 0) +
          ∑ q ∈ s, if Squarefree q then ((2*K^2:ℕ):ℝ)^q.primeFactors.card/q else 0) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (squarefree_reciprocal_weight_bound (K^2) Q) hL)
          (squarefree_reciprocal_weight_bound (2*K^2) Q)) hX
  have hsumE : 0 ≤ ∑ q ∈ s, E q := Finset.sum_nonneg fun q _ => hE q
  have h := hcs.trans (mul_le_mul_of_nonneg_left hsecond hsumE)
  simp only [w, ite_mul, zero_mul] at h
  simpa only [mul_assoc] using h

theorem markedClassError_trivial {X H q a c : ℕ} (hX : 1 ≤ X) (hq : 0 < q)
    (hqX : q ≤ X) (ha : a ≤ H) (hc : c < q) (hsq : Squarefree q) :
    |(∑ m ∈ residueStarts X q c, theta (m+a)) - (X:ℝ)/q.totient| ≤
      (X:ℝ)/(q:ℝ) * (3 * Real.log (2*X+H) + 2^q.primeFactors.card) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hphi : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hXq : (1:ℝ) ≤ (X:ℝ)/q := (le_div_iff₀ hqR).mpr (by simpa using (show (q:ℝ) ≤ X by exact_mod_cast hqX))
  have hboundpos : (1:ℝ) ≤ 2*X+H := by exact_mod_cast (show 1 ≤ 2*X+H by omega)
  have hlog : 0 ≤ Real.log (2*X+H) := Real.log_nonneg hboundpos
  have htheta : ∀ m ∈ residueStarts X q c, theta (m+a) ≤ Real.log (2*X+H) := by
    intro m hm
    have hmhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).2
    by_cases hp : Nat.Prime (m+a)
    · rw [theta, ite_eq_left hp]
      exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show m+a ≤ 2*X+H by omega))
    · simpa [theta, hp]
  have hsum : (∑ m ∈ residueStarts X q c, theta (m+a)) ≤
      3 * ((X:ℝ)/q) * Real.log (2*X+H) := by
    calc
      _ ≤ ∑ m ∈ residueStarts X q c, Real.log (2*X+H) := Finset.sum_le_sum htheta
      _ = ((residueStarts X q c).card:ℝ) * Real.log (2*X+H) := by simp
      _ ≤ ((X:ℝ)/q+2) * Real.log (2*X+H) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have hh := (abs_le.mp (residueStarts_card_error X hq hc)).2
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlog
  have htot : (X:ℝ)/q.totient ≤ (X:ℝ)/q * (2:ℝ)^q.primeFactors.card := by
    have ht : (q:ℝ) ≤ (2:ℝ)^q.primeFactors.card * q.totient := by
      exact_mod_cast squarefree_totient_lower hsq
    apply (div_le_iff₀ hphi).mpr
    have hx := mul_le_mul_of_nonneg_left ht (show 0 ≤ (X:ℝ)/q by positivity)
    field_simp at hx ⊢
    nlinarith
  calc
    _ ≤ (∑ m ∈ residueStarts X q c, theta (m+a)) + (X:ℝ)/q.totient := by
      have hs0 : 0 ≤ ∑ m ∈ residueStarts X q c, theta (m+a) :=
        Finset.sum_nonneg fun m _ => theta_nonneg (m+a)
      have ht0 : 0 ≤ (X:ℝ)/q.totient := by positivity
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ ≤ 3 * ((X:ℝ)/q) * Real.log (2*X+H) + (X:ℝ)/q * 2^q.primeFactors.card :=
      add_le_add hsum htot
    _ = _ := by ring

theorem markedError_trivial {X H q : ℕ} (hX : 1 ≤ X) (hq : 0 < q)
    (hqX : q ≤ X) (hsq : Squarefree q) :
    (markedError X H q : ℝ) ≤
      (X:ℝ)/(q:ℝ) * (3 * Real.log (2*X+H) + 2^q.primeFactors.card) := by
  have hnonneg : 0 ≤ (X:ℝ)/(q:ℝ) *
      (3 * Real.log (2*X+H) + 2^q.primeFactors.card) := by
    have : 0 ≤ Real.log (2*X+H) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H by omega))
    positivity
  change markedError X H q ≤ NNReal.mk _ hnonneg
  apply Finset.sup_le
  rintro ⟨a,c⟩ hac
  have ha : a ≤ H := by simpa using (Finset.mem_product.mp hac).1
  have hc : c < q := Finset.mem_range.mp (Finset.mem_product.mp hac).2
  dsimp only
  split_ifs
  · exact markedClassError_trivial hX hq hqX ha hc hsq
  · exact zero_le

noncomputable def residueSlice (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n

noncomputable def residuePrefix (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  residueSlice f 0 Y q c

theorem residuePrefix_sub (f : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) (q c : ℕ) :
    residuePrefix f U q c - residuePrefix f L q c = residueSlice f L U q c := by
  classical
  have hunion : Finset.Ioc 0 U = Finset.Ioc 0 L ∪ Finset.Ioc L U := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_union]
    omega
  have hd : Disjoint ((Finset.Ioc 0 L).filter fun n => n % q = c)
      ((Finset.Ioc L U).filter fun n => n % q = c) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have hl := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    have hu := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
    omega
  simp only [residuePrefix, residueSlice, hunion, Finset.filter_union, Finset.sum_union hd]
  ring

theorem shifted_sum_eq_residueSlice (f : ℕ → ℝ) (X q a : ℕ) {c : ℕ} (hc : c < q) :
    (∑ m ∈ residueStarts X q c, f (m+a)) =
      residueSlice f (X+a) (2*X+a) q ((c+a)%q) := by
  classical
  apply Finset.sum_bij (fun m _ => m+a)
  · intro m hm
    obtain ⟨hm,hmc⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmlo,hmhi⟩ := Finset.mem_Ioc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    have hh : Nat.ModEq q m c := by
      change m % q = c % q
      rw [hmc, Nat.mod_eq_of_lt hc]
    exact hh.add_right a
  · intro m _ n _ heq
    omega
  · intro n hn
    obtain ⟨hn,hnc⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlo,hnhi⟩ := Finset.mem_Ioc.mp hn
    have ha : a ≤ n := by omega
    refine ⟨n-a, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩,
      Nat.sub_add_cancel ha⟩
    have hh : Nat.ModEq q ((n-a)+a) (c+a) := by
      change ((n-a)+a) % q = (c+a) % q
      simpa only [Nat.sub_add_cancel ha] using hnc
    have hhc := Nat.ModEq.add_right_cancel' a hh
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hc] using hhc
  · intro m _
    rfl

end LargePrimeGaps

end OAI
