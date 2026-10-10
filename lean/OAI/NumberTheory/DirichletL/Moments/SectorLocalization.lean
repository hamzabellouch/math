import OAI.NumberTheory.DirichletL.Moments.Tail
import OAI.NumberTheory.DirichletL.Moments.DescentLedger

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

def cutoff (x : ℝ) : ℝ := Real.smoothTransition (2-2*x)

theorem cutoff_one (x : ℝ) (hx : x ≤ 1/2) : cutoff x=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_zero (x : ℝ) (hx : 1 ≤ x) : cutoff x=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

def annulus (x : ℝ) : ℝ := cutoff x-cutoff (2*x)

theorem annulus_zero_low (x : ℝ) (hx : x ≤ 1/4) : annulus x=0 := by
  rw [annulus, cutoff_one x (by linarith),cutoff_one (2*x) (by linarith),sub_self]

theorem annulus_zero_high (x : ℝ) (hx : 1 ≤ x) : annulus x=0 := by
  rw [annulus,cutoff_zero x hx,cutoff_zero (2*x) (by linarith),sub_self]

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

theorem annulus_smooth : ContDiff ℝ ∞ annulus := by
  have hc : ContDiff ℝ ∞ cutoff :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact hc.sub (hc.comp (contDiff_const.mul contDiff_id))

def dyadicScale (n : ℤ) : ℝ := (2:ℝ)^n

theorem dyadicScale_pos (n : ℤ) : 0 < dyadicScale n := by
  unfold dyadicScale
  positivity

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

def dyadicWeight (n : ℤ) (q : ℝ) : ℝ := annulus (q/dyadicScale n)

theorem dyadicWeight_smooth (n : ℤ) : ContDiff ℝ ∞ (dyadicWeight n) :=
  annulus_smooth.comp (contDiff_id.div_const _)

theorem dyadicWeight_bounds (n : ℤ) (q : ℝ) :
    0 ≤ dyadicWeight n q ∧ dyadicWeight n q ≤ 1 := annulus_bounds _

theorem dyadicWeight_zero_low (n : ℤ) (q : ℝ) (hq : q ≤ dyadicScale n/4) :
    dyadicWeight n q=0 := by
  apply annulus_zero_low
  apply (div_le_iff₀ (dyadicScale_pos n)).mpr
  linarith

theorem dyadicWeight_zero_high (n : ℤ) (q : ℝ) (hq : dyadicScale n ≤ q) :
    dyadicWeight n q=0 := by
  apply annulus_zero_high
  exact (le_div_iff₀ (dyadicScale_pos n)).mpr (by simpa using hq)

theorem dyadicWeight_support (n : ℤ) :
    Function.support (dyadicWeight n) ⊆ Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  intro q hq
  constructor
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_low n q h))
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_high n q h))

theorem dyadicWeight_tsupport (n : ℤ) :
    tsupport (dyadicWeight n) ⊆ Set.Icc (dyadicScale n/4) (dyadicScale n) :=
  closure_minimal (fun _ h => Set.Ioo_subset_Icc_self (dyadicWeight_support n h)) isClosed_Icc

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_finite (q : ℝ) : (Function.support (fun n => dyadicWeight n q)).Finite := by
  by_cases hq : 0 < q
  · obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
    apply (Set.toFinite (({k+1,k+2} : Finset ℤ) : Set ℤ)).subset
    intro n hn
    by_contra hh
    exact hn (dyadicWeight_outside_pair q k hlo hhi n hh)
  · have hz : ∀ n,dyadicWeight n q=0 := fun n =>
      dyadicWeight_zero_low n q ((le_of_not_gt hq).trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))
    simp [hz]

theorem dyadicWeight_summable (q : ℝ) : Summable (fun n => dyadicWeight n q) :=
  summable_of_hasFiniteSupport (dyadicWeight_finite q)

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

def Retained (R : ℝ) (n : ℤ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q ≤ R ∧ q ∈ tsupport (dyadicWeight n)

def retainedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then dyadicWeight n q else 0

def discardedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then 0 else dyadicWeight n q

theorem retained_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then dyadicWeight n q else 0) :=
  (dyadicWeight_summable q).indicator {n | Retained R n}

theorem discarded_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then 0 else dyadicWeight n q) := by
  have h := (dyadicWeight_summable q).sub (retained_summable R q)
  convert h using 1
  ext n
  split_ifs <;> simp

theorem retained_add_discarded (R q : ℝ) (hq : 0 < q) :
    retainedWeight R q+discardedWeight R q=1 := by
  rw [retainedWeight,discardedWeight,← (retained_summable R q).tsum_add (discarded_summable R q)]
  convert dyadicWeight_partition q hq using 1
  apply tsum_congr
  intro n
  split_ifs <;> simp

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem retainedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : retainedWeight R q=0 := by
  simp [retainedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem discardedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : discardedWeight R q=0 := by
  simp [discardedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_nonneg (R q : ℝ) : 0 ≤ retainedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact (dyadicWeight_bounds n q).1
  · exact le_rfl

theorem discardedWeight_nonneg (R q : ℝ) : 0 ≤ discardedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact (dyadicWeight_bounds n q).1

theorem retainedWeight_bounds (R q : ℝ) : 0 ≤ retainedWeight R q ∧ retainedWeight R q ≤ 1 := by
  refine ⟨retainedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := discardedWeight_nonneg R q
    linarith
  · rw [retainedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem discardedWeight_bounds (R q : ℝ) : 0 ≤ discardedWeight R q ∧ discardedWeight R q ≤ 1 := by
  refine ⟨discardedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := retainedWeight_nonneg R q
    linarith
  · rw [discardedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem retained_scale_le (R : ℝ) (n : ℤ) (hn : Retained R n) : dyadicScale n ≤ 4*R := by
  obtain ⟨q,hq,hqR,hs⟩ := hn
  have hb := (dyadicWeight_tsupport n hs).1
  linarith

theorem retainedWeight_zero_above (R q : ℝ) (hq : 4*R ≤ q) : retainedWeight R q=0 := by
  unfold retainedWeight
  trans ∑' _n : ℤ, (0:ℝ)
  · apply tsum_congr
    intro n
    split_ifs with hn
    · exact dyadicWeight_zero_high n q ((retained_scale_le R n hn).trans hq)
    · rfl
  · exact tsum_zero

theorem retainedWeight_enclosure (R q : ℝ) (hq : retainedWeight R q ≠ 0) : 0 < q ∧ q ≤ 4*R := by
  constructor
  · exact lt_of_not_ge (fun h => hq (retainedWeight_zero_nonpos R q h))
  · exact le_of_not_gt (fun h => hq (retainedWeight_zero_above R q h.le))

theorem discardedWeight_zero_below (R q : ℝ) (hq : q ≤ R) : discardedWeight R q=0 := by
  by_cases hp : 0 < q
  · unfold discardedWeight
    trans ∑' _n : ℤ, (0:ℝ)
    · apply tsum_congr
      intro n
      split_ifs with hn
      · rfl
      · by_contra hne
        exact hn ⟨q,hp,hq,subset_tsupport _ hne⟩
    · exact tsum_zero
  · exact discardedWeight_zero_nonpos R q (le_of_not_gt hp)

theorem discardedWeight_support (R q : ℝ) (hq : discardedWeight R q ≠ 0) : R < q :=
  lt_of_not_ge (fun h => hq (discardedWeight_zero_below R q h))

theorem retainedWeight_one_below (R q : ℝ) (hq : 0 < q) (hR : q ≤ R) : retainedWeight R q=1 := by
  have h := retained_add_discarded R q hq
  rwa [discardedWeight_zero_below R q hR,add_zero] at h

theorem finite_retained_integral_dyads (R : ℝ) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, 1 ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc (1:ℤ) (k:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have : (2:ℝ)^(0:ℤ) < (2:ℝ)^n := by simpa [dyadicScale] using hq.trans_lt hs
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp this
    omega
  · have h : (2:ℝ)^n < (2:ℝ)^(k:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hk
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h
    omega

theorem annulus_pos (x : ℝ) (hlo : 1/4 < x) (hhi : x < 1) : 0 < annulus x := by
  by_cases hx : x ≤ 1/2
  · rw [annulus,cutoff_one x hx]
    have h := Real.smoothTransition.lt_one_of_lt_one (by linarith : 2-2*(2*x) < 1)
    exact sub_pos.mpr h
  · rw [annulus,cutoff_zero (2*x) (by linarith),sub_zero]
    exact Real.smoothTransition.pos_of_pos (by linarith)

theorem dyadicWeight_support_eq (n : ℤ) :
    Function.support (dyadicWeight n)=Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  apply Set.Subset.antisymm (dyadicWeight_support n)
  intro q hq
  apply ne_of_gt
  apply annulus_pos
  · apply (lt_div_iff₀ (dyadicScale_pos n)).mpr
    linarith [hq.1]
  · exact (div_lt_one (dyadicScale_pos n)).mpr hq.2

theorem dyadicWeight_tsupport_eq (n : ℤ) :
    tsupport (dyadicWeight n)=Set.Icc (dyadicScale n/4) (dyadicScale n) := by
  rw [tsupport,dyadicWeight_support_eq,closure_Ioo]
  linarith [dyadicScale_pos n]

theorem retained_iff_scale (R : ℝ) (n : ℤ) : Retained R n ↔ dyadicScale n ≤ 4*R := by
  refine ⟨retained_scale_le R n,fun hn => ?_⟩
  refine ⟨dyadicScale n/4,div_pos (dyadicScale_pos n) (by norm_num),by linarith,?_⟩
  rw [dyadicWeight_tsupport_eq]
  exact ⟨le_rfl,by linarith [dyadicScale_pos n]⟩

theorem retained_boundary (n : ℤ) : Retained (dyadicScale n/4) n := by
  rw [retained_iff_scale]
  linarith

def normValue (h : O) : ℝ := Ideal.absNorm (Ideal.span {h})

theorem normValue_eq_embedding (h : O) : normValue h=‖eisEmbedding h‖^2 :=
  (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span h).symm

theorem normValue_mul (v h : O) : normValue (v*h)=normValue v*normValue h := by
  simp only [normValue,← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem retained_pullback (R : ℝ) (v h : O) :
    retainedWeight R (normValue (v*h))=retainedWeight R (normValue v*normValue h) := by
  rw [normValue_mul]

theorem retained_norm_enclosure (R : ℝ) (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : normValue h ≤ 4*R/normValue v := by
  have hb := (retainedWeight_enclosure R _ hne).2
  rw [normValue_mul] at hb
  apply (le_div_iff₀ (normValue_pos v hv)).mpr
  nlinarith

def frequencyRadius (Tsec Z ξ : ℝ) : ℝ := Tsec*Z^(ξ/2)

def frequencyLoss (Z Csec ξ : ℝ) : ℝ := ξ/2+Real.logb Z (4*Csec)

theorem frequencyLoss_nonneg (Z Csec ξ : ℝ) (hZ : 1 < Z) (hC : 1 ≤ Csec) (hξ : 0 ≤ ξ) :
    0 ≤ frequencyLoss Z Csec ξ := by
  have hlog := Real.logb_nonneg hZ (show 1 ≤ 4*Csec by linarith)
  unfold frequencyLoss
  linarith

theorem source_enclosure_power (Z Csec L ξ Nv : ℝ) (hZ : 1 < Z) (hC : 0 < Csec) (hNv : 0 < Nv) :
    4*(Csec*Z^L)*Z^(ξ/2)/Nv=Z^(L-Real.logb Z Nv+frequencyLoss Z Csec ξ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [frequencyLoss,show L-Real.logb Z Nv+(ξ/2+Real.logb Z (4*Csec))=
    (L+ξ/2)+Real.logb Z (4*Csec)-Real.logb Z Nv by ring,
    Real.rpow_sub hz,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz (ne_of_gt hZ),Real.rpow_logb hz (ne_of_gt hZ)]
  · ring
  · exact hNv
  · positivity

theorem actual_retained_row_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ) := by
  have hb := retained_norm_enclosure (frequencyRadius Tsec Z ξ) v h hv hne
  apply hb.trans
  rw [← source_enclosure_power Z Csec L ξ (normValue v) hZ hC (normValue_pos v hv)]
  apply div_le_div_of_nonneg_right _ (normValue_pos v hv).le
  dsimp only [frequencyRadius]
  nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]

theorem actual_nonempty_width (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  have he := (normValue_ge_one h hh).trans (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hne)
  by_contra hn
  have hh := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hn)
  linarith

theorem actual_declared_width_drop (Tsec Z Csec L ξ M J g g₂ t₂ σ q' : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0)
    (hwidth : (L-Real.logb Z (normValue v))+q'=M+J-g-g₂+t₂)
    (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂) :
    max 0 (L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)+q' ≤
      M-σ+frequencyLoss Z Csec ξ :=
  CenteredMomentDescentLedger.declared_width_drop M J g g₂ t₂ σ _ q' _ hwidth hg hcommon
    (actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne)

theorem retained_first_dyad_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z (dyadicScale n) ≤ L+frequencyLoss Z Csec ξ := by
  have hb := retained_scale_le _ n hn
  have hp := source_enclosure_power Z Csec L ξ 1 hZ hC (by norm_num)
  simp only [Real.logb_one,sub_zero,div_one] at hp
  have he : dyadicScale n ≤ Z^(L+frequencyLoss Z Csec ξ) := by
    rw [← hp]
    dsimp only [frequencyRadius] at hb
    nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]
  have hl := Real.logb_le_logb_of_le hZ (dyadicScale_pos n) he
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hl

def kernelReference (Tsec H : ℝ) : ℝ := Real.exp (-2*H)/Tsec

theorem kernelReference_pos (Tsec H : ℝ) (hT : 0 < Tsec) : 0 < kernelReference Tsec H :=
  div_pos (Real.exp_pos _) hT

theorem frequencyLoss_lt (Z Csec H ξ : ℝ) (hZ : 1 < Z) (hH : 0 ≤ H) (hξ : 0 < ξ)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) :
    frequencyLoss Z Csec ξ < ξ := by
  have h := div_nonneg (show 0 ≤ 2*H by linarith) (Real.log_pos hZ).le
  unfold frequencyLoss Real.logb
  linarith

theorem discarded_kernel_argument (Tsec Z Csec H ξ q : ℝ)
    (hT : 0 < Tsec) (hZ : 1 < Z) (hC : 1 ≤ Csec)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4)
    (hne : discardedWeight (frequencyRadius Tsec Z ξ) q ≠ 0) :
    Z^(ξ/4) ≤ kernelReference Tsec H*q := by
  have hlog := Real.log_nonneg (show 1 ≤ 4*Csec by linarith)
  have hlogdiv := div_nonneg hlog (Real.log_pos hZ).le
  have he : 2*H < ξ/4*Real.log Z :=
    (div_lt_iff₀ (Real.log_pos hZ)).mp (by linarith : 2*H/Real.log Z < ξ/4)
  have hs : Z^(ξ/4) ≤ Real.exp (-2*H)*Z^(ξ/2) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ),Real.rpow_def_of_pos (zero_lt_one.trans hZ),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hq := (discardedWeight_support _ q hne).le
  have hm := mul_le_mul_of_nonneg_left hq (kernelReference_pos Tsec H hT).le
  have hid : kernelReference Tsec H*frequencyRadius Tsec Z ξ=Real.exp (-2*H)*Z^(ξ/2) := by
    unfold kernelReference frequencyRadius
    field_simp
  rw [hid] at hm
  exact hs.trans hm

theorem retained_pullback_zero_extension (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) :
    retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) =
      if normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)
      then retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) else 0 := by
  split_ifs with hb
  · rfl
  · by_contra hn
    exact hb (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hn)

theorem actual_discarded_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K B : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K → 0 ≤ B →
      ∀ c : O → ℂ, (∀ h, ‖c h‖ ≤ B) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*
        paperRadialFourier W (K*normValue h)‖ ≤
      B*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := CenteredMomentTail.uniform_sector_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K B hT hZ hCsec hthreshold hK hB c hc
  let D : Set O := {h | discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0}
  have hb := ht W D (kernelReference Tsec H) (Z^(ξ/4)) B
    (kernelReference_pos Tsec H hT) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hB
    (fun h hh => by
      rw [← normValue_eq_embedding]
      exact discarded_kernel_argument Tsec Z Csec H ξ (normValue h) hT hZ hCsec hthreshold hh)
    K hK c (fun h => (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ))
    (fun h _ => hc h) (fun h _ => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg _ _)]
      exact (discardedWeight_bounds _ _).2)
  simp_rw [← normValue_eq_embedding] at hb
  have he := tsum_subtype_eq_of_support_subset (f := fun h : O =>
    (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*paperRadialFourier W (K*normValue h))
    (s := D) (by
      intro h hh
      change discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0
      intro hz
      exact hh (by simp [hz]))
  rwa [he] at hb

theorem actual_discarded_second_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ (u v : O) (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
        (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})),
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        CenteredMomentSupportedCorrelation.actualCorrelation u v hu hv (-h)*
        paperRadialFourier W (K*normValue h)‖ ≤
      (normValue u*normValue v)*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK u v hu hv
  exact ht W Tsec Z Csec H ξ K (normValue u*normValue v) hT hZ hCsec hthreshold hK
    (by unfold normValue; positivity) _ (fun h => CenteredMomentTail.actualCorrelation_norm_le u v hu hv (-h))

theorem actual_discarded_first_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (hinj : Function.Injective P) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
        (_hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (B : Finset ι) (c d : ι → ℕ)
        (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ),
      let r := CenteredMomentInitial.activeModulus P B c d
      let χr := CenteredMomentInitial.commonCharacter P hinj hg B c d
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        (normalizedResidueGauss r (CenteredMomentInitial.activeModulus_ne_zero P B c d) χr
            (Ideal.Quotient.mk _ h)*
          (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h)/
            (Real.sqrt (normValue a):ℂ))*
          star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h))/
            (Real.sqrt (normValue b):ℂ)))*paperRadialFourier W (K*normValue h)‖ ≤
      (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK ι P _ hinj hg hchar B c d a b ha hb χa χb
  dsimp only
  simpa only [one_mul] using ht W Tsec Z Csec H ξ K 1 hT hZ hCsec hthreshold hK zero_le_one _ (by
    intro h
    rw [norm_mul,norm_mul,norm_star]
    calc
      _ ≤ (1*1)*1 := mul_le_mul
        (mul_le_mul (CenteredMomentInitial.common_gauss_norm_le_one P hinj hg hchar B c d h)
          (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one a ha χa _)
          (norm_nonneg _) zero_le_one)
        (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one b hb χb _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num)

theorem retained_product_ne_zero (R : ℝ) (v h : O)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : v ≠ 0 ∧ h ≠ 0 := by
  have hp := (retainedWeight_enclosure R _ hne).1
  constructor <;> intro hz <;> simp [hz,normValue] at hp

theorem actual_nonempty_width_of_weight (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L) (v h : O)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  obtain ⟨hv,hh⟩ := retained_product_ne_zero _ v h hne
  exact actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne

theorem actual_second_pullback (R : ℝ) (Gc V h : O) :
    retainedWeight R (normValue ((Gc*V)*h))=
      retainedWeight R ((normValue Gc*normValue V)*normValue h) := by
  simp only [normValue_mul]

theorem retained_integral_empty (R : ℝ) (hR : 4*R < 1) (h : O) :
    retainedWeight R (normValue h)=0 := by
  by_contra hn
  have hh : h ≠ 0 := by
    intro hz
    subst h
    exact hn (by simpa [normValue] using retainedWeight_zero_nonpos R 0 le_rfl)
  have hb := (retainedWeight_enclosure R _ hn).2
  linarith [normValue_ge_one h hh]

theorem finite_retained_above (R a : ℝ) (ha : 0 < a) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, a ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk,_⟩ := exists_mem_Ico_zpow ha (by norm_num : (1:ℝ) < 2)
  obtain ⟨l,hl⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc k (l:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have h : (2:ℝ)^k < (2:ℝ)^n := hk.trans_lt (hq.trans_lt hs)
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le
  · have h : (2:ℝ)^n < (2:ℝ)^(l:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hl
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le

theorem retainedWeight_finite_formula (R a : ℝ) (ha : 0 < a) :
    ∃ S : Finset ℤ, ∀ q : ℝ, a ≤ q →
      retainedWeight R q=∑ n ∈ S, if Retained R n then dyadicWeight n q else 0 := by
  let hs := finite_retained_above R a ha
  refine ⟨hs.toFinset,fun q hq => ?_⟩
  apply tsum_eq_sum
  intro n hn
  split_ifs with hr
  · by_contra hne
    exact hn (hs.mem_toFinset.mpr ⟨hr,q,hq,hne⟩)
  · rfl

theorem retainedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (retainedWeight R) q := by
  obtain ⟨S,hS⟩ := retainedWeight_finite_formula R (q/2) (by linarith)
  have hc : ContDiff ℝ ∞ (fun x : ℝ => ∑ n ∈ S, if Retained R n then dyadicWeight n x else 0) := by
    apply ContDiff.sum
    intro n hn
    by_cases hr : Retained R n
    · simpa [hr] using dyadicWeight_smooth n
    · simpa [hr] using (contDiff_const : ContDiff ℝ ∞ (fun _x : ℝ => (0:ℝ)))
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show q/2 < q by linarith)] with x hx
  exact hS x hx.le

theorem discardedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (discardedWeight R) q := by
  have hc : ContDiffAt ℝ ∞ (fun x => (1:ℝ)-retainedWeight R x) q :=
    contDiffAt_const.sub (retainedWeight_smooth_positive R q hq)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  have he := retained_add_discarded R x hx
  linarith

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
