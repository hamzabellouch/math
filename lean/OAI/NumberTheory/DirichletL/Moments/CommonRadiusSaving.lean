import OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadiusSaving
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem common_saving_identity (c d x w q wo B sigma branch delta reserve ell : ℝ) :
    firstSaving c (d+x) w q wo B
      (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell =
      c/6+5*d/6+w/3+q/6+wo+B-5*max (d-c-2*w+wo) 0/6-
        5*branch*sigma/6-5*(delta+reserve)/6+ell := by
  unfold firstSaving
  ring

theorem common_saving_lower (c d x w q wo B sigma branch delta reserve ell : ℝ)
    (hc : 0≤c) (hw : 0≤w) (hq : 0≤q) (hwo : 0≤wo) (hB : 0≤B)
    (hallow : 3*c-5*d≤6*B+q) :
    2*(c+w)/3-max (w/3-wo) 0-5*branch*sigma/6-5*(delta+reserve)/6+ell≤
      firstSaving c (d+x) w q wo B
        (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell := by
  rw [common_saving_identity]
  have hm0 := le_max_right (w/3-wo) (0:ℝ)
  have hm1 := le_max_left (w/3-wo) (0:ℝ)
  by_cases h : 0≤d-c-2*w+wo
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem main_saving_lower (c d x q B sigma delta reserve : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q) :
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+x) 0 q 0 B
        (x+max (d-c) 0+2*sigma+delta+reserve) (sigma/3) := by
  have hh := common_saving_lower c d x 0 q 0 B sigma 2 delta reserve (sigma/3)
    hc (by norm_num) hq (by norm_num) hB hallow
  norm_num only [zero_div,sub_zero,add_zero,mul_zero,max_self] at hh
  linarith

theorem error_penalty_le (l sigma : ℝ) (hl : 0≤l) (hu : l≤sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0≤2*sigma/3 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [Nat.cast_ofNat,ite_false,ite_true,
    one_mul,sub_zero] <;> apply max_le <;> linarith

def errorLoss (sigma : ℝ) (k : ℕ) : ℝ :=
  if k=1 then 5*sigma/6 else if k=6 then 3*sigma/2 else 23*sigma/18

theorem error_penalty_refined (l sigma : ℝ) (hl : 0≤l) (hu : l≤sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0+5*sigma/6≤errorLoss sigma k := by
  have hs : 0≤sigma := by linarith
  rcases hk with rfl|rfl|rfl
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_one,one_mul]
    have hm : max (l/3-l) 0=0 := max_eq_right (by linarith)
    rw [hm,zero_add]
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat,sub_zero]
    have hm : max (6*l/3) 0≤2*sigma/3 := max_le (by linarith) (by linarith)
    linarith
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat]
    have hm : max (7*l/3-l) 0≤4*sigma/9 := max_le (by linarith) (by linarith)
    linarith

theorem errorLoss_le (sigma : ℝ) (hs : 0≤sigma) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7) : errorLoss sigma k≤3*sigma/2 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [errorLoss,ite_true,ite_false] <;> linarith

theorem error_saving_refined (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_refined l sigma hl hu k hk]

theorem error_saving_lower (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_le l sigma hl hu k hk]

theorem common_gain_width (d x c w wo sigma delta reserve branch : ℝ)
    (hs : 0≤sigma) (hd : 0≤delta) (hr : 0≤reserve) (hb : 1≤branch)
    (hx : -delta≤x) :
    0≤x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve ∧
    (d+x)-c-2*w+wo+sigma≤
      x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve := by
  have h0 := le_max_right (d-c-2*w+wo) (0:ℝ)
  have h1 := le_max_left (d-c-2*w+wo) (0:ℝ)
  constructor <;> nlinarith

theorem saving_power_factor (Z F c w sigma delta reserve : ℝ) (hZ : 1≤Z)
    (hF : 2*(c+w)/3-3*sigma/2-5*(delta+reserve)/6≤F) :
    Z^(-F)≤Z^(-2*(c+w)/3+3*sigma/2+5*(delta+reserve)/6) := by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  linarith

theorem main_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z) :
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j=
      (K0-j)+max (d-c) 0+2*sigma+delta+reserve := by
  rw [mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem error_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z)
    (p : O) (k : ℕ) :
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j=
      (K0-j)+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+
        sigma+delta+reserve := by
  rw [errorCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem canonical_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    let B := c+d-2*p-R
    0≤c ∧ 0≤q ∧ 0≤B ∧ 3*c-5*d≤6*B+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hh := actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at hh
  have hc : 0≤Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have h0 := le_max_right (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h1 := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h2 := le_max_right (3*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    5*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  exact ⟨hc,hq.1,by linarith,by linarith [hq.2]⟩

theorem actual_main_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  convert main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring

theorem actual_error_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_error_common_saving_refined (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_refined _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_main_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z) (hs : 0≤sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3))≤
      Z^(-2*c/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_main_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

theorem actual_error_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0)≤
      Z^(-2*(c+errorRemoval p0 Z k)/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_error_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve
    hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

open CenteredMomentFirstScale

theorem actual_common_radius_widths (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec)
    (hxi : 0≤xi) (hs : 0≤sigma) (hr : 0≤reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    let j := Real.logb Z (dyadicScale n)
    let delta := frequencyLoss Z Csec xi
    let gm := Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j
    (0≤gm ∧ d+K0-j-c+sigma≤gm) ∧
    ∀p : O,∀k : ℕ,
      let ge := Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j
      0≤ge ∧ d+K0-j-c-2*errorRemoval p Z k+errorMoving p Z k+sigma≤ge := by
  dsimp only
  have hj := retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn
  have hd := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have hx : -frequencyLoss Z Csec xi≤nominalLog I J E K X Z-Real.logb Z (dyadicScale n) := by
    linarith
  constructor
  · rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) 0 0 sigma
      (frequencyLoss Z Csec xi) reserve 2 hs hd hr (by norm_num) hx
    simp only [mul_zero,sub_zero,add_zero] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩
  · intro p k
    rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) (errorRemoval p Z k) (errorMoving p Z k)
      sigma (frequencyLoss Z Csec xi) reserve 1 hs hd hr (by norm_num) hx
    simp only [one_mul] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩

end SevenEighths.CenteredMomentCommonRadiusSaving

end

end OAI
