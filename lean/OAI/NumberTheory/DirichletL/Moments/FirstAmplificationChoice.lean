import OAI.NumberTheory.DirichletL.Moments.FirstExtractedLedger
import OAI.NumberTheory.DirichletL.Moments.FirstScale
import OAI.NumberTheory.DirichletL.Moments.SectorLocalization
import OAI.NumberTheory.DirichletL.Moments.AmplificationSlotGap
import OAI.NumberTheory.DirichletL.Moments.AmplificationOriginalErrors
import OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentFirstAmplificationChoice
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentSectorLocalization CenteredMomentPrimePool
open CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationSlotGap
local notation "O" => ActualEisensteinCubic.O

abbrev ballProfile : 𝓢(ℝ,ℂ) := QuadraticInitialBound.sieveCutoff

theorem ballProfile_nonneg (x : ℝ) : 0 ≤ (ballProfile x).re := by
  simpa only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,Complex.ofReal_re]
    using (QuadraticInitialBound.sieveBump.nonneg (x:=x))

theorem ballProfile_le_one (x : ℝ) : (ballProfile x).re ≤ 1 := by
  simpa only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,Complex.ofReal_re]
    using (QuadraticInitialBound.sieveBump.le_one (x:=x))

theorem ballProfile_one (x : ℝ) (hx : 0≤x) (hx1 : x≤1) : ballProfile x=1 := by
  simp only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,
    QuadraticInitialBound.sieveBump_eq_one hx hx1,Complex.ofReal_one]

theorem ballProfile_majorizes (Y : ℝ) (hY : 0<Y) (z : O)
    (hz : normValue z≤Y) : 1≤(ballProfile (‖eisEmbedding z‖^2/Y)).re := by
  rw [←normValue_eq_embedding]
  have he := ballProfile_one (normValue z/Y)
    (div_nonneg (by unfold normValue; positivity) hY.le) ((div_le_one hY).mpr hz)
  rw [he]
  norm_num

def primeTest : ContDiffBump (3/4 : ℝ) where
  rIn := 1/16
  rOut := 1/8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem primeTest_support : Function.support primeTest ⊆ Set.Ioo (1/2) 1 := by
  intro x hx
  rw [primeTest.support_eq,Metric.mem_ball,Real.dist_eq] at hx
  change |x-3/4|<1/8 at hx
  have hh := abs_lt.mp hx
  constructor <;> linarith

theorem primeTest_tsupport : tsupport primeTest ⊆ Set.Ioi 0 := by
  intro x hx
  rw [primeTest.tsupport_eq,Metric.mem_closedBall,Real.dist_eq] at hx
  change |x-3/4|≤1/8 at hx
  have hh := abs_le.mp hx
  change 0<x
  linarith

theorem primeTest_ne_zero : (primeTest : ℝ→ℝ)≠0 := by
  have h : primeTest (3/4)=1 := primeTest.one_of_mem_closedBall
    (by simp [primeTest,Metric.mem_closedBall])
  intro hz
  have he := congrFun hz (3/4)
  change primeTest (3/4)=0 at he
  linarith

theorem eventually_log_card_power (c ell loss : ℝ)
    (hc : 0<c) (hell : 0<ell) (hloss : 0<loss) :
    ∀ᶠ Z : ℝ in atTop,
      Z^(ell-loss)≤c*Z^ell/Real.log (Z^ell) := by
  have hb := (isLittleO_log_rpow_atTop hloss).bound (div_pos hc hell)
  filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with Z hbound hZ
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlog : 0<Real.log Z := Real.log_pos hZ
  have hpow : 0<Z^loss := Real.rpow_pos_of_pos hz _
  have hh : ell*Real.log Z≤c*Z^loss := by
    have hh' : Real.log Z≤(c/ell)*Z^loss := by
      simpa only [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos hpow] using hbound
    calc
      _ ≤ ell*((c/ell)*Z^loss) := mul_le_mul_of_nonneg_left hh' hell.le
      _ = _ := by field_simp
  rw [Real.log_rpow hz]
  apply (le_div_iff₀ (mul_pos hell hlog)).mpr
  calc
    _ ≤ Z^(ell-loss)*(c*Z^loss) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [mul_left_comm,←Real.rpow_add hz,sub_add_cancel]

section Pool
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

theorem eventually_actual_pool_card (Sbad : Finset (Ideal O))
    (ell loss : ℝ) (hell : 0<ell) (hloss : 0<loss) :
    ∀ᶠ Z : ℝ in atTop,
      Z^(ell-loss)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card := by
  obtain ⟨c,hc,hcard⟩ := eventually_primePool_card M H hH Sbad primeTest
    primeTest.contDiff primeTest.hasCompactSupport primeTest_tsupport
    (fun _ => primeTest.nonneg) primeTest_ne_zero (1/2) 1 1
    (by norm_num) (by norm_num) (by norm_num) primeTest_support (fun _ => primeTest.le_one)
  filter_upwards [(tendsto_rpow_atTop hell).eventually hcard,
    eventually_log_card_power c ell loss hc hell hloss] with Z hcard hpower
  exact hpower.trans hcard

theorem eventually_actual_pool (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad) (ell loss cap b eta : ℝ)
    (hell : 0<ell) (hloss : 0<loss) (hgap : eta<ell/2) :
    ∀ᶠ Z : ℝ in atTop,
      1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^ell)
      P.Nonempty ∧ Z^(ell-loss)≤(P.card:ℝ) ∧
      2*(cap/(ell/2))≤(P.card:ℝ) ∧ b*Z^eta<Z^(ell/2) ∧
      ∀ Q∈P,Prime Q ∧ Q∉fixedBadPrimes ∧
        Z^(ell/2)≤(Ideal.absNorm Q:ℝ) ∧ (Ideal.absNorm Q:ℝ)≤Z^ell := by
  have he : 0<ell/2 := by linarith
  filter_upwards [eventually_actual_pool_card M H hH Sbad ell loss hell hloss,
    eventually_actual_pool_card M H hH Sbad ell (ell/2) hell he,
    (tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2*(cap/(ell/2)))),
    eventually_scale_gap b eta (ell/2) hgap,eventually_gt_atTop (1:ℝ)]
    with Z hcard hlarge htwo hcap hslot hZ
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlarge' : Z^(ell/2)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card := by
    simpa only [show ell-ell/2=ell/2 by ring] using hlarge
  have hp : (primePool M H Sbad (1/2) 1 (Z^ell)).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (ell/2)).trans_le hlarge'
  refine ⟨hZ,hp,hcard,hcap.trans hlarge',hslot.2,?_⟩
  intro Q hQ
  have hdata := primePool_data M H Sbad hbad (1/2) 1 (Z^ell) Q hQ
  have hn := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos hz ell) (Finset.mem_sdiff.mp hQ).1
  have hs : Z^ell=(Z^(ell/2))^2 := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    ring
  refine ⟨hdata.1,hdata.2,?_,?_⟩
  · rw [hs] at hn
    nlinarith [sq_nonneg (Z^(ell/2)-2)]
  · simpa only [mul_one] using hn.2

omit hH in
theorem reciprocal_pool_bound (Sbad : Finset (Ideal O)) (ell loss Z : ℝ)
    (hZ : 0<Z)
    (hc : Z^(ell-loss)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card) :
    ((primePool M H Sbad (1/2) 1 (Z^ell)).card:ℝ)⁻¹≤Z^(-ell+loss) := by
  have hp := Real.rpow_pos_of_pos hZ (ell-loss)
  have he := (inv_le_inv₀ (hp.trans_le hc) hp).mpr hc
  simpa only [←Real.rpow_neg hZ.le,show -(ell-loss)=-ell+loss by ring] using he

end Pool

def dyadRows (n : ℤ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌈dyadicScale n⌉₊).filter
    (fun h => dyadicWeight n (normValue h)≠0)

@[simp] theorem mem_dyadRows (n : ℤ) (h : O) :
    h∈dyadRows n ↔ dyadicWeight n (normValue h)≠0 := by
  constructor
  · exact fun hh => (Finset.mem_filter.mp hh).2
  · intro hh
    refine Finset.mem_filter.mpr ⟨?_,hh⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    have hn := (dyadicWeight_support n hh).2.le.trans (Nat.le_ceil (dyadicScale n))
    unfold normValue at hn
    exact_mod_cast hn

theorem dyadRows_ne_zero (n : ℤ) (h : O) (hh : h∈dyadRows n) : h≠0 := by
  intro he
  have hn := (mem_dyadRows n h).mp hh
  subst h
  exact hn (by simpa [normValue] using dyadicWeight_zero_nonpos n 0 le_rfl)

theorem dyadRows_norm_lt (n : ℤ) (h : O) (hh : h∈dyadRows n) :
    normValue h<dyadicScale n :=
  (dyadicWeight_support n ((mem_dyadRows n h).mp hh)).2

theorem dyadRows_log_nonneg (Z : ℝ) (hZ : 1<Z) (n : ℤ)
    (hne : (dyadRows n).Nonempty) : 0≤Real.logb Z (dyadicScale n) := by
  obtain ⟨h,hh⟩ := hne
  exact Real.logb_nonneg hZ
    ((normValue_ge_one h (dyadRows_ne_zero n h hh)).trans (dyadRows_norm_lt n h hh).le)

theorem dyadic_energy_eq_sum (n : ℤ) (f : O→ℂ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖f h‖^2)=
      ∑ h∈dyadRows n,dyadicWeight n (normValue h)*‖f h‖^2 := by
  apply tsum_eq_sum
  intro h hh
  have hz : dyadicWeight n (normValue h)=0 := by
    by_contra hn
    exact hh ((mem_dyadRows n h).mpr hn)
  rw [hz,zero_mul]

theorem dyadic_energy_le_sum (n : ℤ) (f : O→ℂ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖f h‖^2)≤
      ∑ h∈dyadRows n,‖f h‖^2 := by
  rw [dyadic_energy_eq_sum]
  exact Finset.sum_le_sum (fun h _ =>
    mul_le_of_le_one_left (sq_nonneg _) (dyadicWeight_bounds n (normValue h)).2)

theorem dyadic_energy_empty (n : ℤ) (f : O→ℂ) (h : dyadRows n=∅) :
    (∑' z : O,dyadicWeight n (normValue z)*‖f z‖^2)=0 := by
  rw [dyadic_energy_eq_sum,h,Finset.sum_empty]

def mainGain (D0 c sigma : ℝ) : ℝ := max (D0-c) 0+2*sigma

def errorRemoval (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  (k:ℝ)*Real.logb Z (normValue p)

def errorMoving (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  if k=6 then 0 else Real.logb Z (normValue p)

def errorGain (D0 c sigma Z : ℝ) (p : O) (k : ℕ) : ℝ :=
  max (D0-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma

theorem mainGain_bounds (D0 c sigma : ℝ) (hs : 0≤sigma) :
    2*sigma≤mainGain D0 c sigma ∧ D0-c+sigma≤mainGain D0 c sigma := by
  have h0 := le_max_right (D0-c) (0:ℝ)
  have h1 := le_max_left (D0-c) (0:ℝ)
  unfold mainGain
  constructor <;> linarith

theorem errorGain_bounds (D0 c sigma Z : ℝ) (p : O) (k : ℕ) (hs : 0≤sigma) :
    sigma≤errorGain D0 c sigma Z p k ∧
    D0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma≤errorGain D0 c sigma Z p k ∧
    errorGain D0 c sigma Z p k≤
      max (D0-c-2*errorRemoval p Z k+errorMoving p Z k) 0+2*sigma := by
  have h0 := le_max_right (D0-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)
  have h1 := le_max_left (D0-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)
  unfold errorGain
  constructor
  · linarith
  constructor <;> linarith

theorem error_lengths (p : O) (Z sigma : ℝ) (hs : 0≤sigma) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hl : 0≤Real.logb Z (normValue p))
    (hu : Real.logb Z (normValue p)≤sigma/3) :
    0≤errorMoving p Z k ∧ errorMoving p Z k≤errorRemoval p Z k ∧
      errorRemoval p Z k≤7*sigma/3 := by
  have hk1 : (1:ℝ)≤k := by rcases hk with rfl|rfl|rfl <;> norm_num
  have hk7 : (k:ℝ)≤7 := by rcases hk with rfl|rfl|rfl <;> norm_num
  unfold errorMoving errorRemoval
  split_ifs <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem dyadRows_norm_power (Z : ℝ) (hZ : 1<Z) (n : ℤ)
    (h : O) (hh : h∈dyadRows n) :
    normValue h≤Z^(Real.logb Z (dyadicScale n)) := by
  rw [Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (dyadicScale_pos n)]
  exact (dyadRows_norm_lt n h hh).le

theorem dyad_ball_majorant (Z : ℝ) (hZ : 1<Z) (n : ℤ) (g : ℝ) (hg : 0≤g)
    (h : O) (hh : h∈dyadRows n) :
    1≤(ballProfile (‖eisEmbedding h‖^2/Z^(Real.logb Z (dyadicScale n)+g))).re := by
  apply ballProfile_majorizes _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact (dyadRows_norm_power Z hZ n h hh).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

theorem amplified_ball_majorant (Z sigma D0 c : ℝ) (hZ : 1<Z) (hs : 0≤sigma)
    (n : ℤ) (h p : O) (hh : h∈dyadRows n)
    (hp : normValue p≤Z^(sigma/3)) :
    1≤(ballProfile (‖eisEmbedding (p^6*h)‖^2/
      Z^(Real.logb Z (dyadicScale n)+mainGain D0 c sigma))).re := by
  apply ballProfile_majorizes _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  have hb := outputRow_norm (h,p) Z (Real.logb Z (dyadicScale n)) (sigma/3)
    (zero_lt_one.trans hZ) (dyadRows_norm_power Z hZ n h hh) hp
  change normValue (p^6*h)≤Z^(Real.logb Z (dyadicScale n)+6*(sigma/3)) at hb
  exact hb.trans (Real.rpow_le_rpow_of_exponent_le hZ.le
    (by linarith [(mainGain_bounds D0 c sigma hs).1]))

theorem gaussEnergy_ball_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (Y : ℝ) (hY : 0<Y) :
    0≤(gaussEnergy S a ha c ballProfile Y).re := by
  have hs := CenteredMomentSmoothedWindowEnergy.gaussEnergy_hasSum_re S a ha c ballProfile Y hY
  rw [←hs.tsum_eq]
  exact tsum_nonneg (fun h => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))

theorem errorEnergy_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (h p : O) :
    0≤errorEnergy S a ha c h p := by
  unfold errorEnergy
  positivity

theorem eligible_error_sum {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (rows P : Finset O) (allow : O→O→Prop) :
    (∑x∈eligiblePairs rows P allow,errorEnergy S a ha c x.1 x.2)=
      ∑p∈P,∑h∈rows.filter (fun h => allow h p),errorEnergy S a ha c h p := by
  rw [←sum_eligiblePairs]
  simp only [Finset.sum_filter]
  exact Finset.sum_comm

theorem dyadic_to_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (Z sigma D0 cLog : ℝ) (hZ : 1<Z) (hsigma : 0≤sigma) (n : ℤ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
      (gaussEnergy S a ha c ballProfile
        (Z^(Real.logb Z (dyadicScale n)+(max (D0-cLog) 0+sigma)))).re := by
  apply (dyadic_energy_le_sum n (gaussPolynomial S a ha c)).trans
  apply finite_energy_le_gaussEnergy S a ha c ballProfile _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (dyadRows n)
    (fun _ => ballProfile_nonneg _)
  exact dyad_ball_majorant Z hZ n _ (by positivity)

theorem dyadic_amplification_to_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (P : Finset (Ideal O)) (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hP : P.Nonempty) (R s : Ideal O) (hR0 : R≠0) (hs0 : s≠0)
    (Z sigma BR Bs Mmax D0 cLog : ℝ) (hZ : 1<Z) (hsigma : 0<sigma) (hM : 0≤Mmax)
    (hlower : ∀Q∈P,Z^(sigma/6)≤(Ideal.absNorm Q:ℝ))
    (hupper : ∀Q∈P,(Ideal.absNorm Q:ℝ)≤Z^(sigma/3))
    (hR : (Ideal.absNorm R:ℝ)≤Z^BR) (hs : (Ideal.absNorm s:ℝ)≤Z^Bs)
    (hsize : 2*((BR+Bs+Mmax)/(sigma/6))≤(P.card:ℝ))
    (n : ℤ) (hK : Real.logb Z (dyadicScale n)≤Mmax) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
      (8/(P.card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          (gaussEnergy S a ha c ballProfile
            (Z^(Real.logb Z (dyadicScale n)+mainGain D0 cLog sigma))).re+
          ∑p∈elementPool P,∑h∈(dyadRows n).filter (fun h => eligible R s h p),
            errorEnergy S a ha c h p) := by
  let K := Real.logb Z (dyadicScale n)
  have hY : 0<Z^(K+mainGain D0 cLog sigma) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have henergy := gaussEnergy_ball_nonneg S a ha c _ hY
  by_cases hn : (dyadRows n).Nonempty
  · have hK0 := dyadRows_log_nonneg Z hZ n hn
    have hsize' : 2*((BR+Bs+K)/(sigma/6))≤(P.card:ℝ) := by
      apply le_trans _ hsize
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right (by dsimp [K];linarith) (by linarith)
    have he := actual_eligible_amplification S a ha c (dyadRows n)
      (dyadRows_ne_zero n) P hp hbad hP R s hR0 hs0 Z (sigma/6) BR Bs K (sigma/3)
      hZ (by linarith) hlower hupper hR hs hsize' (dyadRows_norm_power Z hZ n)
    have hmajor : (∑y∈(eligiblePairs (dyadRows n) (elementPool P) (eligible R s)).image outputRow,
        ‖gaussPolynomial S a ha c y‖^2)≤
        (gaussEnergy S a ha c ballProfile (Z^(K+mainGain D0 cLog sigma))).re := by
      apply finite_energy_le_gaussEnergy S a ha c ballProfile _ hY _
        (fun _ => ballProfile_nonneg _) _
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hx' := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
      have hpx := elementPool_data P hp hbad x.2 hx'.2
      exact amplified_ball_majorant Z sigma D0 cLog hZ hsigma.le n x.1 x.2 hx'.1
        (hupper _ hpx.2.1)
    apply (dyadic_energy_le_sum n (gaussPolynomial S a ha c)).trans (he.trans ?_)
    rw [eligible_error_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ le_rfl
    calc
      _ ≤ ((K+6*(sigma/3))/(sigma/6))*
          (gaussEnergy S a ha c ballProfile (Z^(K+mainGain D0 cLog sigma))).re :=
        mul_le_mul_of_nonneg_left hmajor (by dsimp [K];positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by dsimp [K];linarith) (by linarith)) henergy
  · rw [dyadic_energy_empty n _ (Finset.not_nonempty_iff_eq_empty.mp hn)]
    apply mul_nonneg (by positivity)
    apply add_nonneg
    · exact mul_nonneg (by positivity) henergy
    · exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg
        (fun h _ => errorEnergy_nonneg S a ha c h p))

theorem eventually_dyadic_amplification (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧ b*Z^eta<Z^(sigma/6) ∧
      (∀ Q∈P,Prime Q ∧ Q∉fixedBadPrimes ∧
        Z^(sigma/6)≤(Ideal.absNorm Q:ℝ) ∧ (Ideal.absNorm Q:ℝ)≤Z^(sigma/3)) ∧
      ∀ {α : Type*} (S : Finset α) (a : α→O) (ha : ∀i,Supported (Ideal.span {a i}))
        (c : α→ℂ) (R s : Ideal O), R≠0 → s≠0 →
        (Ideal.absNorm R:ℝ)≤Z^BR → (Ideal.absNorm s:ℝ)≤Z^Bs →
        ∀ (n : ℤ),Real.logb Z (dyadicScale n)≤Mmax → ∀ (D0 cLog : ℝ),
        (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
          (8/(P.card:ℝ))*
            (((Mmax+2*sigma)/(sigma/6))*
              (gaussEnergy S a ha c ballProfile
                (Z^(Real.logb Z (dyadicScale n)+mainGain D0 cLog sigma))).re+
              ∑p∈elementPool P,∑h∈(dyadRows n).filter (fun h => eligible R s h p),
                errorEnergy S a ha c h p) := by
  have he := eventually_actual_pool M H hH Sbad hbad (sigma/3) loss
    (BR+Bs+Mmax) b eta (by linarith) hloss (by linarith)
  simp only [show sigma/3/2=sigma/6 by ring] at he
  filter_upwards [he] with Z hz
  obtain ⟨hZ,hP,hcard,hsize,hslot,hdata⟩ := hz
  refine ⟨hZ,hP,hcard,hslot,hdata,?_⟩
  intro α S a ha c R s hR0 hs0 hR hs n hK D0 cLog
  exact dyadic_amplification_to_ball S a ha c _ (fun Q hQ => (hdata Q hQ).1)
    (fun Q hQ => (hdata Q hQ).2.1) hP R s hR0 hs0 Z sigma BR Bs Mmax D0 cLog
    hZ hsigma hM (fun Q hQ => (hdata Q hQ).2.2.1)
    (fun Q hQ => (hdata Q hQ).2.2.2) hR hs hsize n hK

open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentHeckeExpansion
open ConcretePrimeRowBridge CanonicalRowCompletion RayFourExpansion
open HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor

local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

structure OriginalData (ι : Type*) [Fintype ι] where
  S : (ι ⊕ Fin 2) → Finset (Ideal O)
  R : Ideal O
  s : Ideal O
  nu : ι → Ideal O → ℂ
  slot : ι → ℝ → ℂ
  lengths : ι → ℝ
  W₁ : ℝ → ℂ
  W₂ : ℝ → ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  B₁ : Ideal O
  B₂ : Ideal O

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def profile (D : OriginalData ι) : Tuple ι → ℂ :=
  profileCoefficient D.R D.nu D.slot D.lengths D.W₁ D.W₂
    D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ D.s

def columns (D : OriginalData ι) : Finset (Ideal O) :=
  finiteColumns (Fintype.piFinset D.S)

def beta (D : OriginalData ι) : Ideal O → ℂ :=
  finiteColumnCoefficient (Fintype.piFinset D.S) D.profile

def coefficient (D : OriginalData ι) (η : Character) (m : O) (t T : ℝ)
    : supportedColumns D.columns → ℂ :=
  fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)

theorem coefficient_eq (D : OriginalData ι) (η : Character) (m : O) (t T : ℝ) :
    D.coefficient η m t T = fun I : supportedColumns D.columns =>
      (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I) := rfl

def childEnergy (D : OriginalData ι) (τ : RayCharacter → Character)
    (p : O) (n : ℕ) (t T K : ℝ) : ℝ :=
  let C := (Ideal.span {p})^(n+1)
  (16*(n+2:ℝ)*localErrorCost p n) *
    ((∑ χ : RayCharacter,∑ B : actualAllocations D.S C,
      (sourceGaussEnergy
        (finiteColumns (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1))
        (finiteColumnCoefficient
          (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C D.R D.s D.nu D.slot D.lengths D.W₁ D.W₂
            D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂))
        (heightCoeff (τ χ) t) ballProfile K).re) /
      (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)))

theorem childEnergy_nonneg (D : OriginalData ι) (τ : RayCharacter → Character)
    (p : O) (n : ℕ) (t T K : ℝ) (hT : 0≤T) (hK : 0<K) :
    0≤D.childEnergy τ p n t T K := by
  apply mul_nonneg (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_nonneg _ (div_nonneg hT (by positivity))
  exact Finset.sum_nonneg (fun χ _ => Finset.sum_nonneg (fun B _ =>
    sourceGaussEnergy_nonneg _ _ _ ballProfile K hK (fun _ => ballProfile_nonneg _)))

end OriginalData

theorem exists_original_error_ball_family {ι : Type*} [Fintype ι]
    (η : Character) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2∣p-1)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          D.childEnergy τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  have hK : 0<Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  by_cases he : ((dyadRows j).filter (fun h => eligible D.R D.s h p)).Nonempty
  · obtain ⟨h,hh⟩ := he
    have hsc := (eligible_coprime_divisor D.R D.s h p hPid (Finset.mem_filter.mp hh).2).pow_right (n:=n+1)
    have hfull := hτ D.S hS hprime (fun i I hI => ⟨hS _ _ hI,hslot i I hI⟩) D.R D.s hsc
      D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ t T hT
      ((dyadRows j).filter (fun h => eligible D.R D.s h p))
      (fun h hh => eligible_not_dvd_row D.R D.s h p (Finset.mem_filter.mp hh).2)
      ballProfile _ hK (fun _ => ballProfile_nonneg _)
      (fun h hh => dyad_ball_majorant Z hZ j _
        (hsigma.trans (errorGain_bounds D0 cLog sigma Z p (n+1) hsigma).1)
        h (Finset.mem_filter.mp hh).1)
    rw [OriginalData.coefficient_eq]
    dsimp only at hfull
    dsimp only [OriginalData.childEnergy,OriginalData.coefficient,OriginalData.beta,
      OriginalData.columns,OriginalData.profile]
    exact hfull
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact D.childEnergy_nonneg τ p n t T _ hT.le hK

def errorIndex (i : Fin 3) : ℕ := ![0,5,6] i

theorem errorIndex_cases (i : Fin 3) : errorIndex i=0 ∨ errorIndex i=5 ∨ errorIndex i=6 := by
  fin_cases i <;> simp [errorIndex]

theorem exists_pool_error_families {ι : Type*} [Fintype ι]
    (P : Finset (Ideal O)) (hP : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (η : Character) (m : O) (hm : m≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
        rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ p∈elementPool P,∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤sigma → ∀ (j : ℤ),
        (∑p∈elementPool P,∑h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
            (D.coefficient η m t T) h p)≤
        ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
          (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1))) := by
  have hf (p : elementPool P) (i : Fin 3) := by
    have hd := elementPool_data P hP hbad p p.property
    have hPid := hP _ hd.2.1
    letI : (Ideal.span {p.val}).IsMaximal :=
      (Ideal.isPrime_of_prime hPid).isMaximal hPid.ne_zero
    exact exists_original_error_ball_family (ι:=ι) η m p hm hd.1 hPid hd.2.2.2.1
      hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hmLam hm2 (errorIndex i) (errorIndex_cases i)
  choose τ hτ using hf
  refine ⟨τ,fun p i => (hτ p i).1,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  rw [←Finset.sum_coe_sort (elementPool P)]
  apply Finset.sum_le_sum
  intro p hp
  have h0 := (hτ p 0).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h5 := (hτ p 1).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h6 := (hτ p 2).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  simpa only [errorEnergy,Finset.sum_add_distrib,Fin.sum_univ_three,
    show errorIndex 0=0 from rfl,show errorIndex 1=5 from rfl,show errorIndex 2=6 from rfl,Nat.reduceAdd] using
    add_le_add (add_le_add h0 h5) h6

theorem original_slot_coprime {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (Z sigma b eta : ℝ) (hZ : 1≤Z) (hb : 0≤b)
    (hgap : b*Z^eta<Z^(sigma/6))
    (z : ι → ℝ) (hz : ∀i,z i≤eta) (hlen : ∀i,D.lengths i=Z^(z i))
    (hsupp : ∀i,Function.support (D.slot i)⊆Set.Iic b)
    (hslot : ∀i,∀I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0)
    (hprime : ∀i,∀I∈D.S (Sum.inl i),Prime I)
    (Q : Ideal O) (hQ : Prime Q) (hQN : Z^(sigma/6)≤(Ideal.absNorm Q:ℝ)) :
    ∀i,∀I∈D.S (Sum.inl i),IsCoprime Q I := by
  intro i I hI
  have hW := hslot i I hI
  rw [hlen] at hW
  have hN := live_profile_norm_bound (D.slot i) b Z (z i) eta I hb hZ (hz i) (hsupp i) hW
  exact ((HeckeInverseAmplification.prime_coprime_iff ⟨Q,hQ⟩ I).mpr
    (amplifier_not_dvd_slot Q I hQ (hprime i I hI) Z (sigma/6) eta b hgap hQN hN)).symm

theorem eventually_original_source_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,∀ I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_dyadic_amplification M H hH Sbad hbad sigma loss BR Bs Mmax b eta
    hsigma hloss hM hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hsep,hdata,hamp⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,herr⟩ := exists_pool_error_families (ι:=ι) _
    (fun Q hQ => (hdata Q hQ).1) (fun Q hQ => (hdata Q hQ).2.1) η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have hcop (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
      ∀i,∀I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I := by
    have hd := elementPool_data _ (fun Q hQ => (hdata Q hQ).1)
      (fun Q hQ => (hdata Q hQ).2.1) p hp
    exact original_slot_coprime D Z sigma b eta hZ.le hb hsep z hz hlen hsupp hslot hprime
      (Ideal.span {p}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  have he := herr D hS hprime hcop t T Z sigma D0 cLog hT hZ hsigma.le j
  apply (hamp Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) D.R D.s hR0 hs0 hR hs j hK D0 cLog).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (by positivity)

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def active (D : OriginalData ι) : OriginalData ι :=
  { D with S := fun i => match i with
    | Sum.inl j => (D.S i).filter (fun I => D.slot j ((Ideal.absNorm I:ℝ)/D.lengths j)≠0)
    | Sum.inr _ => D.S i }

theorem active_subset (D : OriginalData ι) (i : ι ⊕ Fin 2) : D.active.S i⊆D.S i := by
  cases i <;> simp only [active]
  · exact Finset.filter_subset _ _
  · exact fun _ h => h

theorem active_profile (D : OriginalData ι) : D.active.profile=D.profile := rfl

theorem active_slot (D : OriginalData ι) (i : ι) (I : Ideal O) (hI : I∈D.active.S (Sum.inl i)) :
    D.active.slot i ((Ideal.absNorm I:ℝ)/D.active.lengths i)≠0 :=
  (Finset.mem_filter.mp hI).2

theorem active_profile_zero (D : OriginalData ι) (v : Tuple ι)
    (hv : v∈Fintype.piFinset D.S) (hn : v∉Fintype.piFinset D.active.S) : D.profile v=0 := by
  have hn' : ¬∀i,v i∈D.active.S i := by simpa only [Fintype.mem_piFinset] using hn
  obtain ⟨i,hi⟩ := not_forall.mp hn'
  have hvi := Fintype.mem_piFinset.mp hv i
  cases i with
  | inr j => exact False.elim (hi hvi)
  | inl j =>
    have hz : D.slot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/D.lengths j)=0 := by
      by_contra hne
      exact hi (Finset.mem_filter.mpr ⟨hvi,hne⟩)
    have hp : (∏k,D.nu k (v (Sum.inl k))*D.slot k
        ((Ideal.absNorm (v (Sum.inl k)):ℝ)/D.lengths k))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hz,mul_zero]
    simp only [profile,profileCoefficient,hp,zero_mul]

theorem active_beta (D : OriginalData ι) : D.active.beta=D.beta := by
  funext I
  unfold beta finiteColumnCoefficient
  rw [active_profile]
  apply Finset.sum_subset (Finset.filter_subset_filter _
    (Fintype.piFinset_subset _ _ (D.active_subset)))
  intro v hv hn
  have hv' := Finset.mem_filter.mp hv
  apply D.active_profile_zero v hv'.1
  intro hm
  exact hn (Finset.mem_filter.mpr ⟨hm,hv'.2⟩)

theorem active_columns_subset (D : OriginalData ι) : D.active.columns⊆D.columns :=
  Finset.image_subset_image (Fintype.piFinset_subset _ _ D.active_subset)

theorem active_gaussPolynomial (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (h : O) :
    gaussPolynomial Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T) h=
    gaussPolynomial Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T) h := by
  unfold coefficient
  rw [D.active_beta]
  rw [CenteredMomentLiveDomain.source_gaussPolynomial D.active.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h,
    CenteredMomentLiveDomain.source_gaussPolynomial D.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h]
  apply Finset.sum_subset (Finset.filter_subset_filter _ D.active_columns_subset)
  intro I hI hn
  have hz : D.beta I=0 := by
    by_contra hne
    have hm := CenteredMomentLiveDomain.finite_column_mem
      (Fintype.piFinset D.active.S) D.active.profile I
      (by change D.active.beta I≠0;rw [D.active_beta];exact hne)
    exact hn (Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hI).2⟩)
  rw [hz,zero_mul,mul_zero,zero_mul]

theorem active_gaussEnergy (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    gaussEnergy Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T) W K=
    gaussEnergy Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T) W K := by
  unfold gaussEnergy
  simp_rw [D.active_gaussPolynomial]

end OriginalData

theorem eventually_original_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_original_source_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have he := henergy D.active (fun i I hI => hS i I (D.active_subset i hI))
    (fun i I hI => hprime i I (D.active_subset _ hI)) D.active_slot hsupp z hz hlen
    hR0 hs0 hR hs t T D0 cLog hT j hK
  simpa only [D.active_gaussPolynomial,D.active_gaussEnergy] using he

open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstExtractedLedger
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical ActualEisensteinCubic

def nominalLog (I J E : Ideal O) (K X Z : ℝ) : ℝ :=
  Real.logb Z (firstNominalScale I J E K X)

theorem retained_nominal_choice (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0<K) (hX : 0<X) (hZ : 1<Z)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n)
    (hne : (dyadRows n).Nonempty) :
    0≤Real.logb Z (dyadicScale n) ∧
    Real.logb Z (dyadicScale n)≤nominalLog I J E K X Z+frequencyLoss Z Csec xi ∧
    Real.logb Z ((commonPart J I).absNorm:ℝ)-frequencyLoss Z Csec xi≤
      Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
        Real.logb Z (dyadicScale n) := by
  have hs : Tsec≤Csec*Z^(nominalLog I J E K X Z) := by
    rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (firstNominalScale_pos I J E hE K X hK hX)]
    exact hsec
  have he := retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC hs n hn
  exact ⟨dyadRows_log_nonneg Z hZ n hne,he,by linarith⟩

theorem canonical_active_log_le (η τ : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}) :
    0≤Real.logb Z (τ.modulus.absNorm:ℝ) ∧
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)≤
      Real.logb Z (τ.modulus.absNorm:ℝ) := by
  have hpos : 0<τ.modulus.absNorm := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hd : Ideal.span {activeConductor I J}∣τ.modulus := by
    rw [hmod,←Ideal.span_singleton_mul_span_singleton]
    exact (dvd_mul_left (Ideal.span {activeConductor I J}) _).trans (dvd_mul_left _ _)
  have hN : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤(τ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)
  refine ⟨Real.logb_nonneg hZ (by exact_mod_cast hpos),?_⟩
  exact Real.logb_le_logb_of_le hZ (active_norm_pos I J) hN

theorem retained_main_first_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J) (hE : E≠0)
    (A : Finset (CommonIndex I J)) (K X Z Csec Tsec xi sigma : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec) (hxi : 0≤xi) (hsigma : 0≤sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (hne : (dyadRows n).Nonempty) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let D0 := d+nominalLog I J E K X Z-Real.logb Z (dyadicScale n)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    2*c/3-3*sigma-5*frequencyLoss Z Csec xi/6≤
      firstSaving c D0 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R) (mainGain D0 c sigma) (sigma/3) := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hD := (retained_nominal_choice I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn hne).2.2
  let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
  let D0 := Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
    Real.logb Z (dyadicScale n)
  have he := actual_extracted_first_saving I J hI hJ Z hZ
    D0 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0 (mainGain D0 c sigma) (sigma/3) sigma (frequencyLoss Z Csec xi)
    (by norm_num) hq.1 (by norm_num) hsigma (frequencyLoss_nonneg Z Csec xi hZ hC hxi)
    hq.2 hD (by simp only [mainGain,c,mul_zero,sub_zero,add_zero];exact le_rfl)
    (by positivity) (by positivity)
  simpa only [add_zero] using he

theorem pool_prime_log_range (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (Z sigma : ℝ) (hZ : 1<Z) (p : O)
    (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
    0≤Real.logb Z (normValue p) ∧ Real.logb Z (normValue p)≤sigma/3 := by
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p hp
  have hb := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3)) (Finset.mem_sdiff.mp hd.2.1).1
  have hu : normValue p≤Z^(sigma/3) := by simpa only [normValue,mul_one] using hb.2
  refine ⟨Real.logb_nonneg hZ (normValue_ge_one p hd.1.ne_zero),?_⟩
  have hh := Real.logb_le_logb_of_le hZ (normValue_pos p hd.1.ne_zero) hu
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hh

theorem errorRemoval_power (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z) (k : ℕ) :
    Z^(errorRemoval p Z k)=(normValue p)^k := by
  unfold errorRemoval
  rw [mul_comm,Real.rpow_mul_natCast (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)]

theorem errorMoving_power (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    Z^(2*errorMoving p Z (n+1))=normValue (p^(2*errorMovingExponent n)) := by
  have he := errorRemoval_power p hp Z hZ 2
  have hn2 : normValue (p^2)=(normValue p)^2 := by
    unfold normValue
    rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  rcases hn with rfl|rfl|rfl
  · simpa only [errorMoving,errorMovingExponent,show ¬(0:ℕ)=5 by decide,
      show ¬(1:ℕ)=6 by decide,ite_false,Nat.reduceAdd,mul_one,hn2,errorRemoval,Nat.cast_ofNat] using he
  · norm_num [errorMoving,errorMovingExponent,normValue]
  · simpa only [errorMoving,errorMovingExponent,show ¬(6:ℕ)=5 by decide,
      show ¬(7:ℕ)=6 by decide,ite_false,Nat.reduceAdd,mul_one,hn2,errorRemoval,Nat.cast_ofNat] using he

theorem shortened_raw_exact (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z) (T : ℝ) (k : ℕ) :
    T/(Ideal.absNorm (Ideal.span {p}):ℝ)^k=T/Z^(errorRemoval p Z k) := by
  rw [errorRemoval_power p hp Z hZ]
  rfl

theorem eventually_frequency_loss (Csec xi : ℝ) (hC : 1≤Csec) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧ 0≤frequencyLoss Z Csec xi ∧ frequencyLoss Z Csec xi<xi := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (2*Real.log (4*Csec)/xi)),eventually_gt_atTop (1:ℝ)] with Z hlog hZ
  have hh := (div_lt_iff₀ hxi).mp hlog
  have hr : Real.log (4*Csec)/Real.log Z<xi/2 := by
    apply (div_lt_iff₀ (Real.log_pos hZ)).mpr
    nlinarith
  refine ⟨hZ,frequencyLoss_nonneg Z Csec xi hZ hC hxi.le,?_⟩
  unfold frequencyLoss Real.logb
  linarith

theorem retained_error_first_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J) (hE : E≠0)
    (A : Finset (CommonIndex I J)) (K X Z Csec Tsec xi sigma : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec) (hxi : 0≤xi) (hsigma : 0≤sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (j : ℤ) (hj : Retained (frequencyRadius Tsec Z xi) j) (hne : (dyadRows j).Nonempty)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let D0 := d+nominalLog I J E K X Z-Real.logb Z (dyadicScale j)
    let u := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    2*(c+errorRemoval p Z k)/3-3*sigma-5*frequencyLoss Z Csec xi/6≤
      firstSaving c D0 (errorRemoval p Z k) (Real.logb Z (τ.modulus.absNorm:ℝ))
        (errorMoving p Z k) (c+d-2*u-R) (errorGain D0 c sigma Z p k) 0 := by
  dsimp only
  let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
  let D0 := Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
    Real.logb Z (dyadicScale j)
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hD := (retained_nominal_choice I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec j hj hne).2.2
  have hl := pool_prime_log_range M H Sbad hbad Z sigma hZ p hp
  have hw := error_lengths p Z sigma hsigma k hk hl.1 hl.2
  have hg := (errorGain_bounds D0 c sigma Z p k hsigma).2.2
  exact actual_extracted_first_saving I J hI hJ Z hZ D0 (errorRemoval p Z k)
    (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p Z k)
    (errorGain D0 c sigma Z p k) 0 sigma (frequencyLoss Z Csec xi)
    (hw.1.trans hw.2.1) hq.1 hw.1 hsigma (frequencyLoss_nonneg Z Csec xi hZ hC hxi)
    hq.2 hD hg (by norm_num) hw.2.2

end SevenEighths.CenteredMomentFirstAmplificationChoice

end

end OAI
