import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedPaidReserve
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacitySource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstPhysicalSource CenteredMomentSecondCanonicalScalar CenteredMomentFirstScale
open CenteredMomentSecondRadicalBudget
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def fixedNumerator (N:ℕ)(lower upper cost0 a0:ℝ):ℝ :=
  (N:ℝ)*|Real.log (min 1 lower)|+(N:ℝ)*|Real.log (max 1 upper)|+
    |Real.log fixedPresentationCost|+|Real.log cost0|+
    |Real.log (4/((fixedFactor:ℝ)*a0^2))|

lemma fixedNumerator_nonneg (N:ℕ)(lower upper cost0 a0:ℝ):
    0≤fixedNumerator N lower upper cost0 a0 := by unfold fixedNumerator;positivity

theorem source_reserve_bound (N:ℕ)(lower upper cost0 a0:ℝ)
    (hlower:0<lower)(hcost0:0<cost0)(ha0:0<a0)
    {ι α:Type*}[Fintype ι][Fintype α](s:Input ι)(input:Input α)
    (hn:Fintype.card ι≤N)(hnc:Fintype.card α≤N)
    (hl:lower≤s.lower)(hu:input.upper≤upper)
    (C D:Ideal O)(hC:C≠0)(hD:D≠0)(Z delta reserve cost a:ℝ)
    (hZ:1<Z)(hd:0≤delta)(hr:0≤reserve)(hc:cost0≤cost)(ha:a0≤a):
    sourceReserve s input C D Z delta reserve cost a≤
      delta+reserve+fixedNumerator N lower upper cost0 a0/Real.log Z := by
  have hz:=Real.log_pos hZ
  have hN:(0:ℝ)≤N:=Nat.cast_nonneg _
  have hnc:(Fintype.card α:ℝ)≤N:=by exact_mod_cast hnc
  have hno:(Fintype.card ι:ℝ)≤N:=by exact_mod_cast hn
  have hmin:=Real.logb_le_logb_of_le hZ (lt_min zero_lt_one hlower) (min_le_min_left 1 hl)
  have hmin0:0≤-Real.logb Z (min 1 lower):=by
    have hh:=Real.logb_le_logb_of_le hZ (lt_min zero_lt_one hlower) (min_le_left 1 lower)
    rw [Real.logb_one] at hh
    linarith
  have hlow: -(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)≤(N:ℝ)*(-Real.logb Z (min 1 lower)):=by
    have hh:=mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg (Fintype.card ι): (0:ℝ)≤_)
    have hh':=mul_le_mul_of_nonneg_right hno hmin0
    nlinarith
  have hmax:=Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 input.upper))
    (max_le_max_left 1 hu)
  have hmax0:0≤Real.logb Z (max 1 upper):=Real.logb_nonneg hZ (le_max_left _ _)
  have hupp:(Fintype.card α:ℝ)*Real.logb Z (max 1 input.upper)≤(N:ℝ)*Real.logb Z (max 1 upper):=
    (mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hnc hmax0)
  have hcost:=Real.logb_le_logb_of_le hZ hcost0 hc
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have ha':0<a:=ha0.trans_le ha
  have hfrac:4/((fixedFactor:ℝ)*a^2)≤4/((fixedFactor:ℝ)*a0^2):=by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ ha0.le ha'.le |>.mpr ha) hf.le
  have harg:=Real.logb_le_logb_of_le hZ (by positivity:0<4/((fixedFactor:ℝ)*a^2)) hfrac
  have hCN:(1:ℝ)≤C.absNorm:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hDN:(1:ℝ)≤D.absNorm:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hcommon:0≤min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ)):=
    le_min (Real.logb_nonneg hZ hCN) (Real.logb_nonneg hZ hDN)
  have habs:
      (N:ℝ)*(-Real.logb Z (min 1 lower))+(N:ℝ)*Real.logb Z (max 1 upper)-
        Real.logb Z fixedPresentationCost-Real.logb Z cost0+
        Real.logb Z (4/((fixedFactor:ℝ)*a0^2))≤fixedNumerator N lower upper cost0 a0/Real.log Z:=by
    simp only [Real.logb]
    rw [show (N:ℝ)*(-(Real.log (min 1 lower)/Real.log Z))+
      (N:ℝ)*(Real.log (max 1 upper)/Real.log Z)-Real.log fixedPresentationCost/Real.log Z-
      Real.log cost0/Real.log Z+Real.log (4/((fixedFactor:ℝ)*a0^2))/Real.log Z=
      ((N:ℝ)*(-Real.log (min 1 lower))+(N:ℝ)*Real.log (max 1 upper)-
        Real.log fixedPresentationCost-Real.log cost0+Real.log (4/((fixedFactor:ℝ)*a0^2)))/Real.log Z by ring]
    apply (div_le_div_iff_of_pos_right hz).mpr
    have h1:=mul_le_mul_of_nonneg_left (neg_le_abs (Real.log (min 1 lower))) hN
    have h2:=mul_le_mul_of_nonneg_left (le_abs_self (Real.log (max 1 upper))) hN
    unfold fixedNumerator
    linarith [neg_le_abs (Real.log fixedPresentationCost),neg_le_abs (Real.log cost0),
      le_abs_self (Real.log (4/((fixedFactor:ℝ)*a0^2)))]
  unfold sourceReserve
  apply max_le
  · linarith
  · exact add_nonneg (add_nonneg hd hr) (div_nonneg (fixedNumerator_nonneg _ _ _ _ _) hz.le)

theorem eventually_source_reserve (N:ℕ)(lower upper cost0 a0 theta:ℝ)
    (hlower:0<lower)(hcost0:0<cost0)(ha0:0<a0)(htheta:0<theta):
    ∃Z0:ℝ,1<Z0 ∧ ∀Z:ℝ,Z0≤Z→
      ∀{ι α:Type*}[Fintype ι][Fintype α],∀(s:Input ι)(input:Input α),
      Fintype.card ι≤N→Fintype.card α≤N→lower≤s.lower→input.upper≤upper→
      ∀(C D:Ideal O),C≠0→D≠0→∀delta reserve cost a:ℝ,
      0≤delta→0≤reserve→cost0≤cost→a0≤a→
      sourceReserve s input C D Z delta reserve cost a≤delta+reserve+theta := by
  let L:=fixedNumerator N lower upper cost0 a0
  have hL:0≤L:=fixedNumerator_nonneg _ _ _ _ _
  let Z0:=Real.exp (1+L/theta)
  have hZ0:1<Z0:=Real.one_lt_exp_iff.mpr (by positivity)
  refine ⟨Z0,hZ0,?_⟩
  intro Z hZZ ι α _ _ s input hn hnc hl hu C D hC hD delta reserve cost a hd hr hc ha
  have hZ:1<Z:=hZ0.trans_le hZZ
  have hlog:=Real.log_le_log (Real.exp_pos _) hZZ
  rw [Real.log_exp] at hlog
  have hsmall:L/Real.log Z≤theta:=by
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    have hh:(L/theta)*theta≤(Real.log Z)*theta:=
      mul_le_mul_of_nonneg_right (by linarith) htheta.le
    rw [div_mul_cancel₀ _ htheta.ne'] at hh
    linarith
  have hb:=source_reserve_bound N lower upper cost0 a0 hlower hcost0 ha0 s input
    hn hnc hl hu C D hC hD Z delta reserve cost a hZ hd hr hc ha
  exact hb.trans (by change delta+reserve+L/Real.log Z≤_;linarith)

theorem eventually_actual_amplified_reserves (N:ℕ)(lower upper cost0 a0 theta:ℝ)
    (hlower:0<lower)(hcost0:0<cost0)(ha0:0<a0)(htheta:0<theta):
    ∃Z0:ℝ,1<Z0 ∧ ∀Z:ℝ,Z0≤Z→
      ∀{ι:Type*}[Fintype ι],∀s:Input ι,
      Fintype.card ι≤N→lower≤s.lower→s.upper≤upper→
      ∀(C D R:Ideal O),C≠0→D≠0→∀B:actualAllocations s.pools C,
      ∀(τ:Character)(t delta reserve cost a:ℝ),
      0≤delta→0≤reserve→cost0≤cost→a0≤a→
      sourceReserve s (child s C R B τ t) C D Z delta reserve cost a≤delta+reserve+theta ∧
      ∀(Q:Ideal O)(k:ℕ)
        (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
        (υ:Character)(v:ℝ),
        sourceReserve s (errorInput s C R B τ t Q k Bp υ v) C D Z delta reserve cost a≤
          delta+reserve+theta := by
  obtain ⟨Z0,hZ0,hbound⟩:=eventually_source_reserve N lower upper cost0 a0 theta
    hlower hcost0 ha0 htheta
  refine ⟨Z0,hZ0,?_⟩
  intro Z hZZ ι _ s hn hl hu C D R hC hD B τ t delta reserve cost a hd hr hc ha
  have hchild:Fintype.card (liveIndices B.val)≤N:=(live_card_le B.val).trans hn
  refine ⟨hbound Z hZZ s (child s C R B τ t) hn hchild hl hu C D hC hD
    delta reserve cost a hd hr hc ha,?_⟩
  intro Q k Bp υ v
  have herr:Fintype.card (liveIndices Bp.val)≤N:=(live_card_le Bp.val).trans hchild
  exact hbound Z hZZ s (errorInput s C R B τ t Q k Bp υ v) hn herr hl hu C D hC hD
    delta reserve cost a hd hr hc ha

end SevenEighths.CenteredMomentFirstAmplifiedPaidReserve

end

end OAI
