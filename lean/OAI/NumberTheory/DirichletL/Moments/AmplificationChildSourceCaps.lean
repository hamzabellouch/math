import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import OAI.NumberTheory.DirichletL.Moments.SecondLocalization

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplificationChildSourceCaps
open ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

def geometry (N : ℕ) (b b₁ b₂ : ℝ) : ℝ := b^(2*N)*b₁*b₂

lemma geometry_ge_one (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) : 1≤geometry N b b₁ b₂ := by
  unfold geometry
  have hp : 1≤b^(2*N):=one_le_pow₀ hb
  have hp1 : 1≤b^(2*N)*b₁ := by nlinarith
  nlinarith

lemma norm_ge_one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤I.absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma allocation_product (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) :
    finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2

lemma allocation_ne (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←allocation_product s C B]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

theorem common_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)=
      CenteredMomentAmplificationChildInput.volume s/rawReduction B.val s.P := by
  have hh:=raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  change _ = CenteredMomentAmplificationChildInput.volume s at hh
  rw [←hh]
  congr 1
  unfold CenteredMomentAmplificationChildInput.volume child commonData remainingRaw plainNorm
  dsimp only
  ring

lemma live_card_le (B : Tuple ι) : Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa only [Fintype.card_coe] using (Finset.card_le_univ (liveIndices B))

theorem common_volume_le (N : ℕ) (b : ℝ) (hb : 1≤b) (s : Input ι)
    (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)≤
      b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ) := by
  have hc:=norm_ge_one C (allocation_ne s C B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hn:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower b s.lower_pos
    (fun i x hx=>⟨(s.slot_support i hx).1,((s.slot_support i hx).2).trans hs⟩) hne).2
  rw [max_eq_right hb] at hn
  have hn':(C.absNorm:ℝ)≤b^N*rawReduction B.val s.P := hn.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hcard) hr.le)
  rw [common_volume]
  apply (div_le_div_iff₀ hr (zero_lt_one.trans_le hc)).mpr
  nlinarith [CenteredMomentAmplificationChildInput.volume_pos s]

theorem frozen_zero (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (hz : frozenCoefficient B.val C R s.ν s.W s.P=0) (f : O→ℂ) (z : O) :
    frozenCoefficient B.val C R s.ν s.W s.P*f z=0 := by rw [hz,zero_mul]

theorem radius_le (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 0≤b₁) (_h₂ : 0≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i) (hhib : ∀i,s.hi i≤b)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂) :
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius s ∧ CenteredMomentOriginalCommonHarmonic.sourceRadius s≤(b^N*b₁*b₂)*CenteredMomentAmplificationChildInput.volume s := by
  have hp:0≤∏i,s.hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hp':(∏i,s.hi i)≤b^N := by
    calc
      _ ≤ ∏i:ι,b := Finset.prod_le_prod₀ (fun i _=>hhi i) (fun i _=>hhib i)
      _ = b^Fintype.card ι := by simp
      _ ≤ b^N := pow_le_pow_right₀ hb hc
  have hpp:=mul_le_mul (mul_le_mul hp' hb₁ hs₁ (pow_nonneg (zero_le_one.trans hb) _)) hb₂ hs₂
    (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) h₁)
  change 0≤_ ∧ _≤_
  have he:CenteredMomentOriginalCommonHarmonic.sourceRadius s=((∏i,s.hi i)*s.b₁*s.b₂)*CenteredMomentAmplificationChildInput.volume s := by
    unfold CenteredMomentOriginalCommonHarmonic.sourceRadius CenteredMomentAmplificationChildInput.volume; ring
  rw [he]
  exact ⟨mul_nonneg (mul_nonneg (mul_nonneg hp hs₁) hs₂)
    (CenteredMomentAmplificationChildInput.volume_pos s).le,
    mul_le_mul_of_nonneg_right hpp (CenteredMomentAmplificationChildInput.volume_pos s).le⟩

theorem original_beta (s : Input ι) (R seed : Ideal O) :
    (original s R seed).beta=coefficient s R seed := rfl

theorem child_column_norm (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hne : (original (child s C R B τ t) (R*C) seed).beta I≠0) :
    I≠0 ∧ seed∣I ∧ (I.absNorm:ℝ)≤CenteredMomentOriginalCommonHarmonic.sourceRadius (child s C R B τ t) := by
  rw [original_beta] at hne
  have hn:=original_column_norm (child s C R B τ t) (R*C) seed I hz₁ hz₂ hne
  exact ⟨hn.1,original_column_mask _ _ _ I hne,hn.2⟩

def nominal (s : Input ι) (K : ℝ) : ℝ := CenteredMomentAmplificationChildInput.volume s^2/K

lemma nominal_pos (s : Input ι) (K : ℝ) (hK : 0<K) : 0<nominal s K :=
  div_pos (sq_pos_of_pos (CenteredMomentAmplificationChildInput.volume_pos s)) hK

lemma nominal_lower (s : Input ι) (K : ℝ) :
    (CenteredMomentAmplificationChildInput.volume s)^2/K≤nominal s K := le_rfl

lemma nominal_upper (s : Input ι) (K G H : ℝ) (hK : 0<K) (_hG : 0≤G) (_hH : 0≤H)
    (h : CenteredMomentAmplificationChildInput.volume s≤G*H) :
    nominal s K≤G^2*H^2/K := by
  unfold nominal
  exact div_le_div_of_nonneg_right (by nlinarith [CenteredMomentAmplificationChildInput.volume_pos s]) hK.le

def Endpoints (b b₁ b₂ : ℝ) (s : Input ι) : Prop :=
  s.upper≤b ∧ (∀i,0≤s.hi i) ∧ 0≤s.b₁ ∧ s.b₁≤b₁ ∧ 0≤s.b₂ ∧ s.b₂≤b₂

lemma endpoints_child (b b₁ b₂ : ℝ) (s : Input ι) (h : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Endpoints b b₁ b₂ (child s C R B τ t) :=
  ⟨h.1,fun i=>h.2.1 i.val,h.2.2⟩

lemma radius_bound (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s) :
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius s ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤
      (b^N*b₁*b₂)*CenteredMomentAmplificationChildInput.volume s :=
  radius_le N b b₁ b₂ hb (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc he.2.1
    (fun i=>(s.upper_ge i).trans he.1) he.2.2.1 he.2.2.2.2.1 he.2.2.2.1 he.2.2.2.2.2

def twiceChild (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :=
  child (child s C R B τ t) (Q^k) (R*C) Bp υ v

theorem twiceChild_data (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    (twiceChild s C R B τ t Q k Bp υ v).η=υ ∧
    (twiceChild s C R B τ t Q k Bp υ v).t=v ∧
    (twiceChild s C R B τ t Q k Bp υ v).m=
      fixedBadMask*idealGenerator ((R*C)*(Q^k)) := ⟨rfl,rfl,rfl⟩

theorem twice_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    CenteredMomentAmplificationChildInput.volume (twiceChild s C R B τ t Q k Bp υ v)=
      CenteredMomentAmplificationChildInput.volume s/(rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  rw [twiceChild,child_volume _ Q hQ k hslot,common_volume,div_div]

theorem twice_caps (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    let H:=CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k);
    0<H ∧ 0≤CenteredMomentOriginalCommonHarmonic.sourceRadius d ∧
    CenteredMomentAmplificationChildInput.volume d≤geometry N b b₁ b₂*H ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius d≤geometry N b b₁ b₂*H := by
  dsimp only
  have hC:=norm_ge_one C (allocation_ne s C B)
  have hNp:0<(Q.absNorm:ℝ)^k:=pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k
  have hH:0<CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k):=
    div_pos (CenteredMomentAmplificationChildInput.volume_pos s)
      (mul_pos (zero_lt_one.trans_le hC) hNp)
  have hv:CenteredMomentAmplificationChildInput.volume (twiceChild s C R B τ t Q k Bp υ v)≤
      b^N*(CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
    rw [twiceChild,child_volume _ Q hQ k hslot]
    exact (div_le_div_of_nonneg_right (common_volume_le N b hb s hc he.1 C R B τ t hne) hNp.le).trans_eq (by ring)
  have hc1:= (live_card_le B.val).trans hc
  have hc2:= (live_card_le Bp.val).trans hc1
  have hep:=endpoints_child b b₁ b₂ _ (endpoints_child b b₁ b₂ s he C R B τ t) (Q^k) (R*C) Bp υ v
  have hr:=radius_bound N b b₁ b₂ hb h₁ h₂ _ hc2 hep
  have hbf:0≤b^N*b₁*b₂:=by positivity
  have hpow: b^N≤geometry N b b₁ b₂ := by
    have hp:1≤b^N:=one_le_pow₀ hb
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    have hh:1≤b₁*b₂:=by nlinarith
    nlinarith
  refine ⟨hH,hr.1,hv.trans (mul_le_mul_of_nonneg_right hpow hH.le),?_⟩
  exact hr.2.trans ((mul_le_mul_of_nonneg_left hv hbf).trans_eq (by
    unfold geometry; rw [show 2*N=N+N by omega,pow_add];ring))

theorem twice_column (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hI : (original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) :
    I≠0 ∧ seed∣I ∧ (I.absNorm:ℝ)≤geometry N b b₁ b₂*
      (CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
  have hi:=child_column_norm (child s C R B τ t) (Q^k) (R*C) seed Bp υ v hz₁ hz₂ I hI
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  exact ⟨hi.1,hi.2.1,hi.2.2.trans hcap.2.2.2⟩

theorem twice_nominal (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v K : ℝ) (hK : 0<K) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    0<nominal d K ∧ CenteredMomentAmplificationChildInput.volume d^2/K=nominal d K ∧
    nominal d K≤(geometry N b b₁ b₂)^2*
      (CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2/K := by
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  exact ⟨nominal_pos _ K hK,rfl,nominal_upper _ K _ _ hK
    (zero_le_one.trans (geometry_ge_one N b b₁ b₂ hb h₁ h₂)) hcap.1.le hcap.2.2.1⟩

theorem puncture_norm (R C Q : Ideal O) (k : ℕ) :
    (((R*C)*(Q^k)).absNorm:ℝ)=(R.absNorm:ℝ)*(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
  simp only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow]

theorem live_puncture_bound (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hI : (original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) :
    (C.absNorm:ℝ)*(Q.absNorm:ℝ)^k≤geometry N b b₁ b₂*CenteredMomentAmplificationChildInput.volume s ∧
    (((R*C)*(Q^k)).absNorm:ℝ)≤(R.absNorm:ℝ)*geometry N b b₁ b₂*CenteredMomentAmplificationChildInput.volume s := by
  have hi:=twice_column N b b₁ b₂ hb h₁ h₂ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v hz₁ hz₂ I hI
  have hh:1≤geometry N b b₁ b₂*(CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)):=
    (norm_ge_one I hi.1).trans hi.2.2
  have hd:0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k:=mul_pos
    (zero_lt_one.trans_le (norm_ge_one C (allocation_ne s C B)))
    (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k)
  rw [←mul_div_assoc] at hh
  have hn:=(le_div_iff₀ hd).mp hh
  simp only [one_mul] at hn
  refine ⟨hn,?_⟩
  rw [puncture_norm]
  nlinarith [mul_le_mul_of_nonneg_left hn (show (0:ℝ)≤R.absNorm by positivity)]

theorem eventual_geometry (G ε : ℝ) (hG : 1≤G) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ G≤Z^ε ∧ G^2≤Z^ε := by
  have hh:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (G^2)
  filter_upwards [eventually_gt_atTop (1:ℝ),hh] with Z hZ hpow
  exact ⟨hZ,(by nlinarith : G≤G^2).trans hpow,hpow⟩

theorem polynomial_caps (G V X H K Z A D ε ξ : ℝ)
    (hG : 1≤G) (hZ : 1<Z) (hGp : G^2≤Z^ε)
    (hV : 0<V) (hX : 0<X) (_hH : 0≤H) (hK : 0<K)
    (hXV : X≤G*V) (hHV : H≤G*V) (hVp : V≤Z^A) (hKp : K⁻¹≤Z^D) :
    X≤Z^(A+ε) ∧ H≤Z^(A+ε) ∧ X^2/K≤Z^(2*A+D+ε) ∧
    0<frequencyRadius (X^2/K) Z ξ ∧
    frequencyRadius (X^2/K) Z ξ≤Z^(2*A+D+ε+ξ/2) := by
  have hz:=hZ.trans' zero_lt_one
  have hgp:G≤Z^ε := (by nlinarith : G≤G^2).trans hGp
  have hvpow:0<Z^A:=Real.rpow_pos_of_pos hz A
  have hrpow:0<Z^ε:=Real.rpow_pos_of_pos hz ε
  have hcap:G*V≤Z^(A+ε) := by
    rw [Real.rpow_add hz]
    nlinarith [mul_le_mul hgp hVp hV.le hrpow.le]
  have hsq:X^2≤G^2*(Z^A)^2 := by nlinarith [mul_le_mul_of_nonneg_left hVp (by linarith : 0≤G)]
  have ht:X^2/K≤Z^(2*A+D+ε) := by
    have hm:=mul_le_mul hsq hKp (inv_nonneg.mpr hK.le)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hg:=mul_le_mul_of_nonneg_right hGp (mul_nonneg (sq_nonneg (Z^A)) (Real.rpow_nonneg hz.le D))
    calc
      _ ≤ (G^2*(Z^A)^2)*Z^D := by simpa only [div_eq_mul_inv] using hm
      _ ≤ (Z^ε*(Z^A)^2)*Z^D := by nlinarith [hg]
      _ = _ := by rw [pow_two,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
  refine ⟨hXV.trans hcap,hHV.trans hcap,ht,?_,?_⟩
  · exact mul_pos (div_pos (sq_pos_of_pos hX) hK) (Real.rpow_pos_of_pos hz _)
  · unfold frequencyRadius
    rw [Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hz.le _)

theorem eventual_twice_caps (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀(s:Input ι),
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I) →
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:Character)(v K A D ξ:ℝ),
    0<K → CenteredMomentAmplificationChildInput.volume s≤Z^A → K⁻¹≤Z^D →
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    CenteredMomentAmplificationChildInput.volume d≤Z^(A+ε) ∧
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius d ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius d≤Z^(A+ε) ∧
    0<nominal d K ∧ nominal d K≤Z^(2*A+D+ε) ∧
    0<frequencyRadius (nominal d K) Z ξ ∧
    frequencyRadius (nominal d K) Z ξ≤Z^(2*A+D+ε+ξ/2) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R B τ t hne Q hQ k hslot Bp υ v K A D ξ hK hVp hKp
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  have hd:1≤(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
    have hc:=norm_ge_one C (allocation_ne s C B)
    have hq:1≤(Q.absNorm:ℝ)^k:=one_le_pow₀ (norm_ge_one Q hQ)
    nlinarith
  have hH:CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)≤
      CenteredMomentAmplificationChildInput.volume s :=
    div_le_self (CenteredMomentAmplificationChildInput.volume_pos s).le hd
  have hm:=mul_le_mul_of_nonneg_left hH (zero_le_one.trans (geometry_ge_one N b b₁ b₂ hb h₁ h₂))
  have hh:=polynomial_caps (geometry N b b₁ b₂) _ _ _ K Z A D ε ξ
    (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hZ.1 hZ.2.2
    (CenteredMomentAmplificationChildInput.volume_pos s)
    (CenteredMomentAmplificationChildInput.volume_pos _) hcap.2.1 hK
    (hcap.2.2.1.trans hm) (hcap.2.2.2.trans hm) hVp hKp
  exact ⟨hh.1,hcap.2.1,hh.2.1,nominal_pos _ K hK,hh.2.2⟩

theorem plain_zero (s : Input ι) (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support s.W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support s.W₂⊆Set.Icc a₂ b₂) : s.W₁ 0=0 ∧ s.W₂ 0=0 := by
  constructor
  · by_contra hn; exact (not_le_of_gt ha₁) (hs₁ hn).1
  · by_contra hn; exact (not_le_of_gt ha₂) (hs₂ hn).1

theorem twice_slots_ge_one (s : Input ι) (hs : ∀i,1≤s.P i)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ) (Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character) (v : ℝ) : ∀i,1≤(twiceChild s C R B τ t Q k Bp υ v).P i :=
  fun i=>hs i.val.val

theorem child_localized (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) (hK : 0<K) :
    let d:=child s C R B τ t;
    let S:=(original d (R*C) seed).columns;
    let β:=(original d (R*C) seed).beta;
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy S β (heightCoeff τ t) W K/
      (CenteredMomentAmplificationChildInput.volume d:ℂ)=
      (((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier W 0)*
          CenteredMomentSourceSecondZeroEnergy.sourceSecondZero S β τ t+
        CenteredMomentSecondLocalization.secondRetainedEnergy τ t S β W K (nominal d K) Z ξ+
        CenteredMomentSupportedTailAggregate.secondDiscardedEnergy τ t S β W K (nominal d K) Z ξ)/
      (CenteredMomentAmplificationChildInput.volume d:ℂ) := by
  dsimp only
  rw [CenteredMomentSecondLocalization.sourceGaussEnergy_localized τ t _ _ W K _ Z ξ hK]

theorem child_source_zero (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsmall : CenteredMomentOriginalCommonHarmonic.sourceRadius (child s C R B τ t)<1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta (heightCoeff τ t) W K=0 := by
  have hz (I:Ideal O):(original (child s C R B τ t) (R*C) seed).beta I=0 := by
    by_contra hn
    have hh:=child_column_norm s C R seed B τ t hz₁ hz₂ I hn
    exact (not_le_of_gt hsmall) ((norm_ge_one I hh.1).trans hh.2.2)
  simp [CenteredMomentOriginalChildEnergy.sourceGaussEnergy,CenteredMomentGaussEnergy.gaussEnergy,
    CenteredMomentGaussEnergy.gaussPolynomial,hz]

theorem eventual_live_puncture (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀(s:Input ι),
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I) →
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:Character)(v A P:ℝ),
    s.W₁ 0=0 → s.W₂ 0=0 → CenteredMomentAmplificationChildInput.volume s≤Z^A →
    (R.absNorm:ℝ)≤Z^P →
    (∃I:Ideal O,(original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) →
    (((R*C)*(Q^k)).absNorm:ℝ)≤Z^(A+P+ε) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v A P hz₁ hz₂ hVp hRp ⟨I,hI⟩
  have hn:=(live_puncture_bound N b b₁ b₂ hb h₁ h₂ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v hz₁ hz₂ I hI).2
  have hg:=geometry_ge_one N b b₁ b₂ hb h₁ h₂
  have hm:=mul_le_mul (mul_le_mul hRp hZ.2.1 (zero_le_one.trans hg)
    (Real.rpow_nonneg (by linarith : 0≤Z) P)) hVp
    (CenteredMomentAmplificationChildInput.volume_pos s).le
    (mul_nonneg (Real.rpow_nonneg (by linarith : 0≤Z) P) (Real.rpow_nonneg (by linarith : 0≤Z) ε))
  apply hn.trans (hm.trans_eq ?_)
  rw [←Real.rpow_add (by linarith : 0<Z),←Real.rpow_add (by linarith : 0<Z)]
  congr 1;ring

end SevenEighths.CenteredMomentAmplificationChildSourceCaps

end

end OAI
