import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondActiveErrorGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstSecondInputGates CenteredMomentFirstAnnularInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type*} [Fintype ι]

def errorInput (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v

lemma active_endpoints (s : Input ι) (b b₁ b₂ : ℝ) (he : Endpoints b b₁ b₂ s) :
    Endpoints b b₁ b₂ (activeInput s) := he

theorem error_caps (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    let d := errorInput s C R B τ t Q k Bp υ v;
    let H := volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k);
    0<H ∧ 0≤sourceRadius d ∧ volume d≤geometry N b b₁ b₂*H ∧
      sourceRadius d≤geometry N b b₁ b₂*H := by
  dsimp only
  have hC := norm_ge_one C (allocation_ne s C B)
  have hNp : 0<(Q.absNorm:ℝ)^k := pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k
  have hH : 0<volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k) :=
    div_pos (volume_pos s) (mul_pos (zero_lt_one.trans_le hC) hNp)
  have hv : volume (errorInput s C R B τ t Q k Bp υ v)≤
      b^N*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
    rw [errorInput,child_volume _ Q hQ k hslot,active_volume]
    exact (div_le_div_of_nonneg_right (common_volume_le N b hb s hc he.1 C R B τ t hne)
      hNp.le).trans_eq (by ring)
  have hc1 := (live_card_le B.val).trans hc
  have hc2 := (live_card_le Bp.val).trans hc1
  have hep := endpoints_child b b₁ b₂ _
    (active_endpoints _ b b₁ b₂ (endpoints_child b b₁ b₂ s he C R B τ t))
    (Q^k) (R*C) Bp υ v
  have hr := radius_bound N b b₁ b₂ hb h₁ h₂ _ hc2 hep
  have hpow : b^N≤geometry N b b₁ b₂ := by
    have hp : 1≤b^N := one_le_pow₀ hb
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    have hh : 1≤b₁*b₂ := by nlinarith
    nlinarith
  refine ⟨hH,hr.1,hv.trans (mul_le_mul_of_nonneg_right hpow hH.le),?_⟩
  exact hr.2.trans ((mul_le_mul_of_nonneg_left hv (show 0≤b^N*b₁*b₂ by positivity)).trans_eq (by
    unfold geometry;rw [show 2*N=N+N by omega,pow_add];ring))

theorem eventually_active_error_ready (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type*}[Fintype ι],∀s : Input ι,
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q : Ideal O),Q≠0 → ∀k : ℕ,
    (∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I) →
    ∀(Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
      (υ : Character)(v K A D P q ξ : ℝ),
    0<K → 0≤ξ → s.W₁ 0=0 → s.W₂ 0=0 →
    volume s≤Z^A → K⁻¹≤Z^D → (R.absNorm:ℝ)≤Z^P → (υ.modulus.absNorm:ℝ)≤Z^q →
    (∃I : Ideal O,(original (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) →
    Ready (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) K Z ξ
      (exponent A D P q ε ξ) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε
    (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R seed B τ t hR hB Q hQ k hslot Bp υ v K A D P q ξ
    hK hξ hz₁ hz₂ hVp hKi hRN hυ hlive
  let d := errorInput s C R B τ t Q k Bp υ v
  let G := geometry N b b₁ b₂
  have hg : 1≤G := geometry_ge_one N b b₁ b₂ hb h₁ h₂
  have hcap := error_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hB Q hQ k hslot Bp υ v
  have hd : 0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := mul_pos
    (zero_lt_one.trans_le (norm_ge_one C (allocation_ne s C B)))
    (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k)
  have hd1 : 1≤(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
    have hc := norm_ge_one C (allocation_ne s C B)
    have hq : 1 ≤ (Q.absNorm : ℝ)^k := one_le_pow₀ (norm_ge_one Q hQ)
    nlinarith
  have hHV : volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)≤volume s :=
    div_le_self (volume_pos s).le hd1
  have hm := mul_le_mul_of_nonneg_left hHV (zero_le_one.trans hg)
  have hpoly := polynomial_caps G (volume s) (volume d) (sourceRadius d) K Z A D ε ξ
    hg hZ.1 hZ.2.2 (volume_pos s) (volume_pos d) hcap.2.1 hK
    (hcap.2.2.1.trans hm) (hcap.2.2.2.trans hm) hVp hKi
  obtain ⟨I,hI⟩ := hlive
  have hi := child_column_norm (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v hz₁ hz₂ I hI
  have hone : 1≤G*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) :=
    (norm_ge_one I hi.1).trans (hi.2.2.trans hcap.2.2.2)
  rw [←mul_div_assoc] at hone
  have hprod : (C.absNorm:ℝ)*(Q.absNorm:ℝ)^k≤G*volume s := by
    simpa only [one_mul] using (le_div_iff₀ hd).mp hone
  have hpunct : (((R*C)*(Q^k)).absNorm:ℝ)≤Z^(A+P+ε) := by
    rw [puncture_norm]
    calc
      _≤(R.absNorm:ℝ)*(G*volume s) := by nlinarith [mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg R.absNorm)]
      _≤Z^P*(Z^ε*Z^A) := mul_le_mul hRN
        (mul_le_mul hZ.2.1 hVp (volume_pos s).le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
        (mul_nonneg (zero_le_one.trans hg) (volume_pos s).le)
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
      _=Z^(A+P+ε) := by rw [←Real.rpow_add (zero_lt_one.trans hZ.1),←Real.rpow_add (zero_lt_one.trans hZ.1)];congr 1;ring
  have h₁ : A+ε≤exponent A D P q ε ξ := le_max_left _ _
  have h₂ : 2*A+D+ε+ξ/2≤exponent A D P q ε ξ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : A+P+ε≤exponent A D P q ε ξ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄ : q≤exponent A D P q ε ξ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y : ℝ} (h : x≤y) : Z^x≤Z^y := Real.rpow_le_rpow_of_exponent_le hZ.1.le h
  exact ⟨mul_ne_zero (mul_ne_zero hR (allocation_ne s C B)) (pow_ne_zero k hQ),hK,
    hpoly.1.trans (hpow h₁),hcap.2.1,hpoly.2.1.trans (hpow h₁),
    hυ.trans (hpow h₄),hpunct.trans (hpow h₃),nominal_pos d K hK,
    hpoly.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hpoly.2.2.2.1,hpoly.2.2.2.2.trans (hpow h₂)⟩

end SevenEighths.CenteredMomentFirstSecondActiveErrorGates

end

end OAI
