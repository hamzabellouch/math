import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondInputGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

def commonExponent (A D P C q ε ξ:ℝ):ℝ:=
  max (A+ε) (max (2*A+D+ε+ξ/2) (max (P+C) q))

theorem eventually_common_ready (N:ℕ)(b b₁ b₂ ε:ℝ)
    (hb:1≤b)(hb₁:1≤b₁)(hb₂:1≤b₂)(hε:0<ε):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀K A D P Ccap q ξ:ℝ,0<K → 0≤ξ → volume s≤Z^A → K⁻¹≤Z^D →
    (R.absNorm:ℝ)≤Z^P → (C.absNorm:ℝ)≤Z^Ccap → (τ.modulus.absNorm:ℝ)≤Z^q →
    Ready (child s C R B τ t) (R*C) K Z ξ (commonExponent A D P Ccap q ε ξ):=by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε
    (geometry_ge_one N b b₁ b₂ hb hb₁ hb₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hs he C R B τ t hR hB K A D P Ccap q ξ hK hξ hV hKi hRN hCN hτ
  have hC:=allocation_ne s C B
  have hNc:=norm_ge_one C hC
  have hv:=volume_pos s
  have hbN:0≤b^N:=pow_nonneg (zero_le_one.trans hb) _
  have hcv:volume (child s C R B τ t)≤b^N*volume s:=
    (common_volume_le N b hb s hs he.1 C R B τ t hB).trans
      (div_le_self (mul_nonneg hbN hv.le) hNc)
  have hr:=radius_bound N b b₁ b₂ hb hb₁ hb₂ (child s C R B τ t)
    ((live_card_le B.val).trans hs) (endpoints_child b b₁ b₂ s he C R B τ t)
  have hVg:volume (child s C R B τ t)≤geometry N b b₁ b₂*volume s:=by
    apply hcv.trans
    apply mul_le_mul_of_nonneg_right _ hv.le
    apply (pow_le_pow_right₀ hb (show N≤2*N by omega)).trans
    unfold geometry
    exact (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hb) _) hb₁).trans
      (le_mul_of_one_le_right (by positivity) hb₂)
  have hHg:sourceRadius (child s C R B τ t)≤geometry N b b₁ b₂*volume s:=by
    apply hr.2.trans
    apply (mul_le_mul_of_nonneg_left hcv (show 0≤b^N*b₁*b₂ by positivity)).trans_eq
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    ring
  have hc:=polynomial_caps (geometry N b b₁ b₂) (volume s)
    (volume (child s C R B τ t)) (sourceRadius (child s C R B τ t)) K Z A D ε ξ
    (geometry_ge_one N b b₁ b₂ hb hb₁ hb₂) hZ.1 hZ.2.2 hv (volume_pos _) hr.1 hK
    hVg hHg hV hKi
  have h₁:A+ε≤commonExponent A D P Ccap q ε ξ:=le_max_left _ _
  have h₂:2*A+D+ε+ξ/2≤commonExponent A D P Ccap q ε ξ:=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃:P+Ccap≤commonExponent A D P Ccap q ε ξ:=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄:q≤commonExponent A D P Ccap q ε ξ:=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y:ℝ}(h:x≤y):Z^x≤Z^y:=Real.rpow_le_rpow_of_exponent_le hZ.1.le h
  have hRC:((R*C).absNorm:ℝ)≤Z^(P+Ccap):=by
    rw [map_mul,Nat.cast_mul,Real.rpow_add (zero_lt_one.trans hZ.1)]
    exact mul_le_mul hRN hCN (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hZ.1.le) P)
  refine ⟨mul_ne_zero hR hC,hK,hc.1.trans (hpow h₁),hr.1,hc.2.1.trans (hpow h₁),
    hτ.trans (hpow h₄),hRC.trans (hpow h₃),nominal_pos _ K hK,
    hc.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hc.2.2.2.1,hc.2.2.2.2.trans (hpow h₂)⟩

end SevenEighths.CenteredMomentFirstSecondInputGates

end

end OAI
