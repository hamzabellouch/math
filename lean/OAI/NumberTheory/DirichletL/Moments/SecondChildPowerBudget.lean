import OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondChildPowerBudget
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentFirstChildProfileControl CenteredMomentCommonRadialPointwise
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma endpoint_product (s : Input ι) (N : ℕ) (b : ℝ) (hb : 1≤b)
    (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i) :
    0≤∏i,s.hi i ∧ (∏i,s.hi i)≤b^N := by
  refine ⟨Finset.prod_nonneg (fun i _=>hhi i),?_⟩
  calc
    _≤∏i:ι,b:=Finset.prod_le_prod₀ (fun i _=>hhi i) (fun i _=>(s.upper_ge i).trans hu)
    _=b^Fintype.card ι:=by simp
    _≤b^N:=pow_le_pow_right₀ hb hc

omit [DecidableEq ι] in
lemma main_cost (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (hm : mass s≤A) :
    profileCost s*sourceRadius s≤
      (2*(b₁*b₂)*b^N*A^2)*(b^N*b₁*b₂)*
        CenteredMomentAmplificationChildInput.volume s*mass s^2 := by
  have hg:=CenteredMomentAmplificationChildSourceCaps.radius_le N b b₁ b₂ hb
    (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc hhi
    (fun i=>(s.upper_ge i).trans hu) hs₁ hs₂ hb₁ hb₂
  have hp:=profile_cost_bound s N b A hb hu hc hm
  have he : max 1 s.b₁*max 1 s.b₂≤b₁*b₂ :=
    mul_le_mul (max_le h₁ hb₁) (max_le h₂ hb₂) (by positivity) (by linarith)
  have hp' : profileCost s≤(2*(b₁*b₂)*b^N*A^2)*mass s^2 := by
    apply hp.trans
    gcongr
  have hh:=mul_le_mul hp' hg.2 hg.1 (by positivity)
  convert hh using 1 ; ring

omit [DecidableEq ι] in
lemma diagonal_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) (N : ℕ) (b whi ε : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (hhi : ∀i,0≤s.hi i) (hε : 0≤ε) :
    (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)≤
    (4*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
      (1+b^N*whi^2)^(1+ε))*mass s^2 := by
  have hp:=endpoint_product s N b hb hu hc hhi
  have hx : 1+(∏i,s.hi i)*whi*whi≤1+b^N*whi^2 := by nlinarith [mul_le_mul_of_nonneg_right hp.2 (sq_nonneg whi)]
  have hx0 : 0≤1+(∏i,s.hi i)*whi*whi := by nlinarith [mul_nonneg hp.1 (sq_nonneg whi)]
  have h:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hx (by linarith : 0≤1+ε))
    (sq_nonneg (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s))
  convert h using 1 ; ring

omit [DecidableEq ι] in
lemma tail_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) :
    plainControl s W₁ W₂^2=
      (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*mass s^2 := by
  unfold plainControl mass
  ring

def powers (ε : ℝ) : Fin 4→ℝ := ![1,1/3,ε,0]

lemma powers_nonneg (ε : ℝ) (hε : 0≤ε) : ∀j,0≤powers ε j := by
  intro j
  fin_cases j <;> simp [powers,hε]

def coefficients {wlo whi : ℝ} (N : ℕ) (b b₁ b₂ A : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K t ε seedNorm : ℝ) (a : Fin 4→ℝ) : Fin 4→ℝ :=
  ![a 0*(2*(b₁*b₂)*b^N*A^2)*(b^N*b₁*b₂)/seedNorm,
    a 1*exceptionalConstant N b J Q K*p.control S^2*(1+‖t‖)^(2*J)*A^4/seedNorm,
    a 2*4*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*(1+b^N*whi^2)^(1+ε)/seedNorm,
    a 3*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2]

lemma coefficients_nonneg {wlo whi : ℝ} (N : ℕ) (b b₁ b₂ A : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K t ε seedNorm : ℝ) (a : Fin 4→ℝ)
    (hb : 0≤b) (h₁ : 0≤b₁) (h₂ : 0≤b₂) (hK : 0≤K)
    (hs : 0≤seedNorm) (ha : ∀j,0≤a j) :
    ∀j,0≤coefficients N b b₁ b₂ A S p J Q K t ε seedNorm a j := by
  have h0:=ha 0
  have h1:=ha 1
  have h2:=ha 2
  have h3:=ha 3
  intro j
  fin_cases j <;> dsimp [coefficients,exceptionalConstant] <;> positivity

def sourceCost {wlo whi : ℝ} (s : Input ι) (S : Finset (ℕ×ℕ))
    (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ)
    (a : Fin 4→ℝ) : ℝ :=
    a 0*profileCost s*sourceRadius s/seedNorm+
    a 1*profileFactor S s p J Q K*(CenteredMomentAmplificationChildInput.volume s)^(1/3:ℝ)/seedNorm+
    a 2*(2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)*(CenteredMomentAmplificationChildInput.volume s)^ε/seedNorm+
    a 3*plainControl s (p.profile 0) (p.profile 1)^2

omit [DecidableEq ι] in
theorem source_rhs {wlo whi : ℝ} (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (hm : mass s≤A) (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ) (hK : 0≤K) (hε : 0≤ε)
    (hs : 0≤seedNorm) (a : Fin 4→ℝ) (ha : ∀j,0≤a j) :
    sourceCost s S p J Q K ε seedNorm a ≤
      (∑j,coefficients N b b₁ b₂ A S p J Q K s.t ε seedNorm a j*
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  unfold sourceCost
  have hv := (CenteredMomentAmplificationChildInput.volume_pos s).le
  have hmain:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (main_cost s N b b₁ b₂ A hb h₁ h₂ hu hc hhi hs₁ hs₂ hb₁ hb₂ hm) (ha 0)) hs
  have hexc:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exceptional_factor_bound S p J Q K hK s N b A hb hu hc hm) (ha 1))
      (Real.rpow_nonneg hv (1/3:ℝ))) hs
  have hdiag:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (diagonal_cost s (p.profile 0) (p.profile 1) N b whi ε hb hu hc hhi hε) (ha 2))
      (Real.rpow_nonneg hv ε)) hs
  have htail:=congrArg (fun x:ℝ=>a 3*x) (tail_cost s (p.profile 0) (p.profile 1))
  have hh:=add_le_add (add_le_add (add_le_add hmain hexc) hdiag) (le_of_eq htail)
  convert hh using 1 <;>
    (try simp only [coefficients,powers,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,
      Real.rpow_one,Real.rpow_zero]) <;> ring

omit [DecidableEq ι] in
theorem twice_source_rhs {wlo whi : ℝ} (s : Input ι) (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (C R : Ideal O) (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (P : Ideal O) (k : ℕ)
    (Bp : CenteredMomentCommonAllocationSum.actualAllocations
      (CenteredMomentAmplificationChildInput.child s C R B τ t).pools (P^k))
    (υ : Character) (v : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K ε seedNorm : ℝ) (hK : 0≤K) (hε : 0≤ε) (hs : 0≤seedNorm)
    (a : Fin 4→ℝ) (ha : ∀j,0≤a j) :
    let d:=CenteredMomentAmplificationChildSourceCaps.twiceChild s C R B τ t P k Bp υ v;
    sourceCost d S p J Q K ε seedNorm a≤
      (∑j,coefficients N b b₁ b₂ (mass s) S p J Q K v ε seedNorm a j*
        (CenteredMomentAmplificationChildInput.volume d)^(powers ε j))*mass d^2 := by
  let d:=CenteredMomentAmplificationChildSourceCaps.twiceChild s C R B τ t P k Bp υ v
  have hm : mass d≤mass s :=
    (child_mass (CenteredMomentAmplificationChildInput.child s C R B τ t) (P^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact source_rhs d N b b₁ b₂ (mass s) hb h₁ h₂ hu hn
    (fun i=>hhi i.val.val) hs₁ hs₂ hb₁ hb₂ hm S p J Q K ε seedNorm hK hε hs a ha

end SevenEighths.CenteredMomentSecondChildPowerBudget

end

end OAI
