import OAI.NumberTheory.DirichletL.Moments.ActiveAllocation
import OAI.NumberTheory.DirichletL.Moments.DivisorBoundary

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentActiveDivisorShell
open HeckeFamily CenteredMomentActiveAllocation CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDivisorBoundary CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

structure Source (ι:Type*) [Fintype ι] where
  η : Character
  m : O
  A : O
  t : ℝ
  slots : ι→Finset (Ideal O)
  prime : ∀i,∀I∈slots i,Prime I
  ν : ι→Ideal O→ℂ
  W : ι→ℝ→ℂ
  lo : ι→ℝ
  hi : ι→ℝ
  P : ι→ℝ
  lo_pos : ∀i,0<lo i
  P_pos : ∀i,0<P i
  support : ∀i,Function.support (W i)⊆Set.Icc (lo i) (hi i)
  W₁ : ℝ→ℂ
  W₂ : ℝ→ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Source.active (s:Source ι) (D:Ideal O) : Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  activeAllocations s.η s.m s.A s.t s.slots
    (fun i I=>s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)) D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

def Source.allowance (s:Source ι) (Z:ℝ) : ℝ :=
  (∑i,logWindow (s.lo i) (s.hi i))/Real.log Z

theorem Source.active_boundary (s:Source ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.active D) (Z:ℝ) (hZ:1<Z) :
    Real.logb Z (Ideal.absNorm D:ℝ)≤Real.logb Z (formalReductionFactor D a s.P)+s.allowance Z :=
  active_formal_boundary s.η s.m s.A s.t s.slots s.prime s.ν s.W s.lo s.hi s.P s.lo_pos s.P_pos
    s.support D hD a s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ Z hZ ha

theorem reciprocal_sqrt_log (Z x y:ℝ) (hZ:1<Z) (hx:0<x) (hy:0<y) :
    1/Real.sqrt (x*y)=Z^(-(Real.logb Z x+Real.logb Z y)/2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  calc
    _=(x*y)^(-(1/2:ℝ)):=by rw [Real.sqrt_eq_rpow,one_div,Real.rpow_neg (mul_nonneg hx.le hy.le)]
    _=(Z^(Real.logb Z x+Real.logb Z y))^(-(1/2:ℝ)):=by
      rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hx,Real.rpow_logb hz hZ.ne' hy]
    _=_:=by rw [←Real.rpow_mul hz.le]; congr 1; ring

theorem Source.active_pair_weight {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (ha:a∈s.active D) (hb:b∈v.active D) (Z:ℝ) (hZ:1<Z) :
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)≤
      Z^((s.allowance Z+v.allowance Z)/2)/(Ideal.absNorm D:ℝ) := by
  have hs:0<formalReductionFactor D a s.P:=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))
  have hv:0<formalReductionFactor D b v.P:=
    mul_pos (selectedNorm_pos D b) (Finset.prod_pos (fun i _=>v.P_pos i))
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  rw [reciprocal_sqrt_log Z _ _ hZ hs hv]
  have hl:=s.active_boundary D hD a ha Z hZ
  have hr:=v.active_boundary D hD b hb Z hZ
  have he:-(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P))/2≤
      (s.allowance Z+v.allowance Z)/2-Real.logb Z (Ideal.absNorm D:ℝ):=by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le he
  rwa [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn] at hp

theorem paired_active_divisor_shell {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (Ds:Finset (Ideal O))
    (a:∀D:Ideal O,Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:∀D:Ideal O,Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (hD:∀D∈Ds,Squarefree D) (ha:∀D∈Ds,a D∈s.active D) (hb:∀D∈Ds,b D∈v.active D)
    (T Z:ℝ) (hT:1≤T) (hZ:1<Z)
    (hlo:∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) (hhi:∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) :
    (∑D∈Ds,1/Real.sqrt (formalReductionFactor D (a D) s.P*formalReductionFactor D (b D) v.P))≤
      256*Z^((s.allowance Z+v.allowance Z)/2) := by
  have hs (D:Ideal O):0<formalReductionFactor D (a D) s.P:=
    mul_pos (selectedNorm_pos D (a D)) (Finset.prod_pos (fun i _=>s.P_pos i))
  have hv (D:Ideal O):0<formalReductionFactor D (b D) v.P:=
    mul_pos (selectedNorm_pos D (b D)) (Finset.prod_pos (fun i _=>v.P_pos i))
  simp_rw [reciprocal_sqrt_log Z _ _ hZ (hs _) (hv _)]
  apply paired_raw_divisor_bound Ds T Z ((s.allowance Z+v.allowance Z)/2) hT hZ
    (fun D=>Real.logb Z (formalReductionFactor D (a D) s.P))
    (fun D=>Real.logb Z (formalReductionFactor D (b D) v.P))
    (fun _=>s.allowance Z) (fun _=>v.allowance Z)
    (fun D hd=>(hD D hd).ne_zero) hlo hhi
    (fun D hd=>s.active_boundary D (hD D hd) (a D) (ha D hd) Z hZ)
    (fun D hd=>v.active_boundary D (hD D hd) (b D) (hb D hd) Z hZ)
  intro D hd
  linarith

theorem paired_all_active_shell {κ:Type*} [Fintype κ] [DecidableEq κ]
    (N:ℕ) (hι:Fintype.card ι≤N) (hκ:Fintype.card κ≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2) := by
  obtain ⟨C₁,hC₁,hcard₁⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  obtain ⟨C₂,hC₂,hcard₂⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=κ⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨256*C₁*C₂,by positivity,?_⟩
  intro s v Ds hD T Z hT hZ hlo hhi
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  let θ:ℝ:=(s.allowance Z+v.allowance Z)/2
  have hc₁ (D:Ideal O) (hd:D∈Ds):( (s.active D).card:ℝ)≤C₁*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₁ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hc₂ (D:Ideal O) (hd:D∈Ds):( (v.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((v.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (κ⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₂ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hp (D:Ideal O) (hd:D∈Ds):
      (∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
      (C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=by
    have hn:0<(Ideal.absNorm D:ℝ):=ht.trans_le (hlo D hd)
    have he:((Ideal.absNorm D:ℝ)^ε)*((Ideal.absNorm D:ℝ)^ε)=(Ideal.absNorm D:ℝ)^(2*ε):=by
      rw [←Real.rpow_add hn]; congr 1; ring
    have hpow:(Ideal.absNorm D:ℝ)^(2*ε)≤(2*T)^(2*ε):=
      Real.rpow_le_rpow hn.le (hhi D hd).le (by positivity)
    calc
      _≤∑_a∈s.active D,∑_b∈v.active D,Z^θ/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=>Finset.sum_le_sum (fun b hb=>s.active_pair_weight v D (hD D hd) a b ha hb Z hZ))
      _=((s.active D).card:ℝ)*((v.active D).card:ℝ)*(Z^θ/(Ideal.absNorm D:ℝ)):=by simp;ring
      _≤(C₁*(Ideal.absNorm D:ℝ)^ε)*(C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^θ/(Ideal.absNorm D:ℝ)):=
        mul_le_mul_of_nonneg_right (mul_le_mul (hc₁ D hd) (hc₂ D hd) (by positivity) (by positivity)) (by positivity)
      _=(C₁*C₂)*(Ideal.absNorm D:ℝ)^(2*ε)*(Z^θ/(Ideal.absNorm D:ℝ)):=by rw [←he];ring
      _≤(C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
          (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) ht (hlo D hd)) (by positivity) (by positivity)
  calc
    _≤∑_D∈Ds,(C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=Finset.sum_le_sum hp
    _=(Ds.card:ℝ)*((C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T)):=by simp
    _≤(256*T)*((C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T)):=
      mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT (fun D hd=>(hD D hd).ne_zero) hhi) (by positivity)
    _=(256*C₁*C₂)*(2*T)^(2*ε)*Z^θ:=by field_simp

end SevenEighths.CenteredMomentActiveDivisorShell

end

end OAI
