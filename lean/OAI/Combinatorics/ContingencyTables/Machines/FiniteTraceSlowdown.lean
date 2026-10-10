import OAI.Combinatorics.ContingencyTables.Transport.FiniteChainSlowdown

namespace OAI

/-! # Trace transition matrices under an exact holding slowdown -/

namespace ContingencyTables.FiniteChainSlowdown

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {Y : Type*} [Fintype Y]

def slowKilled (Q : KilledKernel Y) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) : KilledKernel Y where
  Q x y := a*Q.Q x y+if x=y then 1-a else 0
  r := a*Q.r+(1-a)
  nonnegative x y := by
    apply add_nonneg (mul_nonneg ha0.le (Q.nonnegative x y))
    split_ifs
    · linarith
    · rfl
  rnonneg := add_nonneg (mul_nonneg ha0.le Q.rnonneg) (sub_nonneg.mpr ha1)
  rlt := by nlinarith [mul_pos ha0 (sub_pos.mpr Q.rlt)]
  rowbound x := by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (Q.rowbound x) ha0.le
    simpa using add_le_add_right hh (1-a)

lemma slowKilled_apply (Q : KilledKernel Y) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (f : Y → ℝ) (x : Y) :
    (slowKilled Q a ha0 ha1).apply f x=a*Q.apply f x+(1-a)*f x := by
  unfold KilledKernel.apply
  change (∑ y,(a*Q.Q x y+if x=y then 1-a else 0)*f y)=_
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,mul_assoc]
  rw [←Finset.mul_sum]
  simp

variable {X : Type*} [Fintype X]

lemma inner (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (f g : X → ℝ) : (slow C a ha0 ha1).inner f g=C.inner f g := rfl

/-- The observable dual estimate is also stable under the holding
factor. This is the estimate used by trajectory concentration; a full
spectral gap for unrelated observables is not needed. -/
theorem dual_bound (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : 1/2 ≤ a) (K : ℝ) (hK : 0 ≤ K) (g H : X → ℝ)
    (h : (C.inner g H)^2 ≤ K*C.inner g g*C.energy H) :
    ((slow C a ha0 ha1).inner g H)^2 ≤
      (2*K)*(slow C a ha0 ha1).inner g g*(slow C a ha0 ha1).energy H := by
  have he : C.energy H ≤ 2*(slow C a ha0 ha1).energy H := by
    rw [energy]
    have hm := mul_le_mul_of_nonneg_right ha (C.energy_nonneg H)
    linarith
  rw [inner,inner]
  calc
    _ ≤ K*C.inner g g*C.energy H := h
    _ ≤ K*C.inner g g*(2*(slow C a ha0 ha1).energy H) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hK (C.inner_nonneg g))
    _ = _ := by ring

/-- Thus all accepted warm-start trajectory moment estimates transfer
to the implemented holding chain with a factor of at most two. -/
theorem warm_moment_bound (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : 1/2 ≤ a) (K U : ℝ) (hK : 0 ≤ K) (hU : 0 ≤ U) (g : X → ℝ)
    (hdual : ∀ H,(C.inner g H)^2 ≤ K*C.inner g g*C.energy H)
    (nu : X → ℝ) (hwarm : ∀ x,nu x ≤ U*C.π x) (N : ℕ) (hN : 0 < N) :
    (∑ x,nu x*(slow C a ha0 ha1).squareMoment g N x)/(N:ℝ)^2 ≤
      4*U*K*C.inner g g/N := by
  have hh := (slow C a ha0 ha1).warm_squareMoment_bound g (2*K) U
    (mul_nonneg (by norm_num) hK) hU
    (fun H => dual_bound C a ha0 ha1 ha K hK g H (hdual H)) nu hwarm N hN
  simpa only [inner,show 2*U*(2*K)=4*U*K by ring] using hh

lemma slow_apply (C : FiniteChain X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (f : X → ℝ) (x : X) :
    (slow C a ha0 ha1).apply f x=a*C.apply f x+(1-a)*f x := by
  unfold FiniteChain.apply
  change (∑ y,(a*C.P x y+if x=y then 1-a else 0)*f y)=_
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,mul_assoc]
  rw [←Finset.mul_sum]
  simp

lemma slowKilled_matches (C : FiniteChain X) (A : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside A))
    (hQ : ∀ x y : FiniteChain.Outside A,Q.Q x y=C.P x.val y.val)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∀ x y : FiniteChain.Outside A,(slowKilled Q a ha0 ha1).Q x y=
      (slow C a ha0.le ha1).P x.val y.val := by
  intro x y
  simp only [slowKilled,slow]
  rw [hQ]
  by_cases h : x=y
  · subst y
    simp
  · have hv : x.val≠y.val := fun hv => h (Subtype.ext hv)
    simp only [h,hv,ite_false]

/-- A holding step changes when the chain hits the selected set, but
not where it first hits. The equality follows from the Green residual
identity, without manipulating an infinite series term by term. -/
theorem hitKernel (C : FiniteChain X) (A : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside A))
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (x : FiniteChain.Outside A) (y : FiniteChain.Inside A) :
    (slow C a ha0.le ha1).hitKernel A (slowKilled Q a ha0 ha1) x y=C.hitKernel A Q x y := by
  let h : FiniteChain.Outside A → ℝ := fun z => C.hitKernel A Q z y
  have hh (z : FiniteChain.Outside A) : h z=C.P z.val y.val+Q.apply h z := by
    exact Q.green_firstStep (fun z => C.P z.val y.val) z
  have he (z : FiniteChain.Outside A) :
      (slow C a ha0.le ha1).P z.val y.val=h z-(slowKilled Q a ha0 ha1).apply h z := by
    have hzy : z.val≠y.val := fun he => z.property (he.symm ▸ y.property)
    change a*C.P z.val y.val+(if z.val=y.val then 1-a else 0)=_
    rw [ite_eq_right hzy,add_zero,slowKilled_apply]
    nlinarith [hh z]
  unfold FiniteChain.hitKernel
  simp_rw [he]
  exact (slowKilled Q a ha0 ha1).green_residual h x

/-- The trace itself acquires exactly the same holding factor. -/
theorem traceMatrix (C : FiniteChain X) (A : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside A))
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (x y : FiniteChain.Inside A) :
    (slow C a ha0.le ha1).traceMatrix A (slowKilled Q a ha0 ha1) x y=
      a*C.traceMatrix A Q x y+if x=y then 1-a else 0 := by
  unfold FiniteChain.traceMatrix
  simp_rw [hitKernel C A Q a ha0 ha1]
  have he (z : FiniteChain.Outside A) : (slow C a ha0.le ha1).P x.val z.val=a*C.P x.val z.val := by
    have hxz : x.val≠z.val := fun he => z.property (he ▸ x.property)
    change a*C.P x.val z.val+(if x.val=z.val then 1-a else 0)=_
    rw [ite_eq_right hxz,add_zero]
  simp_rw [he,mul_assoc,←Finset.mul_sum]
  change (a*C.P x.val y.val+if x.val=y.val then 1-a else 0)+
    a*(∑ z : FiniteChain.Outside A,C.P x.val z.val*C.hitKernel A Q z y)=_
  have hiff : x.val=y.val ↔ x=y := ⟨Subtype.ext,congrArg Subtype.val⟩
  simp only [hiff]
  ring

theorem trace_energy (C : FiniteChain X) (A : X → Prop)
    [Nonempty (FiniteChain.Inside A)] (Q : KilledKernel (FiniteChain.Outside A))
    (hQ : ∀ x y : FiniteChain.Outside A,Q.Q x y=C.P x.val y.val)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (f : FiniteChain.Inside A → ℝ) :
    ((slow C a ha0.le ha1).traceChain A (slowKilled Q a ha0 ha1)
      (slowKilled_matches C A Q hQ a ha0 ha1)).energy f=
        a*(C.traceChain A Q hQ).energy f := by
  rw [FiniteChain.energy_eq,FiniteChain.energy_eq,←mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  change (C.π x.val/C.insideMass A)*
    (slow C a ha0.le ha1).traceMatrix A (slowKilled Q a ha0 ha1) x y*(f x-f y)^2=
      a*((C.π x.val/C.insideMass A)*C.traceMatrix A Q x y*(f x-f y)^2)
  rw [traceMatrix C A Q a ha0 ha1]
  by_cases h : x=y
  · subst y
    simp
  · simp only [h,ite_false,add_zero]
    ring

/-- This transfers the accepted trace Poincaré estimate to the actual
dyadic holding chain, rather than merely to a separately defined trace. -/
theorem trace_variance_bound (C : FiniteChain X) (A : X → Prop)
    [Nonempty (FiniteChain.Inside A)] (Q : KilledKernel (FiniteChain.Outside A))
    (hQ : ∀ x y : FiniteChain.Outside A,Q.Q x y=C.P x.val y.val)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (ha : 1/2 ≤ a)
    (K : ℝ) (hK : 0 ≤ K) (f : FiniteChain.Inside A → ℝ)
    (h : (C.traceChain A Q hQ).variance f ≤ K*(C.traceChain A Q hQ).energy f) :
    ((slow C a ha0.le ha1).traceChain A (slowKilled Q a ha0 ha1)
      (slowKilled_matches C A Q hQ a ha0 ha1)).variance f ≤
        (2*K)*((slow C a ha0.le ha1).traceChain A (slowKilled Q a ha0 ha1)
          (slowKilled_matches C A Q hQ a ha0 ha1)).energy f := by
  have hv : ((slow C a ha0.le ha1).traceChain A (slowKilled Q a ha0 ha1)
      (slowKilled_matches C A Q hQ a ha0 ha1)).variance f=(C.traceChain A Q hQ).variance f := rfl
  rw [hv,trace_energy C A Q hQ a ha0 ha1]
  have hm := mul_le_mul_of_nonneg_right ha ((C.traceChain A Q hQ).energy_nonneg f)
  have hh := mul_le_mul_of_nonneg_left hm hK
  nlinarith

end

end ContingencyTables.FiniteChainSlowdown

end OAI
