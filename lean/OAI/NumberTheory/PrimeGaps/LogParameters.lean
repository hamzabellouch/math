import OAI.NumberTheory.PrimeGaps.ConductorBounds

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

theorem exists_vaughan_log_parameters {A : ℝ} (hA : 0 < A) {X : ℕ}
    (hX : 16 ≤ X) (hL : 2 ≤ Real.log (X:ℝ))
    (hpower : (Real.log (X:ℝ))^(A+10) ≤ (X:ℝ)^(1/32:ℝ)) :
    ∃ T k r n : ℕ,
      X+1 ≤ 2^k ∧
      2*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10) ≤ ((2^(r+n):ℕ):ℝ) ∧
      2^(r+n) ≤ X ∧
      ((2^(r+n):ℕ):ℝ) ≤ 4*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10) ∧
      (Real.log (X:ℝ))^(A+10) ≤ ((2^r:ℕ):ℝ) ∧
      ((2^r:ℕ):ℝ) ≤ 2*(Real.log (X:ℝ))^(A+10) ∧
      (n:ℝ) ≤ 6*Real.log (X:ℝ) ∧
      (k:ℝ) ≤ 6*Real.log (X:ℝ) ∧
      (T:ℝ) ≤ (X:ℝ)^(1/16:ℝ) ∧
      (X:ℝ)^(1/32:ℝ) ≤ Real.sqrt (T+1:ℕ) := by
  let x : ℝ := X
  let L : ℝ := Real.log x
  let B : ℝ := A+10
  let y : ℝ := 2*x^(1/2:ℝ)*L^(-B)
  let T : ℕ := ⌊x^(1/16:ℝ)⌋₊
  let k : ℕ := dyadicExponent (X+1:ℕ)
  let r : ℕ := dyadicExponent (L^B)
  let m : ℕ := dyadicExponent y
  have hx16 : (16:ℝ) ≤ x := by dsimp [x]; exact_mod_cast hX
  have hx1 : 1 ≤ x := by linarith
  have hx : 0 < x := by linarith
  have hL1 : 1 ≤ L := by dsimp [L,x]; linarith
  have hL0 : 0 < L := by linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hLB : 1 ≤ L^B := Real.one_le_rpow hL1 hB.le
  have hneg : L^(-B) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1 (neg_nonpos.mpr hB.le)
  have hLL : L^B*L^B ≤ x^(1/2:ℝ) := by
    calc
      _ ≤ x^(1/32:ℝ)*x^(1/32:ℝ) := mul_le_mul hpower hpower (by positivity) (by positivity)
      _ = x^(1/16:ℝ) := by rw [←Real.rpow_add hx]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have heB : -B = -A-10 := by dsimp [B]; ring
  have hyeq : y = 2*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10) := by
    simp only [y,heB,L,x]
  have hLy : L^B ≤ y := by
    have he : L^B*L^(-B)=1 := by rw [←Real.rpow_add hL0]; simp
    calc
      _ = (L^B*L^B)*L^(-B) := by rw [mul_assoc,he,mul_one]
      _ ≤ x^(1/2:ℝ)*L^(-B) := mul_le_mul_of_nonneg_right hLL (by positivity)
      _ ≤ y := by dsimp [y]; nlinarith [mul_nonneg (Real.rpow_nonneg hx.le (1/2:ℝ)) (Real.rpow_nonneg hL0.le (-B))]
  have hy1 : 1 ≤ y := hLB.trans hLy
  have hry : r ≤ m := dyadicExponent_mono hLy
  have hrbounds := dyadicUpper_bounds hLB
  have hmbounds := dyadicUpper_bounds hy1
  have hsqrt : 4*x^(1/2:ℝ) ≤ x := by
    rw [←Real.sqrt_eq_rpow]
    have hs : Real.sqrt x ≤ x/4 := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith
    linarith
  have hymX : 2*y ≤ x := by
    calc
      _ = 4*x^(1/2:ℝ)*L^(-B) := by dsimp [y]; ring
      _ ≤ 4*x^(1/2:ℝ) := (mul_le_mul_of_nonneg_left hneg (by positivity)).trans_eq (mul_one _)
      _ ≤ _ := hsqrt
  have hmX : 2^m ≤ X := by
    have hh : ((2^m:ℕ):ℝ) ≤ (X:ℝ) := hmbounds.2.trans hymX
    exact_mod_cast hh
  have hymk : y ≤ (X+1:ℕ) := by
    have hy0 : 0 ≤ y := by positivity
    have hyx : y ≤ x := by linarith
    push_cast
    change y ≤ x+1
    linarith
  have hmk : m ≤ k := dyadicExponent_mono hymk
  have hkbounds := vaughanBinaryExponent_bounds (show 2 ≤ X by omega) (show 1 ≤ Real.log (X:ℝ) by linarith)
  have hrnm : r+(m-r)=m := Nat.add_sub_of_le hry
  refine ⟨T,k,r,m-r,hkbounds.1,?_,?_,?_,?_,?_,?_,hkbounds.2,?_,?_⟩
  · rw [hrnm,←hyeq]
    exact hmbounds.1.le
  · simpa only [hrnm] using hmX
  · rw [hrnm]
    calc
      _ ≤ 2*y := hmbounds.2
      _ = _ := by rw [hyeq]; ring
  · exact hrbounds.1.le
  · exact hrbounds.2
  · exact (by exact_mod_cast (Nat.sub_le m r).trans hmk : ((m-r:ℕ):ℝ) ≤ k).trans hkbounds.2
  · exact Nat.floor_le (Real.rpow_nonneg hx.le _)
  · have ht := (Nat.lt_floor_add_one (x^(1/16:ℝ))).le
    have hh := Real.sqrt_le_sqrt ht
    change Real.sqrt (x^(1/16:ℝ)) ≤ Real.sqrt ((T:ℝ)+1) at hh
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hx.le] at hh
    norm_num at hh
    simpa only [Nat.cast_add,Nat.cast_one] using hh

theorem endpoint_errors_nat_log_bound {A M : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    {X Q : ℕ} (hX : 16 ≤ X) (hL : 2 ≤ Real.log (X:ℝ))
    (hpower : (Real.log (X:ℝ))^(A+10) ≤ (X:ℝ)^(1/32:ℝ))
    (hQ : (Q:ℝ) ≤ 2*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10))
    (hsmall : ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log (X:ℝ))^(A+11) →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError (X:ℝ) χ‖ ≤ M*(X:ℝ)*(Real.log (X:ℝ))^(-2*A-14)) :
    (∑ q∈Finset.Icc 1 Q,(endpointError (X:ℝ) q:ℝ)) ≤
      (8*M+192024)*(X:ℝ)*(Real.log (X:ℝ))^(-A) := by
  obtain ⟨T,k,r,n,hk,hcover,hPX,hP,hRlo,hRhi,hn,hkL,hT,hTroot⟩ :=
    exists_vaughan_log_parameters hA hX hL hpower
  let P : ℕ := 2^(r+n)
  let R : ℕ := 2^r
  let x : ℝ := X
  let L : ℝ := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ X)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hL1 : 1 ≤ L := by dsimp [L,x]; linarith
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hQP : Q ≤ P := by
    change Q ≤ 2^(r+n)
    exact_mod_cast hQ.trans hcover
  have hH : (harmonic P:ℝ) ≤ 2*L := harmonic_le_twice_log hPX hL1
  have hH2 : (harmonic P:ℝ)^2 ≤ 4*L^2 := by nlinarith [harmonic_real_nonneg P]
  have hsmallR : (∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ)) ≤
      (R:ℝ)*(M*x*L^(-2*A-14)) := by
    apply small_conductor_mass_le (by positivity)
    intro d hd hdR χ hχ
    apply hsmall d hd ?_ χ hχ
    calc
      (d:ℝ) ≤ R := by exact_mod_cast hdR
      _ ≤ 2*L^(A+10) := hRhi
      _ ≤ L*L^(A+10) := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = L^(A+11) := by rw [show A+11=1+(A+10) by ring,Real.rpow_add hL0 1 (A+10),Real.rpow_one]
  have hsmallTotal : (∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ)) *
      (harmonic P:ℝ)^2 ≤ 8*M*x*L^(-A) := by
    calc
      _ ≤ (2*L^(A+10)*(M*x*L^(-2*A-14)))*(4*L^2) := by
        apply mul_le_mul (hsmallR.trans (mul_le_mul_of_nonneg_right hRhi (by positivity))) hH2
          (sq_nonneg _) (by positivity)
      _ = 8*M*x*L^(-A-2) := by
        conv_rhs => rw [show -A-2=(A+10)+(-2*A-14)+2 by ring,
          Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_two]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have hhi := highConductorBlockBound_log_le hA (show 2 ≤ X by omega) hL1 hPX
    hP hRlo hkL hT hTroot hpower
  have hhighTotal : ((n:ℝ)*highConductorBlockBound P X T R k)*(harmonic P:ℝ)^2 ≤
      192000*x*L^(-A) := by
    calc
      _ ≤ ((6*L)*(8000*x*L^(-A-3)))*(4*L^2) := by
        apply mul_le_mul (mul_le_mul hn hhi (highConductorBlockBound_nonneg _ _ _ _ _) (by positivity))
          hH2 (sq_nonneg _) (by positivity)
      _ = _ := by
        conv_rhs => rw [show -A=(-A-3)+1+2 by ring,Real.rpow_add hL0,Real.rpow_add hL0,
          Real.rpow_one,Real.rpow_two]
        ring
  have hlog2 : (Nat.log 2 X:ℝ) ≤ 6*L := by
    have hmono : Nat.log 2 X ≤ dyadicExponent (X+1:ℕ) := by
      unfold dyadicExponent
      rw [Nat.floor_natCast]
      exact (Nat.log_mono_right (Nat.le_succ X)).trans (Nat.le_succ _)
    exact (by exact_mod_cast hmono : (Nat.log 2 X:ℝ) ≤ (dyadicExponent (X+1:ℕ):ℝ)).trans
      (vaughanBinaryExponent_bounds (show 2 ≤ X by omega) hL1).2
  have hlogP : Real.log (P:ℝ) ≤ L := log_nat_monotone hPX
  have hcost : (P:ℝ)*(Nat.log 2 X:ℝ)*Real.log P ≤ 24*x*L^(-A) := by
    calc
      _ ≤ (4*x^(1/2:ℝ)*L^(-A-10))*(6*L)*L := by
        gcongr
      _ = 24*x^(1/2:ℝ)*L^(-A-8) := by
        rw [show -A-8=(-A-10)+1+1 by ring,Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_one]
        ring
      _ ≤ _ := by
        have hsx : x^(1/2:ℝ) ≤ x := by
          simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hx1
            (by norm_num : (1/2:ℝ) ≤ 1))
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsx (by norm_num : (0:ℝ) ≤ 24))
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity) (by positivity)
  have hfinite := endpoint_errors_finite_vaughan_reduction_of_le X T k r n Q hk hQP
  apply hfinite.trans
  change ((∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ))+
    (n:ℝ)*highConductorBlockBound P X T R k)*(harmonic P:ℝ)^2+
      (P:ℝ)*(Nat.log 2 X:ℝ)*Real.log P ≤ (8*M+192024)*x*L^(-A)
  rw [add_mul]
  nlinarith [hsmallTotal,hhighTotal,hcost]

theorem endpoint_errors_real_log_bound {A M x : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (hx : 0 ≤ x) (hX : 16 ≤ ⌊x⌋₊) (hL : 2 ≤ Real.log (⌊x⌋₊:ℝ))
    (hpower : (Real.log (⌊x⌋₊:ℝ))^(A+10) ≤ (⌊x⌋₊:ℝ)^(1/32:ℝ))
    (hsmall : ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log (⌊x⌋₊:ℝ))^(A+11) →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError (⌊x⌋₊:ℝ) χ‖ ≤ M*(⌊x⌋₊:ℝ)*(Real.log (⌊x⌋₊:ℝ))^(-2*A-14)) :
    (∑ q∈Finset.Icc 1 ⌊x^(1/2:ℝ)*(Real.log x)^(-(A+10))⌋₊,(endpointError x q:ℝ)) ≤
      ((8*M+192028)*(2:ℝ)^A)*x*(Real.log x)^(-A) := by
  let X : ℕ := ⌊x⌋₊
  let Q : ℕ := ⌊x^(1/2:ℝ)*(Real.log x)^(-(A+10))⌋₊
  let L : ℝ := Real.log (X:ℝ)
  have hX16 : (16:ℝ) ≤ X := by
    change (16:ℝ) ≤ (⌊x⌋₊:ℝ)
    exact_mod_cast hX
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hX0 : (0:ℝ) < X := by linarith
  have hfloor : (X:ℝ) ≤ x := Nat.floor_le hx
  have hceil : x < (X:ℝ)+1 := Nat.lt_floor_add_one x
  have hL1 : 1 ≤ L := by dsimp [L,X]; linarith
  have hL0 : 0 < L := by linarith
  have hloglo : L ≤ Real.log x := Real.log_le_log hX0 hfloor
  have hlogx0 : 0 < Real.log x := hL0.trans_le hloglo
  have hloghi : Real.log x ≤ 2*L :=
    calc
      _ ≤ Real.log (X+1:ℕ) := Real.log_le_log (hX0.trans_le hfloor) (by push_cast; linarith)
      _ ≤ _ := log_add_one_le_twice (by omega)
  have hroot : x^(1/2:ℝ) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
    calc
      _ ≤ Real.sqrt (4*(X:ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
  have hQ : (Q:ℝ) ≤ 2*(X:ℝ)^(1/2:ℝ)*L^(-A-10) := by
    calc
      _ ≤ x^(1/2:ℝ)*(Real.log x)^(-(A+10)) := Nat.floor_le (by positivity)
      _ ≤ (2*(X:ℝ)^(1/2:ℝ))*L^(-(A+10)) := mul_le_mul hroot
        (Real.rpow_le_rpow_of_nonpos hL0 hloglo (by linarith)) (by positivity) (by positivity)
      _ = _ := by congr 1; congr 1; ring
  have hneg : L^(-A-10) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1
      (show -A-10 ≤ 0 by linarith)
  have hQX : Q ≤ X := by
    have hrootsmall : 2*(X:ℝ)^(1/2:ℝ) ≤ X := by
      rw [←Real.sqrt_eq_rpow]
      have hs : Real.sqrt (X:ℝ) ≤ (X:ℝ)/2 := by
        apply (Real.sqrt_le_left (by positivity)).mpr
        nlinarith
      linarith
    have hh₁ : 2*(X:ℝ)^(1/2:ℝ)*L^(-A-10) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hneg
        (by positivity : 0 ≤ 2*(X:ℝ)^(1/2:ℝ))
    have hh : (Q:ℝ) ≤ X := hQ.trans (hh₁.trans hrootsmall)
    exact_mod_cast hh
  have hnat := endpoint_errors_nat_log_bound hA hM hX hL hpower hQ hsmall
  have hH : (harmonic Q:ℝ) ≤ 2*L := harmonic_le_twice_log hQX hL1
  have habs : L^2 ≤ (X:ℝ)*L^(-A) := by
    convert rpow_absorption_of_exponents (c:=2) hX1 hL1 hpower
      (show A+2 ≤ A+10 by linarith) (show (1/32:ℝ) ≤ 1 by norm_num) using 1 <;> norm_num
  have htotal : (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (8*M+192028)*(X:ℝ)*L^(-A) := by
    have hh := sum_endpointError_le_floor_add_harmonic hx Q
    have hH2 : (harmonic Q:ℝ)^2 ≤ 4*L^2 := by nlinarith [harmonic_real_nonneg Q]
    nlinarith [hnat,hh,habs,hH2]
  have hlogscale : L^(-A) ≤ (2:ℝ)^A*(Real.log x)^(-A) := by
    calc
      _ ≤ (Real.log x/2)^(-A) := Real.rpow_le_rpow_of_nonpos (by linarith)
        (by linarith) (by linarith)
      _ = _ := by
        rw [Real.div_rpow (by linarith : 0 ≤ Real.log x) (by norm_num : (0:ℝ) ≤ 2),
          Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
        ring
  apply htotal.trans
  calc
    _ ≤ (8*M+192028)*x*((2:ℝ)^A*(Real.log x)^(-A)) := by gcongr
    _ = _ := by ring

theorem bombieriVinogradov_of_siegelWalfisz (hs : SiegelWalfisz) : BombieriVinogradov := by
  intro A hA
  obtain ⟨M,hM,x₀,hx₀,hSW⟩ := hs (2*A+14) (A+11) (by linarith) (by linarith)
  refine ⟨A+10,by linarith,(8*M+192028)*(2:ℝ)^A,by positivity,?_⟩
  have hf : Tendsto (fun x : ℝ => (⌊x⌋₊:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have he : ∀ᶠ x : ℝ in atTop,
      (∑ q∈Finset.Icc 1 ⌊x^(1/2:ℝ)*(Real.log x)^(-(A+10))⌋₊,(endpointError x q:ℝ)) ≤
        ((8*M+192028)*(2:ℝ)^A)*x*(Real.log x)^(-A) := by
    filter_upwards [eventually_ge_atTop (0:ℝ),
      tendsto_nat_floor_atTop.eventually (eventually_ge_atTop (16:ℕ)),
      (Real.tendsto_log_atTop.comp hf).eventually_ge_atTop 2,
      hf.eventually_ge_atTop x₀,
      hf.eventually (eventually_log_rpow_le_rpow (A+10) (by norm_num : (0:ℝ)<1/32))]
      with x hx hX hL hxsw hp
    apply endpoint_errors_real_log_bound hA hM.le hx hX hL hp
    intro d hd hdL χ hχ
    convert hSW (⌊x⌋₊:ℝ) hxsw d hd hdL χ hχ using 1
    congr 1
    congr 1
    ring
  obtain ⟨z,hz⟩ := eventually_atTop.mp he
  refine ⟨max z 2,by linarith [le_max_right z (2:ℝ)],?_⟩
  intro x hx
  exact hz x ((le_max_left z (2:ℝ)).trans hx)

open Complex Filter Topology

noncomputable def poleRemovedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q else χ.LFunction

noncomputable def primeLogDerivativeRegular {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (poleRemovedL χ) s / poleRemovedL χ s

theorem poleRemovedL_differentiable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Differentiable ℂ (poleRemovedL χ) := by
  unfold poleRemovedL
  split_ifs with hχ
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · exact DirichletCharacter.differentiable_LFunction hχ

theorem poleRemovedL_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    poleRemovedL χ s ≠ 0 := by
  unfold poleRemovedL
  split_ifs with hχ
  · rcases eq_or_ne s 1 with rfl | hs1
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) ?_
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hs
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

theorem primeLogDerivativeRegular_analyticAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : poleRemovedL χ s ≠ 0) :
    AnalyticAt ℂ (primeLogDerivativeRegular χ) s := by
  have h := (poleRemovedL_differentiable χ).analyticAt s
  exact h.deriv.neg.div h hs

theorem primeLogDerivativeRegular_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    primeLogDerivativeRegular χ s =
      LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        (if χ = 1 then 1 / (s - 1) else 0) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  change LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv (LSeries (fun n : ℕ => χ (n : ZMod q))) s /
      LSeries (fun n : ℕ => χ (n : ZMod q)) s at hL
  rw [hL, ← DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  by_cases hχ : χ = 1
  · subst χ
    have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ q) (.inr hs1) hs.le
    simp only [primeLogDerivativeRegular, poleRemovedL, ↓reduceIte]
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    change -((s-1)*deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) /
      ((s-1)*DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) = _
    field_simp
    ring
  · simp [primeLogDerivativeRegular, poleRemovedL, hχ]

theorem poleRemovedL_fixed_height_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, 1-δ ≤ s.re → |s.im| ≤ T →
      poleRemovedL χ s ≠ 0 := by
  let K : Set ℂ := (fun t : ℝ => (1 : ℂ)+(t:ℂ)*I) '' Set.Icc (-T) T
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hO : IsOpen {s : ℂ | poleRemovedL χ s ≠ 0} :=
    isOpen_ne_fun (poleRemovedL_differentiable χ).continuous continuous_const
  have hKO : K ⊆ {s : ℂ | poleRemovedL χ s ≠ 0} := by
    rintro s ⟨t, ht, rfl⟩
    exact poleRemovedL_ne_zero χ (by simp)
  obtain ⟨ε, hε, hεK⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨ε/2, by positivity, ?_⟩
  intro s hs ht
  by_cases hs1 : 1 ≤ s.re
  · exact poleRemovedL_ne_zero χ hs1
  apply hεK
  apply Metric.mem_thickening_iff.mpr
  refine ⟨1+(s.im:ℂ)*I, ⟨s.im, abs_le.mp ht, rfl⟩, ?_⟩
  have hd : dist s (1+(s.im:ℂ)*I) = |s.re-1| := by
    rw [dist_eq_norm]
    have he : s-(1+(s.im:ℂ)*I) = ((s.re-1:ℝ):ℂ) := by
      apply Complex.ext <;> simp
    rw [he, Complex.norm_real, Real.norm_eq_abs]
  rw [hd, abs_of_nonpos (by linarith)]
  linarith

theorem primeLogDerivativeRegular_fixed_height_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ s : ℂ,
      1-δ ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
        AnalyticAt ℂ (primeLogDerivativeRegular χ) s ∧
          ‖primeLogDerivativeRegular χ s‖ ≤ M := by
  obtain ⟨δ, hδ, hn⟩ := poleRemovedL_fixed_height_strip χ T
  let K : Set ℂ := (fun p : ℝ × ℝ => (p.1:ℂ)+(p.2:ℂ)*I) ''
    (Set.Icc (1-δ) 2 ×ˢ Set.Icc (-T) T)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hmem (s : ℂ) : s ∈ K ↔ 1-δ ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ T := by
    constructor
    · rintro ⟨⟨u,v⟩, ⟨hu, hv⟩, rfl⟩
      simpa [abs_le, and_assoc] using And.intro hu hv
    · rintro ⟨hs1, hs2, hs3⟩
      refine ⟨(s.re,s.im), ⟨⟨hs1,hs2⟩,abs_le.mp hs3⟩, ?_⟩
      exact Complex.re_add_im s
  have hc : ContinuousOn (primeLogDerivativeRegular χ) K := by
    intro s hs
    obtain ⟨hs1, hs2, hs3⟩ := (hmem s).mp hs
    exact (primeLogDerivativeRegular_analyticAt χ (hn s hs1 hs3)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨δ, max M 1, hδ, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s hs1 hs2 hs3
  exact ⟨primeLogDerivativeRegular_analyticAt χ (hn s hs1 hs3),
    (hM s ((hmem s).mpr ⟨hs1,hs2,hs3⟩)).trans (le_max_left _ _)⟩

end LargePrimeGaps

end OAI
