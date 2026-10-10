import OAI.NumberTheory.PrimeGaps.DyadicMeans

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

theorem conductor_doubling_error_le (Q X T k D : ℕ) (hD : 1 ≤ D)
    (hQ : 2*D ≤ Q) (hk : X+1 ≤ 2^k) :
    (∑ d∈Finset.Ioc D (2*D),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      highConductorBlockBound Q X T D k := by
  have hDr : 0 < (D:ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hdq : ((2*D:ℕ):ℝ) ≤ Q := by exact_mod_cast hQ
  have hsq : (((2*D:ℕ):ℝ)^2) ≤ ((2*D:ℕ):ℝ)*(Q:ℝ) := by
    nlinarith [show (0:ℝ) ≤ ((2*D:ℕ):ℝ) from Nat.cast_nonneg _]
  have hshort : (((2*D:ℕ):ℝ)^2)*vaughanShortBound (2*D) X T ≤
      (D:ℝ)*(2*(Q:ℝ)*vaughanShortBound Q X T) := by
    calc
      _ ≤ (((2*D:ℕ):ℝ)^2)*vaughanShortBound Q X T :=
        mul_le_mul_of_nonneg_left (vaughanShortBound_mono hQ X T) (sq_nonneg _)
      _ ≤ (((2*D:ℕ):ℝ)*(Q:ℝ))*vaughanShortBound Q X T :=
        mul_le_mul_of_nonneg_right hsq (vaughanShortBound_nonneg _ _ _)
      _ = _ := by push_cast; ring
  have hbilin:=vaughanBilinearBound_doubling Q X T D hD hQ
  have hC : 0 ≤ (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) := by
    have h:=log_nat_nonneg (X+1)
    positivity
  have h:=(conductor_interval_error_le_vaughan (2*D) X T k D hD hk).trans
    (add_le_add hshort (by
      convert mul_le_mul_of_nonneg_left hbilin hC using 1
      ring))
  apply (mul_le_mul_iff_right₀ hDr).mp
  convert h using 1
  unfold highConductorBlockBound
  ring

theorem highConductorBlockBound_antitone_radius (Q X T k : ℕ) {R D : ℕ}
    (hR : 1 ≤ R) (hRD : R ≤ D) :
    highConductorBlockBound Q X T D k ≤ highConductorBlockBound Q X T R k := by
  have hdiv : 4*(X:ℝ)/(D:ℝ) ≤ 4*(X:ℝ)/(R:ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < R by omega))
      (by exact_mod_cast hRD)
  have hC : 0 ≤ (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) := by
    have h:=log_nat_nonneg (X+1)
    positivity
  unfold highConductorBlockBound
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hdiv le_rfl) le_rfl) hC)

theorem sum_Ioc_dyadic {A : Type*} [AddCommMonoid A] (F : ℕ→A) (r n : ℕ) :
    (∑ d∈Finset.Ioc (2^r) (2^(r+n)),F d)=
      ∑ j∈Finset.range n,∑ d∈Finset.Ioc (2^(r+j)) (2^(r+j+1)),F d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,←ih]
    exact (Finset.sum_Ioc_consecutive F (show 2^r ≤ 2^(r+n) from
      pow_le_pow_right₀ (by omega) (by omega))
      (show 2^(r+n) ≤ 2^(r+n+1) from pow_le_pow_right₀ (by omega) (by omega))).symm

theorem high_conductor_error_le (X T k r n : ℕ) (hk : X+1 ≤ 2^k) :
    (∑ d∈Finset.Ioc (2^r) (2^(r+n)),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      (n:ℝ)*highConductorBlockBound (2^(r+n)) X T (2^r) k := by
  rw [sum_Ioc_dyadic]
  calc
    _ ≤ ∑ _j∈Finset.range n,highConductorBlockBound (2^(r+n)) X T (2^r) k := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn:=Finset.mem_range.mp hj
      have hD : 1 ≤ 2^(r+j) := one_le_pow₀ (by omega)
      have hpow : 2^(r+j+1)=2*2^(r+j) := by rw [pow_succ]; omega
      rw [hpow]
      apply (conductor_doubling_error_le (2^(r+n)) X T k (2^(r+j)) hD ?_ hk).trans
      · exact highConductorBlockBound_antitone_radius _ _ _ _ (one_le_pow₀ (by omega))
          (pow_le_pow_right₀ (by omega) (by omega))
      · rw [←hpow]
        exact pow_le_pow_right₀ (by omega) (by omega)
    _ = _ := by simp

theorem endpoint_errors_finite_vaughan_reduction (X T k r n : ℕ) (hk : X+1 ≤ 2^k) :
    (∑ q∈Finset.Icc 1 (2^(r+n)),(endpointError (X:ℝ) q:ℝ)) ≤
      ((∑ d∈Finset.Icc 1 (2^r),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))+
        (n:ℝ)*highConductorBlockBound (2^(r+n)) X T (2^r) k)*(harmonic (2^(r+n)):ℝ)^2+
      ((2^(r+n):ℕ):ℝ)*(Nat.log 2 X:ℝ)*Real.log (2^(r+n):ℕ) := by
  have hR : 2^r ≤ 2^(r+n) := pow_le_pow_right₀ (by omega) (by omega)
  have hRpos : 1 ≤ 2^r := one_le_pow₀ (by omega)
  have he : Finset.Icc 1 (2^(r+n))=Finset.Icc 1 (2^r)∪Finset.Ioc (2^r) (2^(r+n)) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_union,Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 1 (2^r)) (Finset.Ioc (2^r) (2^(r+n))) := by
    apply Finset.disjoint_left.mpr
    intro d h1 h2
    have h1':=Finset.mem_Icc.mp h1
    have h2':=Finset.mem_Ioc.mp h2
    omega
  have h:=endpointErrors_le_primitive_weighted_sum (X:ℝ) (2^(r+n))
  simp only [Nat.floor_natCast] at h
  apply h.trans
  rw [he,Finset.sum_union hd]
  exact add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (high_conductor_error_le X T k r n hk)) (sq_nonneg _)) le_rfl

theorem primitiveErrorMass_one (x : ℝ) :
    primitiveErrorMass x 1 =
      |(∑ n∈Finset.Ioc 0 ⌊x⌋₊,ArithmeticFunction.vonMangoldt n)-x| := by
  have hone (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n:ZMod 1)=1 := by
    apply MulChar.one_apply
    exact (ZMod.isUnit_iff_coprime n 1).mpr (by simp)
  have he : primeCharacterPrefix x (1 : DirichletCharacter ℂ 1)=
      ((∑ n∈Finset.Ioc 0 ⌊x⌋₊,ArithmeticFunction.vonMangoldt n):ℝ) := by
    simp only [primeCharacterPrefix,hone,one_mul,Complex.ofReal_sum]
  simp only [primitiveErrorMass,Finset.sum_filter]
  rw [Fintype.sum_unique]
  rw [DirichletCharacter.level_one (default : DirichletCharacter ℂ 1)]
  simp only [DirichletCharacter.isPrimitive_one_level_one,↓reduceIte,primeCharacterError,
    he,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]

theorem PNT_error_le_small_conductor_mass (x : ℝ) {R : ℕ} (hR : 1 ≤ R) :
    |(∑ n∈Finset.Ioc 0 ⌊x⌋₊,ArithmeticFunction.vonMangoldt n)-x| ≤
      ∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ) := by
  have h := Finset.single_le_sum
    (f:=fun d : ℕ => primitiveErrorMass x d/(d.totient:ℝ))
    (fun d _ => div_nonneg (primitiveErrorMass_nonneg x d) (Nat.cast_nonneg _))
    (Finset.mem_Icc.mpr ⟨le_rfl,hR⟩)
  simpa only [Nat.totient_one,Nat.cast_one,div_one,primitiveErrorMass_one] using h

theorem endpoint_errors_finite_vaughan_reduction_of_le (X T k r n Q : ℕ)
    (hk : X+1 ≤ 2^k) (hQ : Q ≤ 2^(r+n)) :
    (∑ q∈Finset.Icc 1 Q,(endpointError (X:ℝ) q:ℝ)) ≤
      ((∑ d∈Finset.Icc 1 (2^r),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))+
        (n:ℝ)*highConductorBlockBound (2^(r+n)) X T (2^r) k)*(harmonic (2^(r+n)):ℝ)^2+
      ((2^(r+n):ℕ):ℝ)*(Nat.log 2 X:ℝ)*Real.log (2^(r+n):ℕ) := by
  apply le_trans ?_ (endpoint_errors_finite_vaughan_reduction X T k r n hk)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    have h:=Finset.mem_Icc.mp hq
    exact Finset.mem_Icc.mpr ⟨h.1,h.2.trans hQ⟩
  · intro q _ _
    exact NNReal.coe_nonneg _

theorem endpointError_le_floor (x : ℝ) (q : ℕ) :
    (endpointError x q:ℝ) ≤ (endpointError (⌊x⌋₊:ℝ) q:ℝ)+
      |x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ) := by
  have hb : 0 ≤ (endpointError (⌊x⌋₊:ℝ) q:ℝ)+|x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ) := by
    positivity
  change (endpointError x q:ℝ) ≤
    ((⟨(endpointError (⌊x⌋₊:ℝ) q:ℝ)+|x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ),hb⟩:NNReal):ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro c hc
  split_ifs with hcop
  · apply NNReal.coe_le_coe.mp
    change |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient| ≤ _
    calc
      _ ≤ |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-(⌊x⌋₊:ℝ)/q.totient|+
          |(⌊x⌋₊:ℝ)/q.totient-x/q.totient| := abs_sub_le _ _ _
      _ ≤ (endpointError (⌊x⌋₊:ℝ) q:ℝ)+|x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ) := by
        apply add_le_add (endpointClassError_le ⌊x⌋₊ (Finset.mem_range.mp hc) hcop)
        rw [←sub_div,abs_div,abs_of_nonneg (show (0:ℝ) ≤ q.totient from Nat.cast_nonneg _),abs_sub_comm]
  · exact bot_le

theorem sum_endpointError_le_floor (x : ℝ) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (∑ q∈Finset.Icc 1 Q,(endpointError (⌊x⌋₊:ℝ) q:ℝ))+
        |x-(⌊x⌋₊:ℝ)| *(harmonic Q:ℝ)^2 := by
  apply (Finset.sum_le_sum (fun q _ => endpointError_le_floor x q)).trans
  rw [Finset.sum_add_distrib]
  apply add_le_add le_rfl
  calc
    _ = |x-(⌊x⌋₊:ℝ)| *(∑ q∈Finset.Icc 1 Q,(1:ℝ)/(q.totient:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_totient_reciprocal_le Q) (abs_nonneg _)

theorem sum_endpointError_le_floor_add_harmonic {x : ℝ} (hx : 0 ≤ x) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (∑ q∈Finset.Icc 1 Q,(endpointError (⌊x⌋₊:ℝ) q:ℝ))+(harmonic Q:ℝ)^2 := by
  apply (sum_endpointError_le_floor x Q).trans
  apply add_le_add le_rfl
  have h1 : 0 ≤ x-(⌊x⌋₊:ℝ) := sub_nonneg.mpr (Nat.floor_le hx)
  have h2 : |x-(⌊x⌋₊:ℝ)| ≤ 1 := by
    rw [abs_of_nonneg h1]
    have h:=Nat.lt_floor_add_one x
    linarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h2 (sq_nonneg (harmonic Q:ℝ))

theorem endpoint_errors_real_finite_vaughan_reduction {x : ℝ} (hx : 0 ≤ x)
    (T k r n Q : ℕ) (hk : ⌊x⌋₊+1 ≤ 2^k) (hQ : Q ≤ 2^(r+n)) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (((∑ d∈Finset.Icc 1 (2^r),primitiveErrorMass (⌊x⌋₊:ℝ) d/(d.totient:ℝ))+
        (n:ℝ)*highConductorBlockBound (2^(r+n)) ⌊x⌋₊ T (2^r) k)*(harmonic (2^(r+n)):ℝ)^2+
      ((2^(r+n):ℕ):ℝ)*(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log (2^(r+n):ℕ))+(harmonic Q:ℝ)^2 := by
  exact (sum_endpointError_le_floor_add_harmonic hx Q).trans
    (add_le_add (endpoint_errors_finite_vaughan_reduction_of_le ⌊x⌋₊ T k r n Q hk hQ) le_rfl)

open Filter Topology

def SiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log x)^B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError x χ‖ ≤ M*x*(Real.log x)^(-A)

theorem primitiveErrorMass_div_le {x M : ℝ} (hM : 0 ≤ M) {d : ℕ} (hd : 0 < d)
    (h : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → ‖primeCharacterError x χ‖ ≤ M) :
    primitiveErrorMass x d/(d.totient:ℝ) ≤ M := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hphi : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hcard : Fintype.card (DirichletCharacter ℂ d) = d.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  apply (div_le_iff₀ hphi).mpr
  calc
    _ ≤ ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
        DirichletCharacter.IsPrimitive, M := by
      exact Finset.sum_le_sum (fun χ hχ => h χ (Finset.mem_filter.mp hχ).2)
    _ ≤ ∑ _χ : DirichletCharacter ℂ d, M :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hM)
    _ = _ := by simp [hcard, mul_comm]

theorem small_conductor_mass_le {x M : ℝ} (hM : 0 ≤ M) (R : ℕ)
    (h : ∀ d : ℕ, 0 < d → d ≤ R → ∀ χ : DirichletCharacter ℂ d,
      χ.IsPrimitive → ‖primeCharacterError x χ‖ ≤ M) :
    (∑ d ∈ Finset.Icc 1 R, primitiveErrorMass x d/(d.totient:ℝ)) ≤ (R:ℝ)*M := by
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 R, M := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd0, hdR⟩ := Finset.mem_Icc.mp hd
      exact primitiveErrorMass_div_le hM (by omega) (h d (by omega) hdR)
    _ = _ := by simp

noncomputable def dyadicExponent (x : ℝ) : ℕ := Nat.log 2 ⌊x⌋₊+1

theorem dyadicExponent_mono : Monotone dyadicExponent := by
  intro x y hxy
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono hxy)) 1

theorem dyadicUpper_bounds {x : ℝ} (hx : 1 ≤ x) :
    x < ((2^(dyadicExponent x):ℕ):ℝ) ∧ ((2^(dyadicExponent x):ℕ):ℝ) ≤ 2*x := by
  have hf : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hlo := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊x⌋₊
  have hup := Nat.pow_log_le_self 2 (by omega : ⌊x⌋₊ ≠ 0)
  constructor
  · apply (Nat.lt_floor_add_one x).trans_le
    exact_mod_cast hlo
  · unfold dyadicExponent
    rw [pow_succ]
    push_cast
    have hh : ((2^(Nat.log 2 ⌊x⌋₊):ℕ):ℝ) ≤ x :=
      (by exact_mod_cast hup : ((2^(Nat.log 2 ⌊x⌋₊):ℕ):ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le (by linarith))
    push_cast at hh
    nlinarith

theorem log_add_one_le_twice {X : ℕ} (hX : 2 ≤ X) :
    Real.log (X+1:ℕ) ≤ 2*Real.log (X:ℝ) := by
  have hx : (2:ℝ) ≤ X := by exact_mod_cast hX
  calc
    _ ≤ Real.log ((X:ℝ)^2) := Real.log_le_log (by positivity) (by push_cast; nlinarith)
    _ = _ := by rw [Real.log_pow]; ring

theorem vaughanBinaryExponent_bounds {X : ℕ} (hX : 2 ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    X+1 ≤ 2^(dyadicExponent (X+1:ℕ)) ∧
      (dyadicExponent (X+1:ℕ):ℝ) ≤ 6*Real.log (X:ℝ) := by
  constructor
  · exact_mod_cast (dyadicUpper_bounds (show (1:ℝ) ≤ (X+1:ℕ) by exact_mod_cast (by omega : 1 ≤ X+1))).1.le
  · rw [dyadicExponent, Nat.floor_natCast]
    push_cast
    have hn := Real.natLog_le_logb (X+1) 2
    have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hd : Real.log (X+1:ℕ)/Real.log 2 ≤ 4*Real.log (X:ℝ) := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
      have h := log_add_one_le_twice hX
      nlinarith
    norm_num only [Real.logb, Nat.cast_ofNat] at hn
    linarith

theorem vaughanShortBound_power_le {Q X T : ℕ} (hX : 2 ≤ X)
    (hL : 1 ≤ Real.log (X:ℝ)) (hQX : Q ≤ X)
    (hQ : (Q:ℝ) ≤ 4*(X:ℝ)^(1/2:ℝ))
    (hT : (T:ℝ) ≤ (X:ℝ)^(1/16:ℝ)) :
    vaughanShortBound Q X T ≤ 32*(X:ℝ)^(3/8:ℝ)*(Real.log (X:ℝ))^2 := by
  let x : ℝ := X
  let L : ℝ := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ X)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hL0 : 0 ≤ L := by dsimp [L,x]; linarith
  have htX : (T:ℝ) ≤ x := hT.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (1/16:ℝ) ≤ 1))
  have htL : Real.log (T:ℝ) ≤ L := log_nat_monotone (by change (T:ℝ) ≤ (X:ℝ) at htX; exact_mod_cast htX)
  have hqL : Real.log (Q:ℝ) ≤ L := log_nat_monotone hQX
  have hxxL : Real.log (X+1:ℕ) ≤ 2*L := log_add_one_le_twice hX
  have hqroot : Real.sqrt Q ≤ 2*x^(1/4:ℝ) := by
    apply (Real.sqrt_le_sqrt hQ).trans_eq
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow, ←Real.rpow_mul hx.le]
    norm_num
  have hK : Real.sqrt Q*(1+Real.log Q) ≤ 4*x^(1/4:ℝ)*L := by
    calc
      _ ≤ (2*x^(1/4:ℝ))*(2*L) := mul_le_mul hqroot (by dsimp [L,x] at *; linarith)
        (by have hh:=log_nat_nonneg Q; linarith) (by positivity)
      _ = _ := by ring
  have ht2 : ((T*T:ℕ):ℝ) ≤ x^(1/8:ℝ) := by
    calc
      _ = (T:ℝ)^2 := by push_cast; ring
      _ ≤ (x^(1/16:ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg T) hT 2
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]; norm_num
  have httL : Real.log (T*T:ℕ) ≤ 2*L := by
    calc
      _ = 2*Real.log (T:ℝ) := by rw [Nat.cast_mul, ←pow_two,Real.log_pow]; norm_num
      _ ≤ _ := by linarith
  have he1 : x^(1/16:ℝ) ≤ x^(3/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have he2 : x^(5/16:ℝ) ≤ x^(3/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h1 : (T:ℝ)*Real.log T ≤ x^(3/8:ℝ)*L^2 := by
    calc
      _ ≤ x^(3/8:ℝ)*L := mul_le_mul (hT.trans he1) htL (log_nat_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [L,x] at *; nlinarith) (by positivity)
  have h2 : (T:ℝ)*(2*Real.log (X+1:ℕ)*(Real.sqrt Q*(1+Real.log Q))) ≤
      16*x^(3/8:ℝ)*L^2 := by
    calc
      _ ≤ x^(1/16:ℝ)*(2*(2*L)*(4*x^(1/4:ℝ)*L)) := by gcongr
      _ = 16*x^(5/16:ℝ)*L^2 := by
        rw [show (5/16:ℝ)=1/16+1/4 by norm_num,Real.rpow_add hx]; ring
      _ ≤ _ := by gcongr
  have h3 : (((T*T:ℕ):ℝ)*Real.log (T*T:ℕ))*(Real.sqrt Q*(1+Real.log Q)) ≤
      8*x^(3/8:ℝ)*L^2 := by
    calc
      _ ≤ (x^(1/8:ℝ)*(2*L))*(4*x^(1/4:ℝ)*L) := by gcongr
      _ = _ := by rw [show (3/8:ℝ)=1/8+1/4 by norm_num,Real.rpow_add hx]; ring
  unfold vaughanShortBound
  dsimp only
  change _ ≤ 32*x^(3/8:ℝ)*L^2
  nlinarith [mul_nonneg (Real.rpow_nonneg hx.le (3/8:ℝ)) (sq_nonneg L)]

theorem conductorHarmonicBound_le {Q X : ℕ} (hQ : Q ≤ X)
    (hL : 1 ≤ Real.log (X:ℝ)) :
    conductorHarmonicBound Q ≤ 3*Real.log (X:ℝ) := by
  unfold conductorHarmonicBound
  rw [Nat.cast_pow,Real.log_pow]
  have h := log_nat_monotone hQ
  norm_num only [Nat.cast_ofNat]
  linarith

theorem sqrt_conductorHarmonicBound_le {Q X : ℕ} (hQ : Q ≤ X)
    (hL : 1 ≤ Real.log (X:ℝ)) :
    Real.sqrt (conductorHarmonicBound Q) ≤ 2*Real.log (X:ℝ) := by
  apply (Real.sqrt_le_sqrt (conductorHarmonicBound_le hQ hL)).trans
  apply (Real.sqrt_le_left (by linarith)).mpr
  nlinarith

theorem rpow_absorption {x L a b c : ℝ} (hx : 0 < x) (hL : 0 < L)
    (h : L^a ≤ x^b) : x^(1-b)*L^c ≤ x*L^(c-a) := by
  calc
    _ = (x^(1-b)*L^(c-a))*L^a := by
      rw [mul_assoc,←Real.rpow_add hL,sub_add_cancel]
    _ ≤ (x^(1-b)*L^(c-a))*x^b :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [mul_right_comm,←Real.rpow_add hx,sub_add_cancel,Real.rpow_one]

theorem rpow_absorption_of_exponents {x L a b a' b' c : ℝ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (h : L^a ≤ x^b) (ha : a' ≤ a) (hb : b ≤ b') :
    x^(1-b')*L^c ≤ x*L^(c-a') :=
  rpow_absorption (lt_of_lt_of_le zero_lt_one hx) (lt_of_lt_of_le zero_lt_one hL)
    ((Real.rpow_le_rpow_of_exponent_le hL ha).trans
      (h.trans (Real.rpow_le_rpow_of_exponent_le hx hb)))

theorem eventually_log_rpow_le_rpow (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^a ≤ x^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hs).bound (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℝ)] with x h hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _),one_mul] using h

theorem highConductorBlockBound_log_le {Q X T R k : ℕ} {A : ℝ}
    (hA : 0 < A) (hX : 2 ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) (hQX : Q ≤ X)
    (hQ : (Q:ℝ) ≤ 4*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10))
    (hR : (Real.log (X:ℝ))^(A+10) ≤ (R:ℝ))
    (hk : (k:ℝ) ≤ 6*Real.log (X:ℝ))
    (hT : (T:ℝ) ≤ (X:ℝ)^(1/16:ℝ))
    (hTroot : (X:ℝ)^(1/32:ℝ) ≤ Real.sqrt (T+1:ℕ))
    (hpower : (Real.log (X:ℝ))^(A+10) ≤ (X:ℝ)^(1/32:ℝ)) :
    highConductorBlockBound Q X T R k ≤
      8000*(X:ℝ)*(Real.log (X:ℝ))^(-A-3) := by
  let x : ℝ := X
  let L : ℝ := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ X)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hneg : L^(-A-10) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1
      (show -A-10 ≤ 0 by linarith)
  have hQweak : (Q:ℝ) ≤ 4*x^(1/2:ℝ) := by
    apply hQ.trans
    exact (mul_le_mul_of_nonneg_left hneg (by positivity)).trans_eq (mul_one _)
  have hsnonneg := vaughanShortBound_nonneg Q X T
  have hHnonneg := (conductorHarmonicBound_pos Q).le
  have hshort := vaughanShortBound_power_le hX hL hQX hQweak hT
  have hshortAbs : x^(7/8:ℝ)*L^2 ≤ x*L^(-A-3) := by
    convert rpow_absorption_of_exponents (c:=2) hx1 hL1 hpower
      (show A+5 ≤ A+10 by linarith) (show (1/32:ℝ) ≤ 1/8 by norm_num) using 1 <;> norm_num
    all_goals ring_nf
    all_goals simp
  have hshortTotal : 2*(Q:ℝ)*vaughanShortBound Q X T ≤ 256*x*L^(-A-3) := by
    calc
      _ ≤ 2*(4*x^(1/2:ℝ))*(32*x^(3/8:ℝ)*L^2) := by gcongr
      _ = 256*(x^(7/8:ℝ)*L^2) := by
        rw [show (7/8:ℝ)=1/2+3/8 by norm_num, Real.rpow_add hx]; ring
      _ ≤ _ := by nlinarith [hshortAbs]
  have hcoef : (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) ≤ 84*L^3 := by
    calc
      _ ≤ (6*L)*(7*L)*(2*L) := by
        gcongr
        · dsimp [L,x] at *; linarith
        · exact log_add_one_le_twice hX
      _ = _ := by ring
  have hRpos : 0 < (R:ℝ) := (Real.rpow_pos_of_pos hL0 _).trans_le hR
  have hb1 : 4*x/(R:ℝ) ≤ 4*x*L^(-A-6) := by
    calc
      _ ≤ 4*x/L^(A+10) := div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos hL0 _) hR
      _ = 4*x*L^(-A-10) := by
        rw [show -A-10=-(A+10) by ring,Real.rpow_neg hL0.le,div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have habs2 : x^(31/32:ℝ)*L ≤ x*L^(-A-6) := by
    convert rpow_absorption_of_exponents (c:=1) hx1 hL1 hpower
      (show A+7 ≤ A+10 by linarith) (le_refl (1/32:ℝ)) using 1 <;> norm_num
    all_goals ring_nf
    all_goals simp
  have hb2 : 16*Real.sqrt (conductorHarmonicBound Q)*x/Real.sqrt (T+1:ℕ) ≤
      32*x*L^(-A-6) := by
    calc
      _ ≤ 16*(2*L)*x/x^(1/32:ℝ) := by
        apply div_le_div₀ (by positivity) ?_ (Real.rpow_pos_of_pos hx _) hTroot
        gcongr
        exact sqrt_conductorHarmonicBound_le hQX hL
      _ = 32*(x^(31/32:ℝ)*L) := by
        rw [show (31/32:ℝ)=1-1/32 by norm_num,Real.rpow_sub hx,Real.rpow_one]
        ring
      _ ≤ _ := by nlinarith [habs2]
  have hb3 : 4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X ≤ 48*x*L^(-A-6) := by
    calc
      _ ≤ 4*(4*x^(1/2:ℝ)*L^(-A-10))*(3*L)*x^(1/2:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        gcongr
        exact conductorHarmonicBound_le hQX hL
      _ = 48*x*L^(-A-9) := by
        rw [show -A-9=(-A-10)+1 by ring,Real.rpow_add hL0,Real.rpow_one]
        have hh : x^(1/2:ℝ)*x^(1/2:ℝ)=x := by rw [←Real.rpow_add hx]; norm_num
        calc
          _ = 48*(x^(1/2:ℝ)*x^(1/2:ℝ))*(L^(-A-10)*L) := by ring
          _ = _ := by rw [hh]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have hbracket := add_le_add (add_le_add hb1 hb2) hb3
  have hlarge : ((k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ))*
      (4*x/(R:ℝ)+16*Real.sqrt (conductorHarmonicBound Q)*x/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X) ≤ 7056*x*L^(-A-3) := by
    calc
      _ ≤ (84*L^3)*(84*x*L^(-A-6)) := by
        apply mul_le_mul hcoef (by linarith [hbracket]) (by positivity) (by positivity)
      _ = _ := by
        rw [show -A-3=(-A-6)+3 by ring,Real.rpow_add hL0]
        norm_num
        ring
  unfold highConductorBlockBound
  change _ ≤ 8000*x*L^(-A-3)
  nlinarith [mul_pos hx (Real.rpow_pos_of_pos hL0 (-A-3))]

end LargePrimeGaps

end OAI
