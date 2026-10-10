import OAI.NumberTheory.DirichletL.Eisenstein.FredholmAlternative

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CanonicalRowCompletion
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid

lemma good_prime_norm_mod_six (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) : Ideal.absNorm P%6=1 := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,orderOf χ=6 := ⟨_,sexticChar_order P hg hc⟩
  have hdiv:=χ.orderOf_dvd_card_sub_one
  rw [hχ] at hdiv
  have hcard : 1<Fintype.card (ActualEisensteinCubic.O⧸P):=Fintype.one_lt_card
  have hn : Ideal.absNorm P=Fintype.card (ActualEisensteinCubic.O⧸P) := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  rw [hn]
  omega

lemma unit_sixth_exponent_mul (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (ha : a%6=1) (hb : b%6=1) :
    u.val^((a*b-1)/6)=u.val^((a-1)/6)*u.val^((b-1)/6) := by
  have ha' : a=6*(a/6)+1:=by omega
  have hb' : b=6*(b/6)+1:=by omega
  have hab : a*b=6*(a/6+b/6+6*((a/6)*(b/6)))+1 := by
    calc
      a*b=(6*(a/6)+1)*(6*(b/6)+1):=congrArg₂ (·*·) ha' hb'
      _ = _ := by ring
  have hab' : (a*b-1)/6=a/6+b/6+6*((a/6)*(b/6)):=by omega
  have hda : (a-1)/6=a/6:=by omega
  have hdb : (b-1)/6=b/6:=by omega
  rw [hab',hda,hdb,pow_add,pow_add,pow_mul,unit_pow_six,one_pow,mul_one]

private lemma multiset_unit_norm (u : ActualEisensteinCubic.Oˣ) (s : Multiset (Ideal ActualEisensteinCubic.O))
    (hs : ∀P∈s,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    (s.map (localRowValue u.val)).prod =
      eisEmbedding (u.val^(((s.map Ideal.absNorm).prod-1)/6)) ∧
      (s.map Ideal.absNorm).prod%6=1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons P s ih =>
    have hp:=hs P (Multiset.mem_cons_self _ _)
    let : P.IsMaximal:=hp.1
    have htail : ∀Q∈s,Q.IsMaximal ∧ lambda∉Q ∧ ringChar (ActualEisensteinCubic.O⧸Q)≠2:=
      fun Q hQ=>hs Q (Multiset.mem_cons_of_mem hQ)
    obtain ⟨hv,hn⟩:=ih htail
    have hP:=good_prime_norm_mod_six P hp.2.1 hp.2.2
    simp only [Multiset.map_cons,Multiset.prod_cons]
    refine ⟨?_,by rw [Nat.mul_mod,hP,hn]⟩
    rw [localRowValue_good _ P hp.2.1,actualSextic_unit_euler P hp.2.1 hp.2.2,hv]
    have hcard : Nat.card (ActualEisensteinCubic.O⧸P)=Ideal.absNorm P := by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
    rw [hcard,unit_sixth_exponent_mul u _ _ hP hn,map_mul]

theorem idealRowHom_unit_norm (u : ActualEisensteinCubic.Oˣ) (I : Ideal ActualEisensteinCubic.O) (hI : I≠0)
    (hgood : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    idealRowHom u.val I=eisEmbedding (u.val^((Ideal.absNorm I-1)/6)) := by
  have hn (s : Multiset (Ideal ActualEisensteinCubic.O)) : (s.map Ideal.absNorm).prod=Ideal.absNorm s.prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih => simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,ih]
  have hh:=(multiset_unit_norm u (normalizedFactors I) hgood).1
  rw [hn,Ideal.prod_normalizedFactors_eq_self hI] at hh
  change (if I=0 then 0 else _) = _
  rwa [ite_eq_right hI]

lemma ideal_norm_mod_six_of_good (I : Ideal ActualEisensteinCubic.O) (hI : I≠0)
    (hgood : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    Ideal.absNorm I%6=1 := by
  have hn (s : Multiset (Ideal ActualEisensteinCubic.O)) : (s.map Ideal.absNorm).prod=Ideal.absNorm s.prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih => simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,ih]
  have hh:=(multiset_unit_norm (1:ActualEisensteinCubic.Oˣ) (normalizedFactors I) hgood).2
  rwa [hn,Ideal.prod_normalizedFactors_eq_self hI] at hh

theorem idealRowHom_unit_eq_of_norm_mod_thirty_six (u : ActualEisensteinCubic.Oˣ) (I J : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hJ : J≠0)
    (hgI : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (hgJ : ∀P∈normalizedFactors J,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (hmod : Ideal.absNorm I%36=Ideal.absNorm J%36) :
    idealRowHom u.val I=idealRowHom u.val J := by
  rw [idealRowHom_unit_norm u I hI hgI,idealRowHom_unit_norm u J hJ hgJ]
  have hmi:=ideal_norm_mod_six_of_good I hI hgI
  have hmj:=ideal_norm_mod_six_of_good J hJ hgJ
  have hm : (Ideal.absNorm I-1)/6 ≡ (Ideal.absNorm J-1)/6 [MOD 6] := by
    dsimp [Nat.ModEq]
    omega
  exact congrArg eisEmbedding (pow_eq_pow_of_modEq hm (unit_pow_six u))

theorem rowTwist_unit_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z n : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ)
    (hn : n≠0)
    (hgood : ∀P∈normalizedFactors (Ideal.span {n}),
      P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    rowTwist Ψ m f (u.val*z) n = rowTwist Ψ m f z n *
      eisEmbedding (u.val^((Ideal.absNorm (Ideal.span {n})-1)/6)) := by
  change Ψ n*idealRowHom (m^6*f^4*(u.val*z)) (Ideal.span {n}) =
    (Ψ n*idealRowHom (m^6*f^4*z) (Ideal.span {n}))*_
  rw [show m^6*f^4*(u.val*z)=u.val*(m^6*f^4*z) by ring,
    idealRowHom_argument_mul,
    idealRowHom_unit_norm u _ (Ideal.span_singleton_eq_bot.not.mpr hn) hgood]
  ring

end CanonicalUnitEuler

namespace CompletedGauss
open ActualEisensteinCubic CompletedDyadic

theorem normalized_cusp_coefficient (d ζ : ℂ) (m n b : ℝ) (hn : 0<n) (hb : 0<b) :
    ζ*(d/((Real.sqrt ((3:ℝ)^m*n*b^3):ℝ):ℂ)) =
      (4/3:ℂ)*(81*ζ)*(normalizedCuspAmplitude d m b /
        ((4*(3:ℝ)^(m/3)*Real.sqrt n*b:ℝ):ℂ)) := by
  have ha : (3:ℝ)^(m/6)*Real.sqrt b≠0:=by positivity
  have hs : Real.sqrt ((3:ℝ)^m*n*b^3)≠0:=by positivity
  have hr : (3:ℝ)^(m/3)*Real.sqrt n*b≠0:=by positivity
  have hid:=cusp_coefficient_normalization m n b hn hb
  have hcross : ((3:ℝ)^(m/6)*Real.sqrt b)*((3:ℝ)^(m/3)*Real.sqrt n*b)=
      Real.sqrt ((3:ℝ)^m*n*b^3) := by
    have hh:=(div_eq_div_iff hs hr).mp hid
    simpa only [one_mul] using hh
  have hc := congrArg (fun x:ℝ=>(x:ℂ)) hcross
  push_cast at hc
  unfold normalizedCuspAmplitude
  have hsa : (((3:ℝ)^(m/6):ℝ):ℂ)≠0:=by exact_mod_cast (Real.rpow_pos_of_pos (by norm_num) (m/6)).ne'
  have hsb : ((Real.sqrt b:ℝ):ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hb).ne'
  have hsr : (((3:ℝ)^(m/3):ℝ):ℂ)≠0:=by exact_mod_cast (Real.rpow_pos_of_pos (by norm_num) (m/3)).ne'
  have hsn : ((Real.sqrt n:ℝ):ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
  have hbc : (b:ℂ)≠0:=by exact_mod_cast hb.ne'
  rw [←hc]
  push_cast
  field_simp
  ; ring

theorem normalized_reflection_weight (ζ : ℂ) (hζ : ‖ζ‖≤(1:ℝ)/81) :
    ‖(81:ℂ)*ζ‖≤1 := by
  rw [norm_mul]
  norm_num
  linarith

theorem normalized_cusp_coefficient_nat (d ζ : ℂ) (m : ℕ) (n b : ℝ)
    (hn : 0<n) (hb : 0<b) :
    ζ*(d/((Real.sqrt ((3:ℝ)^((m:ℝ)-4)*n*b^3):ℝ):ℂ)) =
      (4/3:ℂ)*(81*ζ)*(normalizedCuspAmplitude d ((m:ℝ)-4) b /
        ((4*ramifiedScale completedRamifiedInitial completedRamifiedStep m*Real.sqrt n*b:ℝ):ℂ)) := by
  rw [actual_ramified_scale]
  exact normalized_cusp_coefficient d ζ ((m:ℝ)-4) n b hn hb

theorem reflection_kernel_scale (X r c0 C K U B k n b D E : ℝ)
    (hX : 0<X) (hc0 : 0<c0) (hC : 0<C) (hK : 0<K) (hU : 0<U) (hB : 0<B)
    (hk : 0<k) (hn : 0<n) (hb : 0<b) (hD : 0<D) (hE : 0<E) :
    ((K^2*C^2/((X/c0^2)*D*E^3))⁻¹*r^3*B^3*U)*
      Real.exp (-2*Real.log (k/K)+Real.log (n/U)+3*Real.log (b/B)) =
      r^3*(D*n)*(E*b)^3*X/(k^2*(c0*C)^2) := by
  rw [positive_log_scale_identity k n b K U B _ hk hn hb hK hU hB]
  field_simp

theorem completed_branch_kernel_argument {ι : Type*} [Fintype ι]
    (P : ι→Ideal ActualEisensteinCubic.O) (hP : ∀i,P i≠0) (e : ι→Fin 3)
    (K X c0 r U B : ℝ) (I F Q H N V : Ideal ActualEisensteinCubic.O)
    (hX : 0<X) (hc0 : 0<c0) (hK : 0<completedResidualScale K I Q)
    (hU : 0<U) (hB : 0<B) (hH : H≠0) (hN : N≠0) (hV : V≠0) :
    ((completedBranchScale K (X/c0^2) I F Q P e)⁻¹*r^3*B^3*U)*
      Real.exp (-2*Real.log ((Ideal.absNorm H:ℝ)/completedResidualScale K I Q)+
        Real.log ((Ideal.absNorm N:ℝ)/U)+3*Real.log ((Ideal.absNorm V:ℝ)/B)) =
      r^3*(Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1*N):ℝ)*
        (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2*V):ℝ)^3*X/
        ((Ideal.absNorm H:ℝ)^2*(c0*(Ideal.absNorm (∏i,P i):ℝ))^2) := by
  have hnorm (J : Ideal ActualEisensteinCubic.O) (hj : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz=>hj (Ideal.absNorm_eq_zero_iff.mp hz))
  have hp : (∏i,P i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hP i)
  have hD:=reflectionExtractedDivisor_ne_zero P hP (fun i=>completedLocalExponent I F (P i)) e 1
  have hE:=reflectionExtractedDivisor_ne_zero P hP (fun i=>completedLocalExponent I F (P i)) e 2
  simpa only [completedBranchScale,map_mul,Nat.cast_mul] using
    reflection_kernel_scale X r c0 (Ideal.absNorm (∏i,P i):ℝ) (completedResidualScale K I Q) U B
      (Ideal.absNorm H:ℝ) (Ideal.absNorm N:ℝ) (Ideal.absNorm V:ℝ)
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1):ℝ)
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2):ℝ)
      hX hc0 (hnorm _ hp) hK hU hB (hnorm _ hH) (hnorm _ hN) (hnorm _ hV) (hnorm _ hD) (hnorm _ hE)

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem shortEnergy_scalar_normalization (C H R Z K X F G ε : ℝ)
    (hC : 0≤C) (hH : 0≤H) (hR : 0≤R) (hZ : 1≤Z) (hK : 0≤K)
    (hX : 0<X) (hF : 0≤F) (hG : 1≤G) (hε : 0≤ε)
    (hFZ : F≤Z^3) (hmass : X*F≤Z^3)
    (hmargin : (2*K)*G≤X*F*Z^(-((1:ℝ)/40))) :
    2*X*((C*H)*R*((2*K)*G*F)^ε*(K*F)*Z^ε)≤
      (C*H)*R*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hs : Z^(-((1:ℝ)/40))≤1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : -((1:ℝ)/40)≤0)
  have hp : (2*K)*G*F≤Z^6 := by
    calc
      _ ≤ (X*F*Z^(-((1:ℝ)/40)))*F:=mul_le_mul_of_nonneg_right hmargin hF
      _ ≤ (X*F)*F:=mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (mul_one _)) hF
      _ ≤ (Z^3)*(Z^3):=mul_le_mul hmass hFZ hF (by positivity)
      _ = _:=by ring
  have hpow : ((2*K)*G*F)^ε≤Z^(6*ε) := by
    apply (Real.rpow_le_rpow (by positivity) hp hε).trans_eq
    rw [←Real.rpow_natCast_mul hZ0.le]
    norm_num
  have hrow : 2*K≤X*F*Z^(-((1:ℝ)/40)) :=
    (le_mul_of_one_le_right (by positivity) hG).trans hmargin
  have hnorm : 2*X*(K*F)≤(X*F)^2*Z^(-((1:ℝ)/40)) := by
    calc
      _ = (X*F)*(2*K):=by ring
      _ ≤ (X*F)*(X*F*Z^(-((1:ℝ)/40))):=mul_le_mul_of_nonneg_left hrow (by positivity)
      _ = _:=by ring
  calc
    _ = (C*H)*R*((2*K)*G*F)^ε*(2*X*(K*F))*Z^ε:=by ring
    _ ≤ (C*H)*R*Z^(6*ε)*((X*F)^2*Z^(-((1:ℝ)/40)))*Z^ε:=by gcongr
    _ = _:=by
      rw [show 7*ε-(1:ℝ)/40=6*ε+(-((1:ℝ)/40))+ε by ring,
        Real.rpow_add hZ0,Real.rpow_add hZ0]
      ring

theorem canonicalShortEnergy_normalized_uniform_twist
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^((1:ℝ)/1000) → 0<X → X*F≤Z^3 →
    ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∀(labels : Finset (Ideal ActualEisensteinCubic.O)),labels⊆idealRange F →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        HasExactCompletedDyadicModels rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (CompletedUnitRows.unitRowFamily Ψ mask u f) lengthScale) →
      2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ)
        mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000))) K≤
      (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  obtain ⟨d,hbound⟩:=canonicalShortEnergy_uniform_twist a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩:=hbound W hs hW
  refine ⟨C,hC,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ hX hmass G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have he:=hb θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have hFZ' : F≤Z^3 := by
    apply hFZ.trans
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  have hGN : 1≤(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz=>hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscalar:=shortEnergy_scalar_normalization C ((1+‖θ‖)^d) ((rays:ℝ)^2*‖lengthScale‖^2)
    Z K X F (Ideal.absNorm G:ℝ) ε hC (by positivity) (by positivity) hZ
    (zero_le_one.trans hK) hX (zero_le_one.trans hF) hGN hε.le hFZ' hmass hmargin
  apply (mul_le_mul_of_nonneg_left he (by positivity : 0≤2*X)).trans
  convert hscalar using 1 <;> ring

end CanonicalRowCompletion

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma rowCoordinates_zero : rowCoordinates (0 : Fin 2 → ActualEisensteinCubic.O)=0 := by
  apply norm_le_zero_iff.mp
  have h := coordinates_norm_bound (0 : Fin 2 → ActualEisensteinCubic.O)
  have he : (fun i : Fin 2 => eisEmbedding ((0 : Fin 2 → ActualEisensteinCubic.O) i))=0 := by
    funext i
    exact map_zero _
  rw [he,norm_zero,mul_zero] at h
  exact h

lemma rowCoordinates_norm_pos {u : Fin 2 → ActualEisensteinCubic.O} (hu : u≠0) :
    0<‖rowCoordinates u‖ := by
  apply norm_pos_iff.mpr
  intro h
  exact hu (rowCoordinates_injective (h.trans rowCoordinates_zero.symm))

lemma rowCoordinates_le_horizontal (u : Fin 2 → ActualEisensteinCubic.O) (z : ℂ) (hz : ‖z‖≤1) :
    ‖rowCoordinates u‖≤2*(‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖+
      ‖eisEmbedding (u 0)‖) := by
  apply (coordinates_norm_bound u).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · simp only [Fin.zero_eta]
    linarith [norm_nonneg (eisEmbedding (u 0)*z+eisEmbedding (u 1))]
  · have h : ‖eisEmbedding (u 1)‖≤
        ‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖+‖eisEmbedding (u 0)*z‖ := by
      simpa only [add_sub_cancel_left] using
        norm_sub_le (eisEmbedding (u 0)*z+eisEmbedding (u 1)) (eisEmbedding (u 0)*z)
    rw [norm_mul] at h
    have hm := mul_le_mul_of_nonneg_left hz (norm_nonneg (eisEmbedding (u 0)))
    rw [mul_one] at hm
    exact h.trans (add_le_add_right hm _)

lemma height_times_coordinate_bound (A c v N : ℝ)
    (_hA : 0≤A) (hc : 1≤c) (hv : 1/2≤v) (hN : N≤2*(A+c)) :
    N*v≤5*(A^2+c^2*v^2) := by
  have hv0 : 0≤v := by linarith
  have hcv : v≤c*v := by nlinarith
  have hcv0 : 1/2≤c*v := by linarith
  have hv2 : v^2≤(c*v)^2 := by nlinarith
  have hcross : 2*v*A≤A^2+c^2*v^2 := by nlinarith [sq_nonneg (A-v)]
  have hlin : 2*c*v≤4*(c*v)^2 := by nlinarith
  have hNv := mul_le_mul_of_nonneg_right hN hv0
  nlinarith [sq_nonneg A]

lemma rowHeight_times_coordinates (u : Fin 2 → ActualEisensteinCubic.O) (hu : u 0≠0)
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    (v/(‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖^2+
       ‖eisEmbedding (u 0)‖^2*v^2))*‖rowCoordinates u‖≤5 := by
  have hc : 1≤‖eisEmbedding (u 0)‖ := by
    have hh := one_le_normSq_embedding (u 0) hu
    rw [Complex.normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg (eisEmbedding (u 0))]
  have hden : 0<‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖^2+
      ‖eisEmbedding (u 0)‖^2*v^2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  simpa only [mul_comm v] using
    height_times_coordinate_bound _ _ _ _ (norm_nonneg _) hc hv
      (rowCoordinates_le_horizontal u z hz)

lemma positive_rpow_of_product_bound (h N C σ : ℝ)
    (hh : 0≤h) (hN : 0<N) (hC : 0≤C) (hσ : 0≤σ) (hb : h*N≤C) :
    h^σ≤C^σ*N^(-σ) := by
  have hdiv : h≤C/N := (le_div_iff₀ hN).mpr hb
  have hr := Real.rpow_le_rpow hh hdiv hσ
  rw [Real.div_rpow hC hN.le,div_eq_mul_inv] at hr
  simpa only [Real.rpow_neg hN.le] using hr

def cuspRemainderProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v-cuspSeedProfile a b s v

lemma cuspRemainderProfile_norm_le (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ‖cuspRemainderProfile a b s v‖≤v^s.re := by
  have hnon : 0≤1-cuspTransition a b v := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hle : 1-cuspTransition a b v≤1 := by
    have := Real.smoothTransition.nonneg ((v-a)/(b-a))
    change 0≤cuspTransition a b v at this
    linarith
  have he : cuspRemainderProfile a b s v=
      ((1-cuspTransition a b v:ℝ):ℂ)*positiveHeightPower s v := by
    simp only [cuspRemainderProfile,cuspSeedProfile,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  rw [he,norm_mul,Complex.norm_of_nonneg hnon,positiveHeightPower_eq_cpow s v hv,
    Complex.norm_cpow_eq_rpow_re_of_pos hv]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hv.le _) hle

lemma cuspRemainderProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : 0<v) (hbv : b≤v) : cuspRemainderProfile a b s v=0 := by
  rw [cuspRemainderProfile,cuspSeedProfile_incoming a b s v hab hbv hv,
    positiveHeightPower_eq_cpow s v hv,sub_self]

lemma cuspRemainderProfile_norm_le_bound (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hb : 0≤b) (hv : 0<v) (hs : 0≤s.re) :
    ‖cuspRemainderProfile a b s v‖≤b^s.re := by
  by_cases h : b≤v
  · rw [cuspRemainderProfile_zero a b s v hab hv h,norm_zero]
    exact Real.rpow_nonneg hb _
  · exact (cuspRemainderProfile_norm_le a b s v hv).trans
      (Real.rpow_le_rpow hv.le (le_of_not_ge h) hs)

end

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_row_embedding_ne_zero {u : Fin 2 → ActualEisensteinCubic.O} (hu : u≠0) :
    (eisEmbedding ∘ u)≠0 := by
  intro h
  apply hu
  funext i
  apply eisEmbedding_injective
  simpa only [Function.comp_apply,Pi.zero_apply,map_zero] using congrFun h i

lemma coprime_row_ne_zero {u : Fin 2 → ActualEisensteinCubic.O} (h : IsCoprime (u 0) (u 1)) : u≠0 := by
  intro hz
  have hh : (0 : ActualEisensteinCubic.O)=1 := by
    simpa only [hz,Pi.zero_apply,isCoprime_zero_left,isUnit_zero_iff] using h
  exact zero_ne_one hh

theorem cuspRemainderProfile_row_bound (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤s.re)
    (u : Fin 2 → ActualEisensteinCubic.O) (hcop : IsCoprime (u 0) (u 1))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    ‖cuspRemainderProfile a b s (transformedHeight z v (eisEmbedding ∘ u))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates u‖^(-s.re) := by
  have hu := coprime_row_ne_zero hcop
  have hN := rowCoordinates_norm_pos hu
  have hv0 : 0<v := by linarith
  have hh : 0<transformedHeight z v (eisEmbedding ∘ u) :=
    div_pos hv0 (heightDenominator_pos z v hv0 _ (integral_row_embedding_ne_zero hu))
  have hC : 0≤max 5 (2*b) := (by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)
  by_cases hc : u 0=0
  · have hunit : IsUnit (u 1) := by simpa only [hc,isCoprime_zero_left] using hcop
    obtain ⟨d,hd⟩ := hunit
    have hdnorm : ‖eisEmbedding (u 1)‖=1 := by
      rw [←hd]
      exact GaussGeneratorTransport.norm_eisEmbedding_unit d
    have hn : ‖rowCoordinates u‖≤2 := by
      apply (coordinates_norm_bound u).trans
      have hm : ‖fun i => eisEmbedding (u i)‖≤1 := by
        apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro i
        fin_cases i
        · change ‖eisEmbedding (u 0)‖≤1
          simp only [hc,map_zero,norm_zero,zero_le_one]
        · exact hdnorm.le
      nlinarith
    apply (cuspRemainderProfile_norm_le_bound a b s _ hab hb hh hs).trans
    exact positive_rpow_of_product_bound b _ _ _ hb hN hC hs
      (by nlinarith [mul_le_mul_of_nonneg_left hn hb,le_max_right (5 : ℝ) (2*b)])
  · apply (cuspRemainderProfile_norm_le a b s _ hh).trans
    apply positive_rpow_of_product_bound _ _ _ _ hh.le hN hC hs
    exact (rowHeight_times_coordinates u hc z hz v hv).trans (le_max_left _ _)

def translatedCuspRow (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets) : Fin 2 → ActualEisensteinCubic.O :=
  Matrix.vecMul (cosetRow r) (M : Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O)

lemma translatedCuspRow_injective (M : SL(2,ActualEisensteinCubic.O)) : Function.Injective (translatedCuspRow M) := by
  intro r t h
  apply cosetRow_injective
  have hh := congrArg (fun u : Fin 2 → ActualEisensteinCubic.O => Matrix.vecMul u
    ((M⁻¹ : SL(2,ActualEisensteinCubic.O)) : Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O)) h
  simpa only [translatedCuspRow,Matrix.vecMul_vecMul,←Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.vecMul_one] using hh

lemma integral_bottom_coprime (M : SL(2,ActualEisensteinCubic.O)) : IsCoprime (M 1 0) (M 1 1) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by
    simpa only [Matrix.det_fin_two] using M.property
  refine ⟨-M 0 1,M 0 0,?_⟩
  linear_combination hd

lemma translatedCuspRow_coprime (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets) :
    IsCoprime (translatedCuspRow M r 0) (translatedCuspRow M r 1) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change IsCoprime (translatedCuspRow M (cosetOf N) 0) (translatedCuspRow M (cosetOf N) 1)
    simpa only [translatedCuspRow,cosetRow_cosetOf,row,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Matrix.vecMul,dotProduct] using integral_bottom_coprime ((N : SL(2,ActualEisensteinCubic.O))*M)

lemma cosetHeight_integral_chart (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    cosetHeight r (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (eisEmbedding ∘ translatedCuspRow M r) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf N) (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (eisEmbedding ∘ translatedCuspRow M (cosetOf N))
    rw [cosetHeight_cosetOf,←integralComplexMatrix_levelThree,
      ←mul_smul,←map_mul,hyperbolicHeight_action_upperPoint]
    simp only [integralComplexMatrix_apply,transformedHeight,heightDenominator,
      Function.comp_apply,translatedCuspRow,cosetRow_cosetOf,row,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Matrix.vecMul,dotProduct]

lemma translated_remainder_majorant (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤s.re)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v)
    (hv0 : 0<v) (r : CuspCosets) :
    ‖(cosetCharacter r)⁻¹*cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates (translatedCuspRow M r)‖^(-s.re) := by
  rw [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul,cosetHeight_integral_chart]
  exact cuspRemainderProfile_row_bound a b s hab hb hs _
    (translatedCuspRow_coprime M r) z hz v hv

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma cuspCutoffTerm_eq_seedProfile (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (r : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm 1 (cuspSeedProfile a b s) r w=
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
  unfold cuspCutoffTerm
  split_ifs with h
  · rfl
  · rw [cuspSeedProfile_zero a b s _ hab ((le_of_not_gt h).trans ha),mul_zero]

lemma cusp_seed_profile_summable (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => (cosetCharacter r)⁻¹*
      cuspSeedProfile a b s (cosetHeight r w)) :=
  (cuspCutoffTerm_summable 1 le_rfl _ w).congr
    (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)

theorem eisenstein_sub_seed_eq_series (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w-smoothCuspSeed a b s w=
      ∑'r : CuspCosets,(cosetCharacter r)⁻¹*
        cuspRemainderProfile a b s (cosetHeight r w) := by
  have hE := (height_series_summable_norm s hs w).of_norm
  have hS := cusp_seed_profile_summable a b ha hab s w
  have heq : smoothCuspSeed a b s w=∑'r : CuspCosets,
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
    unfold smoothCuspSeed cuspCutoffCorrection
    exact tsum_congr (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)
  rw [hyperbolicEisenstein_eq_height_series,heq,←hE.tsum_sub hS]
  apply tsum_congr
  intro r
  rw [cuspRemainderProfile,positiveHeightPower_eq_cpow s _ (cosetHeight_pos r w)]
  ring

def eisensteinRemainderBound (b : ℝ) (s : ℂ) : ℝ :=
  (max 5 (2*b))^s.re * ∑'n : (Fin 2×Fin 2)→ℤ,‖n‖^(-s.re)

lemma eisensteinRemainderBound_nonneg (b : ℝ) (s : ℂ) :
    0≤eisensteinRemainderBound b s :=
  mul_nonneg (Real.rpow_nonneg ((by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)) _)
    (tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _))

theorem eisenstein_sub_seed_chart_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (M : SL(2,ActualEisensteinCubic.O))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    ‖hyperbolicEisenstein s (integralComplexMatrix M • upperPoint z v hv0)-
      smoothCuspSeed a b s (integralComplexMatrix M • upperPoint z v hv0)‖≤
      eisensteinRemainderBound b s := by
  let G : ((Fin 2×Fin 2)→ℤ)→ℝ := fun n => (max 5 (2*b))^s.re*‖n‖^(-s.re)
  let f : CuspCosets→(Fin 2×Fin 2)→ℤ := fun r => rowCoordinates (translatedCuspRow M r)
  let R : CuspCosets→ℂ := fun r => (cosetCharacter r)⁻¹*cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))
  have hg : Summable G := (summable_integer_four_rpow s.re hs).mul_left _
  have hi : Function.Injective f := rowCoordinates_injective.comp (translatedCuspRow_injective M)
  have hb : ∀r,‖R r‖≤G (f r) :=
    translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0
  have hr : Summable (fun r => ‖R r‖) :=
    (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [eisenstein_sub_seed_eq_series a b ha hab s (by linarith)]
  change ‖∑'r,R r‖≤eisensteinRemainderBound b s
  apply (norm_tsum_le_tsum_norm hr).trans
  have hsum : (∑'r,‖R r‖)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

theorem eisenstein_sub_seed_bounded (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (w : HyperbolicSpace) :
    ‖hyperbolicEisenstein s w-smoothCuspSeed a b s w‖≤eisensteinRemainderBound b s := by
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  have hz1 : ‖z‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have hv1 : 1/2≤v := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hh0 := Real.sqrt_nonneg (2/3 : ℝ)
    nlinarith
  have hw : w=integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [←hMw,map_inv,inv_smul_smul]
  rw [hw]
  exact eisenstein_sub_seed_chart_bound a b ha hab s hs M⁻¹ z hz1 v hv1 hv

lemma cuspRemainderProfile_measurable (a b : ℝ) (s : ℂ) :
    Measurable (cuspRemainderProfile a b s) := by
  unfold cuspRemainderProfile cuspSeedProfile positiveHeightPower logRatioPower cuspTransition
  fun_prop

lemma eisenstein_sub_seed_measurable (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) :
    Measurable (fun w => hyperbolicEisenstein s w-smoothCuspSeed a b s w) := by
  simp_rw [eisenstein_sub_seed_eq_series a b ha hab s hs]
  apply Measurable.tsum
  intro r
  exact measurable_const.mul ((cuspRemainderProfile_measurable a b s).comp
    (cosetHeight_continuous r).measurable)

theorem kernel_eisenstein_sub_seed_memLp (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    MemLp (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) 2 (integralQuotientVolume globalKubotaKernel) := by
  have hmeas : Measurable (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) :=
    measurable_from_quotient.mpr (eisenstein_sub_seed_measurable a b ha hab s (by linarith))
  apply MemLp.of_bound hmeas.aestronglyMeasurable (eisensteinRemainderBound b s)
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact eisenstein_sub_seed_bounded a b ha hab s hs w

end CubicEisenstein

end

end OAI
