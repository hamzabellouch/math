import OAI.NumberTheory.DirichletL.RowCompletion.DensityTransfer
import OAI.NumberTheory.DirichletL.Eisenstein.SeedHeight

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

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SecondPassIntegration hiding O
open InitialMeanSquare hiding O
open CanonicalCubeSeparation
open CanonicalCoefficientClass (IsBaseRayTwist)
open FirstPassCubeLabels (primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

theorem hasInitialCanonicalDensityAtRadius_of_theta {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound) :
    HasInitialCanonicalDensityAtRadius χ S hbad := by
  intro deltaLoss hδ P A hA
  let base:=conjugateMonoid (normCharacter χ)
  have hbase : ∀u,‖base u‖≤1:=conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  obtain ⟨d,henergy⟩:=outsideLogEnergy_small_power S hSp hbad base hbase
    ρ q levelBound hρ hq hlevel hmodels deltaLoss hδ A hA
  refine ⟨d,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hV₁ hV₂
  have hs₁ : ContDiff ℝ ∞ (orientedLogProfile true V₁):=Complex.conjCLE.contDiff.comp hVs₁
  have hb₁ : ∀s,orientedLogProfile true V₁ s≠0→|s|≤A := by
    intro s hs
    apply hV₁ s
    intro hz
    exact hs (by simp [orientedLogProfile,hz])
  obtain ⟨C₁,hC₁,he₁⟩:=henergy (orientedLogProfile true V₁) hs₁ hb₁
  obtain ⟨C₂,hC₂,he₂⟩:=henergy (orientedLogProfile false V₂) hVs₂ hV₂
  obtain ⟨A',Vmax,hA',hVmax,hbV₁,hbV₂,hsV₁,hsV₂⟩:=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z₀,hZ₀,hthreshold⟩:=canonicalInitialThreshold S
  let I₀:=∫t : ℝ,firstLogDensity 0 t
  have hI₀ : 0≤I₀:=integral_nonneg (fun t=>FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  let Ccan:=6*(C₁+C₂)*I₀^3
  let Cele:=initialElementaryConstant A' Vmax*I₀^3
  let C:=Ccan+Cele*Z₀^3+1
  have hCcan : 0≤Ccan:=by dsimp only [Ccan];positivity
  have hCele : 0≤Cele:=mul_nonneg (initialElementaryConstant_nonneg A' Vmax) (pow_nonneg hI₀ _)
  have hC : 0<C:=by dsimp only [C];positivity
  have hcanC : Ccan≤C:=by
    have hp : 0≤Cele*Z₀^3:=by positivity
    dsimp only [C]
    linarith
  have heleC : Cele*Z₀^3≤C:=by
    dsimp only [C]
    linarith
  let Cpool:=Real.exp (radiusIter A 3000)
  refine ⟨C,Cpool,max P 3,hC,Real.one_le_exp (radiusIter_nonneg A hA 3000),le_max_left _ _,?_⟩
  intro D Z X lengthScale K R ray T hZ hpool hX hL hK hXP hLP hKP hRP hmass hinv hT hout
  let p:=outsidePrime S D
  let hp:=outsidePrime_ne_zero S hbad D
  let hcop:=outsidePrime_coprime S hbad D
  let hg:=outsidePrime_good S hbad D
  let:=outsidePrime_maximal S hbad D
  let Ψ₁:=secondRayMinus base ray
  let Ψ₂:=secondRayPlus base ray
  let m:=primeSubsetGenerator (fun i=>Ideal.span {p i}) R
  let labels:=T.image Prod.fst
  have hmember : IsBaseRayTwist base base:=Or.inl rfl
  have hη : 0≤canonicalDescentPadding deltaLoss:=(canonicalDescentPadding_budget deltaLoss hδ).1.le
  have hstate₁ := initialCanonicalState S D hbad base Ψ₁ (hmember.secondMinus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hstate₂ := initialCanonicalState S D hbad base Ψ₂ (hmember.secondPlus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hZδ : 1≤Z^deltaLoss:=Real.one_le_rpow hZ hδ.le
  have hD : Real.exp (radiusIter A 3000)*Z^3≤D :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ (le_max_right P 3)) (Real.exp_pos _).le).trans hpool
  have hlabels : ∀z∈T,z.1∈labels:=fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩
  have hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K:=fun z hz=>(hT z hz).2.2.2
  have hzero : ∀z∈T,z.2≠0:=fun z hz=>(hT z hz).2.2.1
  by_cases hlarge : Z₀≤Z
  · obtain ⟨hZgt,hZbig,hfixed⟩:=hthreshold Z hlarge
    have hleft (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₁ t) m labels (orientedLogProfile true V₁) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₁ D Z Ψ₁ m labels X lengthScale K t hstate₁ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₁ t) m labels
        (orientedLogProfile true V₁) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hright (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₂ t) m labels (orientedLogProfile false V₂) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₂ D Z Ψ₂ m labels X lengthScale K t hstate₂ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₂ t) m labels
        (orientedLogProfile false V₂) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hd:=densityChildEnergy_from_canonical_heights p hp hcop hg Finset.univ Ψ₁ Ψ₂ m T labels
      V₁ V₂ X lengthScale K ((C₁+C₂)*Z^deltaLoss) d (by linarith) (by linarith) (by positivity)
      hlabels hrows hzero hleft hright
    change outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤_ at hd
    have hcan : outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤Ccan*Z^deltaLoss*(X*lengthScale)^2 := by
      convert hd using 1 ; dsimp only [Ccan,I₀] ; ring
    exact hcan.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcanC (Real.rpow_nonneg (by linarith) _)) (sq_nonneg _))
  · have hKcap : K≤Z₀^3:=hstate₁.row_le_global.trans
      (pow_le_pow_left₀ (by linarith) (le_of_not_ge hlarge) 3)
    have hΨ₁ : ∀u,‖Ψ₁ u‖≤1:=fun u=>(secondRayMinus_norm_le base ray u).trans (hbase u)
    have hΨ₂ : ∀u,‖Ψ₂ u‖≤1:=fun u=>(secondRayPlus_norm_le base ray u).trans (hbase u)
    have hd:=initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X lengthScale K A' Vmax d (by linarith) hL hK hA' hVmax hbV₁ hbV₂ hsV₁ hsV₂
      (fun z hz=>⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩)
    change outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤Cele*K*(X*lengthScale)^2 at hd
    apply hd.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hKcap hCele).trans
      (heleC.trans (le_mul_of_one_le_right hC.le hZδ))

end CanonicalRowCompletion

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (normalizedColumn columnLog firstLogDensity)

theorem initial_sector_transfer_radius
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU : ∀t,g t≠0→U t=1) (hgA : ∀t,g t≠0→|t|≤A)
    (ε : ℝ) (hε : 0<ε) (N J : ℕ) :
    ∃ (windows : Fin 7→ℝ→ℂ) (C Cₛ : ℝ),0≤C ∧ 0≤Cₛ ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : ActualEisensteinCubic.O→*ℂ) (m r : ActualEisensteinCubic.O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<H → 0<E → 0<V → 0<X → 0<K →
        (∀a,‖Ψ a‖≤1) → (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        ∃ B : Frequency→ℝ,
          (∀q,0≤B q) ∧
          (∀q,(1+H*K/(E^2*V^2*X^2))^N*B q≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S)
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S) W H‖≤
          (C*H*elementNorm r/Z^2*‖secondRayCoefficient ray‖*(K*Real.exp 2)^ε)*
            (∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := initial_sector_fixed_profiles
    U hUc hUs g g W A hA hU hU hgA hgA
  obtain ⟨Cw,hCw,hwbound⟩ := outerWindow_global_bound windows hwc (fun i => (hws i).continuous)
  have hM : 0≤A+2+1 := by linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := initial_source_uniform_transfer ε hε A₁ A₂ W windows
    (fun _ => A+2+1) (fun _ => hM) hwb N J
  refine ⟨windows,Cw*Cₐ,Cₛ,mul_nonneg hCw hCₐ.le,hCₛ,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m r ray s Z H E V X K hZ hH hE hV hX hK hΨ hs hk hz he hv hkap
  let R := H*K/(E^2*V^2*X^2)
  have hR : 0<R := by dsimp [R]; positivity
  obtain ⟨b,hpoint,hbound⟩ := htrans R hR
  let B : Frequency→ℝ := fun q => ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b q‖
  refine ⟨B,fun q => norm_nonneg _,?_,?_⟩
  · intro q
    simpa only [B,R,tripleCoefficient,mul_assoc] using hpoint q.1 q.2.1 q.2.2
  · let T := s.image (sourceObservation p)
    have hT0 : ∀y∈T,y.1≠0 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact sourceRow_nonzero p x (hk x hx)
    have hTK : ∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K*Real.exp 2 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hpos := elementNorm_pos _ (sourceRow_nonzero p x (hk x hx))
      have hl : Real.log (elementNorm (sourceObservation p x).1/K)≤2 :=
        (le_abs_self _).trans (hkap x hx)
      have hh := Real.exp_le_exp.mpr hl
      rw [Real.exp_log (div_pos hpos hK)] at hh
      have hh' := (div_le_iff₀ hK).mp hh
      simpa only [elementNorm,eisEmbedding_norm_sq_eq_absNorm_span,mul_comm] using hh'
    let D := H*elementNorm r/Z^2*‖secondRayCoefficient ray‖
    have hD : 0≤D := by dsimp [D,elementNorm]; positivity
    have hweights : ∀x∈s,‖sourceWeight p hp hcop hg Ψ m ray Z H x‖*
        ‖outerWindow windows (sourceLogZ p Z X x) 0 (sourceLogE p E x) (sourceLogV p V x) (sourceLogK p K x)‖≤D*Cw := by
      intro x hx
      exact mul_le_mul (sourceWeight_norm_fixed p hp hcop hg hinj hc Ψ m r ray Z H x
        (hs x hx) hZ hH.le (hΨ _) (hΨ _)) (hwbound _ _ _ _ _) (norm_nonneg _) hD
    have hh := hbound p hp hcop hg hinj r s T (sourceWeight p hp hcop hg Ψ m ray Z H) (D*Cw)
      (K*Real.exp 2) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r)
      (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K) X X
      (mul_nonneg hD hCw) (by positivity) hs (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) hT0 hTK hweights
    rw [hid p hp hcop hg hinj hpr F Ψ m r ray s Z H E V X K hZ hE hV hX hK hs hk hz he hv hkap]
    convert hh using 1 ; dsimp [D,B,R,T] ; ring

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

theorem initial_subbin_transfer_radius
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset ActualEisensteinCubic.O) (Z H M : ℝ) (j : SecondLogIndex)
        (s : Finset (SecondExpansionData ι)),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        s ⊆ secondLogSector p ∅ F K R Z M j →
        let X := initialLogColumn Z (primeProductNorm p R) j
        let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
        ∃ B : Frequency → ℝ,
          (∀ q, 0 ≤ B q) ∧
          (∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) W H‖ ≤
          (C*H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
            (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,hwb,ht⟩ :=
    initial_sector_transfer_radius U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F R Ψ m ray K Z H M j s hZ hH hΨ hsub
  dsimp only
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let X := initialLogColumn Z (primeProductNorm p R) j
  have hR : 0 < primeProductNorm p R := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hs : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
      (secondLogSector_subset p ∅ F K R Z M j (hsub hx))
  have hk : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp (hsub hx)).1).2.2.2.1
  have hcoords := initial_sector_coordinates p hp F R K Z M hZ j
  obtain ⟨B,hB,hdec,hbound⟩ := ht p hp hcop hg hinj hc hpr F Ψ m r ray s Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) hZ hH
    (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) hΨ hs hk
    (fun x hx => (hcoords x (hsub hx)).1) (fun x hx => (hcoords x (hsub hx)).2.1)
    (fun x hx => (hcoords x (hsub hx)).2.2.1) (fun x hx => (hcoords x (hsub hx)).2.2.2)
  refine ⟨B,hB,?_,?_⟩
  · simpa only [X, initial_log_radial Z H (primeProductNorm p R) hZ.ne' hR.ne'] using hdec
  · simpa only [r, elementNorm, primeSubsetGenerator_norm_eq_productNorm] using hbound

end

section
open ActualEisensteinCubic
open SecondPassArithmetic

theorem initial_source_target_coprime
    {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]
    (bad : Ideal ActualEisensteinCubic.O) (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (s : Finset (SecondExpansionData ι)) :
    ∀z∈sourceIdealTarget (s.image (sourceObservation p)),IsCoprime z.1 bad := by
  intro z hz
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
  change IsCoprime (Ideal.span {(sourceObservation p x).2}) bad
  rw [sourceLabel_span]
  exact (IsCoprime.prod_left (fun i _=>hbad i)).mul_left
    (IsCoprime.prod_left (fun i _=>hbad i))

end

open MeasureTheory
open scoped BigOperators Classical ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

theorem HasInitialCanonicalDensityAtRadius.retained_density {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (a b σ θ ν η : ℝ) (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) (A : ℝ) (hA : 0≤A) :
    ∃ J : ℕ,∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
      ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
      ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧ ∀ (D : ℕ) (Z : ℝ)
        (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (j : SecondLogIndex)
        (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
        1 ≤ Z → Cpool*Z^E ≤ D →
        R ∈ boundedPrimeSupports (outsidePrime S D) Finset.univ (Z*Real.exp (initialErrorWindow a b)) →
        j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z (Z^(1+σ))) →
        initialRadial Z (Z^(1+σ)) (primeProductNorm (outsidePrime S D) R) j ≤ Z^θ →
        (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
          z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2) →
        (∀z∈T,IsCoprime z.1 (∏P∈S,P)) →
        outsideCanonicalDensity χ S hbad D ray R T V₁ V₂
          (initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j) J ≤
        C*Z^η*(initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j*initialLogLabel j)^2 := by
  obtain ⟨J,hJ⟩ := hcan η hη 20 A hA
  refine ⟨J,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hVrad₁ hVrad₂
  obtain ⟨Cc,Cpool,E,hCc,hCpool,hPE,hcanonical⟩ := hJ V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hVrad₁ hVrad₂
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z0,hZ0,hthreshold⟩ := initial_large_threshold a b (initialExcludedNorm S) ν
    (initialExcludedNorm_ge_one S) hν
  let Ce := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  let K0 := initialPolynomialCap a b*Z0^17*Real.exp 2
  let C := Cc+Ce*(K0+1)+1
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hCe : 0 ≤ Ce := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hcap := initialPolynomialCap_ge_one a b
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCcC : Cc ≤ C := by dsimp [C]; nlinarith
  have hCeC : Ce ≤ C := by dsimp [C]; nlinarith
  have hCeKC : Ce*K0 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,Cpool,E,hC,hCpool,hPE,?_⟩
  intro D Z R ray j T hZ hpool hR hj hrad hT hTc
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let lengthScale := initialLogLabel j
  let Kr := secondLogK j*Real.exp 2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hB := primeProductNorm_ge_one p hp R
  have hBpos := zero_lt_one.trans_le hB
  have hX : 0 < X := initialLogColumn_pos Z _ j hZp hBpos
  have hL : 1 ≤ lengthScale := initialLogLabel_ge_one j
  have hKr : 1 ≤ Kr := one_le_mul_of_one_le_of_one_le
    (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hZη : 1 ≤ Z^η := Real.one_le_rpow hZ hη.le
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hΨ₁ : ∀ z,‖secondRayMinus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayMinus_norm_le Ψ ray z).trans (hΨ z)
  have hΨ₂ : ∀ z,‖secondRayPlus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayPlus_norm_le Ψ ray z).trans (hΨ z)
  have hTb : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ Kr := by
    intro z hz
    exact ⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩
  have promote (d : ℝ) (hd : d ≤ C)
      (he : outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ d*(X*lengthScale)^2) :
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^η*(X*lengthScale)^2 :=
    he.trans (mul_le_mul_of_nonneg_right (hd.trans (le_mul_of_one_le_right hC.le hZη)) (sq_nonneg _))
  by_cases hzlarge : Z0 ≤ Z
  · have hgeom := initial_large_bin_geometry p hp Finset.univ R a b Z σ θ ν (initialExcludedNorm S)
      j hZ (initialExcludedNorm_ge_one S) hR hj hσ hmargin (hthreshold Z hzlarge) hrad
    dsimp only at hgeom
    by_cases hxlarge : 1 ≤ X
    · exact (hcanonical D Z X lengthScale Kr R ray T hZ hpool hxlarge hL hKr
        hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1 hgeom.2.2.2.2.2 hT hTc).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcC (Real.rpow_nonneg hZp.le _)) (sq_nonneg _))
    · have hKL : Kr ≤ lengthScale := initial_subunit_row_le_label Z X lengthScale Kr
        (initialExcludedNorm S*primeProductNorm p R) ((1 : ℝ)/20) hZ (le_of_not_ge hxlarge)
        (zero_le_one.trans hL) (zero_le_one.trans hKr)
        (one_le_mul_of_one_le_of_one_le (initialExcludedNorm_ge_one S) hB)
        (by norm_num) (by simpa only [Kr,X,lengthScale,neg_div] using hgeom.2.2.2.2.2)
      apply promote Ce hCeC
      exact initial_subunit_density_bound p hp hcop hg (outsidePrime_odd S hbad D)
        (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hKL hA hVmax hV₁ hV₂ hs₁ hs₂ hTb
  · have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
    have hkr : Kr ≤ K0 := by
      have hbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
        (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
      have hcapZ := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
      have hpow : Z^17 ≤ Z0^17 := pow_le_pow_left₀ hZp.le (le_of_not_ge hzlarge) 17
      calc
        Kr ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
          mul_le_mul_of_nonneg_right (hbin.trans hcapZ) (Real.exp_pos _).le
        _ ≤ K0 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hcap)) (Real.exp_pos _).le
    apply promote (Ce*Kr) ((mul_le_mul_of_nonneg_left hkr hCe).trans hCeKC)
    exact initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hA hVmax hV₁ hV₂ hs₁ hs₂ hTb

end InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem HasInitialCanonicalDensityAtRadius.retained_source {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ θ ν η : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hcop := outsidePrime_coprime S hbad D
      let hg := outsidePrime_good S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z (initialErrorWindow a b) j))
            G G W H‖ else 0) ≤ C*H*Z^(35*η) := by
  obtain ⟨J,hJ⟩ := HasInitialCanonicalDensityAtRadius.retained_density χ S hbad hcan a b σ θ ν η hσ hν hη hmargin
    (initialErrorWindow a b+2+1) (by unfold initialErrorWindow; positivity)
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,hwb,ht⟩ :=
    initial_subbin_transfer_radius U hUc hUs g W (initialErrorWindow a b) hM hU hgs η hη 0 (2*J)
  obtain ⟨Ce,Cpool,E,hCe,hCpool,hPE,henergy⟩ := hJ (windows 5) (windows 6) (hwc 5) (hwc 6) (hws 5) (hws 6) (hwb 5) (hwb 6)
  obtain ⟨Cl,hCl,hlog⟩ := initial_row_log_budget η (initialPolynomialCap a b) hη (initialPolynomialCap_ge_one a b)
  let C0 := Ct*Real.exp 4*Ce*Cs*initialRayMass*Cl
  have hray := initialRayMass_nonneg
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0+1,Cpool,E,by linarith,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hKmax : 1 ≤ Kmax := initialErrorRowBound_ge_one a b Z H hZ hH
  let B : SecondRayIndex → Finset (OutsidePrimeIndex S D) → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  have hB (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  let d := H*Real.exp 4*(Ce*Z^η)*Cs*(Kmax*Real.exp 2)^η
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hterm (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
      (hR : R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M))
      (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
      (hlow : initialRadial Z H (primeProductNorm p R) j ≤ Z^θ) :
      initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j) ≤
        d/primeProductNorm p R*‖secondRayCoefficient ray‖ := by
    have hT := initial_squarefree_target_geometry p hp hg (outsidePrime_odd S hbad D)
      Finset.univ R K Z M j
    have hTe : ∀ z ∈ sourceIdealTarget ((s R j).image (sourceObservation p)),
        Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧ z.2 ≠ 0 ∧
        ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
      intro z hz
      exact ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1,(hT z hz).2.2.2.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (normLogScale_pos _).le)⟩
    have hTc := initial_source_target_coprime p (∏P∈S,P)
      (CanonicalRowCompletion.outside_pool_coprime_excluded S D hbad hSp) (s R j)
    have he := henergy D Z R ray j _ hZ hpool hR hj hlow hTe hTc
    have he' :
        densityChildEnergy p hp hcop hg Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (1*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (sourceIdealTarget ((s R j).image (sourceObservation p)))
          (windows 5) (windows 6) (initialLogColumn Z (primeProductNorm p R) j)
          (initialLogColumn Z (primeProductNorm p R) j) (2*J) ≤
          (Ce*Z^η)*(initialLogColumn Z (primeProductNorm p R) j*initialLogLabel j)^2 := by
      simpa only [outsideCanonicalDensity,one_mul] using he
    exact initial_bin_cost_uniform p hp hcop hg Finset.univ R Ψ 1 ray K Z H M Kmax η Cs
      (Ce*Z^η) hZp hHp hKmax hη.le hCs (by positivity) j hj windows (B ray R j) (2*J) 0
      (hB ray R j).1 (hB ray R j).2.1 he'
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖ else 0) ≤
      Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left
      (initial_harmonic_aggregation p (outsidePrime_injective S hbad D) Finset.univ
        (Z*Real.exp M) Kmax d hd
        (fun ray R j => if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j)
          else 0) (by
          intro ray R hR j hj
          split_ifs with hlow
          · exact hterm ray R hR j hj hlow
          · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
            positivity)) hCt)
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hlow
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialSquarefreeBinCost,s,G,B] ; ring
    · simp
  have hlogBound := hlog Z (Z*Real.exp M) Kmax hZ (by positivity) (zero_lt_one.trans_le hKmax)
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
  calc
    _ ≤ Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := hsum
    _ = (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*
        ((Kmax*Real.exp 2)^η*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by dsimp [d]; ring
    _ ≤ (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*(Cl*Z^(34*η)) :=
      mul_le_mul_of_nonneg_left hlogBound (by positivity)
    _ = C0*H*Z^(35*η) := by
      rw [show 35*η=η+34*η by ring,Real.rpow_add hZp]
      dsimp [C0]
      ring
    _ ≤ (C0+1)*H*Z^(35*η) := by
      gcongr
      linarith

end InitialMeanSquare

end

end OAI
