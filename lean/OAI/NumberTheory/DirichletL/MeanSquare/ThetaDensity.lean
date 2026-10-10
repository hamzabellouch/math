import OAI.NumberTheory.DirichletL.RowCompletion.InitialDensity

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

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem HasInitialCanonicalDensityAtRadius.nonzero_source_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hg := outsidePrime_good S hbad D
      let hinj := outsidePrime_injective S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
        W H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ C*H*Z^ε := by
  let η := min 1 (ε/100)
  let ν := (σ-(1 : ℝ)/20)/3
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : 35*η ≤ ε := by
    have hh : η ≤ ε/100 := min_le_right _ _
    linarith
  have hν : 0 < ν := by dsimp [ν]; linarith
  have hσ0 : 0 ≤ σ := by linarith
  have hmargin : ν+ν ≤ σ-(1 : ℝ)/20 := by dsimp [ν]; linarith
  obtain ⟨Cl,Cpool,E,hCl,hCpool,hPE,hlow⟩ := HasInitialCanonicalDensityAtRadius.retained_source χ S hbad hSp hcan U hUc hUs g W
    a b σ ν ν η hU hgs hσ0 hν hη hmargin
  obtain ⟨Ch,hCh,hhigh⟩ := initial_high_radial_source U hUc hUs g W a b ν 1 η hU hgs hν hη hη1
  refine ⟨Cl+Ch,Cpool,E,by positivity,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let hinj := outsidePrime_injective S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  let f := fun (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖
  let Lsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if initialRadial Z H (primeProductNorm p R) j ≤ Z^ν then f ray R j else 0
  let Hsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if Z^ν < initialRadial Z H (primeProductNorm p R) j then f ray R j else 0
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hL : Lsum ≤ Cl*H*Z^(35*η) := hlow D Z hZ hpool
  have hHi : Hsum ≤ Ch*Z^(-(1 : ℝ)) :=
    hhigh p hp hcop hg hinj (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D)
      Finset.univ Ψ 1 Z H hZ hH hΨ (fun _ R j => s R j) (fun _ _ _ => Finset.filter_subset _ _)
  have hrow : ∀ R ∈ (Finset.univ : Finset (OutsidePrimeIndex S D)).powerset,
      ∀ x ∈ secondSupportedSector p Finset.univ K R Z M,elementNorm (sourceObservation p x).1 ≤ Kmax := by
    intro R hR x hx
    exact initialErrorRowBound_valid p hp Finset.univ R a b Z H hZp hHp x hx
  have htotal := initial_nonzero_source_norm_le_squarefree_bins p hp hcop hg hinj
    (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D) Finset.univ Ψ 1 g W
    Z H M Kmax hZp hgs K hrow
  have hpart : (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j)=Lsum+Hsum := by
    dsimp only [Lsum,Hsum]
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : initialRadial Z H (primeProductNorm p R) j ≤ Z^ν
    · rw [ite_eq_left hh,ite_eq_right (not_lt.mpr hh),add_zero]
    · rw [ite_eq_right hh,ite_eq_left (lt_of_not_ge hh),zero_add]
  have hpower : Z^(35*η) ≤ Z^ε := Real.rpow_le_rpow_of_exponent_le hZ hηε
  have hsmall : Z^(-(1 : ℝ)) ≤ H*Z^ε := by
    have h1 : Z^(-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ (by norm_num)
    exact h1.trans (one_le_mul_of_one_le_of_one_le hH (Real.one_le_rpow hZ hε.le))
  calc
    _ ≤ ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j := htotal
    _ = Lsum+Hsum := hpart
    _ ≤ Cl*H*Z^(35*η)+Ch*Z^(-(1 : ℝ)) := add_le_add hL hHi
    _ ≤ Cl*H*Z^ε+Ch*(H*Z^ε) := add_le_add
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hCl.le hHp.le))
      (mul_le_mul_of_nonneg_left hsmall hCh.le)
    _ = (Cl+Ch)*H*Z^ε := by ring

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_of_canonical_density_at_radius {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → b*Z ≤ D →
      ∀ T : Finset ActualEisensteinCubic.O,
      (∀ z ∈ T,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Z^(1+σ)) →
      (∀ z ∈ T,z ≠ 0) →
      (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
        (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2) ≤ C*Z*(Z^(1+σ))*Z^ε := by
  let g0 := initialLogProfile W a b ha hs hW
  let g := conjugateProfile g0
  let M := initialErrorWindow a b
  have hM : 0 ≤ M := by dsimp [M,initialErrorWindow]; positivity
  have hg0 : ∀ t,g0 t ≠ 0 → |t| ≤ M := initialLogProfile_support W a b ha hs hW
  have hg : ∀ t,g t ≠ 0 → |t| ≤ M := conjugateProfile_support_bound g0 M hg0
  obtain ⟨U,hUc,hUs,hUeq,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  have hU : ∀ t,g t ≠ 0 → U t=1 := fun t ht => hUeq t (hg t ht)
  obtain ⟨Cs,Cpool,E,hCs,hCpool,hE,hsource⟩ := HasInitialCanonicalDensityAtRadius.nonzero_source_bound χ S hbad hSp hcan
    U hUc hUs g rowMajorant a b σ ε hU hg hσ hε
  obtain ⟨Ce,hCe,herrors⟩ := outside_mean_square_source_with_errors W a b ha hs hW
  refine ⟨Cs+Ce,by positivity,?_⟩
  intro D Z hZ hD T hT hT0
  let Db : ℕ := max D ⌈Cpool*Z^E⌉₊
  have hDDb : D ≤ Db := le_max_left _ _
  have hpool : Cpool*Z^E ≤ (Db : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right D ⌈Cpool*Z^E⌉₊)
  have hDb : b*Z ≤ (Db : ℝ) := hD.trans (by exact_mod_cast hDDb)
  let p := outsidePrime S Db
  let hp := outsidePrime_ne_zero S hbad Db
  let hg := outsidePrime_good S hbad Db
  let hinj := outsidePrime_injective S hbad Db
  let := outsidePrime_maximal S hbad Db
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let G := fun V => normalizedColumn p (fun T => g0 (columnLog p Z T)) V
  let MS := ∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S Db) (outsideIdealsUpTo_ne_bot S Db)
    (outside_good S Db hbad) χ (fun n => W (n/Z)) z‖^2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hεZ : 1 ≤ Z^ε := Real.one_le_rpow hZ hε.le
  have he := herrors χ S Db hbad hSp Z H hZp hHp hDb T hT hT0
  have hsrc := hsource Db Z hZ hpool
  have hstar : (fun V => star (G V)) =
      (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) := by
    funext V
    exact star_normalizedColumn p g0 Z V
  have hsrc' :
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ Cs*H*Z^ε := by
    rw [hstar]
    exact hsrc
  change MS/Z ≤
    ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
      rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖+Ce*H-‖G ∅‖^2 at he
  have herr : Ce*H ≤ Ce*H*Z^ε := le_mul_of_one_le_right (mul_nonneg hCe.le hHp.le) hεZ
  have hnorm : MS/Z ≤ (Cs+Ce)*H*Z^ε := by
    nlinarith [sq_nonneg ‖G ∅‖]
  have hfinal := (div_le_iff₀ hZp).mp hnorm
  have hMS : (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)=MS := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [outside_row_cutoff_stable S hbad hDDb χ W b Z hZp (fun t ht => (hs ht).2) hD z]
  rw [hMS]
  convert hfinal using 1 ; dsimp only [H] ; ring

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion

theorem outside_mean_square_of_theta_models {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1:ℝ)/20<σ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(D : ℕ) (Z : ℝ),1≤Z → b*Z≤D →
      ∀T : Finset ActualEisensteinCubic.O,
      (∀z∈T,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Z^(1+σ)) →
      (∀z∈T,z≠0) →
      (∑z∈T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
        (outside_good S D hbad) χ (fun n=>W (n/Z)) z‖^2)≤C*Z*(Z^(1+σ))*Z^ε :=
  outside_mean_square_of_canonical_density_at_radius χ S hbad hSp
    (hasInitialCanonicalDensityAtRadius_of_theta χ S hSp hbad ρ q levelBound hρ hq hlevel hmodels)
    W a b ha hs hW σ ε hσ hε

end InitialMeanSquare

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma cuspBarrierField_local_model (p : SpatialCoordinates) (hp : 0<p 2) :
    (cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun _ => 1)) ∨
    ∃x : FullCuspClasses,1<rowHeight (fullCuspRow x) p ∧
      cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun q => 1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)) := by
  by_cases hx : ∃x : FullCuspClasses,1<rowHeight (fullCuspRow x) p
  · obtain ⟨x,hx⟩ := hx
    refine Or.inr ⟨x,hx,?_⟩
    have hc := (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt
    filter_upwards [hc.eventually_const_lt hx,(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq hpos
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=_
    rw [fullCuspProfileField_eq _ q hpos,fullCuspProfileSum_eq_single _
      (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) _ x
        (by rwa [←fullCuspRow_height x q hpos]),←fullCuspRow_height x q hpos]
  · left
    obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
    have hsmall : ∀ᶠq in 𝓝 p,∀x∈T,rowHeight (fullCuspRow x) q<2 := by
      rw [eventually_all_finset]
      intro x hxT
      apply (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt.eventually_lt_const
      have hn : rowHeight (fullCuspRow x) p≤1 := not_lt.mp (fun h => hx ⟨x,h⟩)
      linarith
    filter_upwards [hT,hsmall] with q hq hqT
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=1
    have hz : ∀x : FullCuspClasses,cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)=0 := by
      intro x
      apply cuspBarrierProfile_zero 2 3 (by norm_num)
      by_cases hmem : x∈T
      · exact (hqT x hmem).le
      · exact (hq x hmem).le.trans (by norm_num)
    simp only [fullCuspProfileField,hz,tsum_zero,add_zero]

lemma cuspBarrierProfile_log_derivative_bound :
    ∃D : ℝ,0≤D ∧ ∀v : ℝ,1<v→
      |v*deriv (cuspBarrierProfile 2 3) v|≤D*(1+cuspBarrierProfile 2 3 v) := by
  have hd := (contDiff_infty_iff_deriv.mp (cuspBarrierProfile_smooth 2 3)).2.continuous
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 3)).image hd.abs).bddAbove
  let D := max 1 (3*max C 0)
  have hD : 0≤D := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨D,hD,fun v hv => ?_⟩
  by_cases hhigh : 3<v
  · have he : cuspBarrierProfile 2 3 =ᶠ[𝓝 v] (fun x => x-1) := by
      filter_upwards [Ioi_mem_nhds hhigh] with x hx
      rw [cuspBarrierProfile,cuspTransition_one 2 3 x (by norm_num) hx.le,one_mul]
    have hder : deriv (cuspBarrierProfile 2 3) v=1 := by rw [he.deriv_eq]; simp
    rw [hder,mul_one,abs_of_pos (by linarith),he.self_of_nhds]
    have h := mul_le_mul_of_nonneg_right (le_max_left 1 (3*max C 0)) (show 0≤v by linarith)
    dsimp only [D]
    nlinarith
  · have hCv : |deriv (cuspBarrierProfile 2 3) v|≤max C 0 :=
      (hC (Set.mem_image_of_mem _ (show v∈Set.Icc (1:ℝ) 3 from ⟨hv.le,not_lt.mp hhigh⟩))).trans (le_max_left _ _)
    have h1 : |v*deriv (cuspBarrierProfile 2 3) v|≤3*max C 0 := by
      rw [abs_mul,abs_of_pos (by linarith)]
      exact mul_le_mul (not_lt.mp hhigh) hCv (abs_nonneg _) (by positivity)
    have hphi := cuspBarrierProfile_nonneg 2 3 (by norm_num) (by norm_num) v
    exact (h1.trans (le_max_right _ _)).trans (by nlinarith)

lemma cuspBarrierField_scaled_deriv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j) (p j)‖≤
        D*cuspBarrierField 2 3 p := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierProfile_log_derivative_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [Function.update_eq_self] using ((continuous_axis_update p j).continuousAt (x := p j)).tendsto
  rcases cuspBarrierField_local_model p hp with hz | ⟨x,hx,he⟩
  · have hzCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p] (fun _ => (1:ℂ)) :=
      hz.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have hzC := hzCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)] (fun _ => (1:ℂ)) at hzC
    rw [hzC.deriv_eq,deriv_const,mul_zero,norm_zero,hz.self_of_nhds,mul_one]
    exact hD
  · have heCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p]
        (fun q => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℝ):ℂ)) :=
      he.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have heC := heCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)]
      (fun t => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) (Function.update p j t)):ℝ):ℂ)) at heC
    rw [heC.deriv_eq]
    simp only [Complex.ofReal_add,Complex.ofReal_one]
    rw [deriv_const_add]
    have hpF := (rowProfile_axis_derivatives (fun v => (cuspBarrierProfile 2 3 v:ℂ))
      (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspBarrierProfile_smooth 2 3).contDiffAt)
      (fullCuspRow x) (fullCuspRow_ne_zero x) p hp j).1
    change ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℂ)) p j) (p j)‖≤_
    rw [hpF.deriv,cast_profile_deriv _ ((cuspBarrierProfile_smooth 2 3).differentiable (by simp))]
    have hid : (p 2:ℂ)*(((deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ)*
        (rowHeight (fullCuspRow x) p:ℂ)*(rowLogD (fullCuspRow x) p j:ℂ))=
        ((p 2*rowLogD (fullCuspRow x) p j:ℝ):ℂ)*
        ((rowHeight (fullCuspRow x) p*deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ) := by
      push_cast
      ring
    rw [hid,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    apply (mul_le_of_le_one_left (abs_nonneg _) (rowLogD_hyperbolic_bound _ (fullCuspRow_ne_zero x) p hp j)).trans
    rw [he.self_of_nhds]
    exact hbound _ hx

lemma kernelBarrier_scaled_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierField_scaled_deriv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  let f : EuclideanSpatial→ℂ := fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞ f q := fun q hq =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) q hq)
  have he : ∀q : SpatialCoordinates,0<q 2→ f (WithLp.toLp 2 q)=(cuspBarrierField 2 3 q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq 2 3 (WithLp.toLp 2 q) hq)
  have ha := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤_
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,ha.deriv_eq]
  change _≤D*cuspBarrier 2 3 (euclideanToHyperbolic p)
  rw [cuspBarrier_euclidean_eq 2 3 p hp]
  exact hbound p.ofLp hp j

lemma kernelBarrier_scaled_real_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      |p 2*fderiv ℝ (fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)) p
        (euclideanCoordinateVector j)|≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := kernelBarrier_scaled_fderiv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have hphi := (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have he := (Complex.ofRealCLM.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  have hh := hbound p hp j
  change ‖(p 2:ℂ)*fderiv ℝ (Complex.ofRealCLM ∘ (fun q => cuspBarrier 2 3 (euclideanToHyperbolic q))) p
      (euclideanCoordinateVector j)‖≤_ at hh
  rw [he] at hh
  simpa only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,←Complex.ofReal_mul,
    Complex.norm_real,Real.norm_eq_abs] using! hh

lemma kernelExhaustionProfile_euler_bounded :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀v : ℝ,|v*deriv (kernelExhaustionProfile n) v|≤C := by
  obtain ⟨C,hC,hbound⟩ := cuspTransition_euler_bounded 1 2 (by norm_num)
  refine ⟨C,hC,fun n v => ?_⟩
  let c : ℝ := (n:ℝ)+1
  have hc : c≠0 := by dsimp [c]; positivity
  have hd := (hasDerivAt_const v (1:ℝ)).sub
    (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/c)).hasDerivAt.comp v
      ((hasDerivAt_id v).div_const c))
  change HasDerivAt (kernelExhaustionProfile n) (0-deriv (cuspTransition 1 2) (v/c)*(1/c)) v at hd
  rw [hd.deriv]
  have he : v*(0-deriv (cuspTransition 1 2) (v/c)*(1/c))= -(v/c*deriv (cuspTransition 1 2) (v/c)) := by ring
  rw [he,abs_neg]
  exact hbound (v/c)

lemma kernelExhaustionCutoff_scaled_fderiv_bound :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤C := by
  obtain ⟨D,hD,hgrad⟩ := kernelBarrier_scaled_real_fderiv_bound
  obtain ⟨B,hB,hprofile⟩ := kernelExhaustionProfile_euler_bounded
  refine ⟨D*B,mul_nonneg hD hB,fun n p hp j => ?_⟩
  let phi : EuclideanSpatial→ℝ := fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)
  have hphi : DifferentiableAt ℝ phi p :=
    (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have hP := ((kernelExhaustionProfile_smooth n).differentiable (by simp) (phi p)).hasDerivAt
  have hd := (hP.ofReal_comp.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  change ‖(p 2:ℂ)*fderiv ℝ ((fun v => (kernelExhaustionProfile n v:ℂ)) ∘ phi) p
    (euclideanCoordinateVector j)‖≤D*B
  rw [hd]
  change ‖(p 2:ℂ)*((fderiv ℝ phi p (euclideanCoordinateVector j):ℝ) •
    ((deriv (kernelExhaustionProfile n) (phi p):ℝ):ℂ))‖≤D*B
  rw [Complex.real_smul,←Complex.ofReal_mul,←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    |p 2*(fderiv ℝ phi p (euclideanCoordinateVector j)*deriv (kernelExhaustionProfile n) (phi p))|
      = |p 2*fderiv ℝ phi p (euclideanCoordinateVector j)| *|deriv (kernelExhaustionProfile n) (phi p)| := by rw [←abs_mul]; congr 1; ring
    _ ≤ (D*phi p)*|deriv (kernelExhaustionProfile n) (phi p)| :=
      mul_le_mul_of_nonneg_right (hgrad p hp j) (abs_nonneg _)
    _ = D*|phi p*deriv (kernelExhaustionProfile n) (phi p)| := by
      rw [abs_mul,abs_of_nonneg (le_trans zero_le_one (kernelQuotientBarrier_one_le 2 3 (by norm_num) (by norm_num) _))]
      ring
    _ ≤ D*B := mul_le_mul_of_nonneg_left (hprofile n (phi p)) hD

lemma kernelExhaustionCutoff_fderiv_eventually_zero (p : EuclideanSpatial) (hp : 0<p 2) :
    ∀ᶠn : ℕ in atTop,
      fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p=0 := by
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [kernelExhaustionCutoff_eventually_one_near (kernelEuclideanProjection p)] with n hn
  have he := hn.comp_tendsto hc
  have heC : (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) =ᶠ[𝓝 p]
      (fun _ => (1:ℂ)) := he.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
  rw [heC.fderiv_eq]
  simp

lemma kernelExhaustionCutoff_energy_density_bound :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→
      (∑j : Fin 3,‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖^2)≤C := by
  obtain ⟨D,hD,hbound⟩ := kernelExhaustionCutoff_scaled_fderiv_bound
  refine ⟨3*D^2,by positivity,fun n p hp => ?_⟩
  calc
    _ ≤ ∑j : Fin 3,D^2 := Finset.sum_le_sum (fun j hj =>
      (sq_le_sq₀ (norm_nonneg _) hD).mpr (hbound n p hp j))
    _ = 3*D^2 := by simp

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace SixthPowerAverage
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O

def totientDensity (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  ∏ P ∈ primeSupport I, (1-(1:ℂ)/(Ideal.absNorm P:ℂ))

theorem idealSupport_card (F : Finset (Ideal ActualEisensteinCubic.O)) {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) :
    (idealSupport F I).card=(primeSupport I).card := by
  rw [primeSupport,←idealSupport_image_eq_factors F hI]
  exact (Finset.card_image_iff.mpr (fun _ _ _ _ h => Subtype.val_injective h)).symm

theorem idealSupport_density (F : Finset (Ideal ActualEisensteinCubic.O)) {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) :
    (∏ i ∈ idealSupport F I, (1-(1:ℂ)/(Ideal.absNorm i.val:ℂ)))=totientDensity I := by
  rw [totientDensity, primeSupport, ←idealSupport_image_eq_factors F hI,
    Finset.prod_image]
  exact fun _ _ _ _ h => Subtype.val_injective h

theorem idealSexticRow_sixth_mask
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (I : Ideal ActualEisensteinCubic.O) (b : ActualEisensteinCubic.O) :
    idealSexticRow F hF hg I (b^6)=
      rowCoprimeMask (fun i : primePool F => i.val) (idealSupport F I) b := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  exact finiteSquarefreeRow_sixth_power _ _ _ _

theorem idealSexticRow_sixth_radial_summable
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (I : Ideal ActualEisensteinCubic.O) (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    Summable (fun b : ActualEisensteinCubic.O => idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y)) := by
  have hs : Summable (fun b : ActualEisensteinCubic.O => V (‖eisEmbedding b‖^2/Y)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest V Y hY)).of_norm
  simp_rw [idealSexticRow_sixth_mask]
  convert hs.indicator {b : ActualEisensteinCubic.O | ¬∃i∈idealSupport F I,b∈i.val} using 1
  funext b
  by_cases hb : ∃i∈idealSupport F I,b∈i.val
  · rw [Set.indicator_of_notMem (show b∉{b : ActualEisensteinCubic.O | ¬∃i∈idealSupport F I,b∈i.val} from fun hn=>hn hb)]
    simp only [rowCoprimeMask,ite_eq_left hb,zero_mul]
  · rw [Set.indicator_of_mem hb]
    simp only [rowCoprimeMask,ite_eq_right hb,one_mul]

theorem idealSexticRow_sixth_average
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    (∑'b : ActualEisensteinCubic.O,idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y))=
      (Y:ℂ)*paperRadialFourier V 0*totientDensity I+
      maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  simp_rw [idealSexticRow_sixth_mask]
  rw [masked_principal_radial_poisson_zero_split _ Subtype.val_injective _ V Y hY,
    idealSupport_density F hI]

theorem idealRowSum_sixth_average {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    (∑'b : ActualEisensteinCubic.O, V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6))=
      (Y:ℂ)*paperRadialFourier V 0*
        (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*totientDensity I)+
      ∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y := by
  have he (b : ActualEisensteinCubic.O) : V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6)=
      ∑I∈F,(baseChangeWeight χ I*W (Ideal.absNorm I))*
        (idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y)) := by
    rw [idealRowSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun I _ =>
    (idealSexticRow_sixth_radial_summable F hF hg I V Y hY).mul_left _)]
  simp_rw [tsum_mul_left]
  rw [show (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
      ∑'b : ActualEisensteinCubic.O,idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y))=
      ∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        ((Y:ℂ)*paperRadialFourier V 0*totientDensity I+
          maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y) by
    apply Finset.sum_congr rfl
    intro I hI
    rw [idealSexticRow_sixth_average F hF hg hI V Y hY]]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem sixth_average_remainder_bound {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y‖≤
      ∑I∈F,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  have hr := maskedPrincipalRemainder_uniform (fun i : primePool F=>i.val)
    (idealSupport F I) V Y hY
  rw [idealSupport_card F hI] at hr
  rw [norm_mul,norm_mul]
  calc
    _≤(1*‖W (Ideal.absNorm I)‖)*((2:ℝ)^(primeSupport I).card*pvControl V) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (baseChangeWeight_norm_le_one χ I) (norm_nonneg _))
        hr (norm_nonneg _) (by positivity)
    _=_ := by ring

theorem sixth_power_fiber_card (s : Finset ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) :
    (s.filter (fun b=>b^6=z)).card≤6 := by
  calc
    _≤(Polynomial.nthRoots 6 z).toFinset.card := by
      apply Finset.card_le_card
      intro b hb
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_nthRoots (by norm_num : 0<6)).mpr (Finset.mem_filter.mp hb).2)
    _≤(Polynomial.nthRoots 6 z).card := Multiset.toFinset_card_le _
    _≤6 := Polynomial.card_nthRoots 6 z

theorem sixth_power_average_cauchy (s : Finset ActualEisensteinCubic.O) (V A : ActualEisensteinCubic.O→ℂ)
    (hV : ∀b∈s,‖V b‖≤1) :
    ‖∑b∈s,V b*A (b^6)‖^2≤
      6*s.card*∑z∈s.image (fun b=>b^6),‖A z‖^2 := by
  have hc := DescentWeightedCauchy.weighted_cauchy_sq s V (fun b=>A (b^6)) (fun _=>1)
  simp only [star_one,mul_one,norm_one,one_pow,mul_one] at hc
  have hp := DescentWeightedCauchy.weighted_energy_pushforward s (s.image (fun b=>b^6))
    (fun b=>b^6) V A (fun _=>6) (fun b hb=>Finset.mem_image.mpr ⟨b,hb,rfl⟩) (by
      intro z hz
      calc
        _≤∑b∈s with b^6=z,(1:ℝ) := Finset.sum_le_sum (fun b hb=>hV b (Finset.mem_filter.mp hb).1)
        _=(s.filter (fun b=>b^6=z)).card := by simp
        _≤6 := by exact_mod_cast sixth_power_fiber_card s z)
  have hv : (∑b∈s,‖V b‖)≤s.card := by
    simpa using Finset.sum_le_sum (fun b hb=>hV b hb)
  apply hc.trans
  calc
    _≤(∑z∈s.image (fun b=>b^6),6*‖A z‖^2)*(s.card:ℝ) :=
      mul_le_mul hp hv (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
        (Finset.sum_nonneg (fun _ _=>by positivity))
    _=_ := by rw [←Finset.mul_sum]; ring

end SixthPowerAverage

end

end OAI
