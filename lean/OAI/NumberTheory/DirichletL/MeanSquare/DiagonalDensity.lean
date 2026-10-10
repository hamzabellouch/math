import OAI.NumberTheory.DirichletL.GaussSum.CompletedDyadicRows

namespace OAI

noncomputable section

namespace InitialMeanSquare

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

section

open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem initial_diagonal_fixed_profile (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y : ℝ),0<Z → 0<Y →
      ∀K : Finset ι→Finset ι→Finset O,
      (∀G∈F.powerset,∀E∈G.powerset,(0:O)∈K G E) →
      ‖truncatedSecondZero p hg F Ψ m c d
        (fun S => star (normalizedColumn p (fun T => g (columnLog p Z T)) S)) W Y K‖≤C*Y := by
  obtain ⟨C₀,hC₀,h₀⟩ := full_uniform_normalized_second_mass (conjugateProfile g) M
    (conjugateProfile_support_bound g M hgM)
  refine ⟨‖paperRadialFourier W 0‖*C₀+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ m c d Z Y hZ hY K hK
  simp_rw [star_normalizedColumn]
  apply (truncatedSecondZero_norm_le p hg hinj F Ψ m c d _ W Y K hK).trans
  rw [abs_of_pos hY]
  have hh := h₀ p hp hg hinj F Ψ hΨ m c d Z hZ
  calc
    _ ≤ Y*‖paperRadialFourier W 0‖*C₀ := mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ (‖paperRadialFourier W 0‖*C₀+1)*Y := by nlinarith

theorem initial_normalized_diagonal
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1)
      (Z Y : ℝ),0<Z → 0<Y →
      ∀K : Finset ι→Finset ι→Finset O,
      (∀G∈F.powerset,∀E∈G.powerset,(0:O)∈K G E) →
      ‖truncatedSecondZero p hg F Ψ 1 1 1
        (fun S => star (normalizedColumn p
          (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) S)) rowMajorant Y K‖≤C*Y := by
  obtain ⟨C,hC,h⟩ := initial_diagonal_fixed_profile (initialLogProfile W a b ha hs hW)
    rowMajorant (|Real.log a|+|Real.log b|+1) (initialLogProfile_support W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ Z Y hZ hY K hK
  exact h p hp hg hinj F Ψ hΨ 1 1 1 Z Y hZ hY K hK

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def initialFrequencyCutoff (Z Y M T : ℝ) : Finset O :=
  secondFrequencyCutoff (Y/(1+Z*Real.exp M)^3) T

theorem initialFrequencyCutoff_zero (Z Y M T : ℝ) :
    (0:O)∈initialFrequencyCutoff Z Y M T := secondFrequencyCutoff_zero _ _

theorem initialFrequencyCutoff_valid
    {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (m c d : O) (g : 𝓢(ℝ,ℂ)) (M Z Y T : ℝ)
    (hZ : 0<Z) (hY : 0<Y) (hgM : ∀t,g t≠0 → |t|≤M)
    (G E S R : Finset ι) (hEG : E⊆G) (hSR : Disjoint S R)
    (hw : residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U)) S R≠0)
    (k : O) (hk : k∉initialFrequencyCutoff Z Y M T) :
    T≤(Y/(‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2))*‖eisEmbedding k‖^2 := by
  let lengthScale : ℝ := 1+Z*Real.exp M
  have hL : 0<lengthScale := by dsimp [lengthScale]; positivity
  obtain ⟨hG,hE,hS,hR⟩ := residualPairWeight_support_bounds p hp hg Ψ m c d g M Z hZ hgM G E S R hEG hw
  have hZL : Z*Real.exp M≤lengthScale := by dsimp [lengthScale]; linarith
  have hn : ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2=primeProductNorm p S*primeProductNorm p R :=
    active_norm_sq_disjoint p S R hSR
  have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2≤lengthScale^3 := by
    rw [primeSubsetGenerator_norm_eq_productNorm,hn]
    have hSRn := mul_le_mul (hS.trans hZL) (hR.trans hZL)
      (FirstPassCubeLabels.primeProductNorm_pos p hp R).le hL.le
    have hESR := mul_le_mul (hE.trans hZL) hSRn
      (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
        (FirstPassCubeLabels.primeProductNorm_pos p hp R).le) hL.le
    nlinarith
  have hden0 : 0<‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2 := by
    rw [primeSubsetGenerator_norm_eq_productNorm,hn]
    exact mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp E)
      (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) (FirstPassCubeLabels.primeProductNorm_pos p hp R))
  have hout := (outside_secondFrequencyCutoff (Y/lengthScale^3) T (by positivity) k hk).le
  exact hout.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hY.le hden0 hden) (sq_nonneg _))

theorem initial_tail_polynomial (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) (A : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y T : ℝ),0<Z → 0<Y → 0≤T →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (normalizedColumn p (fun V => g (columnLog p Z V))) W Y
        (fun _ _ => initialFrequencyCutoff Z Y M T)‖≤
        C*(1+Z*Real.exp M)^4*Y*(1+(1+Z*Real.exp M)^3/Y)^2/(1+T)^A := by
  obtain ⟨s,C,hC,h⟩ := full_uniform_secondSourceTail_bound A
  let P : ℝ := C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C₀ : ℝ := 128^4*(SchwartzMap.seminorm ℝ 0 0 g)^2*P
  have hP : 0≤P := by dsimp [P]; positivity
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Z Y T hZ hY hT
  have hb := h p hp hg hinj hc F Ψ m c d
    (normalizedColumn p (fun V => g (columnLog p Z V))) W Y T hY hT
    (fun _ _ => initialFrequencyCutoff Z Y M T)
    (fun G hG E S hS R hR hSR hw k hk => initialFrequencyCutoff_valid p hp hg Ψ m c d g M Z Y T
      hZ hY hgM G E.val S R (Finset.mem_powerset.mp E.property) hSR hw k hk)
  have hpoly := secondSourceTailCost_polynomial p hp hg hinj F Ψ hΨ m c d g M Z Y T
    (1+Z*Real.exp M) P A hZ hY hT hP (by linarith [mul_pos hZ (Real.exp_pos M)]) (by linarith) hgM
  apply (hb.trans hpoly).trans
  calc
    _ = C₀*(1+Z*Real.exp M)^4*Y*(1+(1+Z*Real.exp M)^3/Y)^2/(1+T)^A := by dsimp [C₀]; ring
    _ ≤ _ := by gcongr; linarith

def initialTailHeight (Z Y M : ℝ) : ℝ :=
  (1+Z*Real.exp M)^2*(1+(1+Z*Real.exp M)^3/Y)

theorem initialTailHeight_pos (Z Y M : ℝ) (hZ : 0<Z) (hY : 0<Y) :
    0 < initialTailHeight Z Y M := by unfold initialTailHeight; positivity

theorem initial_tail_fixed_profile (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y : ℝ),0<Z → 0<Y →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (fun S => star (normalizedColumn p (fun V => g (columnLog p Z V)) S)) W Y
        (fun _ _ => initialFrequencyCutoff Z Y M (initialTailHeight Z Y M))‖≤C*Y := by
  obtain ⟨C,hC,h⟩ := initial_tail_polynomial (conjugateProfile g) W M
    (conjugateProfile_support_bound g M hgM) 2
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Z Y hZ hY
  simp_rw [star_normalizedColumn]
  apply (h p hp hg hinj hc F Ψ hΨ m c d Z Y (initialTailHeight Z Y M) hZ hY
    (initialTailHeight_pos Z Y M hZ hY).le).trans
  have hth := initialTailHeight_pos Z Y M hZ hY
  apply (div_le_iff₀ (by positivity : 0<(1+initialTailHeight Z Y M)^2)).mpr
  have hh : (1+Z*Real.exp M)^4*(1+(1+Z*Real.exp M)^3/Y)^2≤(1+initialTailHeight Z Y M)^2 := by
    have hp := initialTailHeight_pos Z Y M hZ hY
    calc
      _ = (initialTailHeight Z Y M)^2 := by unfold initialTailHeight; ring
      _ ≤ _ := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hh (show 0≤C*Y by positivity)
  nlinarith

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)
open ConcreteTraceCRT (eisEmbedding)

def initialErrorWindow (a b : ℝ) : ℝ := |Real.log a|+|Real.log b|+1

def initialErrorCutoff (a b Z Y : ℝ) : Finset O :=
  initialFrequencyCutoff Z Y (initialErrorWindow a b)
    (initialTailHeight Z Y (initialErrorWindow a b))

theorem initialErrorCutoff_zero (a b Z Y : ℝ) : (0:O)∈initialErrorCutoff a b Z Y :=
  initialFrequencyCutoff_zero _ _ _ _

def initialErrorFrequencyBound (a b Z Y : ℝ) : ℝ :=
  3*(initialTailHeight Z Y (initialErrorWindow a b)*
    (1+Z*Real.exp (initialErrorWindow a b))^3/Y+2)^2

theorem initialErrorCutoff_norm_bound (a b Z Y : ℝ) (hZ : 0<Z) (hY : 0<Y)
    (k : O) (hk : k∈initialErrorCutoff a b Z Y) :
    ‖eisEmbedding k‖^2≤ initialErrorFrequencyBound a b Z Y := by
  let M := initialErrorWindow a b
  let v : ℝ := initialTailHeight Z Y M/(Y/(1+Z*Real.exp M)^3)
  have hv : 0≤v := by
    dsimp [v]
    exact div_nonneg (initialTailHeight_pos Z Y M hZ hY).le (by positivity)
  have hb := secondFrequencyCutoff_norm_sq_le (Y/(1+Z*Real.exp M)^3)
    (initialTailHeight Z Y M) k hk
  have hc : (⌈v⌉₊:ℝ)+1≤v+2 := by
    have hh := (Nat.ceil_lt_add_one hv).le
    linarith
  apply hb.trans
  change 3*((⌈v⌉₊:ℝ)+1)^2≤_
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 2) (by norm_num : (0:ℝ)≤3)
  convert hsq using 1
  dsimp [initialErrorFrequencyBound,v,M]
  congr 2
  field_simp

theorem initial_normalized_errors
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1)
      (Z Y : ℝ),0<Z → 0<Y →
      let G := normalizedColumn p
        (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))
      let K := fun (_ _ : Finset ι) => initialErrorCutoff a b Z Y
      ‖truncatedSecondZero p hg F Ψ 1 1 1 (fun T => star (G T)) rowMajorant Y K‖+
        ‖secondSourceTail p hp hg hinj F Ψ 1 1 1 (fun T => star (G T)) rowMajorant Y K‖≤C*Y := by
  obtain ⟨Cd,hCd,hd⟩ := initial_normalized_diagonal W a b ha hs hW
  obtain ⟨Ct,hCt,ht⟩ := initial_tail_fixed_profile (initialLogProfile W a b ha hs hW)
    rowMajorant (initialErrorWindow a b) (initialLogProfile_support W a b ha hs hW)
  refine ⟨Cd+Ct,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ Z Y hZ hY
  dsimp only
  have h₁ := hd p hp hg hinj F Ψ hΨ Z Y hZ hY
    (fun (_ _ : Finset ι) => initialErrorCutoff a b Z Y)
    (fun G hG E hE => initialErrorCutoff_zero a b Z Y)
  have h₂ := ht p hp hg hinj hc F Ψ hΨ 1 1 1 Z Y hZ hY
  change ‖secondSourceTail p hp hg hinj F Ψ 1 1 1
    (fun T => star (normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V)) T))
    rowMajorant Y (fun (_ _ : Finset ι) => initialErrorCutoff a b Z Y)‖≤Ct*Y at h₂
  linarith

end

open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_source_with_errors
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{q : ℕ} (χ : DirichletCharacter ℂ q)
      (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
      (hSp : ∀P∈S,Prime P) (Z Y : ℝ),0<Z → 0<Y → b*Z≤D →
    ∀T : Finset O,(∀z∈T,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Y) → (∀z∈T,z≠0) →
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    let hg := poolPrimary_good F hF
    letI : ∀i : primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
      intro i j hij
      apply Subtype.ext
      simpa only [p,poolPrimary_span F hF] using hij
    let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
    let Ψ := conjugateMonoid (normCharacter χ)
    (∑z∈T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)/Z≤
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant Y (fun _ _ => (initialErrorCutoff a b Z Y).erase 0)‖+
      C*Y-‖G ∅‖^2 := by
  obtain ⟨C,hC,h⟩ := initial_normalized_errors W a b ha hs hW
  refine ⟨C,hC,?_⟩
  intro q χ S D hbad hSp Z Y hZ hY hD T hT hT0
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let p := poolPrimary F
  let hp := poolPrimary_ne_zero F hF
  let hg := poolPrimary_good F hF
  let : ∀i : primePool F,(Ideal.span {p i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
    intro i j hij
    apply Subtype.ext
    simpa only [p,poolPrimary_span F hF] using hij
  let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
  let Ψ := conjugateMonoid (normCharacter χ)
  let K : Finset (primePool F)→Finset (primePool F)→Finset O := fun _ _ => initialErrorCutoff a b Z Y
  have he := h p hp hg hinj (poolPrimary_odd F hF) Finset.univ Ψ
    (conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)) Z Y hZ hY
  have hm := outside_mean_square_source χ S D hbad hSp W a b Z Y ha hZ hY hs hW hD T hT hT0 K
  have hz := Complex.re_le_norm (truncatedSecondZero p hg Finset.univ Ψ 1 1 1
    (fun V => star (G V)) rowMajorant Y K)
  change ‖truncatedSecondZero p hg Finset.univ Ψ 1 1 1 (fun V => star (G V)) rowMajorant Y K‖+
    ‖secondSourceTail p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V)) rowMajorant Y K‖≤C*Y at he
  apply hm.trans
  linarith

end

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem initial_nonzero_source_norm_le_squarefree_bins
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1) (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g W : 𝓢(ℝ,ℂ)) (Z H M Kmax : ℝ) (hZ : 0 < Z)
    (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      elementNorm (sourceObservation p x).1 ≤ Kmax) :
    let G := fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S
    ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1 G W H (fun C E => (K C E).erase 0)‖ ≤
      ∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)) G G W H‖ := by
  dsimp only
  apply (initial_nonzero_source_norm_le_bins p hp hcop hg hinj hc hpr
    F Ψ m g W Z H M Kmax hZ hgM K hK).trans_eq
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro R hR
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg norm
  apply initial_source_eq_squarefree p hp hcop hg Ψ m ray F _ _ _ _ W H
  intro x hx
  exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp hx).1).2.1

end

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

def initialSquarefreeBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃))

theorem initial_nonzero_source_squarefree_transfer
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O)
        (K : Finset ι → Finset ι → Finset O) (Z H Kmax : ℝ),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z A,
          elementNorm (sourceObservation p x).1 ≤ Kmax) →
        ∃ B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ,
          (∀ ray R j q, 0 ≤ B ray R j q) ∧
          (∀ ray R j q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B ray R j q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            W H (fun C E => (K C E).erase 0)‖ ≤
            C*(∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp A),
              ∑ j ∈ secondLogBinBox (Z*Real.exp A) Kmax,
                initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H A ε j windows (B ray R j)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m K Z H Kmax hZ hH hΨ hK
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j
        (initialSquarefreeSector p (secondLogSector p ∅ F K R Z A j)) hZ hH hΨ
        (Finset.filter_subset _ _))
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j
        (initialSquarefreeSector p (secondLogSector p ∅ F K R Z A j)) hZ hH hΨ
        (Finset.filter_subset _ _))
  refine ⟨B,fun ray R j => (hB ray R j).1,fun ray R j => (hB ray R j).2.1,?_⟩
  apply (initial_nonzero_source_norm_le_squarefree_bins p hp hcop hg hinj hc hpr F Ψ m
    g W Z H A Kmax hZ hgA K hK).trans
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro R hR
  apply Finset.sum_le_sum
  intro j hj
  convert (hB ray R j).2.2 using 1 ; dsimp only [initialSquarefreeBinCost, B] ; ring

end

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem initialSquarefreeBinCost_of_canonical_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hchild : ∀ q,
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X q ≤
        (Cchild*(X*initialLogLabel j)^2)*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ*(∫ t : ℝ,firstLogDensity 0 t)^3)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X
  let E := Cchild*(X*initialLogLabel j)^2
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hpR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hpR)
  have hlabel : 0 < initialLogLabel j := by
    unfold initialLogLabel secondLogE secondLogV
    exact mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) (Real.exp_pos _)
  have hE : 0 ≤ E := mul_nonneg hCc (sq_nonneg _)
  have hS : 0 < S := by
    dsimp [S]
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  have hG : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    intro q
    exact (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X q).trans (hchild q)
  have hb := polynomial_density_cost B G J S Cₛ E hS hCₛ hE hB hG hdec henergy
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3) := mul_le_mul_of_nonneg_left hb hpref
    _ = _ := by
      dsimp only [E,X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hpR.ne',
        mul_pow (Z/primeProductNorm p R) (Real.exp 2) 2]
      have he : (Real.exp 2)^2=Real.exp 4 := by
        rw [pow_two,←Real.exp_add]
        norm_num
      rw [he]
      have hz := hZ.ne'
      have hr := hpR.ne'
      field_simp

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem positive_nested_density_transfer (f G : Frequency → ℝ) (J : ℕ)
    (hG : Continuous G) (M : ℝ) (hGM : ∀ q, ‖G q‖ ≤ M)
    (C : ℝ) (hf : ∀ q, 0 ≤ f q)
    (hbound : ∀ q, f q ≤ C*tripleLogDensity J q*G q) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,f (x,y,z)) ≤
      C*(∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,tripleLogDensity J (x,y,z)*G (x,y,z)) := by
  let u : Frequency → ℝ := fun q => C*(tripleLogDensity J q*G q)
  have hu : Integrable u := (tripleLogDensity_bounded_integrable J G hG M hGM).const_mul C
  have hux (x : ℝ) : Integrable (fun yz : ℝ × ℝ => u (x,yz)) :=
    (tripleLogDensity_slice_integrable J G hG M hGM x).const_mul C
  have huxy (x y : ℝ) : Integrable (fun z : ℝ => u (x,y,z)) := by
    have hd : Integrable (fun z : ℝ =>
        C*firstLogDensity J x*firstLogDensity J y*firstLogDensity J z) :=
      (firstLogDensity_integrable J).const_mul _
    have hgxy : Continuous (fun z : ℝ => G (x,y,z)) :=
      hG.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hi := hd.mul_bdd hgxy.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z : ℝ => hGM (x,y,z)))
    convert hi using 1
    funext z
    dsimp [u,tripleLogDensity]
    ring
  have hz (x y : ℝ) : (∫ z : ℝ,f (x,y,z)) ≤ ∫ z : ℝ,u (x,y,z) := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z : ℝ => hf (x,y,z))) (huxy x y)
    exact Filter.Eventually.of_forall (fun z : ℝ => by simpa only [u,mul_assoc] using hbound (x,y,z))
  have hy (x : ℝ) : (∫ y : ℝ,∫ z : ℝ,f (x,y,z)) ≤ ∫ y : ℝ,∫ z : ℝ,u (x,y,z) := by
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))
      (hux x).integral_prod_left (Filter.Eventually.of_forall (hz x))
  have hui : Integrable (fun x : ℝ => ∫ y : ℝ, ∫ z : ℝ,u (x,y,z)) := by
    apply hu.integral_prod_left.congr
    filter_upwards [] with x
    exact integral_prod _ (hux x)
  have hx := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ => integral_nonneg
      (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))) hui
    (Filter.Eventually.of_forall hy)
  simpa only [u,integral_const_mul] using hx

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem initial_source_density_transfer (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m : O) (T : Finset (O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (B : Frequency → ℝ) (J : ℕ) (S C : ℝ) (hS : 0 < S) (hC : 0 ≤ C)
    (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,S*B q ≤ C*tripleLogDensity J q) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,B (x,y,z)*
      sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (x,y,z)) ≤
    (C/S)*densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m (sourceIdealTarget T) V₁ V₂ X₁ X₂ J := by
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m (sourceIdealTarget T) V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m (sourceIdealTarget T) V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m (sourceIdealTarget T) V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q,0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m (sourceIdealTarget T) V₁ X₁ true false)*
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m (sourceIdealTarget T) V₂ X₂ false true)
  have hGM : ∀ q,‖G q‖ ≤ M := by
    intro q
    rw [Real.norm_of_nonneg (hG0 q)]
    exact mul_le_mul
      (Real.sqrt_le_sqrt (childEnergy_le p hp hcop hg F Ψ₁ m (sourceIdealTarget T) V₁ X₁ true false q.1 q.2.2))
      (Real.sqrt_le_sqrt (childEnergy_le p hp hcop hg F Ψ₂ m (sourceIdealTarget T) V₂ X₂ false true q.2.1 q.2.2))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  change _ ≤ (C/S)*(∫ x : ℝ,∫ y : ℝ,∫ z : ℝ,tripleLogDensity J (x,y,z)*G (x,y,z))
  apply positive_nested_density_transfer
    (fun q => B q*sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q)
    G J hG M hGM (C/S)
  · intro q
    exact mul_nonneg (hB q) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · intro q
    have hb : B q ≤ (C/S)*tripleLogDensity J q := by
      have hd : B q ≤ (C*tripleLogDensity J q)/S :=
        (le_div_iff₀ hS).mpr (by simpa only [mul_comm] using hdec q)
      convert hd using 1 ; ring
    exact mul_le_mul hb (sourceGeometricMean_le_ideal p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (div_nonneg hC hS.le) (tripleLogDensity_nonneg _ _))

end InitialMeanSquare

end

end OAI
