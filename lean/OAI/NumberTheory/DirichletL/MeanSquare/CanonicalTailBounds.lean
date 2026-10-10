import OAI.NumberTheory.DirichletL.MeanSquare.RetainedDensity

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_of_canonical_density {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S,Prime P)
    (hcan : HasInitialCanonicalDensity χ S hbad)
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
  obtain ⟨Cs,Cpool,E,hCs,hCpool,hE,hsource⟩ := HasInitialCanonicalDensity.nonzero_source_bound χ S hbad hcan
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

end InitialMeanSquare

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

lemma firstTail_inverse_scale_bound (K D U:ℝ) (hK:0<K) (hD:0<D) (hU:D≤U):
    ((min 1 (K/D))⁻¹)^2≤(1+U/K)^2 := by
  have hU0:0≤U/K:=div_nonneg (hD.le.trans hU) hK.le
  have hi:(min 1 (K/D))⁻¹≤1+U/K:=by
    by_cases h:1≤K/D
    · rw [min_eq_left h,inv_one];linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)),inv_div]
      exact (div_le_div_of_nonneg_right hU hK.le).trans (by linarith)
  exact pow_le_pow_left₀ (inv_nonneg.mpr (le_min zero_le_one (div_pos hK hD).le)) hi 2

lemma firstTail_scalar_bound (K D E U₁ U₂ lengthScale B G₁ G₂ P H:ℝ) (A:ℕ)
    (hK:0<K) (hD:0<D) (hE:0<E) (hU₁:0<U₁) (hU₂:0<U₂)
    (hL:0≤lengthScale) (hG₁:0≤G₁) (hG₂:0≤G₂) (hP:0≤P) (hH:0≤H)
    (hDb:D≤lengthScale*B^2) (hEb:E≤B^2) (hU₁b:U₁≤lengthScale) (hU₂b:U₂≤lengthScale):
    (128*U₁)*(128*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A))≤
    (128*lengthScale)^2*(G₁*G₂*K)*P*(1+lengthScale^3*B^4/K)^2/(1+H)^A := by
  have hden:D*E*U₁*U₂≤lengthScale^3*B^4:=by
    calc
      _ ≤ (lengthScale*B^2)*B^2*lengthScale*lengthScale:=mul_le_mul
        (mul_le_mul (mul_le_mul hDb hEb hE.le (mul_nonneg hL (sq_nonneg _))) hU₁b hU₁.le (by positivity))
        hU₂b hU₂.le (by positivity)
      _ = _:=by ring
  have hi:=firstTail_inverse_scale_bound K (D*E*U₁*U₂) (lengthScale^3*B^4) hK (by positivity) hden
  have hpref:(128*U₁)*(128*U₂)*(G₁*G₂*K)≤(128*lengthScale)^2*(G₁*G₂*K):=by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (128*lengthScale)*(128*lengthScale):=mul_le_mul (mul_le_mul_of_nonneg_left hU₁b (by norm_num))
        (mul_le_mul_of_nonneg_left hU₂b (by norm_num)) (by positivity) (by positivity)
      _ = _:=by ring
  calc
    _ = ((128*U₁)*(128*U₂)*(G₁*G₂*K))*P*((min 1 (K/(D*E*U₁*U₂)))⁻¹)^2/(1+H)^A:=by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow];ring
    _ ≤ _:=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpref hP) hi (sq_nonneg _) (by positivity)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeCoordinates_radical_bound (b:CubeCoordinates ι) (B:ℝ) (hB:0≤B)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B):
    primeProductNorm p b.support≤B^2 := by
  have hd:(∏i∈b.support,p i)∣primeProduct p b.support b.leftExponent*primeProduct p b.support b.rightExponent:=by
    rw [←primeProduct_add]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (b.support_pos i hi)
  have hb0:=mul_ne_zero (primeProduct_ne_zero p hp b.support b.leftExponent)
    (primeProduct_ne_zero p hp b.support b.rightExponent)
  have hn:=element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeSourceDivisor_norm_bound (b:CubeCoordinates ι) (C D:Finset ι) (B lengthScale:ℝ)
    (hB:0≤B) (hL:0≤lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):
    primeProductNorm p D≤lengthScale*B^2 := by
  calc
    _ ≤ primeProductNorm p (C∪b.support):=primeProductNorm_mono p hp
      (hD.trans (Finset.union_subset_union_right (Finset.filter_subset _ _)))
    _ = primeProductNorm p C*primeProductNorm p b.support:=primeProductNorm_union p _ _ hCB
    _ ≤ _:=mul_le_mul hC (cubeCoordinates_radical_bound p hp b B hB hb₁ hb₂)
      (primeProductNorm_pos p hp _).le hL

lemma cubeSourceDivisors_card
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (b:CubeCoordinates ι) (C:Finset ι) (B lengthScale:ℝ) (hB:0<B) (hL:0<lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale):
    ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)≤128*(lengthScale*B^2) := by
  let M:=C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
  have he:boundedPrimeSupports p M (lengthScale*B^2)=M.powerset:=by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB.le hL.le hCB hb₁ hb₂ hC (Finset.mem_powerset.mp hD)
  rw [←he]
  exact boundedPrimeSupports_card_positive p hp hinj M _ (mul_pos hL (sq_pos_of_pos hB))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceMobiusDivisor_norm_le_one (D:Finset ι):
    ‖(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)‖≤1 := by
  have hmu : ‖(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)‖≤1 := by
    unfold UniqueFactorizationMonoid.moebius
    split_ifs <;> simp
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (primeProductNorm_pos p hp D)]
  exact (div_le_div_of_nonneg_right hmu (primeProductNorm_pos p hp D).le).trans
    ((div_le_one (primeProductNorm_pos p hp D)).mpr (primeProductNorm_ge_one p hp D))

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem canonicalCubeDualTail_support
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:ActualEisensteinCubic.O→*ℂ) (m₁ m₂ f:ActualEisensteinCubic.O) (g₁ g₂ W:𝓢(ℝ,ℂ))
    (ell K M:ℝ) (hell:0<ell) (hgM:∀t,g₁ t≠0→t≤M)
    (hC:¬primeProductNorm p C≤ell*Real.exp M) (T:Finset ι→Finset ActualEisensteinCubic.O):
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K T=0 := by
  have hz (S:Finset ι):g₁ (columnLog p ell ((b.rightDivisor∪C)∪S))=0:=by
    by_contra h
    exact hC ((primeProductNorm_mono p hp
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)).trans
      (columnLog_norm_upper p hp ell M hell _ (hgM _ h)))
  have hcoef (S:Finset ι):canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun R=>g₁ (columnLog p ell R)) S=0:=by
    simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,ite_true,hz,mul_zero,zero_mul]
  simp only [canonicalCubeDualTail,actualFirstKernel,threeGaussRowFactor,hcoef,mul_zero,
    star_zero,zero_mul,ite_self,Finset.sum_const_zero,tsum_zero]

end

theorem full_uniform_canonicalSourceTail_bound (ε:ℝ) (hε:0<ε) (A:ℕ):
    ∃(s:Finset (ℕ×ℕ)) (C:ℝ),0<C ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (a:CubeCoordinates ι→Finset ι→Ideal ActualEisensteinCubic.O→ℂ) (Ψ₁ Ψ₂:ActualEisensteinCubic.O→*ℂ)
      (m₁ m₂:ActualEisensteinCubic.O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell → 1≤B → 1≤F → 1≤lengthScale →
      ell*Real.exp M₁≤lengthScale → ell*Real.exp M₂≤lengthScale →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell‖≤
      C*B^(4+ε)*lengthScale^4*F*Γ*(G₁*G₂*Ksrc)*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        (1+lengthScale^3*B^4/Ksrc)^2/(1+(Ksrc/K)/Real.exp (M₁+M₂))^A := by
  obtain ⟨s,Ct,hCt,hkernel⟩:=full_uniform_canonicalSource_kernel_tail A
  obtain ⟨Cb,hCb,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨s,Cb*128^5*Ct,by positivity,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale
    hΓ hG₁ hG₂ hKsrc hK hell hB hF hL hL₁ hL₂ hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha hg₁ hg₂ hM₁ hM₂
  have hB0:0<B:=zero_lt_one.trans_le hB
  have hL0:0<lengthScale:=zero_lt_one.trans_le hL
  let P:=Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let H:ℝ:=(Ksrc/K)/Real.exp (M₁+M₂)
  let Q:ℝ:=(128*lengthScale)^2*(G₁*G₂*Ksrc)*P*(1+lengthScale^3*B^4/Ksrc)^2/(1+H)^A
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:(bs.card:ℝ)≤Cb*B^(1+ε)*B:=by
    apply hcount p hp hinj bs B B hB hB0.le hadm hb₁ hb₂
    intro b hb
    have hn:primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤B^2:=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    change ‖eisEmbedding (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2≤B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  let z (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal ActualEisensteinCubic.O):ℂ:=
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I)
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)
  have hblock (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) lengthScale) (I:Ideal ActualEisensteinCubic.O):
      ‖z b C I‖≤(128*(lengthScale*B^2))*Q:=by
    have hCb:primeProductNorm p C≤lengthScale:=(Finset.mem_filter.mp hC).2
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hiB)
    let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
    let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
    let U₁:=X₁*Real.exp M₁
    let U₂:=X₂*Real.exp M₂
    let E:=primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
    have hU₁:0<U₁:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hU₂:0<U₂:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hE:0<E:=primeProductNorm_pos p hp _
    have hU₁b:U₁≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₁).le).trans hL₁
    have hU₂b:U₂≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₂).le).trans hL₂
    have hEb:E≤B^2:=(primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
      (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    have hlocal (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
        ‖∑'h:{h:ActualEisensteinCubic.O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S)))
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₂ (columnLog p ell S)))
          W (fun _=>1) (fun _=>1) 1 1 Ksrc (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤Q:=by
      have hDb:=cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB0.le hL0.le hCB (hb₁ b hb) (hb₂ b hb) hCb (Finset.mem_powerset.mp hD)
      exact (hkernel p hp hinj hcop hg hc pool b (hadm b hb) C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I) g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂).trans
        (firstTail_scalar_bound Ksrc (primeProductNorm p D) E U₁ U₂ lengthScale B G₁ G₂ P H A
          hKsrc (primeProductNorm_pos p hp _) hE hU₁ hU₂ hL0.le hG₁ hG₂ hP hH hDb hEb hU₁b hU₂b)
    dsimp only [z,canonicalCubeDualTail]
    rw [norm_mul]
    calc
      _ ≤ ‖∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
          ∑'h:{h:ActualEisensteinCubic.O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
            (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
            (canonicalCubeResidual p hg b C true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S)))
            (canonicalCubeResidual p hg b C false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₂ (columnLog p ell S)))
            W (fun _=>1) (fun _=>1) 1 1 Ksrc (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖:=
        mul_le_of_le_one_left (norm_nonneg _) (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)
      _ ≤ ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,Q:=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro D hD
        rw [norm_mul]
        exact (mul_le_mul (sourceMobiusDivisor_norm_le_one p hp D) (hlocal D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul Q)
      _ = ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)*Q:=by simp
      _ ≤ _:=mul_le_mul_of_nonneg_right (cubeSourceDivisors_card p hp hinj b C B lengthScale hB0 hL0 hCB (hb₁ b hb) (hb₂ b hb) hCb) hQ
  have hcommon (b:CubeCoordinates ι) (hb:b∈bs):
      ‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤
      (128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q):=by
    have heq:(∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I)=
        ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,a b C I*z b C I:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hn:¬primeProductNorm p C≤ell*Real.exp M₁:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h.trans hL₁⟩)
      apply Finset.sum_eq_zero
      intro I hI
      rw [show z b C I=0 from canonicalCubeDualTail_support p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell Ksrc M₁ hell hM₁ hn _,mul_zero]
    rw [heq]
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,‖a b C I*z b C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,Γ*((128*(lengthScale*B^2))*Q):=by
        apply Finset.sum_le_sum
        intro C hC
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact mul_le_mul (ha b hb C (Finset.mem_filter.mp hC).1 I hI) (hblock b hb C hC I) (norm_nonneg _) hΓ
      _ = ((boundedPrimeSupports p (pool\b.support) lengthScale).card:ℝ)*(labels.card:ℝ)*Γ*((128*(lengthScale*B^2))*Q):=by simp;ring
      _ ≤ _:=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hΓ
        exact mul_le_mul (boundedPrimeSupports_card_positive p hp hinj _ lengthScale hL0) hlabel (Nat.cast_nonneg _) (by positivity)
  change ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤_
  calc
    _ ≤ ∑b∈bs,‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,(128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q):=Finset.sum_le_sum hcommon
    _ = (bs.card:ℝ)*((128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q)):=by simp
    _ ≤ (Cb*B^(1+ε)*B)*((128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q)):=
      mul_le_mul_of_nonneg_right hbcount (by positivity)
    _ = _:=by
      dsimp [Q,P,H]
      rw [Real.rpow_add hB0,Real.rpow_add hB0]
      norm_num
      ring

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem globalBin_canonical_child_bound
    (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool) (j:GlobalLogIndex)
    (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (V₁ V₂:ℝ→ℂ) (C E ε K ell B F:ℝ) (A J:ℕ)
    (hC:0≤C) (hE:0≤E) (hε:0<ε) (hK:0<K) (hell:0<ell) (hB:0<B) (hF:0<F)
    (hk:∀x∈source,x.source.frequency≠0)
    (hb₁:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (he:∀ray:SecondRayIndex,∀q∈globalBinTriples p source side j,
      densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J≤
        E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2):
    (∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
      globalDescentWeight C ε 0 0 K ell B F A J j ray q*
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J/
        (globalPooledColumnScale ell j*globalPooledLabelScale j)))≤
    E*C*globalRayTripleConstant*((ell*B^3)*F)*(globalBinLossScale B j)^ε/
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A := by
  let M:=globalPooledColumnScale ell j*globalPooledLabelScale j
  have hM:0<M:=mul_pos (globalPooledColumnScale_pos ell hell j)
    (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))
  calc
    _ ≤ ∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
        globalDescentWeight C ε 0 0 K ell B F A J j ray q*(E*M):=by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (globalDescentWeight_nonneg C ε 0 0 K ell B F A J j ray q hC hK hell hB hF)
      apply (div_le_iff₀ hM).mpr
      simpa only [M,pow_two,mul_assoc] using he ray q hq
    _ = E*(∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
        globalDescentWeight C ε 0 0 K ell B F A J j ray q*M):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hray
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ E*((C*(globalBinLossScale B j)^ε/
        (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A)*
        globalRayTripleConstant*((ell*B^3)*F)):=by
      apply mul_le_mul_of_nonneg_left _ hE
      simpa only [norm_zero,add_zero,one_pow,mul_one,globalRayTripleConstant,M] using
        globalDescentWeight_mass p hp C ε 0 0 K ell B F A J hC hε hK hell hB hF side source j hk hb₁ hb₂
    _ = _:=by ring

end

theorem globalSelected_canonical_child_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Cbox:ℝ,0<Cbox ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool)
      (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (V₁ V₂:ℝ→ℂ) (C E K ell B F M H U:ℝ) (A J:ℕ)
      (keep:GlobalLogIndex→Prop) [DecidablePred keep],
      0≤C → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      (∀x∈source,x.source.frequency≠0) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter keep,
        ∀ray:SecondRayIndex,∀q∈globalBinTriples p source side j,
        densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      (∑j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter keep,
        ∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
        globalDescentWeight C ε 0 0 K ell B F A J j ray q*
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J/
          (globalPooledColumnScale ell j*globalPooledLabelScale j)))≤
        E*C*globalRayTripleConstant*((ell*B^3)*F)*Cbox*U^(deltaLoss+8*ε) := by
  obtain ⟨Cbox,hCbox,hbox⟩:=globalLogBox_total_loss deltaLoss hδ ε hε.le
  refine ⟨Cbox,hCbox,?_⟩
  intro ι _ p hp _ hcop hg pool source side Ψ m V₁ V₂ C E K ell B F M H U A J keep _
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hk hb₁ hb₂ he
  let S:=globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let Q:=E*C*globalRayTripleConstant*((ell*B^3)*F)
  have hB0:0<B:=zero_lt_one.trans_le hB
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hQ:0≤Q:=by dsimp [Q,globalRayTripleConstant];positivity
  have hloss (j:GlobalLogIndex):0≤(globalBinLossScale B j)^ε:=by
    unfold globalBinLossScale
    have hx:=globalLogRep_pos j 4
    have hl:=globalPooledLabelScale_ge_one j
    positivity
  calc
    _ ≤ ∑j∈S.filter keep,Q*(globalBinLossScale B j)^ε:=by
      apply Finset.sum_le_sum
      intro j hj
      have hb:=globalBin_canonical_child_bound p hp hcop hg pool source side j Ψ m V₁ V₂ C E ε K ell B F A J
        hC hE hε hK hell hB0 hF0 hk hb₁ hb₂ (he j hj)
      apply hb.trans
      apply div_le_self (mul_nonneg hQ (hloss j))
      have hr:=globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell
        (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
      exact one_le_pow₀ (by linarith)
    _ ≤ ∑j∈S,Q*(globalBinLossScale B j)^ε:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j hj hnot=>mul_nonneg hQ (hloss j))
    _ = Q*∑j∈S,(globalBinLossScale B j)^ε:=by rw [Finset.mul_sum]
    _ ≤ Q*(Cbox*U^(deltaLoss+8*ε)):=mul_le_mul_of_nonneg_left
      (hbox K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) hQ
    _ = _:=by dsimp [Q];ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

theorem globalPooled_mass_le_parent (_K ell B F:ℝ) (hell:0<ell) (hB:0<B) (hF:0<F)
    (j:GlobalLogIndex) (hJ:globalLogRep j 4≤B^2) (hlarge:Real.exp 4≤B*F):
    globalPooledColumnScale ell j*globalPooledLabelScale j≤(ell*B^3)*F := by
  have hD:=globalPooledDelta_pos B F hB hF j
  have hM:0<(ell*B^3)*F:=by positivity
  rw [globalPooled_mass ell B F hB hF j]
  calc
    _ ≤ Real.exp 4*((ell*B^3)*F)*B^2/(globalPooledDelta B F j*B^2):=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = Real.exp 4*((ell*B^3)*F)/globalPooledDelta B F j:=by field_simp
    _ ≤ (ell*B^3)*F:=by
      apply (div_le_iff₀ hD).mpr
      have he:=hlarge.trans (globalPooledDelta_ge B F hB.le hF.le j)
      nlinarith

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit hp in
theorem globalArithmeticTargets_nonzero (source:Finset (GlobalSecondData ι)) (side:Bool)
    (q:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j:GlobalLogIndex)
    (hk:∀x∈source,x.source.frequency≠0):
    ∀z∈globalArithmeticTargets p source side q j,z.2≠0 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
  have hxs:x∈source:=(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  exact actualSecondRow_ne_zero p _ _ _ (hk x hxs)

include hp in

theorem globalRetained_canonical_geometry
    (source:Finset (GlobalSecondData ι)) (side:Bool) (q:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j:GlobalLogIndex)
    (hq:q∈globalBinTriples p source side j)
    (Z η Ksrc K ell B F:ℝ) (m:ActualEisensteinCubic.O)
    (hZ:1<Z) (hη:η≤(1:ℝ)/1000) (hKsrc:0<Ksrc) (hK:0<K) (hKle:K≤Ksrc)
    (hell:0<ell) (hB:0<B) (hF:1≤F) (hprogress:Z^((1:ℝ)/1000)≤B*F)
    (hlarge:Real.exp 4≤B*F) (hstart:Ksrc≤Z^3)
    (hk:∀x∈source,x.source.frequency≠0)
    (hb₁:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hretained:globalBinRadial ell (globalPooledRowScale K ell B F j) j≤Z^η):
    let X:=globalPooledColumnScale ell j
    let lengthScale:=globalPooledLabelScale j
    let Kchild:=globalLogRep j 8*Real.exp 1
    0<X ∧ 1≤lengthScale ∧ 1≤Kchild ∧ X*lengthScale≤(ell*B^3)*F ∧
      Kchild≤Ksrc/Z^((1:ℝ)/1000) ∧ fixedDepthRank Z Kchild+1≤fixedDepthRank Z Ksrc ∧
      fixedDepthRank Z Ksrc≤3000 ∧ Kchild*‖eisEmbedding (fixedTripleMask m q)‖^2/(X*lengthScale)≤
        Z^η*(K*‖eisEmbedding m‖^2/((ell*B^3)*F)) ∧
      (∀z∈globalArithmeticTargets p source side q j,
        Squarefree z.1 ∧ z.2≠0 ∧ (Ideal.absNorm z.1:ℝ)≤lengthScale ∧ ‖eisEmbedding z.2‖^2≤Kchild) := by
  obtain ⟨x,hx,hqx⟩:=Finset.mem_image.mp hq
  obtain ⟨hxs,hj⟩:=Finset.mem_filter.mp hx
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hJ:globalLogRep j 4≤B^2:=by
    simpa only [hj] using globalPooled_J_bound p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
  have hD:Z^η≤globalPooledDelta B F j:=
    (Real.rpow_le_rpow_of_exponent_le hZ.le hη).trans
      (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
  have hr:globalLogRep j 8*Real.exp 1≤K/globalPooledDelta B F j:=
    globalPooledRow_contraction K ell B F hK hell hB hF0 j hJ (hretained.trans hD)
  have hKchild:1≤globalLogRep j 8*Real.exp 1:=one_le_mul_of_one_le_of_one_le
    (globalLogRep_ge_one j 8) (Real.one_le_exp (by norm_num))
  have hsmall:globalLogRep j 8*Real.exp 1≤Ksrc/Z^((1:ℝ)/1000):=by
    apply hr.trans
    calc
      _ ≤ K/Z^((1:ℝ)/1000):=div_le_div_of_nonneg_left hK.le
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
        (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
      _ ≤ _:=div_le_div_of_nonneg_right hKle (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hinv:=globalBin_invariant_small_padding p hp Z η K ell B F hZ hK hell hB hF side x
    (hk x hxs) m (hb₁ x hxs) (hb₂ x hxs) (by simpa only [hj] using hretained)
  simp only [hj,hqx] at hinv
  refine ⟨globalPooledColumnScale_pos ell hell j,globalPooledLabelScale_ge_one j,hKchild,
    globalPooled_mass_le_parent K ell B F hell hB hF0 j hJ hlarge,hsmall,
    fixedDepthRank_step Z Ksrc _ hZ hKsrc hKchild hsmall,
    fixedDepthRank_initial Z Ksrc hZ hKsrc hstart,hinv,?_⟩
  intro z hz
  have hb:=globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨globalArithmeticTargets_squarefree p source side q j z hz,
    globalArithmeticTargets_nonzero p source side q j hk z hz,hb.2.1,hb.2.2⟩

end SecondPassArithmetic

end

end OAI
