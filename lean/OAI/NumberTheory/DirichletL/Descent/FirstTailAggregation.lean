import OAI.NumberTheory.DirichletL.Descent.FirstWholeCanonicalTail
import OAI.NumberTheory.DirichletL.Descent.CubeSupportNorm

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstLocalPhysicalTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
    (K:ℝ) (T:Finset ι→Finset O) (D:Finset ι):ℂ :=
  ∑'h:{h:O // h∉T D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
    (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
    (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) W (fun _=>1) (fun _=>1) 1 1 K
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val

theorem cube_tail_support_test (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
    (K L:ℝ) (T:Finset ι→Finset O)
    (hs:∀U,H₁ U≠0→primeProductNorm p U≤L) (hC:¬primeProductNorm p C≤L) :
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T=0 := by
  have hz (U:Finset ι):H₁ ((b.rightDivisor∪C)∪U)=0:=by
    by_contra h
    exact hC ((primeProductNorm_mono p hp
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)).trans (hs _ h))
  have hcoef (U:Finset ι):canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ U=0:=by
    simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,ite_true,hz,mul_zero,zero_mul]
  simp only [canonicalCubeDualTail,actualFirstKernel,threeGaussRowFactor,hcoef,mul_zero,
    star_zero,zero_mul,ite_self,Finset.sum_const_zero,tsum_zero]

end

theorem full_first_tail_from_local (ε:ℝ) (hε:0<ε) :
    ∃Ctail:ℝ,0<Ctail ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (H₁ H₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (K B L F Γ E:ℝ)
      (T:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→Finset O),
      1≤B → 0<L → 1≤F → 0≤Γ → 0≤E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (∀b∈bs,∀U,H₁ b U≠0→primeProductNorm p U≤L) →
      (∀b∈bs,∀C∈boundedPrimeSupports p (pool\b.support) L,∀I∈labels,
        ∀D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I) (H₁ b) (H₂ b) W K (T b C I) D‖≤E) →
      ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
        canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I) (H₁ b) (H₂ b) W K (T b C I)‖≤
        Ctail*B^(4+ε)*L^2*F*Γ*E := by
  obtain ⟨Cb,hCb,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨Cb*128^3,by positivity,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ W K B L F Γ E T
    hB hL hF hΓ hE hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha hs hlocal
  have hBp:0<B:=zero_lt_one.trans_le hB
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:(bs.card:ℝ)≤Cb*B^(1+ε)*B:=by
    apply hcount p hp hinj bs B B hB hBp.le hadm hb₁ hb₂
    intro b hb
    have hn:primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤B^2:=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cube_whole_support_dyad p hp b B hBp.le (hb₁ b hb) (hb₂ b hb))
    change ‖eisEmbedding (∏i∈cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2≤B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  let z (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O):ℂ:=
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (H₁ b) (H₂ b) W K (T b C I)
  have hblock (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι)
      (hC:C∈boundedPrimeSupports p (pool\b.support) L) (I:Ideal O) (hI:I∈labels):
      ‖z b C I‖≤128*(L*B^2)*E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    dsimp only [z,canonicalCubeDualTail]
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C
      Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)).trans
    calc
      _≤∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,E:=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro D hD
        rw [norm_mul]
        exact (mul_le_mul (sourceMobiusDivisor_norm_le_one p hp D)
          (hlocal b hb C hC I hI D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul E)
      _= ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)*E:=by simp
      _≤_:=mul_le_mul_of_nonneg_right (cubeSourceDivisors_card p hp hinj b C B L hBp hL hCB
        (hb₁ b hb) (hb₂ b hb) (Finset.mem_filter.mp hC).2) hE
  have hcommon (b:CubeCoordinates ι) (hb:b∈bs):
      ‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤
      (128*L)*(128*F)*Γ*(128*(L*B^2)*E):=by
    have heq:(∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I)=
        ∑C∈boundedPrimeSupports p (pool\b.support) L,∑I∈labels,a b C I*z b C I:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hn:¬primeProductNorm p C≤L:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
      apply Finset.sum_eq_zero
      intro I hI
      rw [show z b C I=0 from cube_tail_support_test p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ _
        (H₁ b) (H₂ b) W K L (T b C I) (hs b hb) hn,mul_zero]
    rw [heq]
    calc
      _≤∑C∈boundedPrimeSupports p (pool\b.support) L,∑I∈labels,Γ*(128*(L*B^2)*E):=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro C hC
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact mul_le_mul (ha b hb C (Finset.mem_filter.mp hC).1 I hI) (hblock b hb C hC I hI) (norm_nonneg _) hΓ
      _= ((boundedPrimeSupports p (pool\b.support) L).card:ℝ)*(labels.card:ℝ)*Γ*(128*(L*B^2)*E):=by simp;ring
      _≤_:=by gcongr;exact boundedPrimeSupports_card_positive p hp hinj _ _ hL
  change ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤_
  calc
    _≤∑b∈bs,(128*L)*(128*F)*Γ*(128*(L*B^2)*E):=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hcommon)
    _= (bs.card:ℝ)*((128*L)*(128*F)*Γ*(128*(L*B^2)*E)):=by simp
    _≤(Cb*B^(1+ε)*B)*((128*L)*(128*F)*Γ*(128*(L*B^2)*E)):=by gcongr
    _= _:=by
      have he:B^(1+ε)*B*B^2=B^(4+ε):=by
        calc
          _=B^(1+ε)*B^(1:ℝ)*B^(2:ℝ):=by rw [Real.rpow_one,Real.rpow_two]
          _=B^((1+ε)+1+2):=by rw [←Real.rpow_add hBp,←Real.rpow_add hBp]
          _= _:=by congr 1;ring
      calc
        _=(Cb*128^3)*(B^(1+ε)*B*B^2)*L^2*F*Γ*E:=by ring
        _= _:=by rw [he]

end SevenEighths.InverseMoment

end

end OAI
