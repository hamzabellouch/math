import OAI.NumberTheory.DirichletL.MeanSquare.CanonicalTailBounds

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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)

theorem globalChildBudget_canonical_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Clo Chi:ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool)
      (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (windows:Fin 7→ℝ→ℂ)
      (C E K ell B F M H U Z θ A₀ Vmax:ℝ) (N J:ℕ),
      0≤C → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀u,‖Ψ u‖≤1) → (∀x∈source,x.source.frequency≠0) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
        ∀ray:SecondRayIndex,∀q∈globalBinTriples p source side j,
        densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J)≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H (N+1) (2*J) side≤
        C*globalRayTripleConstant*((ell*B^3)*F)*U^(deltaLoss+8*ε)*
          (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N)) := by
  obtain ⟨Clo,hClo,hlow⟩:=globalSelected_canonical_child_bound deltaLoss hδ ε hε
  obtain ⟨Chi,hChi,hhigh⟩:=globalChild_large_radial_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool source side Ψ m windows C E K ell B F M H U Z θ A₀ Vmax N J
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂ he
  have hlo:=hlow p hp hcop hg pool source side Ψ m (windows 5) (windows 6) C E K ell B F M H U (N+1) (2*J)
    (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ)
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hk hb₁ hb₂ he
  have hhi:=hhigh p hp hcop hg hc hinj pool Ψ m (windows 5) (windows 6) C K ell B F M H U Z θ A₀ Vmax N J
    source side hC hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂
  let S:=globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let f:=fun j:GlobalLogIndex=>∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
      globalDescentWeight C ε 0 0 K ell B F (N+1) (2*J) j ray q*
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J)/
        (globalPooledColumnScale ell j*globalPooledLabelScale j))
  have hsplit:(∑j∈S,f j)=
      (∑j∈S.filter (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),f j)+
      (∑j∈S.filter (fun j=>Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),f j):=by
    simpa only [not_lt] using (Finset.sum_filter_add_sum_filter_not S
      (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ) f).symm
  change (∑j∈S,f j)≤_
  rw [hsplit]
  apply (add_le_add hlo hhi).trans_eq
  ring

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

def reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) : Finset (CubeCoordinates ι) :=
  (((v₁.support ∪ v₂.support).powerset).product
    ((v₁.support ∪ v₂.support).powerset)).image
    (fun A => ⟨v₁,v₂,A.2,A.1⟩)

lemma mem_reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFiber v₁ v₂ ↔
      b.leftExponent=v₁ ∧ b.rightExponent=v₂ ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h₂,h₁⟩ := Finset.mem_product.mp hA
    exact ⟨rfl,rfl,Finset.mem_powerset.mp h₁,Finset.mem_powerset.mp h₂⟩
  · rintro ⟨hl,hr,hb⟩
    apply Finset.mem_image.mpr
    refine ⟨(b.rightDivisor,b.leftDivisor),?_,?_⟩
    · apply Finset.mem_product.mpr
      have hs : b.support=v₁.support∪v₂.support := by rw [CubeCoordinates.support,hl,hr]
      exact ⟨Finset.mem_powerset.mpr (hs ▸ hb.2),Finset.mem_powerset.mpr (hs ▸ hb.1)⟩
    · exact CubeCoordinates.ext hl.symm hr.symm rfl rfl

def reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) : Finset (CubeCoordinates ι) :=
  (Q.product Q).biUnion (fun v => reopenedCubeFiber v.2 v.1)

lemma mem_reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFamily Q ↔ b.leftExponent ∈ Q ∧ b.rightExponent ∈ Q ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨v,hv,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    exact ⟨hl ▸ (Finset.mem_product.mp hv).2,hr ▸ (Finset.mem_product.mp hv).1,ha⟩
  · rintro ⟨hl,hr,ha⟩
    exact Finset.mem_biUnion.mpr ⟨(b.rightExponent,b.leftExponent),Finset.mem_product.mpr ⟨hr,hl⟩,
      (mem_reopenedCubeFiber _ _ b).mpr ⟨rfl,rfl,ha⟩⟩

lemma reopenedCubeFamily_admissible (Q : Finset (ι →₀ ℕ)) :
    ∀ b ∈ reopenedCubeFamily Q,b.Admissible :=
  fun b hb => ((mem_reopenedCubeFamily Q b).mp hb).2.2

lemma reopenedCubeFamily_support (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (hQ : ∀ v ∈ Q,v.support ⊆ pool) :
    ∀ b ∈ reopenedCubeFamily Q,b.support ⊆ pool := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  exact Finset.union_subset (hQ _ hl) (hQ _ hr)

theorem sum_reopenedCubeFamily {M : Type*} [AddCommMonoid M]
    (Q : Finset (ι →₀ ℕ)) (f : CubeCoordinates ι → M) :
    (∑ b ∈ reopenedCubeFamily Q,f b) =
      ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ A₂ ∈ (v₁.support∪v₂.support).powerset,
        ∑ A₁ ∈ (v₁.support∪v₂.support).powerset,f ⟨v₁,v₂,A₁,A₂⟩ := by
  unfold reopenedCubeFamily
  rw [Finset.sum_biUnion]
  · change (∑ x ∈ Q ×ˢ Q,∑ i ∈ reopenedCubeFiber x.2 x.1,f i)=_
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro v₂ hv₂
    apply Finset.sum_congr rfl
    intro v₁ hv₁
    unfold reopenedCubeFiber
    rw [Finset.sum_image]
    · change (∑ x ∈ (v₁.support∪v₂.support).powerset ×ˢ (v₁.support∪v₂.support).powerset,
        f ⟨v₁,v₂,x.2,x.1⟩)=_
      rw [Finset.sum_product]
    · intro A hA B hB he
      exact Prod.ext (congrArg CubeCoordinates.rightDivisor he) (congrArg CubeCoordinates.leftDivisor he)
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro b hb hc
    obtain ⟨hbl,hbr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    obtain ⟨hcl,hcr,hc⟩ := (mem_reopenedCubeFiber w.2 w.1 b).mp hc
    exact hne (Prod.ext (hbr.symm.trans hcr) (hbl.symm.trans hcl))

omit [DecidableEq ι] in
lemma primeProduct_finsupp_support (p : ι → ActualEisensteinCubic.O) (B : Finset ι) (v : ι →₀ ℕ)
    (hv : v.support ⊆ B) : primeProduct p B v=primeProduct p v.support v := by
  unfold primeProduct
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

lemma reopenedCubeFamily_cube_norms (p : ι → ActualEisensteinCubic.O) (Q : Finset (ι →₀ ℕ)) (B : ℝ)
    (hQ : ∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ b ∈ reopenedCubeFamily Q,
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2 ≤ B ∧
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2 ≤ B := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  rw [primeProduct_finsupp_support p b.support b.leftExponent Finset.subset_union_left,
    primeProduct_finsupp_support p b.support b.rightExponent Finset.subset_union_right]
  exact ⟨hQ _ hl,hQ _ hr⟩

def reopenedPairCoefficient (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (b : CubeCoordinates ι) (_C : Finset ι) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  star (β I b.rightExponent)*β I b.leftExponent

omit [DecidableEq ι] in
lemma reopenedPairCoefficient_independent_common (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (b : CubeCoordinates ι) (C D : Finset ι) (I : Ideal ActualEisensteinCubic.O) :
    reopenedPairCoefficient β b C I=reopenedPairCoefficient β b D I := rfl

lemma reopenedPairCoefficient_bound (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hβ : ∀ I ∈ labels,∀ v ∈ Q,‖β I v‖ ≤ Γ) :
    ∀ b ∈ reopenedCubeFamily Q,∀ C,∀ I ∈ labels,
      ‖reopenedPairCoefficient β b C I‖ ≤ Γ^2 := by
  intro b hb C I hI
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  simp only [reopenedPairCoefficient,norm_mul,norm_star]
  simpa only [pow_two] using mul_le_mul (hβ I hI _ hr) (hβ I hI _ hl) (norm_nonneg _) hΓ

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

theorem reopenedCanonicalRow_smoothed_eq_source {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (g W : 𝓢(ℝ,ℂ)) (K ell : ℝ) (hK : 0 < K) :
    (∑ I ∈ labels,∑' z : ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/K)*
      (‖reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun S => g (columnLog p ell S)) z‖^2 : ℝ)) =
    canonicalSourceTotal p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W K ell := by
  rw [canonicalSourceTotal,sum_reopenedCubeFamily]
  simp only [reopenedPairCoefficient,CubeCoordinates.support]
  calc
    _ = ∑ I ∈ labels,∑ v₂ ∈ Q,∑ v₁ ∈ Q,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (fun S => g (columnLog p ell S))
          (fun S => g (columnLog p ell S)) W K := by
      apply Finset.sum_congr rfl
      intro I hI
      exact reopenedCanonicalRow_smoothed_expand p hp hcop hg pool Q hQ (β I) Ψ m
        (idealGenerator I) (fun S => g (columnLog p ell S)) W K hK
    _ = ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ I ∈ labels,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (fun S => g (columnLog p ell S))
          (fun S => g (columnLog p ell S)) W K := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      apply Finset.sum_congr rfl
      intro v₁ hv₁
      have hs : v₁.support∪v₂.support ⊆ pool := Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂)
      simp_rw [canonicalCubeCorrelation_eq_blocks p hp hcop hg hinj hpr pool v₁ v₂ hs,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₂ hA₂
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₁ hA₁
      rw [Finset.sum_comm]

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]

theorem reopenedCubeFamily_card (Q : Finset (ι →₀ ℕ)) :
    (reopenedCubeFamily Q).card =
      ∑ v₂ ∈ Q,∑ v₁ ∈ Q,(2^((v₁.support∪v₂.support).card))^2 := by
  have h := sum_reopenedCubeFamily Q (fun _ => (1 : ℕ))
  simpa [pow_two] using h

theorem reopenedCubeFamily_card_le (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (hQ : ∀ v ∈ Q,v.support ⊆ pool) :
    (reopenedCubeFamily Q).card ≤ Q.card^2*(2^pool.card)^2 := by
  rw [reopenedCubeFamily_card]
  calc
    _ ≤ ∑ v₂ ∈ Q,∑ v₁ ∈ Q,(2^pool.card)^2 := by
      apply Finset.sum_le_sum
      intro v₂ hv₂
      apply Finset.sum_le_sum
      intro v₁ hv₁
      have hc := Finset.card_le_card (Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂))
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hc) 2
    _ = _ := by simp [pow_two,mul_assoc]

theorem reopenedSourceBlocks_bounds (p : ι → ActualEisensteinCubic.O) (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (B : ℝ) (hQ : ∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ q ∈ canonicalSourceBlocks pool (reopenedCubeFamily Q),GlobalCubeAdmissible q ∧
      ‖eisEmbedding (primeProduct p q.cube.support q.cube.leftExponent)‖^2 ≤ B ∧
      ‖eisEmbedding (primeProduct p q.cube.support q.cube.rightExponent)‖^2 ≤ B := by
  intro q hq
  exact ⟨canonicalSourceBlocks_admissible pool _ (reopenedCubeFamily_admissible Q) q hq,
    canonicalSourceBlocks_cube_norms p pool _ B
      (fun b hb => (reopenedCubeFamily_cube_norms p Q B hQ b hb).1)
      (fun b hb => (reopenedCubeFamily_cube_norms p Q B hQ b hb).2) q hq⟩

end

theorem reopenedCubeFamily_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (_hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (Q : Finset (ι →₀ ℕ)) (B : ℝ),1 ≤ B →
      (∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) →
      ((reopenedCubeFamily Q).card : ℝ) ≤ C*B^(2+ε) := by
  obtain ⟨C,hC,hcount⟩ := cube_coordinates_parity_count ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Q B hB hQ
  have hBp := zero_lt_one.trans_le hB
  have hb := reopenedCubeFamily_cube_norms p Q B hQ
  have hactive (b : CubeCoordinates ι) (hbf : b ∈ reopenedCubeFamily Q) :
      ‖eisEmbedding (∏ i ∈ cubeActiveSupport b.support
        (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖ ≤ B := by
    have hn : primeProductNorm p (cubeActiveSupport b.support
        (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) ≤ B^2 :=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cubeCoordinates_radical_bound p hp b B hBp.le (hb b hbf).1 (hb b hbf).2)
    change ‖eisEmbedding (∏ i ∈ cubeActiveSupport b.support
      (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2 ≤ B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏ i ∈ cubeActiveSupport b.support
      (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  have h := hcount p hp hinj (reopenedCubeFamily Q) B B hB hBp.le
    (reopenedCubeFamily_admissible Q) (fun b hb' => (hb b hb').1)
    (fun b hb' => (hb b hb').2) hactive
  apply h.trans_eq
  calc
    C*B^(1+ε)*B = C*(B^(1+ε)*B^(1 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = C*B^((1+ε)+1) := by rw [Real.rpow_add hBp (1+ε) (1 : ℝ)]
    _ = C*B^(2+ε) := by congr 2; ring

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

theorem reopenedCanonicalRow_smoothed_split {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (g W : 𝓢(ℝ,ℂ)) (Ksrc K ell : ℝ)
    (hKsrc : 0 < Ksrc) (hK : 0 ≤ K) :
    (∑ I ∈ labels,∑' z : ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/Ksrc)*
      (‖reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun S => g (columnLog p ell S)) z‖^2 : ℝ)) =
    canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc ell+
    canonicalSourceFinite p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell+
    canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell := by
  rw [reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m g W Ksrc ell hKsrc]
  exact canonicalSourceTotal_split p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell hKsrc hK

theorem reopenedCanonicalBlockCoefficient_bound {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hβ : ∀ I ∈ labels,∀ v ∈ Q,‖β I v‖ ≤ Γ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀ u,‖Ψ u‖ ≤ 1) (m : ActualEisensteinCubic.O) (K ell : ℝ)
    (b : GlobalCubeBlock ι) (hb : b ∈ canonicalSourceBlocks pool (reopenedCubeFamily Q))
    (x : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) (hx : x ∈ canonicalBlockFrequencies p K ell labels b) :
    ‖canonicalBlockCoefficient p hp hcop hg (reopenedPairCoefficient β) Ψ Ψ m m b x‖ ≤ Γ^2 := by
  exact canonicalBlockCoefficient_bound p hp hcop hg hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m (Γ^2) K ell (sq_nonneg _) hΨ hΨ
    (fun b hb C hC I hI => reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb C I hI) b hb x hx

end SecondPassArithmetic

namespace CubicEisenstein
open MeasureTheory
open scoped SchwartzMap

lemma euclideanIntegral_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     ∫p,g p) =
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanIntegrable_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Integrable g volume) ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeIntegral_eq_borel (g : EuclideanSpatial→ℝ) :
    (∫p,g p)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) :=
  euclideanIntegral_borel_transport inferInstance inferInstance g

lemma euclideanNativeIntegrable_iff_borel (g : EuclideanSpatial→ℝ) :
    Integrable g volume ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) :=
  euclideanIntegrable_borel_transport inferInstance inferInstance g

def euclideanLp_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) := by
  have he := hm.measurable_eq
  subst m
  exact LinearIsometryEquiv.refl ℂ _

def euclideanNativeLpBorelEquiv : EuclideanL2 ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) :=
  euclideanLp_borel_transport inferInstance inferInstance

lemma euclideanLp_borel_transport_schwartz (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanLp_borel_transport m hm
      (letI : MeasurableSpace EuclideanSpatial := m
       letI : BorelSpace EuclideanSpatial := hm
       f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeLpBorelEquiv_schwartz (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanNativeLpBorelEquiv (f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) :=
  euclideanLp_borel_transport_schwartz inferInstance inferInstance f

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

namespace CubicEisenstein
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

lemma euclideanOriginalMeasurable_eq_borel :
    (inferInstance : MeasurableSpace EuclideanSpatial)=borel EuclideanSpatial :=
  BorelSpace.measurable_eq

local instance : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance : BorelSpace EuclideanSpatial := ⟨rfl⟩

def kernelLocalizedRealTest (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) : C1c (E := EuclideanSpatial) :=
  ⟨fun p => projection (kernelLocalizedField χ f p),
    (projection.contDiff.comp (kernelLocalizedField_smooth χ f)).of_le (by simp),
    (kernelLocalizedField_compact χ f).comp_left (map_zero projection)⟩

lemma sourceC1c_toL2_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2 («μ» := volume) g‖^2=∫p,‖g.1 p‖^2 := by
  calc
    ‖toL2 («μ» := volume) g‖^2=inner ℝ (toL2 («μ» := volume) g) (toL2 («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2 («μ» := volume) g p) (toL2 («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)
        (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma sourceC1c_toL2Grad_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2Grad («μ» := volume) g‖^2=∫p,‖grad g.1 p‖^2 := by
  calc
    ‖toL2Grad («μ» := volume) g‖^2=inner ℝ (toL2Grad («μ» := volume) g) (toL2Grad («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2Grad («μ» := volume) g p) (toL2Grad («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_grad_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)
        (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma kernelLocalizedRealTest_grad_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) (p : EuclideanSpatial) :
    ‖grad (kernelLocalizedRealTest χ f projection).1 p‖^2≤
      ∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2 := by
  have hdiff : DifferentiableAt ℝ (kernelLocalizedField χ f) p :=
    ((kernelLocalizedField_smooth χ f).differentiable (by simp)).differentiableAt
  have hd := (projection.hasFDerivAt.comp p hdiff.hasFDerivAt).fderiv
  change fderiv ℝ (kernelLocalizedRealTest χ f projection).1 p=_ at hd
  unfold grad
  rw [LinearIsometryEquiv.norm_map,hd,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual]
  apply Finset.sum_le_sum
  intro j hj
  have hh := hprojection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
  change (projection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)))^2≤_
  simp only [Real.norm_eq_abs] at hh
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2

lemma kernelLocalizedRealTest_energy_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) :
    ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
      ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤
        ‖kernelLocalizedH1 χ f‖^2 := by
  let g := kernelLocalizedRealTest χ f projection
  rw [sourceC1c_toL2_norm_sq,sourceC1c_toL2Grad_norm_sq,kernelLocalizedH1_norm_sq,
    ←integral_add (memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq]
  rw [euclideanNativeIntegral_eq_borel]
  have hden := (euclideanNativeIntegrable_iff_borel (kernelLocalizedDensity χ f)).mp
    (kernelLocalizedDensity_integrable χ f)
  apply integral_mono
    ((memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq.add
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq)
    hden
  intro p
  have hm := hprojection (kernelLocalizedField χ f p)
  have hg := kernelLocalizedRealTest_grad_le χ f projection hprojection p
  change ‖projection (kernelLocalizedField χ f p)‖^2+_≤_
  unfold kernelLocalizedDensity
  nlinarith [norm_nonneg (projection (kernelLocalizedField χ f p)),norm_nonneg (kernelLocalizedField χ f p)]

lemma kernelLocalizedRealTest_support (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) :
    Function.support (kernelLocalizedRealTest χ f projection).1⊆tsupport χ.func := by
  intro p hp
  apply kernelLocalizedField_tsupport χ f
  apply subset_tsupport
  intro hz
  apply hp
  change projection (kernelLocalizedField χ f p)=0
  rw [hz,map_zero]

theorem kernelLocalizedReal_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖)
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)) '' family)) := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  have hCB : 0≤C*B := mul_nonneg hC hB
  have henergy : ∀f∈family,
      ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
        ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤C*B := by
    intro f hf
    exact (kernelLocalizedRealTest_energy_le χ f projection hprojection).trans
      ((hbound f).trans (mul_le_mul_of_nonneg_left (hfamily f hf) hC))
  have hh := euclidean_C1c_family_precompact (tsupport χ.func) χ.compact
    ((fun f => kernelLocalizedRealTest χ f projection) '' family) (Real.sqrt (C*B))
    (by
      rintro _ ⟨f,hf,rfl⟩
      exact kernelLocalizedRealTest_support χ f projection)
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection))])
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection))])
  simpa only [Set.image_image,Function.comp_def] using hh

abbrev RellichRealL2 := Lp ℝ 2 (volume : Measure EuclideanSpatial)
abbrev RellichComplexL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)

def kernelComplexL2Assemble : (RellichRealL2 × RellichRealL2) →L[ℝ] RellichComplexL2 :=
  (Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.fst ℝ RellichRealL2 RellichRealL2)+
  (Complex.I • Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.snd ℝ RellichRealL2 RellichRealL2)

lemma kernelComplexL2Assemble_localized (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    kernelComplexL2Assemble
      (toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
        toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM))=
      (kernelLocalizedSchwartz χ f).toLp 2 volume := by
  let r := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM)
  let i := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)
  let R := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) r
  let I := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) i
  have hr : (r : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).re :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM).2).coeFn_toLp
  have hi : (i : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).im :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM).2).coeFn_toLp
  change R+Complex.I•I=(kernelLocalizedSchwartz χ f).toLp 2 volume
  apply Lp.ext
  filter_upwards [hr,hi,Complex.ofRealCLM.coeFn_compLpL r,Complex.ofRealCLM.coeFn_compLpL i,
    Lp.coeFn_add R (Complex.I•I),Lp.coeFn_smul Complex.I I,
    (kernelLocalizedSchwartz χ f).coeFn_toLp 2 volume] with p hrp hip hR hI ha hs hf
  rw [ha,Pi.add_apply,hs,Pi.smul_apply,hR,hI,hrp,hip,hf]
  change ((kernelLocalizedField χ f p).re:ℂ)+Complex.I*((kernelLocalizedField χ f p).im:ℂ)=kernelLocalizedField χ f p
  simpa only [mul_comm] using Complex.re_add_im (kernelLocalizedField χ f p)

theorem kernelLocalizedComplex_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => (kernelLocalizedSchwartz χ f).toLp 2 volume) '' family)) := by
  have hr := kernelLocalizedReal_family_precompact χ hinj Complex.reCLM
    (fun z => by change ‖z.re‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z) family B hB hfamily
  have hi := kernelLocalizedReal_family_precompact χ hinj Complex.imCLM
    (fun z => by change ‖z.im‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm z) family B hB hfamily
  have hc := (hr.prod hi).image kernelComplexL2Assemble.continuous
  apply hc.closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
    toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)),?_,?_⟩
  · exact ⟨subset_closure ⟨f,hf,rfl⟩,subset_closure ⟨f,hf,rfl⟩⟩
  · exact kernelComplexL2Assemble_localized χ f

theorem kernelLocalizedNative_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)) := by
  have hc := kernelLocalizedComplex_family_precompact χ hinj family B hB hfamily
  apply (hc.image euclideanNativeLpBorelEquiv.symm.continuous).closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(kernelLocalizedSchwartz χ f).toLp 2 volume,subset_closure ⟨f,hf,rfl⟩,?_⟩
  apply euclideanNativeLpBorelEquiv.injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [kernelL2Localize_core χ hinj]
  exact (euclideanNativeLpBorelEquiv_schwartz _).symm

def kernelEnergyLocalizeL2 (χ : PositiveChartCutoff) : KernelEnergyGraph →L[ℂ] EuclideanL2 :=
  (kernelL2Localize χ).comp kernelEnergyMass

theorem kernelEnergyLocalizeL2_isCompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    IsCompactOperator (kernelEnergyLocalizeL2 χ) := by
  let family : Set kernelSmoothTests := {f | ‖kernelEnergyGraphCore f‖≤2}
  let C := closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)
  have hc : IsCompact C := kernelLocalizedNative_family_precompact χ hinj family 4 (by norm_num) (by
    intro f hf
    rw [←kernelEnergyGraphCore_norm_sq]
    change ‖kernelEnergyGraphCore f‖≤2 at hf
    nlinarith [norm_nonneg (kernelEnergyGraphCore f)])
  let T := kernelEnergyLocalizeL2 χ
  have hclosed : IsClosed (T ⁻¹' C) := hc.isClosed.preimage T.continuous
  have hsub : closure (kernelEnergyGraphCore ''
      (kernelEnergyGraphCore ⁻¹' Metric.ball (0 : KernelEnergyGraph) 2))⊆T ⁻¹' C := by
    apply hclosed.closure_subset_iff.mpr
    rintro _ ⟨f,hf,rfl⟩
    change kernelL2Localize χ (kernelEnergyMass (kernelEnergyGraphCore f))∈C
    rw [kernelEnergyMass_core]
    apply subset_closure
    refine ⟨f,?_,rfl⟩
    change ‖kernelEnergyGraphCore f‖≤2
    exact le_of_lt (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hf)
  have hball : Metric.ball (0 : KernelEnergyGraph) 2⊆T ⁻¹' C := by
    intro u hu
    exact hsub (kernelEnergyGraphCore_dense.subset_closure_image_preimage_of_isOpen
      Metric.isOpen_ball hu)
  refine ⟨C,hc,?_⟩
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : KernelEnergyGraph) (by norm_num : (0 : ℝ)<2)) hball

end CubicEisenstein

end

end OAI
