import OAI.NumberTheory.DirichletL.MeanSquare.OutsideIdeals

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare

section
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_source {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (W : ℝ → ℂ) (a b Z Y : ℝ)
    (ha : 0 < a) (hZ : 0 < Z) (hY : 0 < Y)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hD : b*Z ≤ D) (T : Finset O)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0)
    (K : Finset (primePool (outsideSquarefreeIdeals S D)) →
      Finset (primePool (outsideSquarefreeIdeals S D)) → Finset O) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    let hg := poolPrimary_good F hF
    letI : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
      intro i j hij
      apply Subtype.ext
      simpa only [p, poolPrimary_span F hF] using hij
    let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
    let Ψ := conjugateMonoid (normCharacter χ)
    (∑ z ∈ T, ‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)/Z ≤
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y (fun C E => (K C E).erase 0)‖+
      (truncatedSecondZero p hg Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K).re+
      ‖secondSourceTail p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K‖-‖G ∅‖^2 := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let p := poolPrimary F
  let hp := poolPrimary_ne_zero F hF
  let hg := poolPrimary_good F hF
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
    intro i j hij
    apply Subtype.ext
    simpa only [p, poolPrimary_span F hF] using hij
  let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
  have he := mobiusRow_finite_source p hg hp hinj (poolPrimary_odd F hF) Finset.univ
    (normCharacter χ) 1 G Y hY T hT hT0 K
  calc
    _ = ∑ z ∈ T, ‖mobiusRow p hg Finset.univ (normCharacter χ) 1 G z‖^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      exact outside_idealRowSum_initial_energy χ S D hbad hSp W a b Z ha hZ hs hW hD z
    _ ≤ _ := he

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma initial_actual_row_norm (x : SecondExpansionData ι) :
    ‖eisEmbedding (actualSecondRow p ∅ x.divisor x.frequency)‖^2 =
      elementNorm (sourceObservation p x).1 := by
  simp only [actualSecondRow, sourceObservation, elementNorm,
    map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm,
    primeProductNorm, Finset.prod_empty, map_one, norm_one, one_pow, one_mul]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma initialLogIndex_eq_second (x : SecondExpansionData ι) :
    initialLogIndex p x = secondLogIndex p ∅ x := by
  simp only [initialLogIndex, secondLogIndex, initial_actual_row_norm]

theorem initial_sector_coordinates (hp : ∀ i, p i ≠ 0)
    (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (Z M : ℝ) (hZ : 0 < Z) (j : SecondLogIndex)
    (x : SecondExpansionData ι) (hx : x ∈ secondLogSector p ∅ F K R Z M j) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    |sourceLogZ p Z X x| ≤ 2 ∧ |sourceLogE p (secondLogE j) x| ≤ 2 ∧
    |sourceLogV p (secondLogV j) x| ≤ 2 ∧ |sourceLogK p (secondLogK j) x| ≤ 2 := by
  obtain ⟨hx',hj⟩ := Finset.mem_filter.mp hx
  obtain ⟨hG,hE,hV,hk,hkf,hR,hs⟩ := secondSupportedSector_mem p F K R Z M x hx'
  have hsec := secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
    (Finset.mem_filter.mp hx').1
  have heq : initialLogIndex p x=j := (initialLogIndex_eq_second p x).trans hj
  have hc := initial_log_coordinates p hp Z hZ x hE hk
  dsimp only at hc ⊢
  rw [heq,quotient_norm_fixed p _ x hsec] at hc
  simpa only [sourceLogZ, sourceLogE, sourceLogV, sourceLogK, elementNorm,
    primeSubsetGenerator_norm_eq_productNorm] using hc

end

theorem initial_bin_transfer
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
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (Z H M : ℝ) (j : SecondLogIndex),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        let s := secondLogSector p ∅ F K R Z M j
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
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_sector_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F R Ψ m ray K Z H M j hZ hH hΨ
  dsimp only
  let s := secondLogSector p ∅ F K R Z M j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let X := initialLogColumn Z (primeProductNorm p R) j
  have hR : 0 < primeProductNorm p R := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hs : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
      (secondLogSector_subset p ∅ F K R Z M j hx)
  have hk : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp hx).1).2.2.2.1
  have hcoords := initial_sector_coordinates p hp F R K Z M hZ j
  obtain ⟨B,hB,hdec,hbound⟩ := ht p hp hcop hg hinj hc hpr F Ψ m r ray s Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) hZ hH
    (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) hΨ hs hk
    (fun x hx => (hcoords x hx).1) (fun x hx => (hcoords x hx).2.1)
    (fun x hx => (hcoords x hx).2.2.1) (fun x hx => (hcoords x hx).2.2.2)
  refine ⟨B,hB,?_,?_⟩
  · simpa only [X, initial_log_radial Z H (primeProductNorm p R) hZ.ne' hR.ne'] using hdec
  · simpa only [r, elementNorm, primeSubsetGenerator_norm_eq_productNorm] using hbound

end InitialMeanSquare

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

theorem sum_powerset_split {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→β) :
    (∑S∈F.powerset,f S)=∑A∈B.powerset,∑U∈(F\B).powerset,f (A∪U) := by
  have hsplit (S : Finset ι) : S∩B∪S\B=S := by
    ext i
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have he : (∑S∈F.powerset,f S)=
      ∑AU∈B.powerset ×ˢ (F\B).powerset,f (AU.1∪AU.2) := by
    apply Finset.sum_bij (fun S _ => (S∩B,S\B))
    · intro S hS
      rw [Finset.mem_product,Finset.mem_powerset,Finset.mem_powerset]
      refine ⟨Finset.inter_subset_right,?_⟩
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) (Finset.mem_sdiff.mp hi).1,(Finset.mem_sdiff.mp hi).2⟩
    · intro S hS T hT he
      have hi := congrArg (fun AU : Finset ι×Finset ι => AU.1∪AU.2) he
      simpa only [hsplit] using hi
    · intro AU hAU
      rcases Finset.mem_product.mp hAU with ⟨hA,hU⟩
      have hAB := Finset.mem_powerset.mp hA
      have hUFB := Finset.mem_powerset.mp hU
      refine ⟨AU.1∪AU.2,Finset.mem_powerset.mpr (Finset.union_subset (hAB.trans hB) (hUFB.trans Finset.sdiff_subset)),?_⟩
      apply Prod.ext <;> ext i
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_inter,Finset.mem_union]
        tauto
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_sdiff,Finset.mem_union]
        tauto
    · intro S hS
      rw [hsplit]
  simpa only [Finset.sum_product] using he

theorem sum_pair_split_cube {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→Finset ι→β) :
    (∑S∈F.powerset,∑T∈F.powerset,f S T)=
      ∑A₂∈B.powerset,∑A₁∈B.powerset,∑C∈(F\B).powerset,
        ∑N∈((F\B)\C).powerset,∑P∈((F\B)\C).powerset,
          if Disjoint N P then f ((A₂∪C)∪N) ((A₁∪C)∪P) else 0 := by
  rw [sum_powerset_split F B hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  simp_rw [sum_powerset_split F B hB]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  rw [sum_pair_eq_overlap]
  simp only [Finset.union_assoc]

end FiniteOverlapDecomposition

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

def canonicalSourceCoefficient (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏i∈S,p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f^4 * H S

theorem canonicalSourceCoefficient_union
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (D S : Finset ι) (hd : Disjoint D S) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f H (D∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) D *
      (columnCoefficient p hp hcop hg S *
        multiplicativeCoreColumn p Ψ m (fun U => H (D∪U)) S *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏i∈D,p i)^4 *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f^4) := by
  have hA := columnCoefficient_union_row_four p hp hcop hg hpr S D hd.symm
  rw [Finset.union_comm S D] at hA
  simp only [canonicalSourceCoefficient,hA,Finset.prod_union hd,map_mul,
    row_union _ hg D S hd,mask_union _ hg D S hd,mul_pow,multiplicativeCoreColumn]
  ring

theorem canonicalCube_pair_row
    (B C N P : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hcover : ∀ i∈B,0<v₁ i+v₂ i)
    (hCB : Disjoint C B) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N B) (hPB : Disjoint P B) (hNP : Disjoint N P)
    (z : O) :
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
      (((B.filter fun i => ε₂ i)∪C)∪N) z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
        (((B.filter fun i => ε₁ i)∪C)∪P) z *
      star (multiplicityRow (fun i => Ideal.span {p i}) hg B v₂ z^3) *
      multiplicityRow (fun i => Ideal.span {p i}) hg B v₁ z^3 =
    rowCoprimeMask (fun i => Ideal.span {p i})
      (C∪cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
    blockRow p hg ((N∪P)∪cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
      (threeBlockExponent N P (fun i => v₁ i+v₂ i) ε₁ ε₂) z := by
  have hA₁C : Disjoint (B.filter fun i => ε₁ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂C : Disjoint (B.filter fun i => ε₂ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₁P : Disjoint (B.filter fun i => ε₁ i) P := hPB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂N : Disjoint (B.filter fun i => ε₂ i) N := hNB.symm.mono_left (Finset.filter_subset _ _)
  have hCp : Disjoint C (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) :=
    hCB.mono_right (Finset.filter_subset _ _)
  have hsel : cubePairRow (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂ z =
      rowCoprimeMask (fun i => Ideal.span {p i}) (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
      blockRow p hg (cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
        (fun i => (conductorExponent (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i)).val) z := by
    exact cubePairRow_conductor_selection (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂
      (fun i hi => by have := hcover i hi;omega) z
  rw [row_union _ hg _ N (Finset.disjoint_union_left.mpr ⟨hA₂N,hNC.symm⟩),
    row_union _ hg _ P (Finset.disjoint_union_left.mpr ⟨hA₁P,hPC.symm⟩),
    row_union _ hg _ C hA₂C,row_union _ hg _ C hA₁C]
  simp only [star_mul]
  calc
    _ = (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg C z)*
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg C z)*
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N z)*
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P z)*
      cubePairRow (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂ z := by
        simp only [cubePairRow];ring
    _ = _ := by
      rw [ActualEisensteinCubic.finiteSquarefreeRow_self_pair (fun i => Ideal.span {p i}) hg C z,
        hsel,
        threeBlockRow_factor p hg N P B hNP hNB hPB,
        mask_union _ hg C _ hCp]
      ring

theorem canonicalSourceCoefficient_cube_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (B C S : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (hCB : Disjoint C B) (hSC : Disjoint S C) (hSB : Disjoint S B) :
    let A := B.filter (fun i => if negative then ε₂ i else ε₁ i)
    canonicalSourceCoefficient p hp hcop hg Ψ m f H ((A∪C)∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) (A∪C) *
      (columnCoefficient p hp hcop hg S *
        originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => H ((A∪C)∪U)))
          (∏i∈C,p i) f S) := by
  dsimp only
  have hAC : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) C :=
    hCB.symm.mono_left (Finset.filter_subset _ _)
  have hAS : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) S :=
    hSB.symm.mono_left (Finset.filter_subset _ _)
  rw [canonicalSourceCoefficient_union p hp hcop hg hpr Ψ m f H _ S
    (Finset.disjoint_union_left.mpr ⟨hAS,hSC.symm⟩)]
  have hA : (∏i∈B.filter (fun i => if negative then ε₂ i else ε₁ i),p i) =
      aLabel p B (if negative then ε₂ else ε₁) := by
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,aLabel,primeProduct,
      Finset.prod_filter,bit]
    all_goals
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> simp_all
  rw [Finset.prod_union hAC,hA]
  simp only [originalLabelColumn,cubeRadical,commonProduct_mask p hg hinj S B,ite_eq_left hSB,mul_one]
  ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalPairMode (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (d h : O) : ℂ :=
  (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
    ((K:ℂ)/(‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖:ℂ))*
    paperRadialFourier W (K*‖eisEmbedding h‖^2/
      (‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h

lemma canonicalPairMode_summable (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    Summable (canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d) := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  let t := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  have ht : 0<t := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hs : Summable (fun h : O => paperRadialFourier W (t*‖eisEmbedding h‖^2)*star (blockRow p hg S e h)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W t ht)
    intro h
    rw [norm_mul,norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (blockRow_norm_le_one p hg S e h)
  let a : ℂ := (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
    ((K:ℂ)/(‖eisEmbedding (∏i∈S,p i)‖:ℂ))*
    (star (columnCoefficient p hp hcop hg N*C₁ N)*(columnCoefficient p hp hcop hg P*C₂ P)*
    FiniteGaussPhase.canonicalProductGauss (fun i:S => p i.val) (fun i=>hp i.val)
      (columnPrimeCoprime p hcop S) (fun i=>hg i.val) (fun i=>e i.val))*blockRow p hg S e d
  apply (hs.mul_left a).congr
  intro h
  dsimp only [canonicalPairMode,threeGaussRowFactor,a,t,S,e]
  have ht' : K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂))*
      ‖eisEmbedding h‖^2 = K*‖eisEmbedding h‖^2/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) := by ring
  rw [ht']
  ring

lemma actualFirstKernel_summable (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    Summable (actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d) := by
  apply summable_sum
  intro N hN
  apply summable_sum
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    change Summable (canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d)
    exact
      canonicalPairMode_summable p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd
  · simp only [hNP,ite_false]
    exact summable_zero

theorem canonicalPair_first_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (M N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) :
    (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
      (star (columnCoefficient p hp hcop hg N*C₁ N)*(columnCoefficient p hp hcop hg P*C₂ P))*
      (∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i}) M z*
        blockRow p hg ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)
          (threeBlockExponent N P v ε₁ ε₂) z*W (‖eisEmbedding z‖^2/K)) =
    ∑D∈M.powerset,(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/
      (primeProductNorm p D:ℂ)*
      ∑'h:O,canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  have he : ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
    intro i hi
    by_cases hn:i∈N
    · simp [threeBlockExponent,hn]
    by_cases hp':i∈P
    · simp [threeBlockExponent,hn,hp']
    · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
      simp only [threeBlockExponent,ite_eq_right hn,ite_eq_right hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  have he6 : ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
    intro i hi
    unfold threeBlockExponent
    split_ifs <;> first | omega | exact ZMod.val_lt _
  rw [masked_block_radial_poisson_product p hp hinj hcop hg hc M _ _ he he6 W K hK]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro h
  dsimp only [canonicalPairMode,threeGaussRowFactor]
  rw [SecondPassArithmetic.primeSubsetGenerator_norm_eq_productNorm p D]
  simp only [primeProductNorm]
  ring

lemma tsum_actualFirstKernel (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    (∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)=
      ∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
        ∑'h:O,canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h else 0 := by
  have hs (N P : Finset ι) : Summable (fun h:O => if Disjoint N P then
      canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h else 0) := by
    by_cases hNP : Disjoint N P
    · simp only [hNP,ite_true]
      exact canonicalPairMode_summable p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd
    · simp only [hNP,ite_false]
      exact summable_zero
  change (∑'h:O,∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
      canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h else 0)=_
  rw [Summable.tsum_finsetSum (fun N hN => summable_sum (fun P hP => hs N P))]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Summable.tsum_finsetSum (fun P hP => hs N P)]
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs <;> simp

def disjointCanonicalSource (F M B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ K : ℝ) : ℂ :=
  ∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
    (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
      (star (columnCoefficient p hp hcop hg N*C₁ N)*(columnCoefficient p hp hcop hg P*C₂ P))*
      (∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i}) M z*
        blockRow p hg ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)
          (threeBlockExponent N P v ε₁ ε₂) z*W (‖eisEmbedding z‖^2/K)) else 0

theorem disjointCanonicalSource_poisson
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (F M B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) :
    disjointCanonicalSource p hp hcop hg F M B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K =
    ∑D∈M.powerset,(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/
      (primeProductNorm p D:ℂ)*
      ∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  simp_rw [tsum_actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK _
    (primeSubsetGenerator_ne_zero _ _)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    exact canonicalPair_first_poisson p hp hcop hg hinj hc M N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK
  · simp only [hNP,ite_false,mul_zero,Finset.sum_const_zero]

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open MixedCrossSeparation (columnCoefficient)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalCubeSourcePair (B S T : Finset ι) (v₁ v₂ : ι→ℕ)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  star (canonicalSourceCoefficient p hp hcop hg Ψ₁ m₁ f H₁ S)*
    canonicalSourceCoefficient p hp hcop hg Ψ₂ m₂ f H₂ T*
    ∑'z:O,(star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg T z*
      star (multiplicityRow (fun i=>Ideal.span {p i}) hg B v₂ z^3)*
      multiplicityRow (fun i=>Ideal.span {p i}) hg B v₁ z^3)*W (‖eisEmbedding z‖^2/K)

def canonicalCubeOuter (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) : ℂ :=
  star (canonicalSourceCoefficient p hp hcop hg Ψ₁ m₁ f (fun _=>1) (b.rightDivisor∪C))*
    canonicalSourceCoefficient p hp hcop hg Ψ₂ m₂ f (fun _=>1) (b.leftDivisor∪C)

def canonicalCubeResidual (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) : Finset ι→ℂ :=
  originalLabelColumn p hg b.support b.leftBit b.rightBit negative
    (multiplicativeCoreColumn p Ψ m (fun S=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪S)))
    (∏i∈C,p i) f

def canonicalCubeBeforePoisson (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    disjointCanonicalSource p hp hcop hg (pool\(b.support∪C))
      (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
      b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
      W (fun _=>1) (fun _=>1) 1 1 K

lemma cube_filter_left (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.leftBit i)=b.leftDivisor := by
  ext i
  simp only [CubeCoordinates.leftBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.1 hi)

lemma cube_filter_right (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.rightBit i)=b.rightDivisor := by
  ext i
  simp only [CubeCoordinates.rightBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.2 hi)

theorem canonicalCubeSourcePair_factor
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1)
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N P : Finset ι)
    (hCB : Disjoint C b.support) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N b.support) (hPB : Disjoint P b.support) (hNP : Disjoint N P)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeSourcePair p hp hcop hg b.support ((b.rightDivisor∪C)∪N) ((b.leftDivisor∪C)∪P)
      b.leftExponent b.rightExponent Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
    canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
      (star (columnCoefficient p hp hcop hg N*canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ N)*
        (columnCoefficient p hp hcop hg P*canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂ P))*
      ∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i})
        (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit) z*
        blockRow p hg ((N∪P)∪cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
          (threeBlockExponent N P (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) z*
        W (‖eisEmbedding z‖^2/K) := by
  have hN := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₁ m₁ f H₁
    b.support C N b.leftBit b.rightBit true hCB hNC hNB
  have hP := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₂ m₂ f H₂
    b.support C P b.leftBit b.rightBit false hCB hPC hPB
  simp only [Bool.false_eq_true,ite_true,ite_false,cube_filter_left b hb,cube_filter_right b hb] at hN hP
  have hz (z : O) := canonicalCube_pair_row p hg b.support C N P b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos hCB hNC hPC hNB hPB hNP z
  simp only [cube_filter_left b hb,cube_filter_right b hb] at hz
  simp only [canonicalCubeSourcePair,hN,hP,star_mul,canonicalCubeOuter,canonicalCubeResidual]
  simp only [Bool.false_eq_true,ite_true,ite_false]
  simp_rw [hz]
  ring

def canonicalCubeCorrelation (pool B : Finset ι) (v₁ v₂ : ι→ℕ)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑S∈pool.powerset,∑T∈pool.powerset,
    canonicalCubeSourcePair p hp hcop hg B S T v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K

theorem canonicalCubeCorrelation_eq_blocks
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (v₁ v₂ : ι→₀ℕ)
    (hB : v₁.support∪v₂.support⊆pool)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      ∑A₂∈(v₁.support∪v₂.support).powerset,∑A₁∈(v₁.support∪v₂.support).powerset,
        ∑C∈(pool\(v₁.support∪v₂.support)).powerset,
          canonicalCubeBeforePoisson p hp hcop hg pool ⟨v₁,v₂,A₁,A₂⟩ C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K := by
  unfold canonicalCubeCorrelation
  rw [FiniteOverlapDecomposition.sum_pair_split_cube pool _ hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  apply Finset.sum_congr rfl
  intro C hC
  let b : CubeCoordinates ι:=⟨v₁,v₂,A₁,A₂⟩
  have hb : b.Admissible:=⟨Finset.mem_powerset.mp hA₁,Finset.mem_powerset.mp hA₂⟩
  have hCB : Disjoint C b.support := Finset.disjoint_left.mpr (fun i hiC hiB =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hiC)).2 hiB)
  have hpool : (pool\(v₁.support∪v₂.support))\C=pool\(b.support∪C) := by
    ext i
    simp only [CubeCoordinates.support,b,Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hpool]
  change _=canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  simp only [canonicalCubeBeforePoisson,disjointCanonicalSource,Finset.mul_sum,one_mul]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    have hNC : Disjoint N C:=Finset.disjoint_left.mpr (fun i hiN hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_right _ hiC))
    have hPC : Disjoint P C:=Finset.disjoint_left.mpr (fun i hiP hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_right _ hiC))
    have hNB : Disjoint N b.support:=Finset.disjoint_left.mpr (fun i hiN hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_left _ hiB))
    have hPB : Disjoint P b.support:=Finset.disjoint_left.mpr (fun i hiP hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_left _ hiB))
    simpa only [mul_assoc,b,CubeCoordinates.support] using canonicalCubeSourcePair_factor p hp hcop hg hinj hpr b hb C N P
      hCB hNC hPC hNB hPB hNP Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  · simp only [hNP,ite_false,mul_zero]

theorem canonicalCubeBeforePoisson_eq_all_modes
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f *
      ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
        ∑'h:O,actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
          W (fun _=>1) (fun _=>1) 1 1 K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  unfold canonicalCubeBeforePoisson
  rw [disjointCanonicalSource_poisson p hp hcop hg hinj hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK]

lemma canonicalSourceCoefficient_norm_le_one
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ:O→*ℂ) (hΨ:∀u,‖Ψ u‖≤1) (m f:O) (S:Finset ι) :
    ‖canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _=>1) S‖≤1 := by
  have hm : ‖rowCoprimeMask (fun i=>Ideal.span {p i}) S m‖≤1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  simp only [canonicalSourceCoefficient,norm_mul,norm_pow,mul_one,
    columnCoefficient_norm_one p hp hcop hg hc,one_mul]
  calc
    ‖Ψ (∏i∈S,p i)‖*‖rowCoprimeMask (fun i=>Ideal.span {p i}) S m‖*
      ‖finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S f‖^4 ≤ (1:ℝ)*1*1^4 := by
      exact mul_le_mul
        (mul_le_mul (hΨ _) hm (norm_nonneg _) (by norm_num))
        (pow_le_pow_left₀ (norm_nonneg _) (finiteSquarefreeRow_norm_le_one _ hg _ _) 4)
        (pow_nonneg (norm_nonneg _) 4) (by norm_num)
    _ = 1 := by norm_num

lemma canonicalCubeOuter_norm_le_one
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (b:CubeCoordinates ι) (C:Finset ι) (Ψ₁ Ψ₂:O→*ℂ)
    (hΨ₁:∀u,‖Ψ₁ u‖≤1) (hΨ₂:∀u,‖Ψ₂ u‖≤1) (m₁ m₂ f:O) :
    ‖canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f‖≤1 := by
  simp only [canonicalCubeOuter,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (canonicalSourceCoefficient_norm_le_one p hp hcop hg hc Ψ₁ hΨ₁ m₁ f _)).trans
    (canonicalSourceCoefficient_norm_le_one p hp hcop hg hc Ψ₂ hΨ₂ m₂ f _)

end SecondPassArithmetic

end

end OAI
