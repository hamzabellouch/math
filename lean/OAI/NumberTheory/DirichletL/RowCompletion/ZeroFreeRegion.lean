import OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding

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

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance collectionUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_four_mul_value
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).value
      W X 1 completedRamifiedStep k=
        compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ J W X := by
  let : ∀h:Eis⧸Ideal.span {reflectionConductor q},
      Fintype (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue :=
    fun h=>Fintype.ofFinite _
  let d:=reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
  let f:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      (d.branch (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq)
        ⟨h,rho,u⟩,encodeReflectionSix ⟨B,l⟩)).value W X 1 completedRamifiedStep k
  let g:=fun (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
  let chosen:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))=>
      (data q m hm rows R F hF hrows v J).sourceRowResidue
        (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
        h (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
        (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J)
  let α:=fun h=>sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J
  let shape:=fun h B=>sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J
  let w:=FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q)
  have hbranch:∀h rho u B l,4*f h rho u B l=
      if rho=chosen h B then α h*shape h B*g h u B l else 0 := by
    intro h rho u B l
    exact reflectedFiber_encoded_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound
      J h rho u B l W lo hi hlo hsupp hW X hX hK hk
  have hvalue:d.value W X 1 completedRamifiedStep k=
      ∑h,∑rho,∑u,∑B,w B*∑l,f h rho u B l := by
    rw [reflectedFiber_value q hq m hm rows R F hR hF hrows v K Ψ hΨ W X k]
    exact sum_fixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq) _
  change 4*d.value W X 1 completedRamifiedStep k=_
  rw [hvalue]
  exact finite_selected_branch_collection f g chosen α shape w hbranch

theorem completedT_eq_reflectedFiber_idealValue
    (Ψ:Eis→*ℂ)
    (hΨperiod:CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨ:∀n,‖Ψ n‖≤1)
    (K:ℝ) (hshell:∀I∈rows,K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      (4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
        (reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).idealValue W X 1 completedRamifiedStep
          (rowResidualPart J.val (maskIdeal q m F)) := by
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,(hshell I hI).2⟩) J
  have hs:=residual_shell q m rows R F K (fun I hI=>⟨hrows I hI,hshell I hI⟩) J
  have he:=reflectedFiber_four_mul_value q hq m hm rows R F hR hF hrows v K Ψ hΨ
    (fun I hI=>(hshell I hI).2) J W lo hi hlo hsupp hW X hX hs.1 hs.2
  rw [completedT_eq_compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ hΨperiod hΨ
    J W lo hi hlo hsupp hW X hX,←he]
  have hid:rowResidualPart J.val (maskIdeal q m F)=k.val:=rfl
  rw [hid,ReflectedFiberData.idealValue_at]
  ring

end CanonicalRowCompletion.ActualFiber

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def actualReflectionScale : ℂ :=
  4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar

theorem actual_fixedShellModels (q:ℕ) (hq:q≠0) (χ:DirichletCharacter ℂ q) :
    HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      actualReflectionScale 1 completedRamifiedStep
      (fixedCuspLevelBound (reflectionConductor q)) := by
  let : Finite (Eis⧸Ideal.span {reflectionConductor q}) :=
    ConcreteTraceCRT.finite_quotient_span (reflectionConductor_ne_zero q hq)
  let : Fintype (Eis⧸Ideal.span {reflectionConductor q}) := Fintype.ofFinite _
  apply fixedShellModels_of_actual_fiber_identity q hq χ actualReflectionScale
  intro Ψ hperiod hnorm m hm F hF u W a b ha hs hW K X hK hX rows hrows R hR J
  exact ActualFiber.completedT_eq_reflectedFiber_idealValue q hq m hm rows R F
    (hrows R hR).1 hF (fun I hI=>(hrows I hI).1) u Ψ hperiod hnorm K
    (fun I hI=>(hrows I hI).2) J W a b ha hs hW X hX

theorem exists_actual_fixedShellModels (q:ℕ) [NeZero q] (χ:DirichletCharacter ℂ q) :
    ∃(rays:ℕ) (scale:ℂ),
      HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
        rays scale 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) := by
  exact ⟨fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q (NeZero.ne q)),
    actualReflectionScale,actual_fixedShellModels q (NeZero.ne q) χ⟩

end

theorem dirichletTarget_unconditional : ShortDraft.DirichletTarget :=
  dirichletTarget_of_reflection_shells exists_actual_fixedShellModels

end CanonicalRowCompletion

namespace ShortDraft

theorem dirichlet_LFunction_ne_zero (q:ℕ) [NeZero q]
    (χ:DirichletCharacter ℂ q) (s:ℂ)
    (hs:(23/24:ℝ)<s.re) (hpole:¬(χ=1 ∧ s=1)) :
    DirichletCharacter.LFunction χ s≠0 :=
  CanonicalRowCompletion.dirichletTarget_unconditional q χ s hs hpole

theorem riemannZeta_ne_zero_of_re_gt (s:ℂ)
    (hs:(23/24:ℝ)<s.re) (hs1:s≠1) : riemannZeta s≠0 :=
  zeta_nonvanishing_of_dirichletTarget
    CanonicalRowCompletion.dirichletTarget_unconditional s hs hs1

end ShortDraft

end

end OAI
