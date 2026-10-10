import OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller
import OAI.NumberTheory.DirichletL.Descent.FirstRetainedFamily

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight InversePrincipalEnergy RayFourExpansion
open InverseSecondPrincipalCaller
local notation "Eis" => ActualEisensteinCubic.O

theorem first_retained_radius_one {ι : Type*} [DecidableEq ι]
    (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (labels : Finset (Ideal Eis)) (b : CubeCoordinates ι) (Y : ℝ)
    (hlabels : ∀ f∈labels,f≠0) (hne : (firstRetainedSource p labels b Y).Nonempty) : 1≤Y := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨hf,hk⟩ := (mem_firstRetainedSource p labels b Y x).mp hx
  have hm : firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1≠0 := by
    unfold firstPhysicalMultiplier
    exact mul_ne_zero (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero _ (hlabels _ hf)))
      (primeProduct_ne_zero p hp _ _)
  by_contra hy
  rw [nonzeroChildFrequencyBall_empty _ hm Y (lt_of_not_ge hy)] at hk
  exact Finset.notMem_empty _ hk

theorem firstCore_variable_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y : ℝ) (R : Finset ι→Finset ι→ℝ),b≤Real.exp M → 0<X → 1≤Y → (∀ G E,0≤R G E) →
      let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (fun G E=>secondPhysicalCutoff p d (R G E) G E)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (fun G E=>secondPhysicalMask p d (R G E) G E)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists coeff hslots hcoeff F D B v ε₁ ε₂ hD
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR H Ψ₀ m₀ c₀
  let V := principalWindow om a b ha hs negative t
  let H₀ := markedRadial p slots lists coeff ∅ V X
  have he (U : Finset ι) : secondInputCoefficient p hg Ψ₀ m₀ c₀ d H U=
      secondInputCoefficient p hg Ψ₀ m₀ c₀ d H₀ U :=
    firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX Ψ₀
      (m*b0Label p B v ε₁ ε₂) c₀ d
  rw [zero_congr_input p hg F Ψ₀ m₀ c₀ d H H₀ he,
    restoration_congr_input p hp hg hinj F Ψ₀ m₀ c₀ d H H₀ he]
  have hz : ∀ G∈F.powerset,∀ E∈G.powerset,(0:Eis)∈secondPhysicalCutoff p d (R G E) G E := by
    intro G hG E hE
    exact zero_mem_childFrequencyBall _ (mul_ne_zero hd (primeSubsetGenerator_ne_zero _ _)) _ (hR G E)
  have hbnd := hbound p hp hg hinj hcop slots lists coeff hslots hcoeff ∅ F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z)) m₀ c₀ d V W X M Y
    hX hY (principalWindow_upper om a b ha hs M hb negative t)
    (fun G E=>secondPhysicalCutoff p d (R G E) G E) hz
    (fun G E=>secondPhysicalMask p d (R G E) G E)
    (fun G _ E k=>secondPhysicalMask_norm_le_one p d (R G E.val) G E.val k.val)
  simpa only [H₀,V,Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero] using hbnd

end SevenEighths.InverseMoment

end

end OAI
