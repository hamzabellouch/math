import OAI.NumberTheory.DirichletL.Descent.FirstRetainedPhysical
import OAI.NumberTheory.DirichletL.Descent.FirstFamilyToSecond

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def retainedCubeWeight (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ)
    (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (x : Ideal O×O) : ℂ :=
  a x * canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1) *
    cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2

theorem retainedCubeWeight_norm
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (x : Ideal O×O) :
    ‖retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a x‖≤‖a x‖ := by
  simp only [retainedCubeWeight,norm_mul]
  calc
    _ ≤ ‖a x‖*1*1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _) (norm_nonneg _))
        (cubeBaseFactor_norm_le_one p hp hcop hg hc _ _ _ _ _ _)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

include hp in
theorem retained_physical_row_support (b : CubeCoordinates ι) (x : Ideal O×O) (hx : x.1≠0)
    (Y : ℝ) (hcut : x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y) :
    DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) x ∈
        nonzeroChildFrequencyBall 1 Y := by
  have hh := (mem_nonzeroChildFrequencyBall _
    (firstPhysicalMultiplier_ne_zero p hp _ _ _ _ _ x.1 hx) _ _).mp hcut
  apply (mem_nonzeroChildFrequencyBall 1 one_ne_zero _ _).mpr
  simpa only [one_mul,firstPhysicalMultiplier_row] using hh

theorem retained_cube_energy_to_second (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (source : Finset (Ideal O×O)) (Γ Y : ℝ),0≤Γ → 0<Y →
      (∀ x∈source,Squarefree x.1) → (∀ x∈source,x.1≠0) → (∀ x∈source,‖a x‖≤Γ) →
      (∀ x∈source,x.2∈nonzeroChildFrequencyBall
        (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y) →
      ∀ (negative : Bool) (H : Finset ι→ℂ) (selector : Finset ι→ℂ)
        (ω : ℝ→ℂ) (X t : ℝ),0<X →
      let Ψ := if negative then Ψ₁ else Ψ₂
      let m := if negative then m₁ else m₂
      let Hshift := fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)
      let w := retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a
      firstFamilyEnergy p hg source F (fun _=>selector)
        (fun x=>firstOldLabelCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (multiplicativeCoreColumn p Ψ m Hshift)
          (∏i∈C,p i) d x.1) w negative ω X t Prod.snd ≤
      Γ*K*Y^ε*((32*512)*∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
          ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
          (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m Hshift ω X (∏i∈C,p i) d core t Y).re) := by
  obtain ⟨K,hK,hstep⟩ := first_family_original_to_second ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a source Γ Y hΓ hY
    hs hn ha hcut negative H selector ω X t hX Ψ m Hshift w
  apply hstep p hp hinj hcop hg hc hpr F b.support selector _ _ _ b.support_pos negative Ψ m
    (by intro u; cases negative
        · exact hΨ₂ u
        · exact hΨ₁ u) Hshift ω X t hX (∏i∈C,p i) d source
    (nonzeroChildFrequencyBall 1 Y) w Γ Y hΓ hY hs
  · intro x hx
    exact retained_physical_row_support p hp b x (hn x hx) Y (hcut x hx)
  · intro z hz
    exact (Finset.mem_erase.mp hz).1
  · intro z hz
    have hb := ((mem_nonzeroChildFrequencyBall 1 one_ne_zero Y z).mp hz).2
    simpa only [one_mul,eisEmbedding_norm_sq_eq_absNorm_span] using hb
  · intro x hx
    exact (retainedCubeWeight_norm p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a x).trans (ha x hx)

end
end SevenEighths.InverseMoment

end OAI
