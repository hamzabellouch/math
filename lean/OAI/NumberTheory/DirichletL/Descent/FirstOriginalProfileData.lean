import OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceEnergy
import OAI.NumberTheory.DirichletL.Descent.PriorityProfile
import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsCells

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open CompletedHeight FourierBridge
local notation "O" => ActualEisensteinCubic.O
abbrev OriginalIndex (ι : Type*) := Σ _ : FirstOriginalOuter ι,Ideal O×O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def leftNorm (x : OriginalIndex ι) : ℝ := ‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2
def rightNorm (x : OriginalIndex ι) : ℝ := ‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2
def commonNorm (x : OriginalIndex ι) : ℝ := primeProductNorm p x.1.2.1
def activeNorm (x : OriginalIndex ι) : ℝ := primeProductNorm p (cubeActiveSupport x.1.1.support
  (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)
def divisorElement (k : FirstOriginalOuter ι) : O := primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2

include hp in
theorem original_source_positive (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) :
    ∀x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      0<leftNorm p x ∧ 0<rightNorm p x ∧ 0<commonNorm p x ∧ 0<activeNorm p x ∧
      divisorElement p x.1≠0 ∧ x.2.2≠0 := by
  intro x hx
  have hm := (Finset.mem_sigma.mp hx).2
  have hk := ((mem_firstRetainedSource p labels x.1.1 Y x.2).mp hm).2
  refine ⟨?_,?_,primeProductNorm_pos p hp _,primeProductNorm_pos p hp _,?_,(Finset.mem_erase.mp hk).1⟩
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero
      (primeProduct_ne_zero p hp _ _)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero
      (primeProduct_ne_zero p hp _ _)))
  · exact primeSubsetGenerator_ne_zero _ _

include hp in
theorem original_source_norms_ge_one (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) :
    ∀x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      ∀i,1≤InverseMomentFirstChildWindows.sourceNorms (leftNorm p) (rightNorm p) (commonNorm p)
        (activeNorm p) (fun x=>divisorElement p x.1) (fun x=>x.2.2) x i := by
  intro x hx
  have hh := original_source_positive p hp pool Q labels Y x hx
  apply InverseMomentFirstChildWindows.sourceNorms_ge_one
  · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact hh.2.2.2.2.1
  · exact hh.2.2.2.2.2

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem original_weight_bound (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Γ Y : ℝ)
    (hΓ : 0≤Γ) (hβ : ∀I∈labels,∀v∈Q,‖β I v‖≤Γ) :
    ∀k∈firstOriginalOuter pool Q,∀x∈firstRetainedSource p labels k.1 Y,
      ‖firstOriginalWeight p β R k x‖≤Γ^2 := by
  intro k hk x hx
  have hb := (mem_firstOriginalOuter pool Q k).mp hk
  have hf := ((mem_firstRetainedSource p labels k.1 Y x).mp hx).1
  exact (firstOriginalWeight_norm_le p β R k x).trans
    (reopenedPairCoefficient_bound Q labels β Γ hΓ hβ k.1 hb.1 k.2.1 x.1 hf)

theorem actual_old_profile (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om⊆Set.Icc a b) (theta x : ℝ) (hx : 0<x) :
    InverseMomentFirstProfileUniform.positiveSource (priorityLogWindow om a b ha hs false) 1 theta x=
      normTwistedSource om theta x ∧
    InverseMomentFirstProfileUniform.positiveSource (priorityLogWindow om a b ha hs true) 1 (-theta) x=
      star (normTwistedSource om theta x) := by
  constructor
  · simp [InverseMomentFirstProfileUniform.positiveSource,priorityLogWindow,
      CubicReflectionKernel.logSchwartz_apply,Real.exp_log hx,normTwistedSource]
  · simp [InverseMomentFirstProfileUniform.positiveSource,priorityLogWindow,
      SecondPassIntegration.conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,
      Real.exp_log hx,normTwistedSource,SecondPassIntegration.logPhase_conjugate]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
