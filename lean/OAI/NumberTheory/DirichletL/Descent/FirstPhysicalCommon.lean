import OAI.NumberTheory.DirichletL.Descent.FirstCommonProfile

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCommonCoefficient (C₁ C₂ : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (D U V : Finset ι) (h : Eis) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) U *
    (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) *
  (supportMobius (fun i => Ideal.span {p i}) V *
    (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V h))

def firstPhysicalCommonRows (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis) : ℂ :=
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius (fun i => Ideal.span {p i}) D *
      rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      ∑ U ∈ (F \ D).powerset, ∑ V ∈ (F \ D).powerset,
        firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
          ![A₁,A₂,C,‖eisEmbedding d‖^2,R,primeProductNorm p D,
            ‖eisEmbedding h‖^2,primeProductNorm p U,primeProductNorm p V] *
          firstCommonCoefficient p hg C₁ C₂ r D U V h

theorem actual_first_physical_common
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C K : ℝ) (d h : Eis) :
    (‖eisEmbedding d‖^2 : ℂ)⁻¹ *
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ Φ
          (fun y => W₁ (A₁*C*Real.exp y)) (fun y => W₂ (A₂*C*Real.exp y)) 1 1 K d h else 0) =
    (K:ℂ) * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      firstPhysicalCommonRows p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d)
        W₁ W₂ Φ A₁ A₂ C (primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)) K d h := by
  let R := primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)
  let H := fun N P : Finset ι => firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
    ![A₁,A₂,C,‖eisEmbedding d‖^2,R,1,‖eisEmbedding h‖^2,primeProductNorm p N,primeProductNorm p P]
  calc
    _ = (K:ℂ) * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        H N P*threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : Disjoint N P
      · simp only [hd,ite_true]
        simpa only [H,R,mul_assoc] using canonicalPairMode_whole_profile p hp hcop hg
          N P B hd (hFB.mono_left (Finset.mem_powerset.mp hN))
          (hFB.mono_left (Finset.mem_powerset.mp hP)) v ε₁ ε₂ C₁ C₂ W₁ W₂ Φ A₁ A₂ C K d h
      · simp [hd]
    _ = _ := by
      rw [actual_first_gauss_coupled_reindex p hp hcop hg hinj hc hpr F B hFB]
      rw [mul_assoc]
      apply congrArg (fun z : ℂ => (K:ℂ)*(cubeBaseFactor p hp hg B v ε₁ ε₂ d h*z))
      unfold firstCoupledRayColumns firstPhysicalCommonRows
      apply Finset.sum_congr rfl
      intro r hr
      apply congrArg (fun z : ℂ => crossCoeff r.1 r.2*z)
      apply Finset.sum_congr rfl
      intro D hD
      apply congrArg (fun z : ℂ => supportMobius (fun i => Ideal.span {p i}) D *
        rowCoprimeMask (fun i => Ideal.span {p i}) D h*z)
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      have hDU : Disjoint D U := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
      have hDV : Disjoint D V := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
      dsimp only [H]
      rw [firstNormProfile_actual_common p hp D U V hDU hDV]
      simp only [firstCommonCoefficient,R,mul_assoc]

end
end SevenEighths.InverseMoment

end OAI
