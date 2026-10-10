import OAI.NumberTheory.DirichletL.Descent.SecondProfileIdentity

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondSourcePairKernel_mark_factors {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (A₁ A₂ : Finset ι) (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (S T : Finset ι) :
    secondSourcePairKernel p e k
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*H₁ U)
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*H₂ U) W Y S T =
      star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)) * primeMark slots₂ lists₂ a₂ (A₂ ∪ T) *
        secondSourcePairKernel p e k H₁ H₂ W Y S T := by
  simp only [secondSourcePairKernel,star_mul]
  ring

theorem secondChildKernelPair_whole_profile {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F G V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂
      m r c d e k (-k)
      (secondSourcePairKernel p e k
        (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*W₁ (primeProductNorm p G*primeProductNorm p U))
        (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*W₂ (primeProductNorm p G*primeProductNorm p U)) Φ Y) =
    ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
      (star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V,p i)
        (d*e*k) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V,p i)
          (d*e*(-k)) (fun _ => 1) M) *
      (star (primeMark slots₁ lists₁ a₁ (A₁ ∪ (V ∪ N))) *
        primeMark slots₂ lists₂ a₂ (A₂ ∪ (V ∪ M))) *
      secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
        ![primeProductNorm p G,‖eisEmbedding e‖^2,primeProductNorm p V,
          ‖eisEmbedding k‖^2,primeProductNorm p N,primeProductNorm p M] := by
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondSourcePairKernel_mark_factors]
  have hp := secondSourcePairKernel_profile p hp G V N M hVN hVM e k W₁ W₂ Φ Y
  rw [← hp]
  ring

end
end SevenEighths.InverseMoment

end OAI
