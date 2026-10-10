import OAI.NumberTheory.DirichletL.Descent.FullProfile

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def firstNormProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (q : Fin 9 → ℝ) : ℂ :=
  (∏ i, V i (Real.log (q i))) * W₁ (q 0*q 2*q 5*q 7) *
    W₂ (q 1*q 2*q 5*q 8) *
    paperRadialFourier Φ (R*q 6/(q 3*q 4*(q 5)^2*q 7*q 8)) /
      ((q 3:ℂ)*(Real.sqrt (q 4):ℂ)*(q 5:ℂ)*
        (Real.sqrt (q 7):ℂ)*(Real.sqrt (q 8):ℂ))

theorem firstPoissonProfile_log (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (q : Fin 9 → ℝ) (hq : ∀ i, 0 < q i) :
    firstPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) =
      firstNormProfile W₁ W₂ Φ V R q := by
  have hl : (∑ i, firstLeftSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 5)+Real.log (q 7) := by
    simp [Fin.sum_univ_succ,firstLeftSlope]; ring
  have hr : (∑ i, firstRightSlope i * Real.log (q i)) =
      Real.log (q 1)+Real.log (q 2)+Real.log (q 5)+Real.log (q 8) := by
    simp [Fin.sum_univ_succ,firstRightSlope]; ring
  have hk : (∑ i, firstKernelSlope i * Real.log (q i)) =
      Real.log (q 6) - (Real.log (q 3)+Real.log (q 4)+Real.log (q 5)+
        Real.log (q 5)+Real.log (q 7)+Real.log (q 8)) := by
    simp [Fin.sum_univ_succ,firstKernelSlope]; ring
  unfold firstPoissonProfile firstNormProfile
  rw [hl,hr,hk]
  simp only [Real.exp_add,Real.exp_sub,Real.exp_log (hq _)]
  rw [show R*(q 6/(q 3*q 4*q 5*q 5*q 7*q 8)) =
    R*q 6/(q 3*q 4*(q 5)^2*q 7*q 8) from by ring]
  simp only [Fin.prod_univ_succ,firstRootWindows,inverseNormWindow,inverseRootWindow,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,Real.exp_log (hq _),
    Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  norm_num
  ring

theorem canonicalPairMode_whole_profile {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C K : ℝ) (d h : Eis) :
    (‖eisEmbedding d‖^2 : ℂ)⁻¹ *
      canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ Φ
        (fun y => W₁ (A₁*C*Real.exp y)) (fun y => W₂ (A₂*C*Real.exp y)) 1 1 K d h =
    (K:ℂ) * firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
      ![A₁,A₂,C,‖eisEmbedding d‖^2,primeProductNorm p (cubeActiveSupport B v ε₁ ε₂),
        1,‖eisEmbedding h‖^2,primeProductNorm p N,primeProductNorm p P] *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) :=
    hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) :=
    hPB.mono_right (Finset.filter_subset _ _)
  have hs (S : Finset ι) : ‖eisEmbedding (∏ i ∈ S,p i)‖ =
      Real.sqrt (primeProductNorm p S) := by
    simp only [primeProductNorm,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  unfold canonicalPairMode firstNormProfile
  simp only [columnLog,div_one,Real.exp_log (primeProductNorm_pos p hp _),
    Matrix.cons_val_zero,Fin.isValue,
    Finset.prod_const_one,one_mul,]
  rw [primeProductNorm_union p (N ∪ P) _ (Finset.disjoint_union_left.mpr ⟨hNC,hPC⟩),
    primeProductNorm_union p N P hNP]
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hNC,hPC⟩),Finset.prod_union hNP]
  simp only [map_mul,norm_mul,hs]
  rw [show K*‖eisEmbedding h‖^2 /
      (‖eisEmbedding d‖^2*(primeProductNorm p N*primeProductNorm p P*
        primeProductNorm p (cubeActiveSupport B v ε₁ ε₂))) =
      K*‖eisEmbedding h‖^2 /
      (‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*
        primeProductNorm p N*primeProductNorm p P) from by ring]
  push_cast
  ring_nf

end
end SevenEighths.InverseMoment

end OAI
