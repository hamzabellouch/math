import OAI.NumberTheory.DirichletL.Descent.FirstNominal
import OAI.NumberTheory.DirichletL.Descent.FirstCoupledReindex

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem firstNormProfile_common_support (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C D R T H X₁ X₂ K : ℝ) (hT : 0 ≤ T) :
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K ![A₁,A₂,C,D,R,1,H,T*X₁,T*X₂] =
      firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K ![A₁,A₂,C,D,R,T,H,X₁,X₂] := by
  have hroot : Real.sqrt (T*X₁)*Real.sqrt (T*X₂) =
      T*Real.sqrt X₁*Real.sqrt X₂ := by
    rw [Real.sqrt_mul hT,Real.sqrt_mul hT]
    calc
      _ = (Real.sqrt T)^2*Real.sqrt X₁*Real.sqrt X₂ := by ring
      _ = _ := by rw [Real.sq_sqrt hT]
  unfold firstNormProfile
  simp only [Finset.prod_const_one,one_mul,Matrix.cons_val_zero,
    Fin.isValue,]
  change W₁ (A₁*C*1*(T*X₁))*W₂ (A₂*C*1*(T*X₂))*
      EisensteinSchwartzPoisson.paperRadialFourier Φ (K*H/(D*R*1^2*(T*X₁)*(T*X₂))) /
        ((D:ℂ)*(Real.sqrt R:ℂ)*(1:ℂ)*(Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ)) =
    W₁ (A₁*C*T*X₁)*W₂ (A₂*C*T*X₂)*
      EisensteinSchwartzPoisson.paperRadialFourier Φ (K*H/(D*R*T^2*X₁*X₂)) /
        ((D:ℂ)*(Real.sqrt R:ℂ)*(T:ℂ)*(Real.sqrt X₁:ℂ)*(Real.sqrt X₂:ℂ))
  simp only [mul_one,one_pow]
  rw [show A₁*C*(T*X₁) = A₁*C*T*X₁ from by ring,
    show A₂*C*(T*X₂) = A₂*C*T*X₂ from by ring,
    show K*H/(D*R*(T*X₁)*(T*X₂)) = K*H/(D*R*T^2*X₁*X₂) from by ring]
  have hc : (Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ) =
      (T:ℂ)*(Real.sqrt X₁:ℂ)*(Real.sqrt X₂:ℂ) := by exact_mod_cast hroot
  rw [show (D:ℂ)*(Real.sqrt R:ℂ)*(Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ) =
    (D:ℂ)*(Real.sqrt R:ℂ)*((Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ)) from by ring,hc]
  ring

theorem firstNormProfile_actual_common {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) (D U V : Finset ι)
    (hDU : Disjoint D U) (hDV : Disjoint D V)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C E R H K : ℝ) :
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
      ![A₁,A₂,C,E,R,1,H,primeProductNorm p (D∪U),primeProductNorm p (D∪V)] =
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
      ![A₁,A₂,C,E,R,primeProductNorm p D,H,primeProductNorm p U,primeProductNorm p V] := by
  rw [primeProductNorm_union p D U hDU,primeProductNorm_union p D V hDV]
  exact firstNormProfile_common_support W₁ W₂ Φ A₁ A₂ C E R _ H _ _ K
    (primeProductNorm_pos p hp D).le

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCoupledRayColumns (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (H : Finset ι → Finset ι → ℂ) (h : Eis) : ℂ :=
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      ∑ U ∈ (F \ D).powerset, ∑ V ∈ (F \ D).powerset,
        H (D ∪ U) (D ∪ V) *
        star (supportMobius (fun i => Ideal.span {p i}) U *
          (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) *
        (supportMobius (fun i => Ideal.span {p i}) V *
          (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V h))

theorem actual_first_gauss_coupled_reindex
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (H : Finset ι → Finset ι → ℂ) (d h : Eis) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      H N P * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      firstCoupledRayColumns p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d) H h := by
  rw [firstCoupledRayColumns, ← first_quadratic_coupled_reindex p hp hinj hg hc]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hd : Disjoint N P
  · simp only [hd,ite_true]
    rw [threeGaussRowFactor_eq_ray_columns p hp hcop hg hc hpr N P B hd
      (hFB.mono_left (Finset.mem_powerset.mp hN)) (hFB.mono_left (Finset.mem_powerset.mp hP))]
    ring
  · simp [hd]

end
end SevenEighths.InverseMoment

end OAI
