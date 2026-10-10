import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.SobolevSpace

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma derivative_basis (b : OrthonormalBasis κ ℝ E) (v : E) (u : 𝓢'(E,F)) :
    ∂_{v} u = ∑ i, ⟪b i,v⟫ • ∂_{b i} u := by
  have he := b.sum_repr v
  conv_lhs => rw [← he]
  simp only [lineDerivOp_left_sum,lineDerivOp_left_smul,OrthonormalBasis.repr_apply_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma scalar_product_smul (g : 𝓢(E,ℂ)) (r : ℝ) (u : 𝓢'(E,F)) :
    smulLeftCLM F ((r • g) : 𝓢(E,ℂ)) u = r • smulLeftCLM F g u := by
  ext φ
  simp only [smulLeftCLM_apply_apply,_root_.smul_apply]
  have he : SchwartzMap.smulLeftCLM ℂ (r • g) φ = r • SchwartzMap.smulLeftCLM ℂ g φ := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (r • g).hasTemperateGrowth]
    simp only [_root_.smul_apply]
    rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
    exact smul_assoc r (g x) (φ x)
  rw [he]
  exact ContinuousLinearMap.map_smul_of_tower (show 𝓢(E,ℂ) →L[ℂ] F from u) r _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma scalar_product_sum {τ : Type*} [Fintype τ] (g : τ → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    smulLeftCLM F (∑ i,g i : 𝓢(E,ℂ)) u = ∑ i,smulLeftCLM F (g i) u := by
  ext φ
  simp only [smulLeftCLM_apply_apply,_root_.sum_apply]
  have he : SchwartzMap.smulLeftCLM ℂ (∑ i,g i : 𝓢(E,ℂ)) φ = ∑ i,SchwartzMap.smulLeftCLM ℂ (g i) φ := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (∑ i,g i).hasTemperateGrowth]
    simp only [_root_.sum_apply]
    simp only [SchwartzMap.smulLeftCLM_apply_apply (g _).hasTemperateGrowth,Finset.sum_smul]
  rw [he,map_sum]

def directionalPrincipal (v : ι → E) (g : ι → ι → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  ∑ i, ∑ j,smulLeftCLM F (g i j) (∂_{v i} (∂_{v j} u))

def principalInBasis (b : OrthonormalBasis κ ℝ E) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (k l : κ) : 𝓢(E,ℂ) :=
  ∑ i, ∑ j, (⟪b k,v i⟫ * ⟪b l,v j⟫) • g i j

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma directionalPrincipal_basis (b : OrthonormalBasis κ ℝ E) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    directionalPrincipal v g u = directionalPrincipal b (principalInBasis b v g) u := by
  unfold directionalPrincipal principalInBasis
  conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; rw [derivative_basis b (v i),derivative_basis b (v j)]
  simp only [scalar_product_sum,scalar_product_smul]
  simp only [lineDerivOp_sum,lineDerivOp_smul,map_sum,
    ContinuousLinearMap.map_smul_of_tower,Finset.smul_sum,smul_smul]
  let H := fun (i j : ι) (k l : κ) => (⟪b k,v i⟫*⟪b l,v j⟫) •
    smulLeftCLM F (g i j) (∂_{b k} (∂_{b l} u))
  change (∑ i, ∑ j, ∑ k, ∑ l,H i j k l) = ∑ k, ∑ l, ∑ i, ∑ j,H i j k l
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l,H i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, ∑ l,H i j k l := by rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ l, ∑ j,H i j k l := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

end TamingCompatibility.HilbertSobolev

end

end OAI
