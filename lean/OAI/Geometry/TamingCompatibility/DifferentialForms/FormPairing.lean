import Mathlib

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
namespace TamingCompatibility.FormMetric
open RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

def sharp : (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ⋀[ℝ]^k E :=
  (InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm.toLinearEquiv.toLinearMap ∘ₗ
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    exteriorPower.alternatingMapLinearEquiv.toLinearMap ∘ₗ
    ContinuousAlternatingMap.toAlternatingMapLinear

lemma sharp_inner (α : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    ⟪sharp α, exteriorPower.ιMulti ℝ k v⟫ = α v := by
  simp [sharp, InnerProductSpace.toDual_symm_apply]

lemma sharp_injective : Function.Injective (sharp (E := E) (k := k)) := by
  intro α β h
  ext v
  simpa only [sharp_inner] using congrArg (fun a => ⟪a, exteriorPower.ιMulti ℝ k v⟫) h

def pairing (α β : E [⋀^Fin k]→L[ℝ] ℝ) : ℝ := ⟪sharp α, sharp β⟫

lemma pairing_symm (α β : E [⋀^Fin k]→L[ℝ] ℝ) : pairing β α = pairing α β :=
  real_inner_comm _ _

lemma pairing_self_nonneg (α : E [⋀^Fin k]→L[ℝ] ℝ) : 0 ≤ pairing α α :=
  real_inner_self_nonneg

lemma pairing_self_eq_zero {α : E [⋀^Fin k]→L[ℝ] ℝ} : pairing α α = 0 ↔ α = 0 := by
  rw [pairing, inner_self_eq_zero]
  exact ⟨fun h => sharp_injective (h.trans (map_zero sharp).symm), fun h => by simp [h]⟩

def pairLeft : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
def pairRight : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

def wedgeFamily (b : OrthonormalBasis (Fin 4) ℝ E) (i : Fin 6) : ⋀[ℝ]^2 E :=
  exteriorPower.ιMulti ℝ 2 ![b (pairLeft i), b (pairRight i)]

lemma wedgeFamily_orthonormal (b : OrthonormalBasis (Fin 4) ℝ E) :
    Orthonormal ℝ (wedgeFamily b) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [wedgeFamily, exteriorPower.inner_ιMulti_ιMulti, Matrix.det_fin_two]
  have hb := orthonormal_iff_ite.mp b.orthonormal
  fin_cases i <;> fin_cases j <;>
    simp [pairLeft, pairRight, hb]

def wedgeBasis (b : OrthonormalBasis (Fin 4) ℝ E) :
    OrthonormalBasis (Fin 6) ℝ (⋀[ℝ]^2 E) :=
  OrthonormalBasis.mk (wedgeFamily_orthonormal b)
    ((wedgeFamily_orthonormal b).linearIndependent.span_eq_top_of_card_eq_finrank (by
      rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b.toBasis]
      norm_num [Nat.choose])).ge

lemma wedgeBasis_apply (b : OrthonormalBasis (Fin 4) ℝ E) (i : Fin 6) :
    wedgeBasis b i = wedgeFamily b i := by
  simp only [wedgeBasis, OrthonormalBasis.coe_mk]

lemma wedgeBasis_repr (b : OrthonormalBasis (Fin 4) ℝ E)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) (i : Fin 6) :
    (wedgeBasis b).repr (sharp α) i = α ![b (pairLeft i), b (pairRight i)] := by
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm, wedgeBasis_apply]
  exact sharp_inner _ _

lemma pairing_eq_sum (b : OrthonormalBasis (Fin 4) ℝ E)
    (α β : E [⋀^Fin 2]→L[ℝ] ℝ) :
    pairing α β = ∑ i, α ![b (pairLeft i), b (pairRight i)] *
      β ![b (pairLeft i), b (pairRight i)] := by
  have h := (wedgeBasis b).repr.inner_map_map (sharp α) (sharp β)
  rw [pairing, ← h]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, wedgeBasis_repr]
  congr 1
  ext i
  exact mul_comm _ _

end TamingCompatibility.FormMetric

namespace TamingCompatibility.FormMetric
open RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

instance formFiniteDimensional : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective (sharp (E := E) (k := k)) sharp_injective

def sharpCLM : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k E :=
  LinearMap.toContinuousLinearMap sharp

def pairingCLM : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp sharpCLM sharpCLM

lemma pairingCLM_apply (α β : E [⋀^Fin k]→L[ℝ] ℝ) : pairingCLM (E := E) (k := k) α β = pairing α β := rfl

lemma pairing_add_left (α β γ : E [⋀^Fin k]→L[ℝ] ℝ) :
    pairing (α+β) γ = pairing α γ + pairing β γ := by
  simp only [pairing, map_add, inner_add_left]

lemma pairing_smul_left (c : ℝ) (α β : E [⋀^Fin k]→L[ℝ] ℝ) :
    pairing (c • α) β = c * pairing α β := by
  simp only [pairing, map_smul, real_inner_smul_left]

lemma pairing_add_right (α β γ : E [⋀^Fin k]→L[ℝ] ℝ) :
    pairing α (β+γ) = pairing α β + pairing α γ := by
  simp only [pairing, map_add, inner_add_right]

lemma pairing_smul_right (c : ℝ) (α β : E [⋀^Fin k]→L[ℝ] ℝ) :
    pairing α (c • β) = c * pairing α β := by
  simp only [pairing, map_smul, real_inner_smul_right]

lemma pairing_sub_left (α β γ : E [⋀^Fin k]→L[ℝ] ℝ) :
    pairing (α-β) γ = pairing α γ - pairing β γ := by
  simp only [pairing, map_sub, inner_sub_left]

lemma pairing_sub_right (α β γ : E [⋀^Fin k]→L[ℝ] ℝ) :
    pairing α (β-γ) = pairing α β - pairing α γ := by
  simp only [pairing, map_sub, inner_sub_right]

lemma contDiff_pairing {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : WithTop ℕ∞} {f g : D → E [⋀^Fin k]→L[ℝ] ℝ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => pairing (f x) (g x)) := by
  change ContDiff ℝ n (fun x => pairingCLM (E := E) (k := k) (f x) (g x))
  exact ((pairingCLM (E := E) (k := k)).contDiff.comp hf).clm_apply hg

def tripleIndices : Fin 4 → Fin 3 → Fin 4 := ![![1,2,3], ![0,2,3], ![0,1,3], ![0,1,2]]

def tripleFamily (b : OrthonormalBasis (Fin 4) ℝ E) (i : Fin 4) : ⋀[ℝ]^3 E :=
  exteriorPower.ιMulti ℝ 3 (fun j => b (tripleIndices i j))

lemma tripleFamily_orthonormal (b : OrthonormalBasis (Fin 4) ℝ E) :
    Orthonormal ℝ (tripleFamily b) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [tripleFamily, exteriorPower.inner_ιMulti_ιMulti, Matrix.det_fin_three]
  have hb := orthonormal_iff_ite.mp b.orthonormal
  fin_cases i <;> fin_cases j <;> simp [tripleIndices, hb]

def tripleBasis (b : OrthonormalBasis (Fin 4) ℝ E) :
    OrthonormalBasis (Fin 4) ℝ (⋀[ℝ]^3 E) :=
  OrthonormalBasis.mk (tripleFamily_orthonormal b)
    ((tripleFamily_orthonormal b).linearIndependent.span_eq_top_of_card_eq_finrank (by
      rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b.toBasis]
      norm_num [Nat.choose])).ge

lemma tripleBasis_repr (b : OrthonormalBasis (Fin 4) ℝ E)
    (α : E [⋀^Fin 3]→L[ℝ] ℝ) (i : Fin 4) :
    (tripleBasis b).repr (sharp α) i = α (fun j => b (tripleIndices i j)) := by
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
  simp only [tripleBasis, OrthonormalBasis.coe_mk, tripleFamily]
  exact sharp_inner _ _

lemma pairing_three (b : OrthonormalBasis (Fin 4) ℝ E)
    (α β : E [⋀^Fin 3]→L[ℝ] ℝ) :
    pairing α β = ∑ i, α (fun j => b (tripleIndices i j)) *
      β (fun j => b (tripleIndices i j)) := by
  have h := (tripleBasis b).repr.inner_map_map (sharp α) (sharp β)
  rw [pairing, ← h]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, tripleBasis_repr]
  congr 1
  ext i
  exact mul_comm _ _

end TamingCompatibility.FormMetric

end

end OAI
