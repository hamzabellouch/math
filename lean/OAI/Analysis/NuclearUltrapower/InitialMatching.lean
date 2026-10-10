import OAI.Analysis.NuclearUltrapower.InducedApproximation

namespace OAI

section

noncomputable section
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v

theorem matrixMap_injective {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (n : Type*) [Fintype n] [DecidableEq n] (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) :
    Function.Injective (matrixMap n φ) := by
  intro M N h
  ext i j
  exact hφ (congrArg (fun X : CStarMatrix n n B => X i j) h)

section Bounds
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)
local instance : PartialOrder B := CStarAlgebra.spectralOrder B
local instance : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

@[simp] theorem matchingTuple_coe (π : FiniteUnitaryRep.{u,v} Γ) (g : Γ)
    (z : E ⊗[ℂ] π) : matchingTuple ρ u π g (z : TensorHilbert E π) =
      (TensorProduct.congrIsometry (representedUnitary ρ (u g)) (π.action g) z : TensorHilbert E π) := by
  change completedTensorMap (ρ (u g)) (π.action g : π →L[ℂ] π) z = _
  rw [completedTensorMap_coe]
  congr 1
  simp only [TensorProduct.mapL_apply, TensorProduct.congrIsometry_apply]
  rfl

theorem matching_energy_coe (π : FiniteUnitaryRep.{u,v} Γ) (z : E ⊗[ℂ] π) :
    tupleEnergy S (matchingTuple ρ u π) (z : TensorHilbert E π) =
      ∑ s ∈ S, ‖TensorProduct.congrIsometry (representedUnitary ρ (u s)) (π.action s) z-z‖^2 := by
  apply Finset.sum_congr rfl
  intro s _
  rw [matchingTuple_coe, ← UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.norm_coe]

/-- Failure of matching is a matrix norm bound, with no relation imposed on u. -/
theorem not_matches_coefficient_bound (hρ : Function.Injective ρ)
    (π : FiniteUnitaryRep.{u,v} Γ) {n : Type*} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n ℂ π) (a : ℝ) (ha : a ≤ 4 * (S.card : ℝ))
    (hm : ¬ Matches ρ S u a π) :
    ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n B) -
      laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π.action s (b j)) i) (u s : B))‖
      ≤ 4 * (S.card : ℝ) - a := by
  have he (z : E ⊗[ℂ] π) : a * ‖z‖^2 ≤
      ∑ s ∈ S, ‖TensorProduct.congrIsometry (representedUnitary ρ (u s)) (π.action s) z-z‖^2 := by
    have hh : ¬ ∃ x : TensorHilbert E π,
        tupleEnergy S (matchingTuple ρ u π) x < a * ‖x‖^2 :=
      fun hx => hm ((matches_iff_homogeneous ρ S u a π).mpr hx)
    have hn := not_lt.mp (fun h => hh ⟨(z : TensorHilbert E π), h⟩)
    rwa [matching_energy_coe, UniformSpace.Completion.norm_coe] at hn
  have hb := tensorMatrix_complement_bound S b (fun s => representedUnitary ρ (u s)) π.action ha he
  let M : CStarMatrix n n B := (4 * (S.card : ℝ)) • 1 -
    laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π.action s (b j)) i) (u s : B))
  have hmap : matrixMap n ρ M = (4 * (S.card : ℝ)) •
      (1 : CStarMatrix n n (E →L[ℂ] E)) -
      laplacian S (fun s => tensorOperatorMatrix b (representedUnitary ρ (u s)) (π.action s)) := by
    dsimp only [M]
    rw [map_sub, show matrixMap n ρ ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n B)) =
      (4 * (S.card : ℝ)) • matrixMap n ρ 1 from (matrixMap n ρ).toAlgHom.map_smul_of_tower _ _]
    simp only [map_one, map_laplacian]
    congr 1
    apply congrArg (laplacian S)
    funext s
    rw [matrixMap_coefficientMatrix]
    rfl
  rw [← hmap] at hb
  have hn := NonUnitalStarAlgHom.norm_map (matrixMap n ρ).toNonUnitalStarAlgHom
    (matrixMap_injective n ρ hρ) M
  exact hn.symm.le.trans hb
end Bounds
end NuclearUltrapower
end
end

section

noncomputable section
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
section Obstruction
variable {Γ A K F : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (S : Finset Γ) (w : Γ → A) (ψ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
  (σ : Γ → K ≃ₗᵢ[ℂ] K) (π : Γ → F ≃ₗᵢ[ℂ] F)
  {n : Type*} [Fintype n] [DecidableEq n] (b : OrthonormalBasis n ℂ F)
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- The full algebra can see an invariant tensor in any representation. A
strict complemented-matrix bound would exclude that tensor. -/
theorem coefficient_bound_no_invariant (hψ : ∀ g, ψ (w g) = (σ g : K →L[ℂ] K))
    (a : ℝ) (ha : 0 < a)
    (hb : ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n A) -
      laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π s (b j)) i) (w s))‖ ≤
        4 * (S.card : ℝ) - a)
    (z : K ⊗[ℂ] F) (hz : ∀ s ∈ S, TensorProduct.congrIsometry (σ s) (π s) z = z) : z = 0 := by
  let M : CStarMatrix n n A := (4 * (S.card : ℝ)) • 1 -
    laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π s (b j)) i) (w s))
  let Ψ := (operatorMatrixActionHom (n := n) (H := K)).comp (matrixMap n ψ)
  have he : Ψ M = (4 * (S.card : ℝ)) • (1 : PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K)) -
      laplacian S (fun s => (tensorPiUnitary b (σ s) (π s) :
        PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K))) := by
    dsimp only [M]
    rw [map_sub, show Ψ ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n A)) =
      (4 * (S.card : ℝ)) • Ψ 1 from Ψ.toAlgHom.map_smul_of_tower _ _]
    simp only [map_one, map_laplacian]
    congr 1
    apply congrArg (laplacian S)
    funext s
    change operatorMatrixActionHom (n := n) (H := K)
      (matrixMap n ψ (coefficientMatrix (fun i j => b.repr (π s (b j)) i) (w s))) = _
    rw [matrixMap_coefficientMatrix, hψ]
    exact tensorOperatorMatrix_conjugacy b (σ s) (π s)
  have hbound := (NonUnitalStarAlgHom.norm_apply_le Ψ M).trans hb
  rw [he] at hbound
  have hez := no_invariant_of_complement_norm S
    (fun s => (tensorPiUnitary b (σ s) (π s) :
      PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K))) ha hbound
      (tensorPiIsometry b z) (by
        intro s hs
        change tensorPiUnitary b (σ s) (π s) (tensorPiIsometry b z) = _
        rw [tensorPiUnitary_apply_tensorPi, hz s hs])
  exact (tensorPiIsometry b).injective (hez.trans (map_zero _).symm)
end Obstruction
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u
section InitialMatch
variable {Γ A B E K : Type u} [Group Γ] [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (hρ : Function.Injective ρ)
  (S : Finset Γ) (ω : Ultrafilter ℕ)
  (φ : A →⋆ₐ[ℂ] VariableUltra.Algebra (fun _ : ℕ => B) ω) (hφ : Function.Injective φ)
  (w : Γ → A) (u : Γ → ℕ → unitary B)
  (hu : ∀ g, φ (w g) = VariableUltra.mk (fun _ : ℕ => B) ω
    (VariableUltra.unitarySequence (fun _ : ℕ => B) (u g)))
  (ψ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : Γ → K ≃ₗᵢ[ℂ] K)
  (hψ : ∀ g, ψ (w g) = (σ g : K →L[ℂ] K))
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance : PartialOrder B := CStarAlgebra.spectralOrder B
local instance : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
local instance : PartialOrder (VariableUltra.Algebra (fun _ : ℕ => B) ω) :=
  CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (VariableUltra.Algebra (fun _ : ℕ => B) ω) :=
  CStarAlgebra.spectralOrderedRing _

include hρ hu hφ hψ in
/-- A full-algebra invariant tensor forces matching on an ultrafilter-large
set. This is fixed-size matrix amplification, not an illicit varying-size one. -/
theorem initial_match (π : FiniteUnitaryRep.{u,u} Γ) (a : ℝ)
    (ha0 : 0 < a) (ha : a ≤ 4 * (S.card : ℝ))
    (z : K ⊗[ℂ] π) (hz0 : z ≠ 0)
    (hz : ∀ s ∈ S, TensorProduct.congrIsometry (σ s) (π.action s) z = z) :
    ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u g n) a π := by
  classical
  by_contra hm
  have hn := (ω.eventually_not).mpr hm
  let b := stdOrthonormalBasis ℂ π
  let n := Fin (Module.finrank ℂ π)
  let : Nonempty n := ⟨⟨0,Module.finrank_pos⟩⟩
  let c : Γ → n → n → ℂ := fun s i j => b.repr (π.action s (b j)) i
  have hb : ∀ᶠ i in (ω : Filter ℕ),
      ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n B) -
        laplacian S (fun s => coefficientMatrix (c s) (u s i : B))‖ ≤
          4 * (S.card : ℝ) - a := by
    filter_upwards [hn] with i hi
    exact not_matches_coefficient_bound ρ S (fun g => u g i) hρ π b a ha hi
  have hq := VariableUltra.coefficient_complement_quotient_bound (fun _ : ℕ => B) ω n S
    (fun g => (VariableUltra.unitarySequence (fun _ : ℕ => B) (u g) : VariableUltra.Seq (fun _ : ℕ => B)))
      c (4 * (S.card : ℝ)) (4 * (S.card : ℝ) - a) hb
  let M : CStarMatrix n n A := (4 * (S.card : ℝ)) • 1 -
    laplacian S (fun s => coefficientMatrix (c s) (w s))
  have hmap : matrixMap n φ M = (4 * (S.card : ℝ)) •
      (1 : CStarMatrix n n (VariableUltra.Algebra (fun _ : ℕ => B) ω)) -
      laplacian S (fun s => coefficientMatrix (c s)
        (VariableUltra.mk (fun _ : ℕ => B) ω
          (VariableUltra.unitarySequence (fun _ : ℕ => B) (u s)))) := by
    dsimp only [M]
    rw [map_sub, show matrixMap n φ ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n A)) =
      (4 * (S.card : ℝ)) • matrixMap n φ 1 from (matrixMap n φ).toAlgHom.map_smul_of_tower _ _]
    simp only [map_one, map_laplacian]
    simp only [matrixMap_coefficientMatrix, hu]
  have hnorm := NonUnitalStarAlgHom.norm_map (matrixMap n φ).toNonUnitalStarAlgHom
    (matrixMap_injective n φ hφ) M
  have hmnorm : ‖M‖ ≤ 4 * (S.card : ℝ) - a := by
    apply hnorm.symm.le.trans
    change ‖matrixMap n φ M‖ ≤ _
    rw [hmap]
    exact hq
  exact hz0 (coefficient_bound_no_invariant S w ψ σ π.action b hψ a ha0 hmnorm z hz)
end InitialMatch
end NuclearUltrapower
end
end

end OAI
