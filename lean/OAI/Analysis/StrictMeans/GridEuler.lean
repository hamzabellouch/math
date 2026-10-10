import OAI.Analysis.StrictMeans.GridComplex

namespace OAI

section
open Polynomial Set Module
namespace StrictInverseFirstPower.Grid
noncomputable section

def augmentation : Chain →ₗ[ℚ] ℚ where
  toFun p := eval 1 (eval 1 p)
  map_add' := by intros; simp
  map_smul' := by intros; simp

lemma augmentation_boundary₁ (h v d : Chain) : augmentation (boundary₁ h v d) = 0 := by
  simp [augmentation,boundary₁,x,y]

def vertexAugmentation (S : Set (ℕ × ℕ)) : chainSpace S →ₗ[ℚ] ℚ :=
  augmentation.comp (chainSpace S).subtype

lemma vertexAugmentation_boundary (S : Set (ℕ × ℕ)) :
    vertexAugmentation S ∘ₗ edgeBoundary S = 0 := by
  apply LinearMap.ext
  intro e
  exact augmentation_boundary₁ e.1.1 e.2.1.1 e.2.2.1

lemma vertexAugmentation_ne_zero {S : Set (ℕ × ℕ)} (hne : S.Nonempty) :
    vertexAugmentation S ≠ 0 := by
  classical
  obtain ⟨⟨i,j⟩,hv⟩ := hne
  let p : Chain := monomial j (monomial i 1)
  have hp : p ∈ chainSpace S := by
    rw [mem_chainSpace]
    intro l m hm
    by_cases hmi : m=j
    · subst m
      have hli : l ≠ i := by rintro rfl; exact hm hv
      simp [p,coeff,coeff_monomial,Ne.symm hli]
    · simp [p,coeff,coeff_monomial,Ne.symm hmi]
  intro he
  have hh := congrArg (fun f : chainSpace S →ₗ[ℚ] ℚ => f ⟨p,hp⟩) he
  simp [vertexAugmentation,augmentation,p,eval_monomial] at hh

lemma sublevel_euler {u : ℕ × ℕ → ℝ} {c : ℝ}
    (hfin : {v | u v ≤ c}.Finite) (hne : {v | u v ≤ c}.Nonempty)
    (hascent : ∀ i j, c < u (i,j) → 0 < i → 0 < j →
      u (i,j) < u (i+1,j) ∨ u (i,j) < u (i,j+1) ∨
      u (i,j) < u (i-1,j) ∨ u (i,j) < u (i,j-1)) :
    (horizontalSet {v | u v ≤ c}).ncard + (verticalSet {v | u v ≤ c}).ncard +
      (diagonalSet {v | u v ≤ c}).ncard + 1 ≤
    {v | u v ≤ c}.ncard + (lowerSet {v | u v ≤ c}).ncard + (upperSet {v | u v ≤ c}).ncard := by
  let S := {v | u v ≤ c}
  have hH : (horizontalSet S).Finite := hfin.subset fun _ h => h.1
  have hV : (verticalSet S).Finite := hfin.subset fun _ h => h.1
  have hD : (diagonalSet S).Finite := hfin.subset fun _ h => h.1
  have hL : (lowerSet S).Finite := hfin.subset fun _ h => h.1
  have hU : (upperSet S).Finite := hfin.subset fun _ h => h.1
  let := hfin.fintype
  let := hH.fintype
  let := hV.fintype
  let := hD.fintype
  let := hL.fintype
  let := hU.fintype
  have he := finite_euler_inequality (K := ℚ) (V₀ := chainSpace S) (V₁ := EdgeSpace S) (V₂ := FaceSpace S) (edgeBoundary S) (faceBoundary S) (vertexAugmentation S)
    (faceBoundary_injective S) (boundary_exact hascent) (vertexAugmentation_boundary S)
    (vertexAugmentation_ne_zero hne)
  let (T : Set (ℕ × ℕ)) : Module.Free ℚ (chainSpace T) := Module.Free.of_equiv (chainSpaceEquiv T).symm
  have hdimE : finrank ℚ (EdgeSpace S) = finrank ℚ (chainSpace (horizontalSet S)) + finrank ℚ (chainSpace (verticalSet S)) + finrank ℚ (chainSpace (diagonalSet S)) := by
    dsimp only [EdgeSpace]
    rw [Module.finrank_prod,Module.finrank_prod]
    omega
  have hdimF : finrank ℚ (FaceSpace S) = finrank ℚ (chainSpace (lowerSet S)) + finrank ℚ (chainSpace (upperSet S)) := by
    exact Module.finrank_prod
  rw [hdimE,hdimF] at he
  simp only [finrank_chainSpace S hfin,
    finrank_chainSpace _ hH,finrank_chainSpace _ hV,finrank_chainSpace _ hD,
    finrank_chainSpace _ hL,finrank_chainSpace _ hU] at he
  dsimp only [S] at he
  omega

end
end StrictInverseFirstPower.Grid

end

end OAI
