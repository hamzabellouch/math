import Mathlib.Tactic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi

namespace OAI

noncomputable section

open Classical Set

open Classical
namespace FiniteIntegralContraction
variable {I J K : Type*}

def rowEval (r : List (I × ℤ)) (c : I → ℤ) : ℤ :=
  (r.map (fun p => p.2 * c p.1)).sum

def rowsMap (r : J → List (I × ℤ)) : (I → ℤ) →ₗ[ℤ] (J → ℤ) :=
  LinearMap.pi (fun j => ((r j).map (fun p => p.2 • LinearMap.proj p.1)).sum)

@[simp] theorem rowsMap_apply (r : J → List (I × ℤ)) (c : I → ℤ) (j : J) :
    rowsMap r c j = rowEval (r j) c := by
  simp only [rowsMap,LinearMap.pi_apply]
  induction r j with
  | nil => rfl
  | cons p r ih => simp [rowEval,List.map_cons,ih]

def matrixMap [Fintype I] (a : I → J → ℤ) : (I → ℤ) →ₗ[ℤ] (J → ℤ) :=
  Matrix.mulVecLin (fun j i => a i j)

@[simp] theorem matrixMap_single [Fintype I] (a : I → J → ℤ) (i : I) :
    matrixMap a (Pi.single i 1) = a i := by
  funext j
  change ∑ k : I, a k j * ((Pi.single i (1 : ℤ) : I → ℤ) k) = a i j
  simp [Pi.single_apply]

theorem map_eq_of_single [Fintype I] {f g : (I → ℤ) →ₗ[ℤ] (J → ℤ)}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply (Pi.basisFun ℤ I).ext
  intro i
  simpa using h i

/-- A checked integral contraction in degrees 0,1,2 gives both exactness
and injectivity of the two-dimensional boundary. -/
theorem exactness [Fintype I] [Fintype J] [Fintype K]
    (d₁ : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (d₂ : (K → ℤ) →ₗ[ℤ] (J → ℤ))
    (h₀ : (I → ℤ) →ₗ[ℤ] (J → ℤ)) (h₁ : (J → ℤ) →ₗ[ℤ] (K → ℤ))
    (hleft : ∀ i, h₁ (d₂ (Pi.single i 1)) = Pi.single i 1)
    (hmid : ∀ j, d₂ (h₁ (Pi.single j 1)) + h₀ (d₁ (Pi.single j 1)) = Pi.single j 1) :
    Function.Injective d₂ ∧ ∀ c, d₁ c = 0 → ∃ b, d₂ b = c := by
  have he : h₁.comp d₂ = LinearMap.id := map_eq_of_single hleft
  have hm : d₂.comp h₁ + h₀.comp d₁ = LinearMap.id := map_eq_of_single hmid
  constructor
  · intro a b hab
    have ha := LinearMap.congr_fun he a
    have hb := LinearMap.congr_fun he b
    simp only [LinearMap.comp_apply,LinearMap.id_apply] at ha hb
    exact ha.symm.trans ((congrArg h₁ hab).trans hb)
  · intro c hc
    refine ⟨h₁ c,?_⟩
    have hh := LinearMap.congr_fun hm c
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,hc,map_zero,add_zero] using hh

variable [Fintype I] [Fintype J] [Fintype K]
    (edge : J → I × I) (face : K → J × J × J)
    (r₁ : I → List (J × ℤ)) (r₂ : J → List (K × ℤ))
    (a₀ : I → J → ℤ) (a₁ : J → K → ℤ) (root : I)

omit [Fintype I] [Fintype J] in
 theorem rows_single_one (h : ∀ i e, rowEval (r₁ i) (fun j => if j = e then 1 else 0) =
    (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0)) (e : J) :
    rowsMap r₁ (Pi.single e 1) = Pi.single (edge e).2 1 - Pi.single (edge e).1 1 := by
  funext i
  have he : (Pi.single e 1 : J → ℤ) = fun j => if j = e then 1 else 0 := by funext j; simp [Pi.single_apply]
  rw [rowsMap_apply,he]
  simpa only [Pi.sub_apply,Pi.single_apply] using h i e

omit [Fintype J] [Fintype K] in
 theorem rows_single_two (h : ∀ j t, rowEval (r₂ j) (fun i => if i = t then 1 else 0) =
    (if j = (face t).1 then 1 else 0) - (if j = (face t).2.1 then 1 else 0) +
      (if j = (face t).2.2 then 1 else 0)) (t : K) :
    rowsMap r₂ (Pi.single t 1) = Pi.single (face t).1 1 - Pi.single (face t).2.1 1 +
      Pi.single (face t).2.2 1 := by
  funext j
  have he : (Pi.single t 1 : K → ℤ) = fun i => if i = t then 1 else 0 := by funext i; simp [Pi.single_apply]
  rw [rowsMap_apply,he]
  simpa only [Pi.sub_apply,Pi.add_apply,Pi.single_apply] using h j t

omit [Fintype J] in
 theorem certificate_bottom (h : ∀ i v, rowEval (r₁ i) (a₀ v) =
    (if i = v then 1 else 0) - (if i = root then 1 else 0)) (v : I) :
    rowsMap r₁ (matrixMap a₀ (Pi.single v 1)) = Pi.single v 1 - Pi.single root 1 := by
  rw [matrixMap_single]
  funext i
  simpa only [rowsMap_apply,Pi.sub_apply,Pi.single_apply] using h i v

omit [Fintype K] in
 theorem certificate_left (hd : ∀ t, rowsMap r₂ (Pi.single t 1) =
    Pi.single (face t).1 1 - Pi.single (face t).2.1 1 + Pi.single (face t).2.2 1)
    (h : ∀ t j, a₁ (face t).1 j - a₁ (face t).2.1 j + a₁ (face t).2.2 j =
      if j = t then 1 else 0) (t : K) :
    matrixMap a₁ (rowsMap r₂ (Pi.single t 1)) = Pi.single t 1 := by
  rw [hd,map_add,map_sub,matrixMap_single,matrixMap_single,matrixMap_single]
  funext j
  simpa only [Pi.sub_apply,Pi.add_apply,Pi.single_apply] using h t j

omit [Fintype K] in
 theorem certificate_middle (hd : ∀ e, rowsMap r₁ (Pi.single e 1) =
    Pi.single (edge e).2 1 - Pi.single (edge e).1 1)
    (h : ∀ j e, rowEval (r₂ j) (a₁ e) + a₀ (edge e).2 j - a₀ (edge e).1 j =
      if j = e then 1 else 0) (e : J) :
    rowsMap r₂ (matrixMap a₁ (Pi.single e 1)) +
      matrixMap a₀ (rowsMap r₁ (Pi.single e 1)) = Pi.single e 1 := by
  rw [hd,map_sub,matrixMap_single,matrixMap_single,matrixMap_single]
  funext j
  simpa only [rowsMap_apply,Pi.sub_apply,Pi.add_apply,Pi.single_apply,add_sub_assoc] using h j e

end FiniteIntegralContraction

namespace FiniteIntegralContraction
noncomputable section
open Classical
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def sumCoordinates : (I → ℤ) →ₗ[ℤ] ℤ where
  toFun := fun v => ∑ i, v i
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum]

@[simp] theorem sumCoordinates_single (i : I) : sumCoordinates (Pi.single i 1) = 1 := by
  simp [sumCoordinates,Pi.single_apply]

def rootCoordinates (root : I) : ℤ →ₗ[ℤ] (I → ℤ) :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight (Pi.single root 1)

omit [Fintype I] in
@[simp] theorem rootCoordinates_one (root : I) : rootCoordinates root 1 = Pi.single root 1 := by
  simp [rootCoordinates]

def corrected (d₁ : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (h₀ : (I → ℤ) →ₗ[ℤ] (J → ℤ))
    (h₁ : (J → ℤ) →ₗ[ℤ] (K → ℤ)) := h₁.comp (LinearMap.id - h₀.comp d₁)

/-- A stable rank equality turns a checked split boundary and a checked bottom
contraction into the full middle identity. This avoids a large redundant finite
matrix certificate; no rational exactness is substituted for integer exactness. -/
theorem middle_of_rank
    (card : Fintype.card J + 1 = Fintype.card K + Fintype.card I)
    (root : I) (d₁ : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (d₂ : (K → ℤ) →ₗ[ℤ] (J → ℤ))
    (h₀ : (I → ℤ) →ₗ[ℤ] (J → ℤ)) (h₁ : (J → ℤ) →ₗ[ℤ] (K → ℤ))
    (hd : ∀ t, d₁ (d₂ (Pi.single t 1)) = 0)
    (hb : ∀ i, d₁ (h₀ (Pi.single i 1)) = Pi.single i 1 - Pi.single root 1)
    (hl : ∀ t, h₁ (d₂ (Pi.single t 1)) = Pi.single t 1) :
    (∀ t, corrected d₁ h₀ h₁ (d₂ (Pi.single t 1)) = Pi.single t 1) ∧
    (∀ j, d₂ (corrected d₁ h₀ h₁ (Pi.single j 1)) + h₀ (d₁ (Pi.single j 1)) = Pi.single j 1) := by
  have hd' : d₁.comp d₂ = 0 := map_eq_of_single hd
  have hb' : d₁.comp h₀ = LinearMap.id - (rootCoordinates root).comp sumCoordinates := by
    apply map_eq_of_single
    intro i
    simpa only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
      sumCoordinates_single,rootCoordinates_one] using hb i
  have hl' : h₁.comp d₂ = LinearMap.id := map_eq_of_single hl
  have dz (t : K → ℤ) : d₁ (d₂ t) = 0 := LinearMap.congr_fun hd' t
  have bz (i : I → ℤ) : d₁ (h₀ i) = i - rootCoordinates root (sumCoordinates i) :=
    LinearMap.congr_fun hb' i
  have lz (t : K → ℤ) : h₁ (d₂ t) = t := LinearMap.congr_fun hl' t
  let F : ((K → ℤ) × (I → ℤ)) →ₗ[ℤ] ((J → ℤ) × ℤ) :=
    (((d₂.comp (LinearMap.fst ℤ _ _)) + (h₀.comp (LinearMap.snd ℤ _ _))).prod
      (sumCoordinates.comp (LinearMap.snd ℤ _ _)))
  let D : ((J → ℤ) × ℤ) →ₗ[ℤ] (I → ℤ) :=
    d₁.comp (LinearMap.fst ℤ _ _) + (rootCoordinates root).comp (LinearMap.snd ℤ _ _)
  let H : ((J → ℤ) × ℤ) →ₗ[ℤ] ((K → ℤ) × (I → ℤ)) :=
    (h₁.comp (LinearMap.fst ℤ _ _ - h₀.comp D)).prod D
  have hDF (p : (K → ℤ) × (I → ℤ)) : D (F p) = p.2 := by
    change d₁ (d₂ p.1 + h₀ p.2) + rootCoordinates root (sumCoordinates p.2) = p.2
    rw [map_add,dz,bz,zero_add,sub_add_cancel]
  have hHF (p : (K → ℤ) × (I → ℤ)) : H (F p) = p := by
    apply Prod.ext
    · change h₁ ((d₂ p.1 + h₀ p.2) - h₀ (D (F p))) = p.1
      rw [hDF,add_sub_cancel_right,lz]
    · exact hDF p
  let ei : J ⊕ Unit ≃ K ⊕ I := Fintype.equivOfCardEq (by simpa using card)
  let e : ((J → ℤ) × ℤ) ≃ₗ[ℤ] ((K → ℤ) × (I → ℤ)) :=
    (LinearEquiv.prodCongr (LinearEquiv.refl ℤ (J → ℤ)) (LinearEquiv.funUnique Unit ℤ ℤ).symm).trans
      ((LinearEquiv.sumArrowLequivProdArrow J Unit ℤ ℤ).symm.trans
        ((LinearEquiv.piCongrLeft ℤ (fun _ : K ⊕ I => ℤ) ei).trans
          (LinearEquiv.sumArrowLequivProdArrow K I ℤ ℤ)))
  have hi : Function.Injective H := IsNoetherian.injective_of_surjective_of_injective
    e.toLinearMap H e.injective (fun p => ⟨F p,hHF p⟩)
  have hFH (p : (J → ℤ) × ℤ) : F (H p) = p := hi (hHF (H p))
  constructor
  · intro t
    simp only [corrected,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,hd,map_zero,sub_zero,hl]
  · intro j
    have he := congrArg Prod.fst (hFH (Pi.single j 1,0))
    change d₂ (h₁ (Pi.single j 1 - h₀ (d₁ (Pi.single j 1) + rootCoordinates root 0))) +
      h₀ (d₁ (Pi.single j 1) + rootCoordinates root 0) = Pi.single j 1 at he
    simpa only [map_zero,add_zero,corrected,LinearMap.comp_apply,LinearMap.sub_apply,
      LinearMap.id_apply] using he

end
end FiniteIntegralContraction



end

end OAI
