import Mathlib
import OAI.Geometry.NilpotentCharts.AdjointPolynomials

namespace OAI

/-! Smooth inverse coordinates and triangular differential equations for multiplication. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
open RawLieAdjoint

lemma adjoint_orderedAxes_inv_prefix {n : ℕ} (v : Fin n → E₀) (a : Fin n → ℝ)
    (l : E₀ →ₗ[ℝ] ℝ) (k : ℕ)
    (hl : ∀ i : Fin n, k ≤ i.val → ∀ t : ℝ, ∀ x : E₀,
      l (adjoint (G := G) (E₀ := E₀) (curve (v i) t) x) = l x) (x : E₀) :
    l (adjoint (G := G) (E₀ := E₀) (orderedAxes v a)⁻¹ x) =
      l (adjoint (G := G) (E₀ := E₀)
        (orderedAxes v (fun i => if i.val < k then a i else 0))⁻¹ x) := by
  change Fin n → GroupLieAlgebra I₀ G at v
  induction n generalizing k x with
  | zero => rfl
  | succ n ih =>
    rw [orderedAxes_succ,orderedAxes_succ,mul_inv_rev,mul_inv_rev,adjoint_mul,adjoint_mul]
    change l (adjoint (orderedAxes (fun i => v i.succ) (fun i => a i.succ))⁻¹
        (adjoint (curve (v 0) (a 0))⁻¹ x)) =
      l (adjoint (orderedAxes (fun i => v i.succ)
        (fun i => if i.succ.val < k then a i.succ else 0))⁻¹
        (adjoint (curve (v 0) (if (0 : Fin (n+1)).val < k then a 0 else 0))⁻¹ x))
    cases k with
    | zero =>
      have hl' : ∀ i : Fin n, 0 ≤ i.val → ∀ t : ℝ, ∀ y : E₀,
          l (adjoint (G := G) (E₀ := E₀) (curve (v i.succ) t) y) = l y :=
        fun i _ t y => hl i.succ (Nat.zero_le _) t y
      have hz : orderedAxes (G := G) (fun i : Fin n => v i.succ) (fun _ => 0) = 1 :=
        orderedAxes_zero _
      have hh := ih (v := fun i => v i.succ) (hl := hl') (fun i => a i.succ) 0
        (adjoint (G := G) (E₀ := E₀) (curve (v 0) (a 0))⁻¹ x)
      simp only [Nat.not_lt_zero,ite_false,hz] at hh
      rw [hh]
      simp only [Nat.not_lt_zero,ite_false,hz,curve_zero,inv_one,adjoint_one,
        one_apply_eq_self]
      rw [← curve_neg]
      exact hl 0 (Nat.zero_le _) _ _
    | succ k =>
      have hl' : ∀ i : Fin n, k ≤ i.val → ∀ t : ℝ, ∀ y : E₀,
          l (adjoint (G := G) (E₀ := E₀) (curve (v i.succ) t) y) = l y :=
        fun i hi t y => hl i.succ (by simpa using Nat.succ_le_succ hi) t y
      simpa only [Fin.val_zero,Nat.zero_lt_succ,ite_true,Fin.val_succ,Nat.succ_lt_succ_iff] using
        ih (v := fun i => v i.succ) (hl := hl') (fun i => a i.succ) k
          (adjoint (curve (v 0) (a 0))⁻¹ x)

lemma axisTail_eq_orderedAxes_mask {n : ℕ} (v : Fin n → E₀) (a : Fin n → ℝ) (i : Fin n) :
    axisTail (G := G) v a i = orderedAxes v (fun k => if i < k then a k else 0) := by
  change Fin n → GroupLieAlgebra I₀ G at v
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [orderedAxes_succ]
      simp only [lt_self_iff_false,ite_false,curve_zero,one_mul,axisTail,Fin.cases_zero,
        Fin.lt_def,Fin.val_zero,Fin.val_succ,Nat.zero_lt_succ,ite_true]
    · rw [orderedAxes_succ]
      simp only [Fin.not_lt_zero,ite_false,curve_zero,one_mul,axisTail,Fin.cases_succ,
        Fin.succ_lt_succ_iff]
      exact ih (v := fun k => v k.succ) (fun k => a k.succ) j

lemma adjoint_axisTail_inv_prefix {n s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (a : Fin n → ℝ) (i j : Fin n) (x : E₀) :
    b.equivFun (adjoint (G := G) (E₀ := E₀) (axisTail b a i)⁻¹ x) j =
      b.equivFun (adjoint (G := G) (E₀ := E₀)
        (axisTail b (fun k => if k < j then a k else 0) i)⁻¹ x) j := by
  rw [axisTail_eq_orderedAxes_mask,axisTail_eq_orderedAxes_mask]
  let l : E₀ →ₗ[ℝ] ℝ := (LinearMap.proj j).comp b.equivFun.toLinearMap
  have hh := adjoint_orderedAxes_inv_prefix b (fun k => if i < k then a k else 0) l j.val
    (fun k hk t y => adjoint_axis_row hstop b hb k j hk y t) x
  have hm : (fun k : Fin n => if k.val < j.val then (if i < k then a k else 0) else 0) =
      (fun k : Fin n => if i < k then (if k < j then a k else 0) else 0) := by
    ext k
    change (if k < j then (if i < k then a k else 0) else 0) = _
    split_ifs <;> rfl
  simpa only [hm,l,LinearMap.comp_apply,LinearMap.proj_apply,LinearEquiv.coe_coe] using hh
end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

def normalizedAxes {n : ℕ} (v : Fin n → GroupLieAlgebra I₀ G) (a x : Fin n → ℝ) : G :=
  (orderedAxes v a)⁻¹ * orderedAxes v x

lemma normalizedAxes_contMDiff {n : ℕ} (v : Fin n → GroupLieAlgebra I₀ G) (a : Fin n → ℝ) :
    ContMDiff 𝓘(ℝ,Fin n → ℝ) I₀ ∞ (normalizedAxes v a) :=
  contMDiff_const.mul (orderedAxes_contMDiff v)

@[simp] lemma normalizedAxes_self {n : ℕ} (v : Fin n → GroupLieAlgebra I₀ G) (a : Fin n → ℝ) :
    normalizedAxes v a a = 1 := inv_mul_cancel _

lemma normalizedAxes_shift {n : ℕ} (v : Fin n → GroupLieAlgebra I₀ G) (a : Fin n → ℝ)
    (i : Fin n) (t : ℝ) :
    normalizedAxes v a (a + Pi.single i t) = MulAut.conj (axisTail v a i)⁻¹ (curve (v i) t) := by
  simp only [normalizedAxes,orderedAxes_shift,inv_mul_cancel_left,MulAut.conj_apply,inv_inv]

lemma normalizedAxes_derivative_column {n : ℕ} (v : Fin n → GroupLieAlgebra I₀ G)
    (a : Fin n → ℝ) (i : Fin n) :
    mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes v a) a (Pi.single i 1) =
      RawLieAdjoint.adjoint (E₀ := E₀) (axisTail v a i)⁻¹ (v i) := by
  let L : ℝ →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i
  let f : ℝ → (Fin n → ℝ) := fun t => a + L t
  have hf0 : f 0 = a := by simp [f]
  have hf : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin n → ℝ) f 0 L :=
    (L.hasFDerivAt.const_add a).hasMFDerivAt
  have hD : HasMFDerivAt 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes v a) (f 0)
      (mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes v a) a) := by
    rw [hf0]
    exact ((normalizedAxes_contMDiff v a).mdifferentiable (by simp) a).hasMFDerivAt
  have H := hD.comp 0 hf
  let g := MulAut.conj (axisTail v a i)⁻¹
  have hg : HasMFDerivAt I₀ I₀ (g : G → G) (curve (v i) 0)
      (RawLieAdjoint.adjoint (E₀ := E₀) (axisTail v a i)⁻¹) := by
    rw [curve_zero]
    exact ((RawLieAdjoint.conjugation_smooth (E₀ := E₀) _).mdifferentiableAt one_ne_zero).hasMFDerivAt
  have H' := hg.comp 0 (curve_derivative_zero (v i))
  have he : normalizedAxes v a ∘ f = (g : G → G) ∘ curve (v i) :=
    funext (normalizedAxes_shift v a i)
  rw [he] at H
  have heq := H.mfderiv.symm.trans H'.mfderiv
  have hval := congrArg (fun D : ℝ →L[ℝ] E₀ => D 1) heq
  change mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes v a) a (L 1) =
    RawLieAdjoint.adjoint (E₀ := E₀) (axisTail v a i)⁻¹ ((1 : ℝ) • v i) at hval
  simpa only [L,ContinuousLinearMap.single_apply,one_smul] using hval

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

lemma normalizedAxes_derivative_injective {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (E₀ := E₀) g).toLinearMap)
    (a : Fin n → ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes (G := G) b a) a) := by
  let D : (Fin n → ℝ) →L[ℝ] E₀ := mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes (G := G) b a) a
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := b.equivFun.toLinearMap.comp D.toLinearMap
  have hL : ∀ i j, j ≤ i → L (Pi.single i 1) j = if i = j then 1 else 0 := by
    intro i j hji
    change b.equivFun (D (Pi.single i 1)) j = _
    rw [show D (Pi.single i 1) = RawLieAdjoint.adjoint (E₀ := E₀) (axisTail b a i)⁻¹ (b i) from
      normalizedAxes_derivative_column b a i]
    have h := hb (axisTail b a i)⁻¹ i j hji
    simp only [map_sub,Pi.sub_apply,ContinuousLinearMap.coe_coe] at h
    rw [sub_eq_zero] at h
    rw [h]
    simp
  have hi := RawTriangular.injective_of_unit_triangular L hL
  intro x y he
  apply hi
  exact congrArg b.equivFun he

lemma orderedAxes_derivative_equiv {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (E₀ := E₀) g).toLinearMap)
    (a : Fin n → ℝ) :
    ∃ L : (Fin n → ℝ) ≃L[ℝ] E₀,
      (mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (orderedAxes (G := G) b) a : (Fin n → ℝ) →L[ℝ] E₀) =
        L.toContinuousLinearMap := by
  let D : (Fin n → ℝ) →L[ℝ] E₀ := mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (orderedAxes (G := G) b) a
  have hn := normalizedAxes_derivative_injective (G := G) b hb a
  have hc : mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes (G := G) b a) a =
      (mfderiv I₀ I₀ (fun g : G => (orderedAxes b a)⁻¹ * g) (orderedAxes b a)).comp D := by
    exact mfderiv_comp a ((contMDiff_mul_left (I := I₀) (n := ∞)).mdifferentiableAt (by simp))
      ((orderedAxes_contMDiff b).mdifferentiableAt (by simp))
  have hD : Function.Injective D := by
    intro x y hxy
    apply hn
    rw [hc]
    change (mfderiv I₀ I₀ (fun g : G => (orderedAxes b a)⁻¹ * g) (orderedAxes b a)) (D x) =
      (mfderiv I₀ I₀ (fun g : G => (orderedAxes b a)⁻¹ * g) (orderedAxes b a)) (D y)
    exact congrArg _ hxy
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := b.equivFun.toLinearMap.comp D.toLinearMap
  have hA : Function.Injective A := b.equivFun.injective.comp hD
  have hsA : Function.Surjective A := LinearMap.injective_iff_surjective.mp hA
  have hsD : Function.Surjective D := by
    intro y
    obtain ⟨x,hx⟩ := hsA (b.equivFun y)
    exact ⟨x,b.equivFun.injective hx⟩
  exact ⟨(LinearEquiv.ofBijective D.toLinearMap ⟨hD,hsD⟩).toContinuousLinearEquiv,rfl⟩

lemma orderedAxes_inverse_contMDiff {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (E₀ := E₀) g).toLinearMap)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes b) :
    ContMDiff I₀ 𝓘(ℝ,Fin n → ℝ) ∞ h.symm := by
  apply RawSmoothInverse.contMDiff_inverse h
  · rw [hh]; exact orderedAxes_contMDiff b
  · intro a; rw [hh]; exact orderedAxes_derivative_equiv b hb a
end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

def coordinateProduct {n : ℕ} (h : (Fin n → ℝ) ≃ₜ G) (a c : Fin n → ℝ) : Fin n → ℝ :=
  h.symm (h a * h c)

lemma orderedAxes_coordinateProduct {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b)
    (a c : Fin n → ℝ) :
    orderedAxes (G := G) b (coordinateProduct h a c) = orderedAxes (G := G) b a * orderedAxes (G := G) b c := by
  rw [← hh]
  exact h.apply_symm_apply _

lemma coordinateProduct_contDiff {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b) (a : Fin n → ℝ) :
    ContDiff ℝ ∞ (coordinateProduct h a) := by
  have hhs : ContMDiff 𝓘(ℝ,Fin n → ℝ) I₀ ∞ h := hh.symm ▸ orderedAxes_contMDiff b
  exact ((orderedAxes_inverse_contMDiff b hb h hh).comp (contMDiff_const.mul hhs)).contDiff

lemma normalizedAxes_coordinateProduct {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b)
    (a c z : Fin n → ℝ) :
    normalizedAxes (G := G) b (coordinateProduct h a c) (coordinateProduct h a z) = normalizedAxes (G := G) b c z := by
  simp only [normalizedAxes,orderedAxes_coordinateProduct b h hh,mul_inv_rev]
  group

lemma coordinateProduct_normalized_derivative {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b)
    (a c : Fin n → ℝ) :
    (mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes (G := G) b (coordinateProduct h a c)) (coordinateProduct h a c) :
      (Fin n → ℝ) →L[ℝ] E₀).comp (fderiv ℝ (coordinateProduct h a) c) =
      (mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes (G := G) b c) c : (Fin n → ℝ) →L[ℝ] E₀) := by
  have hc := coordinateProduct_contDiff b hb h hh a
  have hN := normalizedAxes_contMDiff (G := G) b (coordinateProduct h a c)
  have he : normalizedAxes (G := G) b (coordinateProduct h a c) ∘ coordinateProduct h a = normalizedAxes (G := G) b c :=
    funext (normalizedAxes_coordinateProduct b h hh a c)
  have hd := mfderiv_comp c (hN.mdifferentiableAt (by simp)) (hc.contMDiff.mdifferentiableAt (by simp))
  rw [he,mfderiv_eq_fderiv] at hd
  exact hd.symm

 
def coordinateMC {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀) (a : Fin n → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  b.equivFun.toLinearMap.comp
    (mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes (G := G) b a) a).toLinearMap

lemma coordinateMC_column {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀) (a : Fin n → ℝ) (i j : Fin n) :
    coordinateMC (G := G) b a (Pi.single i 1) j =
      b.equivFun (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) (axisTail (G := G) b a i)⁻¹ (b i)) j := by
  change b.equivFun (mfderiv 𝓘(ℝ,Fin n → ℝ) I₀ (normalizedAxes (G := G) b a) a (Pi.single i 1)) j = _
  exact congrArg (fun x => b.equivFun x j) (normalizedAxes_derivative_column b a i)

lemma coordinateMC_triangular {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (a : Fin n → ℝ) (i j : Fin n) (hji : j ≤ i) :
    coordinateMC (G := G) b a (Pi.single i 1) j = if i = j then 1 else 0 := by
  rw [coordinateMC_column]
  have hh := hb (axisTail (G := G) b a i)⁻¹ i j hji
  simp only [map_sub,Pi.sub_apply,ContinuousLinearMap.coe_coe] at hh
  rw [sub_eq_zero] at hh
  rw [hh]
  simp

lemma coordinateMC_product_derivative {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b)
    (a c v : Fin n → ℝ) :
    coordinateMC (G := G) b (coordinateProduct h a c) (fderiv ℝ (coordinateProduct h a) c v) =
      coordinateMC (G := G) b c v := by
  have he := congrArg (fun D : (Fin n → ℝ) →L[ℝ] E₀ => D v)
    (coordinateProduct_normalized_derivative b hb h hh a c)
  exact congrArg b.equivFun he
end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

lemma coordinateMC_polynomials {n s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) g).toLinearMap) :
    ∃ M : Fin n → Fin n → MvPolynomial (Fin n) ℝ,
      (∀ j i a, MvPolynomial.eval a (M j i) = coordinateMC (G := G) b a (Pi.single i 1) j) ∧
      (∀ j i a, MvPolynomial.eval a (M j i) =
        MvPolynomial.eval (fun k => if k < j then a k else 0) (M j i)) := by
  classical
  choose M hM using (fun j i => RawLieAdjoint.polynomial_normalizedAxes_column hstop b i j)
  refine ⟨M,?_,?_⟩
  · intro j i a
    rw [coordinateMC_column]
    exact hM j i a
  · intro j i a
    rw [hM,hM]
    exact adjoint_axisTail_inv_prefix hstop b hb a i j (b i)

def coordinateLine {n : ℕ} (h : (Fin n → ℝ) ≃ₜ G) (a v : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  coordinateProduct h a (t • v)

lemma coordinateLine_zero {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b)
    (a v : Fin n → ℝ) : coordinateLine h a v 0 = a := by
  apply h.injective
  change h (h.symm (h a * h (0 • v))) = h a
  rw [h.apply_symm_apply,zero_smul]
  have h0 : h 0 = 1 := by rw [hh]; exact orderedAxes_zero b
  rw [h0,mul_one]

lemma coordinateLine_hasDerivAt {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b)
    (a v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (coordinateLine h a v) (fderiv ℝ (coordinateProduct h a) (t • v) v) t := by
  have H := ((coordinateProduct_contDiff b hb h hh a).differentiable (by simp) (t • v)).hasFDerivAt
  apply H.comp_hasDerivAt t
  convert (hasDerivAt_id t).smul_const v using 1 <;> first | rfl | exact (one_smul ℝ v).symm

lemma coordinateLine_ode {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (RawLieAdjoint.adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (h : (Fin n → ℝ) ≃ₜ G) (hh : (h : (Fin n → ℝ) → G) = orderedAxes (G := G) b)
    (M : Fin n → Fin n → MvPolynomial (Fin n) ℝ)
    (hM : ∀ j i a, MvPolynomial.eval a (M j i) = coordinateMC (G := G) b a (Pi.single i 1) j)
    (a v : Fin n → ℝ) (t : ℝ) (j : Fin n) :
    HasDerivAt (fun t => coordinateLine h a v t j)
      (v j + ∑ i : Fin j.val,
        (MvPolynomial.eval (t • v) (M j ⟨i.val,lt_trans i.isLt j.isLt⟩) *
          v ⟨i.val,lt_trans i.isLt j.isLt⟩ -
        MvPolynomial.eval (coordinateLine h a v t) (M j ⟨i.val,lt_trans i.isLt j.isLt⟩) *
          deriv (fun t => coordinateLine h a v t ⟨i.val,lt_trans i.isLt j.isLt⟩) t)) t := by
  let w := fderiv ℝ (coordinateProduct h a) (t • v) v
  have HD := coordinateLine_hasDerivAt b hb h hh a v t
  have hw : ∀ i, deriv (fun t => coordinateLine h a v t i) t = w i :=
    fun i => (hasDerivAt_pi.mp HD i).deriv
  have he := congrFun (coordinateMC_product_derivative b hb h hh a (t • v) v) j
  rw [RawTriangular.row_of_unit_triangular _ (coordinateMC_triangular b hb _) _ j,
    RawTriangular.row_of_unit_triangular _ (coordinateMC_triangular b hb _) _ j,
    RawTriangular.sum_lower,RawTriangular.sum_lower] at he
  have hs : (∑ i : Fin j.val,
        (MvPolynomial.eval (t • v) (M j ⟨i.val,lt_trans i.isLt j.isLt⟩) *
          v ⟨i.val,lt_trans i.isLt j.isLt⟩ -
        MvPolynomial.eval (coordinateLine h a v t) (M j ⟨i.val,lt_trans i.isLt j.isLt⟩) *
          deriv (fun t => coordinateLine h a v t ⟨i.val,lt_trans i.isLt j.isLt⟩) t)) =
      (∑ i : Fin j.val, v ⟨i.val,lt_trans i.isLt j.isLt⟩ *
        coordinateMC (G := G) b (t • v) (Pi.single ⟨i.val,lt_trans i.isLt j.isLt⟩ 1) j) -
      (∑ i : Fin j.val, w ⟨i.val,lt_trans i.isLt j.isLt⟩ *
        coordinateMC (G := G) b (coordinateLine h a v t) (Pi.single ⟨i.val,lt_trans i.isLt j.isLt⟩ 1) j) := by
    rw [Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> rw [hM] <;> simp only [hw,mul_comm]
  apply (hasDerivAt_pi.mp HD j).congr_deriv
  rw [hs]
  simp only [coordinateLine,w] at *
  linarith
end RawLieIntegration
end

end OAI
