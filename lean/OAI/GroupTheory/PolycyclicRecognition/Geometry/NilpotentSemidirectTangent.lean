import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectGroup
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlowDerivative

namespace OAI

/-! # The tangent bracket of the codimension-one extension -/

noncomputable section
namespace PolycyclicRecognition

open VectorField
open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

section TangentComputation

variable [Group (L × ℝ)]

variable [LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ)]
  (hone : (inferInstance : Group (L × ℝ)).one = 0)
  (hmul : ∀ x y : L × ℝ,
    (inferInstance : Group (L × ℝ)).mul x y =
      (x.1 * nilpotentDerivationFlow D hD x.2 y.1, x.2 + y.2))

local instance : LieRing (L × ℝ) :=
  inferInstanceAs (LieRing (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)))
local instance : LieAlgebra ℝ (L × ℝ) :=
  inferInstanceAs (LieAlgebra ℝ (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)))

include D hD hone hmul

local notation "ST" => GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)

def semidirectIdealInclusion :
    @MonoidHom L (L × ℝ) P.group.toMulOne
      (inferInstance : Group (L × ℝ)).toMulOne := by
  letI : MulOneClass (L × ℝ) := (inferInstance : Group (L × ℝ)).toMulOneClass
  exact {
  toFun x := (x, 0)
  map_one' := by
    change ((1 : L), (0 : ℝ)) = (inferInstance : Group (L × ℝ)).one
    rw [hone, P.one_eq_zero]
    rfl
  map_mul' x y := by
    change (x * y, (0 : ℝ)) = (inferInstance : Group (L × ℝ)).mul (x, 0) (y, 0)
    rw [hmul]
    simp only [nilpotentDerivationFlow_zero, zero_add] }

omit [LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ)] in
theorem contMDiff_semidirectIdealInclusion :
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L × ℝ)) ∞ (semidirectIdealInclusion D hD hone hmul) :=
  (contDiff_id.prodMk contDiff_const).contMDiff

def semidirectIdealLieHom : L →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ) :=
  (homLieDifferential (semidirectIdealInclusion D hD hone hmul)
    (contMDiff_semidirectIdealInclusion D hD hone hmul)).comp P.tangentEquiv.toLieHom

theorem semidirectIdealLieHom_apply (v : L) :
    semidirectIdealLieHom D hD hone hmul v = (v, 0) := by
  change mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, L × ℝ))
    (fun x : L => (x, (0 : ℝ))) 1 (P.tangentEquiv v) = _
  rw [P.one_eq_zero]
  have hd := (ContinuousLinearMap.inl ℝ L ℝ).hasFDerivAt (x := (0 : L))
  change (mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, L × ℝ))
    (ContinuousLinearMap.inl ℝ L ℝ) 0) (show L from P.tangentEquiv v) = _
  have he : (show L from P.tangentEquiv v) = v := P.tangentEquiv_apply v
  rw [he]
  exact congrArg (fun A : L →L[ℝ] (L × ℝ) => A v) hd.hasMFDerivAt.mfderiv

theorem semidirect_ideal_bracket (v w : L) :
    ⁅((v, 0) : ST), ((w, 0) : ST)⁆ = (⁅v, w⁆, 0) := by
  have h := (semidirectIdealLieHom D hD hone hmul).map_lie v w
  rw [semidirectIdealLieHom_apply, semidirectIdealLieHom_apply,
    semidirectIdealLieHom_apply] at h
  exact h.symm

omit [LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ)] in
theorem semidirect_invariant_axis (v : L × ℝ) (t : ℝ) :
    mulInvariantVectorField (I := 𝓘(ℝ, L × ℝ)) (G := L × ℝ) v (0, t) =
      (nilpotentDerivationFlow D hD t v.1, v.2) := by
  let A := (nilpotentDerivationFlow D hD t).toLinearEquiv.toContinuousLinearEquiv
  let B : (L × ℝ) →L[ℝ] (L × ℝ) :=
    (A.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ L ℝ)).prod
      (ContinuousLinearMap.snd ℝ L ℝ)
  have heq : (fun p : L × ℝ => (inferInstance : Group (L × ℝ)).mul (0, t) p) =
      (fun p => (A p.1, t + p.2)) := by
    funext p
    rw [hmul]
    rw [← P.one_eq_zero, one_mul]
    rfl
  have hd : HasFDerivAt (fun p : L × ℝ => (A p.1, t + p.2)) B 0 :=
    ((A.toContinuousLinearMap.hasFDerivAt.comp 0
      (ContinuousLinearMap.fst ℝ L ℝ).hasFDerivAt).prodMk
      ((ContinuousLinearMap.snd ℝ L ℝ).hasFDerivAt.const_add t))
  change mfderiv (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, L × ℝ))
    (fun p : L × ℝ => (inferInstance : Group (L × ℝ)).mul (0, t) p)
      (inferInstance : Group (L × ℝ)).one v = _
  rw [hone, heq, hd.hasMFDerivAt.mfderiv]
  rfl

theorem semidirect_invariant_time (g : L × ℝ) :
    mulInvariantVectorField (I := 𝓘(ℝ, L × ℝ)) (G := L × ℝ) (0, 1) g = (0, 1) := by
  let f : (L × ℝ) → (L × ℝ) := fun p => (inferInstance : Group (L × ℝ)).mul g p
  let : Monoid (L × ℝ) := (inferInstance : Group (L × ℝ)).toMonoid
  let : Mul (L × ℝ) := (inferInstance : Group (L × ℝ)).toMul
  have hs : ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, L × ℝ)) ∞ f :=
    contMDiff_mul_left (I := 𝓘(ℝ, L × ℝ)) (a := g)
  have hf : DifferentiableAt ℝ f 0 :=
    (hs.contDiff.differentiable (by simp)).differentiableAt
  have hline : HasDerivAt (fun t : ℝ => ((0 : L), t)) (0, 1) 0 :=
    (hasDerivAt_const 0 (0 : L)).prodMk (hasDerivAt_id 0)
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt 0 hline
  have heq : (fun t : ℝ => f (0, t)) = fun t => (g.1, g.2 + t) := by
    funext t
    dsimp only [f]
    rw [hmul, map_zero, ← P.one_eq_zero, mul_one]
  have hd : HasDerivAt (fun t : ℝ => f (0, t)) (0, 1) 0 := by
    rw [heq]
    exact (hasDerivAt_const 0 g.1).prodMk ((hasDerivAt_id 0).const_add g.2)
  have hval := hcomp.unique hd
  change mfderiv (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, L × ℝ)) f
    (inferInstance : Group (L × ℝ)).one (0, 1) = _
  rw [hone, mfderiv_eq_fderiv]
  exact hval

theorem semidirect_time_bracket (v : L) :
    ⁅((0, 1) : ST), ((v, 0) : ST)⁆ = (D v, 0) := by
  let u : ST := (0, 1)
  let w : ST := (v, 0)
  let V : (L × ℝ) → (L × ℝ) := fun g =>
    mulInvariantVectorField (I := 𝓘(ℝ, L × ℝ)) (G := L × ℝ) w g
  have hV : ContDiff ℝ ∞ V := contMDiff_vectorSpace_iff_contDiff.mp
    (contMDiff_invariantVectorField_infty (E := L × ℝ) (G := L × ℝ) w)
  have hline : HasDerivAt (fun t : ℝ => ((0 : L), t)) (0, 1) 0 :=
    (hasDerivAt_const 0 (0 : L)).prodMk (hasDerivAt_id 0)
  have hc := (hV.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline
  have heq : (fun t : ℝ => V (0, t)) =
      (fun t => (nilpotentDerivationFlow D hD t v, (0 : ℝ))) := by
    funext t
    exact semidirect_invariant_axis D hD hone hmul (v, 0) t
  have hd : HasDerivAt (fun t : ℝ => V (0, t)) (D v, 0) 0 := by
    rw [heq]
    exact (hasDerivAt_nilpotentDerivationFlow_zero D hD v).prodMk (hasDerivAt_const 0 0)
  have hder := hc.unique hd
  change ⁅u, w⁆ = _
  rw [GroupLieAlgebra.bracket_def]
  change @Eq (L × ℝ) (mlieBracket (𝓘(ℝ, L × ℝ))
    (fun g : L × ℝ => (mulInvariantVectorField u g : L × ℝ)) V
    (inferInstance : Group (L × ℝ)).one) (D v, 0)
  rw [hone]
  apply (congrFun (mlieBracketWithin_eq_lieBracketWithin
    (V := fun g : L × ℝ => (mulInvariantVectorField u g : L × ℝ))
    (W := V) (s := Set.univ)) (0 : L × ℝ)).trans
  have htime : mulInvariantVectorField (I := 𝓘(ℝ, L × ℝ)) (G := L × ℝ) u =
      (fun _ : L × ℝ => (0, 1)) := funext (semidirect_invariant_time D hD hone hmul)
  rw [htime]
  rw [lieBracketWithin_univ]
  change fderiv ℝ V 0 (0, 1) - fderiv ℝ (fun _ : L × ℝ => (0, 1)) 0 (V 0) = _
  have hz : fderiv ℝ (fun _ : L × ℝ => ((0 : L), (1 : ℝ))) (0 : L × ℝ) = 0 :=
    (hasFDerivAt_const ((0 : L), (1 : ℝ)) (0 : L × ℝ)).fderiv
  rw [hz, zero_apply]
  exact (sub_zero ((fderiv ℝ V (0 : L × ℝ)) (0, 1))).trans hder

theorem semidirect_tangent_bracket (v w : L) (s t : ℝ) :
    ⁅((v, s) : ST), ((w, t) : ST)⁆ =
      (⁅v, w⁆ + s • D w - t • D v, 0) := by
  let u : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ) := (0, 1)
  let a : ST := (v, 0)
  let b : ST := (w, 0)
  let vs : ST := (v, s)
  let wt : ST := (w, t)
  have hv : vs = a + s • u := by
    change (v, s) = ((v, 0) : L × ℝ) + s • ((0, 1) : L × ℝ)
    ext <;> simp
  have hw : wt = b + t • u := by
    change (w, t) = ((w, 0) : L × ℝ) + t • ((0, 1) : L × ℝ)
    ext <;> simp
  have hcross : ⁅a, u⁆ = -((D v, 0) : ST) := by
    exact (lie_skew a u).symm.trans
      (congrArg (fun z : ST => -z) (semidirect_time_bracket D hD hone hmul v))
  have hideal : ⁅a, b⁆ = ((⁅v, w⁆, 0) : ST) :=
    semidirect_ideal_bracket D hD hone hmul v w
  have htime : ⁅u, b⁆ = ((D w, 0) : ST) :=
    semidirect_time_bracket D hD hone hmul w
  change @Eq ST ⁅vs, wt⁆ ((⁅v, w⁆ + s • D w - t • D v, 0) : ST)
  rw [hv, hw, add_lie, lie_add, lie_add, lie_smul, smul_lie, smul_lie, lie_smul,
    hideal, hcross, htime, lie_self]
  change @Eq (L × ℝ) _ _
  apply Prod.ext
  · change (⁅v, w⁆ + t • -D v) + (s • D w + s • t • (0 : L)) =
      ⁅v, w⁆ + s • D w - t • D v
    simp only [smul_neg, smul_zero, add_zero, sub_eq_add_neg]
    abel
  · change ((0 : ℝ) + t * -0) + (s * 0 + s * (t * 0)) = 0
    simp

end TangentComputation
end PolycyclicRecognition

end

end OAI
