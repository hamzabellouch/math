import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactRotationalTwist
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactSemidirectModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialExponentialCoordinates

namespace OAI

/-! # The analytic solvable model on an invariant graph

The graph uses the original vector-space chart. Its operations are analytic,
and its dimension is the dimension of the nilpotent group alone.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance] semidirectProductTopology
variable {L V : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group.IsSolvable L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (φ : Multiplicative V →* MulAut L) (τ : L →* Multiplicative V)
  (hinv : ∀ v x, τ (φ v x) = τ x)
  (hφ : ContDiff ℝ ⊤ (fun p : V × L => φ (Multiplicative.ofAdd p.1) p.2))
  (hτ : ContDiff ℝ ⊤ (fun x => (τ x).toAdd))

def invariantGraphEquiv : L ≃ rotationalTwist φ τ hinv where
  toFun x := ⟨⟨x, (τ x)⁻¹⟩, rfl⟩
  invFun x := x.val.left
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact x.property.symm

@[instance_reducible]
def invariantGraphGroup : Group L := (invariantGraphEquiv φ τ hinv).group

include hφ hτ in
omit [Group.IsSolvable L] [FiniteDimensional ℝ V] in
theorem invariantGraphLieGroup :
    letI := invariantGraphGroup φ τ hinv
    LieGroup (𝓘(ℝ, L)) ⊤ L := by
  have hm : ContMDiff ((𝓘(ℝ, L)).prod (𝓘(ℝ, L))) (𝓘(ℝ, L)) ⊤
      (fun p : L × L => P.group.mul p.1 (φ ((τ p.1)⁻¹) p.2)) := by
    have hs : ContDiff ℝ ⊤ (fun p : L × L =>
        φ (Multiplicative.ofAdd (-(τ p.1).toAdd)) p.2) :=
      hφ.comp (((hτ.comp contDiff_fst).neg).prodMk contDiff_snd)
    exact contMDiff_fst.mul (hs.comp_contMDiff (contMDiff_fst.prodMk_space contMDiff_snd))
  have hi : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ⊤
      (fun x : L => φ (τ x) (P.group.inv x)) := by
    have hs : ContDiff ℝ ⊤ (fun x : L =>
        φ (Multiplicative.ofAdd (τ x).toAdd) (P.group.inv x)) :=
      hφ.comp (hτ.prodMk (contMDiff_id.inv.contDiff))
    exact hs.contMDiff
  have hig (x : L) : (invariantGraphGroup φ τ hinv).inv x = φ (τ x) (P.group.inv x) := by
    change φ (((τ x)⁻¹)⁻¹) (P.group.inv x) = _
    rw [inv_inv]
  let := invariantGraphGroup φ τ hinv
  refine { toIsManifold := inferInstance, contMDiff_mul := hm, contMDiff_inv := ?_ }
  convert hi using 1
  funext x
  exact hig x

def invariantGraphMulEquiv :
    let T := rotationalTwist φ τ hinv
    letI := invariantGraphGroup φ τ hinv
    L ≃* T := by
  let T := rotationalTwist φ τ hinv
  let e := invariantGraphEquiv φ τ hinv
  letI := invariantGraphGroup φ τ hinv
  refine { e with map_mul' := ?_ }
  intro x y
  change e (e.symm (e x * e y)) = e x * e y
  exact e.apply_symm_apply _

include hφ hτ in
def invariantGraphLieModel : SimplyConnectedSolvableLieModel := by
  let T := rotationalTwist φ τ hinv
  have hsolv : Group.IsSolvable T := by
    let : Group.IsSolvable (L ⋊[φ] Multiplicative V) := semidirect_solvable φ
    infer_instance
  let e1 := invariantGraphMulEquiv φ τ hinv
  have hLie := invariantGraphLieGroup φ τ hinv hφ hτ
  let g := invariantGraphGroup φ τ hinv
  letI : Group L := g
  letI : Mul L := g.toMul
  letI : One L := g.toOne
  letI : Monoid L := g.toMonoid
  letI : MulOneClass L := g.toMulOneClass
  letI : LieGroup (𝓘(ℝ, L)) ⊤ L := hLie
  let e : L ≃* T := e1
  let := hsolv
  letI : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact { modelSpace := L, carrier := L }

def invariantGraphModelEquiv : (invariantGraphLieModel φ τ hinv hφ hτ).carrier ≃*
    rotationalTwist φ τ hinv :=
  invariantGraphMulEquiv φ τ hinv

omit [FiniteDimensional ℝ V] in
theorem invariantGraphModelEquiv_continuous : Continuous (invariantGraphModelEquiv φ τ hinv hφ hτ) :=
  (rotationalTwistHomeomorph φ τ hinv hτ.continuous).symm.continuous

omit [FiniteDimensional ℝ V] in
theorem invariantGraphModelEquiv_symm_continuous :
    Continuous (invariantGraphModelEquiv φ τ hinv hφ hτ).symm :=
  (rotationalTwistHomeomorph φ τ hinv hτ.continuous).continuous

end PolycyclicRecognition

end

end OAI
