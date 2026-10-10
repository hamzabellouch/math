import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceCurveCoordinates
import OAI.Geometry.SurfaceImmersion.Whitney.RegularArcPaths

namespace OAI

/-! A compact regular surface curve is a finite concatenation of actual
smooth embedded pieces. It need not itself be embedded. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma regular_curve_local_injective {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    {t : ℝ} (ht : t ∈ U)
    (hreg : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧ V ⊆ U ∧ V.InjOn γ := by
  obtain ⟨c,V,hV,htV,hVU,_,_,hcoord⟩ := surface_curve_coordinates hU hγ ht hreg
  refine ⟨V,hV,htV,hVU,?_⟩
  intro x hx y hy he
  have hc : (![0,x] : Base) = ![0,y] :=
    (hcoord x hx).2.symm.trans ((congrArg c he).trans (hcoord y hy).2)
  have h1 := congrFun hc 1
  simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using h1

theorem regular_curve_finite_pieces {γ : ℝ → M} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    (hreg : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t))
    (hab : a ≤ b) (hsub : Icc a b ⊆ U) :
    ∃ (τ : ℕ → ℝ) (N : ℕ), τ 0 = a ∧ Monotone τ ∧
      (∀ n, a ≤ τ n ∧ τ n ≤ b) ∧ (∀ n ≥ N, τ n = b) ∧
      ∀ n, τ n < τ (n+1) → ∃ P : SmoothCompactArc planeModel M,
        P.curve = γ ∧ P.start = τ n ∧ P.finish = τ (n+1) := by
  have hl (t : Icc a b) := regular_curve_local_injective hU hγ
    (hsub t.property) (hreg t (hsub t.property))
  choose V hV htV hVU hVi using hl
  let C : Icc a b → Set (Icc a b) := fun t => Subtype.val ⁻¹' V t
  have hC : ∀ t, IsOpen (C t) := fun t => (hV t).preimage continuous_subtype_val
  have hcover : univ ⊆ ⋃ t, C t := by
    intro t _
    exact mem_iUnion.mpr ⟨t,htV t⟩
  obtain ⟨τ,hzero,hmono,⟨N,hend⟩,hpieces⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hC hcover
  refine ⟨fun n => (τ n).val,N,hzero,fun _ _ h => hmono h,
    fun n => (τ n).property,hend,?_⟩
  intro n hn
  obtain ⟨t,ht⟩ := hpieces n
  have hinterval : Icc (τ n).val (τ (n+1)).val ⊆ V t := by
    intro s hs
    have hsab : s ∈ Icc a b :=
      ⟨(τ n).property.1.trans hs.1,hs.2.trans (τ (n+1)).property.2⟩
    exact ht (show (⟨s,hsab⟩ : Icc a b) ∈ Icc (τ n) (τ (n+1)) from hs)
  let P : SmoothCompactArc planeModel M :=
    ⟨γ,τ n,τ (n+1),hn,V t,hV t,hinterval,hγ.mono (hVU t),
      fun s hs => hreg s (hVU t hs),(hVi t).mono hinterval⟩
  exact ⟨P,rfl,rfl,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
