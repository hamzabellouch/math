import OAI.Geometry.SurfaceImmersion.Geometry.PublishedInputs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

/-! Regular two-dimensional coordinate values have finite fibers on a
compact set. This supplies the finite crossing sets for generic radii. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PublishedInputs

lemma regular_point_locally_injective {f : Plane → Plane} (hf : ContDiff ℝ ∞ f)
    {x : Plane} (hreg : Function.Surjective (fderiv ℝ f x)) :
    ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧ U.InjOn f := by
  have hinj : Function.Injective (fderiv ℝ f x) :=
    LinearMap.injective_iff_surjective.mpr hreg
  let L : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.ofBijective (fderiv ℝ f x)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hreg)
  have hd : HasFDerivAt f L.toContinuousLinearMap x :=
    (hf.differentiable (by simp) x).hasFDerivAt
  let e := hf.contDiffAt.toOpenPartialHomeomorph f hd (by simp)
  exact ⟨e.source,e.open_source,hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),e.injOn⟩

theorem finite_compact_regular_fiber {f : Plane → Plane} (hf : ContDiff ℝ ∞ f)
    {K : Set Plane} (hK : IsCompact K) (y : Plane)
    (hreg : ∀ x ∈ K, f x = y → Function.Surjective (fderiv ℝ f x)) :
    (K ∩ {x | f x = y}).Finite := by
  have hcompact : IsCompact (K ∩ {x | f x = y}) :=
    hK.inter_right (isClosed_eq hf.continuous continuous_const)
  apply hcompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨U,hU,hxU,hUinj⟩ := regular_point_locally_injective hf (hreg x hx.1 hx.2)
  refine ⟨U,hU,?_⟩
  ext z
  constructor
  · rintro ⟨hzU,hzK,hzy⟩
    exact mem_singleton_iff.mpr (hUinj hzU hxU (hzy.trans hx.2.symm))
  · rintro rfl
    exact ⟨hxU,hx⟩

/-- Simultaneous regular values with finite fibers exist in every nonempty
open parameter set. -/
theorem exists_simultaneous_finite_regular_fibers {ι : Type*} [Countable ι]
    (f : ι → Plane → Plane) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (K : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (U : Set Plane) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y ∈ U, (∀ i x, f i x = y → Function.Surjective (fderiv ℝ (f i) x)) ∧
      ∀ i, (K i ∩ {x | f i x = y}).Finite := by
  obtain ⟨y,hy,hreg⟩ := exists_simultaneous_regular_value_unconditional f hf U hU hne
  exact ⟨y,hy,hreg,fun i => finite_compact_regular_fiber (hf i) (hK i) y
    (fun x _ hxy => hreg i x hxy)⟩

end ClosedSurfaceR4.PublishedInputs

end

end OAI
