import Mathlib
import OAI.Analysis.FreeWords.FactorStructure
import OAI.Analysis.FreeWords.VariableUltraBundle

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKUltraTrace KKFreeLiftFrontier

open scoped ComplexOrder InnerProductSpace BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gns_factor_of_center_scalar (τ : A →ₚ[ℂ] ℂ)
    (hrange : τ.gnsStarAlgHom.range = (gnsVonNeumann τ).toStarSubalgebra)
    (hcenter : ∀ a : A, (∀ b : A, Commute (τ.gnsStarAlgHom a) (τ.gnsStarAlgHom b)) →
      τ.gnsStarAlgHom a = τ a • 1) : IsFactor (gnsVonNeumann τ) := by
  intro x hx
  have hmem : x.val ∈ τ.gnsStarAlgHom.range := by
    rw [hrange]
    exact x.property
  obtain ⟨a, ha⟩ := hmem
  change τ.gnsStarAlgHom a = x.val at ha
  have hac : ∀ b : A, Commute (τ.gnsStarAlgHom a) (τ.gnsStarAlgHom b) := by
    intro b
    rw [ha]
    exact congrArg Subtype.val (hx (gnsBiHom τ b)).eq
  refine ⟨τ a, ?_⟩
  apply Subtype.ext
  change x.val = τ a • 1
  rw [← ha]
  exact hcenter a hac

variable (R : ℕ → StarSubalgebra ℂ A) [∀ j, IsClosed (R j : Set A)]

local instance ultraFactorOrder : PartialOrder (coordinateAlgebra R) := CStarAlgebra.spectralOrder _

local instance ultraFactorLE : LE (coordinateAlgebra R) := (ultraFactorOrder R).toLE

local instance ultraFactorPreorder : Preorder (coordinateAlgebra R) := (ultraFactorOrder R).toPreorder

local instance ultraFactorSOR : StarOrderedRing (coordinateAlgebra R) := CStarAlgebra.spectralOrderedRing _

theorem map_commutator_zero {B C : Type*} [Ring B] [Ring C]
    [Algebra ℂ B] [Algebra ℂ C] [StarRing B] [StarRing C]
    (f : B →⋆ₐ[ℂ] C) (x y : B) (h : Commute (f x) (f y)) : f (x*y-y*x)=0 := by
  rw [map_sub,map_mul,map_mul,h.eq,sub_self]

theorem gns_commutator_norm_zero (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (x y : A)
    (hxy : Commute (τ.gnsStarAlgHom x) (τ.gnsStarAlgHom y)) :
    ‖gnsVector τ (x*y-y*x)‖ = 0 := by
  have hzero := map_commutator_zero τ.gnsStarAlgHom x y hxy
  have hτ := (tracial_gns_zero τ htr (x*y-y*x)).mp hzero
  rw [gns_norm_sqrt,hτ,Complex.zero_re,Real.sqrt_zero]

theorem map_eq_scalar_of_centered_zero {B C : Type*} [Ring B] [Ring C]
    [Algebra ℂ B] [Algebra ℂ C] [StarRing B] [StarRing C]
    (f : B →⋆ₐ[ℂ] C) (x : B) (c : ℂ) (hx : f (x-c•1)=0) :
    f x = c • 1 := by
  rwa [map_sub,map_smul,map_one,sub_eq_zero] at hx

theorem gns_center_scalar_of_commutator_norm (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (x : A)
    (hx : ∀ y : A, Commute (τ.gnsStarAlgHom x) (τ.gnsStarAlgHom y))
    (hbound : ∃ y : A, ‖gnsVector τ (x*y-y*x)‖ = 0 →
      ‖gnsVector τ (x-τ x•1)‖ = 0) :
    τ.gnsStarAlgHom x = τ x • 1 := by
  obtain ⟨y, hy⟩ := hbound
  have hzero := norm_eq_zero.mp (hy (gns_commutator_norm_zero τ htr x y (hx y)))
  have hτ : τ (star (x-τ x•1)*(x-τ x•1)) = 0 := by
    rw [← gnsVector_inner,hzero,inner_zero_left]
  exact map_eq_scalar_of_centered_zero τ.gnsStarAlgHom x (τ x)
    ((tracial_gns_zero τ htr (x-τ x•1)).mpr hτ)

theorem coordinate_gns_zero_of_norm_tendsto (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (ω : Ultrafilter ℕ) (x : coordinateAlgebra R)
    (hx : Tendsto (fun j => ‖gnsVector τ (x.val j)‖) (ω : Filter ℕ) (𝓝 0)) :
    (coordinateTrace R τ ω).gnsStarAlgHom x=0 := by
  apply (tracial_gns_zero _ (coordinateTrace_tracial R τ ω htr) x).mpr
  have hn := tendsto_nhds_unique (coordinate_norm_tendsto R τ ω x) hx
  have hz := norm_eq_zero.mp hn
  rw [← gnsVector_inner, hz,inner_zero_left]

theorem coordinate_centered_norm_tendsto_zero (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (x w : coordinateAlgebra R)
    (hbound : ∀ j, ‖gnsVector τ (x.val j - τ (x.val j) • 1)‖ ≤
      2 * ‖gnsVector τ (w.val j)‖)
    (hwlim : Tendsto (fun j => ‖gnsVector τ (w.val j)‖) (ω : Filter ℕ) (𝓝 0)) :
    Tendsto (fun j => ‖gnsVector τ ((x - (coordinateTrace R τ ω x) • 1).val j)‖)
      (ω : Filter ℕ) (𝓝 0) := by
  let c := coordinateTrace R τ ω x
  have hbound' (j : ℕ) : ‖gnsVector τ ((x-c•1).val j)‖ ≤
      2*‖gnsVector τ (w.val j)‖+‖τ (x.val j)-c‖*‖gnsVector τ 1‖ := by
    have hid : (x-c•1).val j=(x.val j-τ (x.val j)•1)+(τ (x.val j)-c)•1 := by
      change x.val j-c•1=_
      rw [sub_smul]; abel
    rw [hid,map_add]
    apply (norm_add_le _ _).trans
    rw [map_smul,norm_smul]
    exact add_le_add (hbound j) le_rfl
  have hc : Tendsto (fun j => ‖τ (x.val j)-c‖) (ω : Filter ℕ) (𝓝 0) := by
    have ht : Tendsto (fun j => τ (x.val j)) (ω : Filter ℕ) (𝓝 c) :=
      tendsto_ultraTraceValue τ ω x.val
    simpa only [sub_self,norm_zero] using (ht.sub_const c).norm
  have hr : Tendsto (fun j => 2*‖gnsVector τ (w.val j)‖+‖τ (x.val j)-c‖*‖gnsVector τ 1‖)
      (ω : Filter ℕ) (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using
      (hwlim.const_mul 2).add (hc.mul_const ‖gnsVector τ 1‖)
  exact squeeze_zero (fun j => norm_nonneg _) hbound' hr

omit [∀ j, IsClosed (R j : Set A)] in
theorem coordinate_commutator_bound (τ : A →ₚ[ℂ] ℂ)
    (hw : ∀ j, ∀ x∈R j, ∃ u : unitary A, u.val∈R j ∧
      ‖gnsVector τ (x-τ x•1)‖ ≤ 2*‖gnsVector τ (x*u.val-u.val*x)‖)
    (x : coordinateAlgebra R) :
    ∃ y : coordinateAlgebra R, ∀ j, ‖gnsVector τ (x.val j-τ (x.val j)•1)‖ ≤
      2*‖gnsVector τ ((x*y-y*x).val j)‖ := by
  choose u huR hu using (fun j => hw j (x.val j) (x.property j))
  let y₀ : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun j => (u j).val) continuous_of_discreteTopology ‖(1 : A)‖
    (fun j => by simpa only [mul_one] using (CStarRing.norm_coe_unitary_mul (u j) (1 : A)).le)
  exact ⟨⟨y₀,huR⟩, hu⟩

theorem coordinate_center_scalar (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y)=τ (y*x))
    (hw : ∀ j, ∀ x∈R j, ∃ u : unitary A, u.val∈R j ∧
      ‖gnsVector τ (x-τ x•1)‖ ≤ 2*‖gnsVector τ (x*u.val-u.val*x)‖)
    (ω : Ultrafilter ℕ) (x : coordinateAlgebra R)
    (hx : ∀ y : coordinateAlgebra R,
      Commute ((coordinateTrace R τ ω).gnsStarAlgHom x)
        ((coordinateTrace R τ ω).gnsStarAlgHom y)) :
    (coordinateTrace R τ ω).gnsStarAlgHom x=(coordinateTrace R τ ω x)•1 := by
  apply gns_center_scalar_of_commutator_norm (coordinateTrace R τ ω)
    (coordinateTrace_tracial R τ ω htr) x hx
  obtain ⟨y, hu⟩ := coordinate_commutator_bound R τ hw x
  refine ⟨y, fun hwnorm => ?_⟩
  let w := x*y-y*x
  have hwlim : Tendsto (fun j => ‖gnsVector τ (w.val j)‖) (ω : Filter ℕ) (𝓝 0) := by
    simpa only [w,hwnorm] using coordinate_norm_tendsto R τ ω w
  let c := coordinateTrace R τ ω x
  let v : coordinateAlgebra R := x-c•1
  have hlim := coordinate_centered_norm_tendsto_zero R τ ω x w hu hwlim
  exact tendsto_nhds_unique (coordinate_norm_tendsto R τ ω v) hlim

theorem coordinate_factor (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y)=τ (y*x))
    (hw : ∀ j, ∀ x∈R j, ∃ u : unitary A, u.val∈R j ∧
      ‖gnsVector τ (x-τ x•1)‖ ≤ 2*‖gnsVector τ (x*u.val-u.val*x)‖)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop) :
    IsFactor (gnsVonNeumann (coordinateTrace R τ ω)) := by
  exact gns_factor_of_center_scalar (coordinateTrace R τ ω)
    (coordinate_gns_range R τ htr ω hω) (coordinate_center_scalar R τ htr hw ω)

end

end KKVariableUltra
end

end OAI
