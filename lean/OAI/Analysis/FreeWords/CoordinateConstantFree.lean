import Mathlib
import OAI.Analysis.FreeWords.CoordinateFreeExtract

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace

open Filter Topology

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (R : ℕ → StarSubalgebra ℂ A) [∀ j, IsClosed (R j : Set A)]

local instance constantFreeOrder : PartialOrder (coordinateAlgebra R) := CStarAlgebra.spectralOrder _

local instance coordinateConstantFreeLE : LE (coordinateAlgebra R) := (constantFreeOrder R).toLE

local instance coordinateConstantFreePreorder : Preorder (coordinateAlgebra R) := (constantFreeOrder R).toPreorder

local instance coordinateConstantFreeSOR : StarOrderedRing (coordinateAlgebra R) := CStarAlgebra.spectralOrderedRing _

def coordinateConstant (x : A) (hx : ∀j,x∈R j) : coordinateAlgebra R :=
  ⟨BoundedContinuousFunction.const ℕ x,hx⟩

theorem trace_coordinateConstant (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (x : A) (hx : ∀j,x∈R j) : coordinateTrace R τ ω (coordinateConstant R x hx)=τ x := by
  exact tendsto_nhds_unique (tendsto_ultraTraceValue τ ω (BoundedContinuousFunction.const ℕ x))
    tendsto_const_nhds

theorem coordinate_constant_free (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ)≤atTop)
    (hF : IsFactor (gnsVonNeumann (coordinateTrace R τ ω)))
    (hD : IsDiffuse (gnsVonNeumann (coordinateTrace R τ ω)))
    (K : Finset ℤ) (F : Finset (List (ℤ × A)))
    (hFne : ∀ w∈F, w≠[])
    (hcenter : ∀ w∈F, ∀ z∈w, z.1≠0 ∧ τ z.2=0)
    (hmem : ∀ w∈F, ∀ z∈w, ∀j, z.2∈R j)
    (ε : ℝ) (hε : 0<ε) (N : ℕ) :
    ∃ j : ℕ, N≤j ∧ ∃ u : unitary A, u.val∈R j ∧
      (∀ k∈K, k≠0 → ‖τ ((u^k).val)‖<ε) ∧
      (∀ w∈F, ‖τ ((w.map (fun z => ((u^z.1).val)*z.2)).prod)‖<ε) := by
  classical
  let lift (x : A) : coordinateAlgebra R :=
    if hx : ∀j,x∈R j then coordinateConstant R x hx else 0
  have hlift (x : A) (hx : ∀j,x∈R j) : lift x=coordinateConstant R x hx := dite_eq_left hx
  let wf : List (ℤ × A) → List (ℤ × coordinateAlgebra R) :=
    List.map (fun z => (z.1,lift z.2))
  have hn : ∀ w∈F.image wf, w≠[] := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    intro hz
    exact hFne v hv (List.map_eq_nil_iff.mp hz)
  have hc : ∀ w∈F.image wf, ∀ z∈w,
      z.1≠0 ∧ coordinateTrace R τ ω z.2=0 := by
    intro w hw z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    refine ⟨(hcenter v hv a ha).1,?_⟩
    change coordinateTrace R τ ω (lift a.2)=0
    rw [hlift a.2 (hmem v hv a ha),trace_coordinateConstant]
    exact (hcenter v hv a ha).2
  obtain ⟨j,hjN,u,huR,huK,huF⟩ := coordinate_free_extract R τ h1 htr ω hω hF hD
    K (F.image wf) hn hc ε hε N
  refine ⟨j,hjN,u,huR,huK,?_⟩
  intro w hw
  have hh := huF (wf w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
  have he : ((wf w).map (fun z => (u^z.1).val*(z.2.val j)))=
      w.map (fun z => (u^z.1).val*z.2) := by
    simp only [wf,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro z hz
    rw [hlift z.2 (hmem w hw z hz)]
    rfl
  rwa [he] at hh

end

end KKVariableUltra
end

end OAI
