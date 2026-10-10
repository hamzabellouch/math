import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.PatchConstruction

namespace OAI

/-! Residual filling for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace Rep

def trivial {p : M} (hp : IsStarProjection p) : Rep G M where
  val _ := p
  mul _ _ := hp.isIdempotentElem.eq.symm
  inv _ := hp.isSelfAdjoint.star_eq.symm

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma trivial_support {p : M} (hp : IsStarProjection p) :
    (trivial (G:=G) hp).support=p := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma residual_orthogonal (v : Rep G M) : v.support*(1-v.support)=0 := by
  rw [mul_sub,mul_one,v.support_projection.isIdempotentElem.eq,sub_self]

def fill (v : Rep G M) : Rep G M :=
  v.add (trivial v.support_projection.one_sub) v.residual_orthogonal

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma fill_apply (v : Rep G M) (g : G) : v.fill g=v g+(1-v.support) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma fill_support (v : Rep G M) : v.fill.support=1 := by
  change v.support+(1-v.support)=1
  abel

def toUnitary (v : Rep G M) (hv : v.support=1) : G →* unitary M where
  toFun g := ⟨v g,by
    rw [Unitary.mem_iff]
    exact ⟨(v.star_mul_self g).trans hv,(v.mul_star_self g).trans hv⟩⟩
  map_one' := Subtype.ext hv
  map_mul' g h := Subtype.ext (v.mul g h)

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma toUnitary_coe (v : Rep G M) (hv) (g) : (v.toUnitary hv g:M)=v g := rfl
end Rep

variable {C B : Type*}
lemma fill_evaluate_error (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (h1 : τ 1=1) (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G)
    (v : Rep G M) (d : ℝ) (hd : 0≤d) (hv : (τ (1-v.support)).re≤d^2)
    (l : List (Letter C B)) :
    ‖τ (evaluate a γ v.fill l)-τ (evaluate a γ v l)‖≤(l.length:ℝ)*d := by
  have hp := v.support_projection.one_sub
  have hsq : ‖τ.toPreGNS (1-v.support)‖^2=(τ (1-v.support)).re := by
    rw [PopaMatrices.System.norm_sq_eq_trace,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  have hnorm : ‖τ.toPreGNS (1-v.support)‖≤d := by nlinarith [norm_nonneg (τ.toPreGNS (1-v.support))]
  have he (x : Letter C B) (_ : x ∈ l) :
      ‖τ.toPreGNS (letterValue a γ v.fill x-letterValue a γ v x)‖≤d := by
    cases x with
    | inl c => simpa only [letterValue,Sum.elim_inl,sub_self,map_zero,norm_zero] using hd
    | inr b =>
      change ‖τ.toPreGNS ((v (γ b)+(1-v.support))-v (γ b))‖≤d
      simpa only [add_sub_cancel_left] using hnorm
  rw [←map_sub]
  exact (HochschildUltrapower.norm_trace_le τ h1 _).trans
    (prod_gns_sub_uniform τ htr l (letterValue a γ v.fill) (letterValue a γ v)
      (fun x _ => letter_norm_le a ha γ v.fill x)
      (fun x _ => letter_norm_le a ha γ v x) d he)

universe u v
variable {C B D : Type u} [Fintype C] [Fintype B]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include e hτ htr hfaith h1 hfactor in

theorem finite_unitary_moments (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → FreeGroup D) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ v : Rep (FreeGroup D) M, v.support=1 ∧
      ∀ l : List (Letter C B), l.length≤L → degree γ l ≠ 1 → ‖τ (evaluate a γ v l)‖<η := by
  let d : ℝ := η/(2*((L:ℝ)+1))
  have hd : 0<d := div_pos hη (by positivity)
  obtain ⟨v,hv,hgood⟩ := exists_almost_full_good e τ hτ htr hfaith h1 hfactor hdiff
    a ha γ b0 hb0 L (d^2) (η/2) (sq_pos_of_pos hd) (by positivity)
  refine ⟨v.fill,v.fill_support,fun l hl hdg => ?_⟩
  have he := fill_evaluate_error τ htr h1 a ha γ v d hd.le hv.le l
  have ho := hgood l hl hdg
  have hdeq : d*(2*((L:ℝ)+1))=η := div_mul_cancel₀ _ (by positivity)
  have hlen : (l.length:ℝ)≤L := by exact_mod_cast hl
  have hbound := norm_add_le (τ (evaluate a γ v.fill l)-τ (evaluate a γ v l)) (τ (evaluate a γ v l))
  rw [sub_add_cancel] at hbound
  nlinarith
end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching
universe u v
variable {C B D : Type u} [Fintype C] [Fintype B]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem finite_unitary_moments (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → FreeGroup D) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ v : Rep (FreeGroup D) M, v.support=1 ∧
      ∀ l : List (Letter C B), l.length≤L → degree γ l ≠ 1 → ‖τ (evaluate a γ v l)‖<η := by
  let d : ℝ := η/(2*((L:ℝ)+1))
  have hd : 0<d := div_pos hη (by positivity)
  obtain ⟨v,hv,hgood⟩ := exists_almost_full_good e τ hτ htr hfaith h1 hII
    a ha γ b0 hb0 L (d^2) (η/2) (sq_pos_of_pos hd) (by positivity)
  refine ⟨v.fill,v.fill_support,fun l hl hdg => ?_⟩
  have he := fill_evaluate_error τ htr h1 a ha γ v d hd.le hv.le l
  have ho : ‖τ (evaluate a γ v l)‖<η/2 := by
    rw [←trace_average e τ hτ htr hfaith h1]
    exact (HochschildUltrapower.norm_trace_le τ h1 _).trans_lt (hgood l hl hdg)
  have hdeq : d*(2*((L:ℝ)+1))=η := div_mul_cancel₀ _ (by positivity)
  have hlen : (l.length:ℝ)≤L := by exact_mod_cast hl
  have hbound := norm_add_le (τ (evaluate a γ v.fill l)-τ (evaluate a γ v l)) (τ (evaluate a γ v l))
  rw [sub_add_cancel] at hbound
  nlinarith
end PopaCenter

end

end OAI
