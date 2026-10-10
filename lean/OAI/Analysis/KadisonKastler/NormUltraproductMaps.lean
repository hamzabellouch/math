import OAI.Analysis.KadisonKastler.NormUltraproduct
import OAI.Analysis.KadisonKastler.VaryingQuotient

namespace OAI

/-! # Coordinate embeddings induce faithful norm-ultraproduct embeddings -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B C : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  [∀ j, CStarAlgebra (C j)] [∀ j, Nontrivial (C j)]

def normProductMap (φ : ∀ j, B j →⋆ₐ[ℂ] C j) :
    VaryingBoundedSequence B →⋆ₐ[ℂ] VaryingBoundedSequence C where
  toFun x := ⟨fun j => φ j (x j),
    (lp.memℓp x).mono' (fun j => NonUnitalStarAlgHom.norm_apply_le (φ j) (x j))⟩
  map_zero' := lp.ext (by funext j; exact map_zero (φ j))
  map_one' := lp.ext (by funext j; exact map_one (φ j))
  map_add' x y := lp.ext (by funext j; exact map_add (φ j) (x j) (y j))
  map_mul' x y := lp.ext (by funext j; exact map_mul (φ j) (x j) (y j))
  commutes' z := lp.ext (by funext j; exact (φ j).commutes z)
  map_star' x := lp.ext (by funext j; exact map_star (φ j) (x j))

@[simp] theorem normProductMap_apply (φ : ∀ j, B j →⋆ₐ[ℂ] C j)
    (x : VaryingBoundedSequence B) (j : ℕ) : normProductMap φ x j = φ j (x j) := rfl

theorem NormNullSequence.map {ω : Ultrafilter ℕ} {x : VaryingBoundedSequence B}
    (hx : NormNullSequence B ω x) (φ : ∀ j, B j →⋆ₐ[ℂ] C j) :
    NormNullSequence C ω (normProductMap φ x) :=
  squeeze_zero (fun _ => norm_nonneg _) (fun j => NonUnitalStarAlgHom.norm_apply_le (φ j) _) hx

def normUltraproductInducedMap (φ : ∀ j, B j →⋆ₐ[ℂ] C j) (ω : Ultrafilter ℕ) :
    NormUltraproduct B ω →⋆ₐ[ℂ] NormUltraproduct C ω :=
  starAlgHomDescend (normUltraproductMap B ω) (normUltraproductMap_surjective B ω)
    ((normUltraproductMap C ω).comp (normProductMap φ))
    (fun x hx => (normUltraproductMap_eq_zero_iff C ω _).mpr
      (((normUltraproductMap_eq_zero_iff B ω x).mp hx).map φ))

@[simp] theorem normUltraproductInducedMap_apply_map (φ : ∀ j, B j →⋆ₐ[ℂ] C j)
    (ω : Ultrafilter ℕ) (x : VaryingBoundedSequence B) :
    normUltraproductInducedMap φ ω (normUltraproductMap B ω x) =
      normUltraproductMap C ω (normProductMap φ x) :=
  starAlgHomDescend_apply_map _ _ _ _ x

theorem normUltraproductInducedMap_injective (φ : ∀ j, B j →⋆ₐ[ℂ] C j)
    (hφ : ∀ j, Function.Injective (φ j)) (ω : Ultrafilter ℕ) :
    Function.Injective (normUltraproductInducedMap φ ω) := by
  intro a b hab
  have hz : normUltraproductInducedMap φ ω (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨x, hx⟩ := normUltraproductMap_surjective B ω (a - b)
  have hzero : normUltraproductMap C ω (normProductMap φ x) = 0 := by
    rw [← normUltraproductInducedMap_apply_map, hx]
    exact hz
  have hnull := (normUltraproductMap_eq_zero_iff C ω _).mp hzero
  have hnorm : (fun j => ‖normProductMap φ x j‖) = (fun j => ‖x j‖) := by
    funext j
    exact NonUnitalStarAlgHom.norm_map (φ j) (hφ j) (x j)
  have hnullx : NormNullSequence B ω x := by
    change Tendsto (fun j => ‖x j‖) (ω : Filter ℕ) (𝓝 0)
    rw [← hnorm]
    exact hnull
  exact sub_eq_zero.mp (hx ▸ (normUltraproductMap_eq_zero_iff B ω x).mpr hnullx)

end

end KadisonKastler

end OAI
