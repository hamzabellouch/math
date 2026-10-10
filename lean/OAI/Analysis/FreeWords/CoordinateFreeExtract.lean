import Mathlib
import OAI.Analysis.FreeWords.FreePreimage
import OAI.Analysis.FreeWords.VariableUltraBundle

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace

open Filter Topology

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (R : ℕ → StarSubalgebra ℂ A) [∀ j, IsClosed (R j : Set A)]

local instance coordExtractOrder : PartialOrder (coordinateAlgebra R) := CStarAlgebra.spectralOrder _

local instance coordinateFreeExtractLE : LE (coordinateAlgebra R) := (coordExtractOrder R).toLE

local instance coordinateFreeExtractPreorder : Preorder (coordinateAlgebra R) := (coordExtractOrder R).toPreorder

local instance coordinateFreeExtractSOR : StarOrderedRing (coordinateAlgebra R) := CStarAlgebra.spectralOrderedRing _

def coordinateEval (j : ℕ) : coordinateAlgebra R →⋆ₐ[ℂ] A where
  toFun x := x.val j
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

omit [PartialOrder A] [StarOrderedRing A] [∀ j, IsClosed (R j : Set A)] in
@[simp] theorem coordinateEval_apply (j : ℕ) (x : coordinateAlgebra R) :
    coordinateEval R j x=x.val j := rfl

theorem coordinate_gns_surjective (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ)≤atTop) :
    Function.Surjective (gnsBiHom (coordinateTrace R τ ω)) := by
  intro x
  have hx := (SetLike.ext_iff.mp (coordinate_gns_range R τ htr ω hω) x.val).mpr x.property
  obtain ⟨preimage, hpreimage⟩ := hx
  exact ⟨preimage, Subtype.ext hpreimage⟩

theorem coordinate_unitary_extract (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ)≤atTop)
    (K : Finset ℤ) (F : Finset (List (ℤ × coordinateAlgebra R)))
    (v : unitary (coordinateAlgebra R)) (ε : ℝ)
    (hK : ∀ k∈K, k≠0 → ‖coordinateTrace R τ ω ((v^k).val)‖<ε)
    (hW : ∀ w∈F, ‖coordinateTrace R τ ω ((w.map (fun z => (v^z.1).val*z.2)).prod)‖<ε)
    (N : ℕ) :
    ∃ j : ℕ, N≤j ∧ ∃ u : unitary A, u.val∈R j ∧
      (∀ k∈K, k≠0 → ‖τ ((u^k).val)‖<ε) ∧
      (∀ w∈F, ‖τ ((w.map (fun z => ((u^z.1).val)*(z.2.val j))).prod)‖<ε) := by
  have hKt : ∀ᶠ j in (ω : Filter ℕ), ∀ k∈K, k≠0 →
      ‖τ (((Unitary.map (StarMonoidHom.ofClass (coordinateEval R j)) v)^k).val)‖<ε := by
    apply (Filter.eventually_all_finset K).mpr
    intro k hk
    by_cases hk0 : k=0
    · exact Eventually.of_forall (fun _ h => (h hk0).elim)
    · have ht := (tendsto_ultraTraceValue τ ω ((v^k).val.val)).norm
      have hh := (tendsto_order.mp ht).2 ε (hK k hk hk0)
      filter_upwards [hh] with j hj
      intro _
      rw [← unitary_map_zpow]
      change ‖τ ((v^k).val.val j)‖<ε
      exact hj
  have hFt : ∀ᶠ j in (ω : Filter ℕ), ∀ w∈F,
      ‖τ ((w.map (fun z => (((Unitary.map (StarMonoidHom.ofClass (coordinateEval R j)) v)^z.1).val)*
        (z.2.val j))).prod)‖<ε := by
    apply (Filter.eventually_all_finset F).mpr
    intro w hw
    have ht := (tendsto_ultraTraceValue τ ω ((w.map (fun z => (v^z.1).val*z.2)).prod.val)).norm
    have hh := (tendsto_order.mp ht).2 ε (hW w hw)
    filter_upwards [hh] with j hj
    have hew := unitary_map_word (coordinateEval R j) v w
    change ‖τ ((coordinateEval R j) ((w.map (fun z => (v^z.1).val*z.2)).prod))‖<ε at hj
    rw [hew] at hj
    simpa only [List.map_map,Function.comp_def,coordinateEval_apply] using hj
  have hN : ∀ᶠ j in (ω : Filter ℕ), N≤j := hω (eventually_ge_atTop N)
  obtain ⟨j,hjN,hjK,hjF⟩ := (hN.and (hKt.and hFt)).exists
  exact ⟨j,hjN,Unitary.map (StarMonoidHom.ofClass (coordinateEval R j)) v,v.val.property j,hjK,hjF⟩

theorem coordinate_free_extract (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ)≤atTop)
    (hF : IsFactor (gnsVonNeumann (coordinateTrace R τ ω)))
    (hD : IsDiffuse (gnsVonNeumann (coordinateTrace R τ ω)))
    (K : Finset ℤ) (F : Finset (List (ℤ × coordinateAlgebra R)))
    (hFne : ∀ w∈F, w≠[])
    (hcenter : ∀ w∈F, ∀ z∈w, z.1≠0 ∧ coordinateTrace R τ ω z.2=0)
    (ε : ℝ) (hε : 0<ε) (N : ℕ) :
    ∃ j : ℕ, N≤j ∧ ∃ u : unitary A, u.val∈R j ∧
      (∀ k∈K, k≠0 → ‖τ ((u^k).val)‖<ε) ∧
      (∀ w∈F, ‖τ ((w.map (fun z => ((u^z.1).val)*(z.2.val j))).prod)‖<ε) := by
  obtain ⟨v,hvK,hvF⟩ := finite_free_preimage
    (gnsVonNeumann (coordinateTrace R τ ω))
    (gnsNormalTrace (coordinateTrace R τ ω) (coordinateTrace_one R τ ω h1)
      (coordinateTrace_tracial R τ ω htr)) hF hD
    (gnsBiHom (coordinateTrace R τ ω)) (coordinate_gns_surjective R τ htr ω hω)
    (coordinateTrace R τ ω) (gnsNormalTrace_image _ _ _) K F hFne hcenter ε hε
  exact coordinate_unitary_extract R τ ω hω K F v ε hvK hvF N

end

end KKVariableUltra
end

end OAI
