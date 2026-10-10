import Mathlib
import OAI.Analysis.Commutator.ArvesonCorner
import OAI.Analysis.Commutator.CpUltralimit

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra Topology

open Filter

namespace Kadison.OperatorSystem

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_extension (S : Submodule ℂ A) (h1 : (1 : A)∈S)
    (hs : ∀ a∈S,star a∈S) (f : S →ₗ[ℂ] (H →L[ℂ] H))
    (hf : IsCompletelyPositive S f) :
    ∃ Φ : A →CP (H →L[ℂ] H),∀ a : S,Φ a=f a := by
  classical
  have he (t : Finset H) : ∃ Φ : A →CP (H →L[ℂ] H),
      (∀ a,‖Φ a‖≤‖f ⟨1,h1⟩‖*‖a‖) ∧
      ∀ a : S,∀ x∈t,∀ y∈t,⟪Φ a x,y⟫_ℂ=⟪f a x,y⟫_ℂ := by
    let E := Submodule.span ℂ (t : Set H)
    let : FiniteDimensional ℂ E := FiniteDimensional.span_of_finite ℂ t.finite_toSet
    obtain ⟨Φ,hb,hf⟩ := exists_corner_extension S h1 hs f hf E
    exact ⟨Φ,hb,fun a x hx y hy => hf a x (Submodule.subset_span hx) y (Submodule.subset_span hy)⟩
  choose φ hφ hext using he
  let ω := Ultrafilter.of (atTop : Filter (Finset H))
  obtain ⟨Φ,hΦ,hlim⟩ := CpOperations.exists_cp_ultralimit ω φ ‖f ⟨1,h1⟩‖ (norm_nonneg _) hφ
  refine ⟨Φ,?_⟩
  intro a
  ext x
  apply ext_inner_right ℂ
  intro y
  apply tendsto_nhds_unique (hlim a x y)
  have hev : ∀ᶠ t in (ω : Filter (Finset H)),⟪φ t a x,y⟫_ℂ=⟪f a x,y⟫_ℂ := by
    apply (Ultrafilter.of_le _)
    filter_upwards [eventually_ge_atTop ({x,y} : Finset H)] with t ht
    exact hext t a x (ht (by simp)) y (ht (by simp))
  exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hev)

end Kadison.OperatorSystem

end

end
end

end OAI
