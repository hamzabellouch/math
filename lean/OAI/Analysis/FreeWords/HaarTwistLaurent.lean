import Mathlib
import OAI.Analysis.FreeWords.HaarTwistGenerators
import OAI.Analysis.FreeWords.LaurentSpan

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

omit [StarOrderedRing A] in
theorem haar_twist_laurent_free (hτ : FaithfulTracial τ)
    (s U : unitary A) (hs : (s:A) ∈ S) (hU : (U:A) ∈ P)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) :
    ScalarFree τ (binaryCopy (laurentAlgebra (s*U)) P) := by
  have hvHaar := (haar_twist_moments hτ s U hs hU hHaar hfree).1
  intro w hne hchain hcenter
  apply linear_prod_zero_of_span (powerPSet τ (s*U) P) w τ.toLinearMap
  · intro a ha
    obtain ⟨b,x⟩ := a
    have hx := hcenter (b,x) ha
    cases b with
    | false =>
      exact trace_zero_laurent_mem_span hτ.1 (s*U) hvHaar hx.1 hx.2
    | true => exact Submodule.subset_span hx
  · intro y hy hmem
    have hyn : y ≠ [] := by
      intro h
      subst y
      have he : w = [] := List.map_eq_nil_iff.mp hy.symm
      exact hne he
    have hyc : y.IsChain (fun a b => a.1 ≠ b.1) := by
      have hc : (w.map Prod.fst).IsChain Ne := (List.isChain_map Prod.fst).mpr hchain
      rw [← hy] at hc
      exact (List.isChain_map Prod.fst).mp hc
    exact trace_twisted_generator_word hτ s U hs hU hHaar hfree hyn hyc hmem

omit [StarOrderedRing A] in
theorem twisted_conjugates_scalarFree (hτ : FaithfulTracial τ)
    (s U : unitary A) (hs : (s:A) ∈ S) (hU : (U:A) ∈ P)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) :
    ScalarFree τ (fun k : ℤ => conjugateCopy (s*U) P k) := by
  apply conjugates_scalarFree hτ.2.1
    (s*U) (S := laurentAlgebra (s*U))
  · exact StarAlgebra.subset_adjoin ℂ _ (Set.mem_singleton _)
  · exact (haar_twist_moments hτ s U hs hU hHaar hfree).1
  · exact haar_twist_laurent_free hτ s U hs hU hHaar hfree

end

end KKFreeWords
end

end OAI
