import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Kasch.ProjectiveSplitting

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace Kasch
universe v w
variable {R : Type u} [Ring R]
section SplitBasic
variable {k : Type u} [Field k] [Algebra k R]
variable {ι : Type u} (χ : R →ₐ[k] (ι → k))
variable (a : ι → R) (ha : ∀ i, a i ≠ 0)
  (hmul : ∀ i r, a i * r = χ r i • a i)
include ha hmul in
lemma projective_of_hasFiniteBound [Finite ι]
    (hχ : Function.Surjective χ) (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    (M : ModuleCat.{u} R) (n : ℕ) [HasProjectiveDimensionLT M n] : Projective M := by
  induction n generalizing M with
  | zero =>
    exact (CategoryTheory.isZero_of_hasProjectiveDimensionLT_zero M).projective
  | succ n ih =>
    cases n with
    | zero => exact projective_iff_hasProjectiveDimensionLT_one.mpr inferInstance
    | succ n =>
      let S := ShortComplex.mk (Limits.kernel.ι (Projective.π M)) (Projective.π M)
        (Limits.kernel.condition (Projective.π M))
      have hs : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π M) }
      let : HasProjectiveDimensionLT S.X₁ (n + 1) :=
        (hs.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
      let : Projective S.X₁ := ih S.X₁
      obtain ⟨r, hr⟩ := projective_mono_splits χ a ha hmul hχ hJ S.f.hom
        ((ModuleCat.mono_iff_injective S.f).mp hs.mono_f)
      let spl := ShortComplex.Splitting.ofExactOfRetraction S hs.exact
        (ModuleCat.ofHom r) (ModuleCat.hom_ext hr) hs.epi_g
      exact (show Retract M S.X₂ from
        { i := spl.s, r := S.g, retract := spl.s_g }).projective

include ha hmul in
lemma projective_of_finiteDimension [Finite ι]
    (hχ : Function.Surjective χ) (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    (M : ModuleCat.{u} R) (hM : projectiveDimension M < ⊤) : Projective M := by
  obtain ⟨n, hn⟩ := (projectiveDimension_ne_top_iff M).mp hM.ne
  let := hn
  exact projective_of_hasFiniteBound χ a ha hmul hχ hJ M (n + 1)

end SplitBasic
end Kasch

end LittleFinitistic
end
end
end

end OAI
