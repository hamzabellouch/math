import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.RealVirtualSolvability
import OAI.Probability.CriticalPercolation.Harmonic.HarmonicLinearQuotient
import OAI.Probability.CriticalPercolation.Criticality.IndicableDegreeStep
import OAI.Probability.CriticalPercolation.Criticality.VirtualIndicability

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.SparseGrowth

lemma infinite_finiteIndex_subgroup {A : Type*} [Group A] [Infinite A]
    (H : Subgroup A) [H.FiniteIndex] : Infinite H := by
  rcases finite_or_infinite H with hf | hi
  · let := hf
    let : Finite A := H.finite_iff_finite_and_finiteIndex.mpr ⟨hf,inferInstance⟩
    exact False.elim (_root_.not_finite A)
  · exact hi

lemma indicability_of_finiteIndex {A : Type*} [Group A] (P : Subgroup A) [P.FiniteIndex]
    (hp : ∃ Q : Subgroup P, Q.FiniteIndex ∧ ∃ f : Q →* Multiplicative ℤ, Surjective f) :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  obtain ⟨Q,hQi,f,hf⟩ := hp
  let H := Q.map P.subtype
  let e := Q.equivMapOfInjective P.subtype Subtype.val_injective
  have hHi : H.FiniteIndex := by
    constructor
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hQi.index_ne_zero (inferInstance : P.FiniteIndex).index_ne_zero
  exact ⟨H,hHi,f.comp e.symm.toMonoidHom,hf.comp e.symm.surjective⟩

lemma indicability_of_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Surjective f)
    (hb : ∃ P : Subgroup B, P.FiniteIndex ∧ ∃ q : P →* Multiplicative ℤ, Surjective q) :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ, Surjective q := by
  obtain ⟨P,hPi,q,hq⟩ := hb
  let := hPi
  let H := P.comap f
  let ψ : H →* P := (f.comp H.subtype).codRestrict P (fun h => h.property)
  have hψ : Surjective ψ := by
    intro p
    obtain ⟨a,ha⟩ := hf p.val
    refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
    change f a∈P
    rw [ha]
    exact p.property
  exact ⟨H,LinearGrowth.finiteIndex_comap_surjective f hf P,q.comp ψ,hq.comp hψ⟩

lemma HasPolynomialDegree.linear_virtually_indicable {A : Type*} [Group A] [DecidableEq A]
    {d : ℕ} (hg : HasPolynomialDegree A d) [Infinite A] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  let : DecidableEq A := Classical.decEq A
  obtain ⟨S,h1,hi,hgen,hgS⟩ := (hasPolynomialDegree_iff d).mp hg
  let W : HarmonicAnalysis.WordGeometry A := ⟨S,h1,hi,hgen⟩
  obtain ⟨V,hV,hM,hfd,ρ,hρ⟩ := W.exists_infinite_finiteDimensional_linear_image d hgS
  let := hV
  let := hM
  let := hfd
  have hgR := hg.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  let : Infinite ρ.range := hρ.to_subtype
  obtain ⟨P,hPi,hPs⟩ := LinearGrowth.virtually_solvable_real_linear_general
    ρ.range.subtype Subtype.val_injective hgR
  let := hPi
  let := hPs
  let : Infinite P := infinite_finiteIndex_subgroup P
  apply indicability_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  apply indicability_of_finiteIndex P
  exact (hgR.finiteIndex_subgroup P).virtually_indicable

universe u

theorem sparse_polynomial_virtuallyNilpotent (d : ℕ) :
    ∀ (A : Type u) [Group A] [DecidableEq A],
      HasPolynomialDegree A d → Group.IsVirtuallyNilpotent A := by
  induction d with
  | zero =>
    intro A _ _ hg
    let : Finite A := hg.finite
    exact virtuallyNilpotent_of_finite
  | succ d ih =>
    intro A _ _ hg
    rcases finite_or_infinite A with hf | hi
    · let := hf
      exact virtuallyNilpotent_of_finite
    let := hi
    exact virtuallyNilpotent_of_indicability_degree_step d ih A hg hg.linear_virtually_indicable

end CriticalPercolation.SparseGrowth
end
end

end OAI
