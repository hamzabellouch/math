import OAI.Analysis.OInfinity.CentralBuffer
import OAI.Analysis.WeakInfiniteness.OInfinityMap

namespace OAI

/-! # The central buffer commutes with both complete factor images

Generator density puts every constant factor element in the actual buffer
commutant. Thus finite split data chosen in either factor inherit exact
commutation; no extra centrality assumption on those data is needed.
-/

noncomputable section
open Filter Topology
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Exact commutation on the canonical generators extends to the whole
image of O∞ by its proved closed star-span density. -/
lemma oInfinity_image_mem_centralizer (f : OInfinity →⋆ₐ[ℂ] E) (r : ℕ → E)
    (hgen : ∀ i j, Commute (f (oInfinityIsometry i)) (r j) ∧
      Commute (star (f (oInfinityIsometry i))) (r j)) :
    ∀ x : OInfinity, f x ∈ StarSubalgebra.centralizer ℂ (Set.range r) := by
  let C := (StarSubalgebra.centralizer ℂ (Set.range r)).comap f
  have hC : IsClosed (C : Set OInfinity) := by
    change IsClosed (f ⁻¹' (StarSubalgebra.centralizer ℂ (Set.range r) : Set E))
    exact (Set.isClosed_centralizer _).preimage (starHom_continuous f)
  have hd : closedStarSpan (Set.range oInfinityIsometry) ≤ C := by
    apply closedStarSpan_le _ C hC
    rintro _ ⟨i, rfl⟩
    change f (oInfinityIsometry i) ∈ StarSubalgebra.centralizer ℂ (Set.range r)
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨(hgen i j).1.symm.eq, by
      simpa only [star_star] using (hgen i j).2.star_star.symm.eq⟩
  rw [oInfinity_generators_dense] at hd
  intro x
  exact hd (show x ∈ (⊤ : StarSubalgebra ℂ OInfinity) from trivial)

/-- The already constructed third row centralizes every element of both
constant O∞ factor images, including all finite vacuum-split data. -/
lemma exists_normUltrapower_factor_buffer [Nontrivial E]
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (f g : OInfinity →⋆ₐ[ℂ] E)
    (hfg : ∀ x y, Commute (f x) (g y)) :
    ∃ r : ℕ → NormUltra.QuotientAlgebra (fun _ : ℕ => E) U,
      (∀ i j, star (r i) * r j = if i = j then 1 else 0) ∧
      (∀ x : OInfinity, NormUltra.QuotientAlgebra.diagonalHom U (f x) ∈
        StarSubalgebra.centralizer ℂ (Set.range r)) ∧
      ∀ x : OInfinity, NormUltra.QuotientAlgebra.diagonalHom U (g x) ∈
        StarSubalgebra.centralizer ℂ (Set.range r) := by
  let s : ℕ → E := fun i => f (oInfinityIsometry i)
  let t : ℕ → E := fun i => g (oInfinityIsometry i)
  have hs (i j : ℕ) : star (s i) * s j = if i = j then 1 else 0 := by
    change star (f (oInfinityIsometry i)) * f (oInfinityIsometry j) = _
    rw [← map_star, ← map_mul, oInfinityIsometry_relations]
    split_ifs <;> simp only [map_one, map_zero]
  have hc : bergRowsCommute s t := by
    intro i j
    constructor
    · exact hfg _ _
    · change Commute (f (oInfinityIsometry i)) (star (g (oInfinityIsometry j)))
      rw [← map_star]
      exact hfg _ _
  obtain ⟨r, hr, hrf, hrg⟩ := exists_normUltrapower_central_cuntz_row U s t hs hc
  let d := NormUltra.QuotientAlgebra.diagonalHom (A := E) U
  have hfgen (i j : ℕ) : Commute ((d.comp f) (oInfinityIsometry i)) (r j) ∧
      Commute (star ((d.comp f) (oInfinityIsometry i))) (r j) :=
    ⟨(hrf j i).1.symm, (hrf j i).2.symm⟩
  have hggen (i j : ℕ) : Commute ((d.comp g) (oInfinityIsometry i)) (r j) ∧
      Commute (star ((d.comp g) (oInfinityIsometry i))) (r j) :=
    ⟨(hrg j i).1.symm, (hrg j i).2.symm⟩
  exact ⟨r, hr, oInfinity_image_mem_centralizer (d.comp f) r hfgen,
    oInfinity_image_mem_centralizer (d.comp g) r hggen⟩

end WeakPureInfiniteness

end

end OAI
