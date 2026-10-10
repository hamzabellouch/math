import Mathlib

namespace OAI

/-! A finite-partition local-to-global principle for homotopy classes of actual
continuous paths. This will convert open-star control into edge generation. -/
noncomputable section

open Set
open scoped unitInterval
namespace HyperbolicObstruction.PathLocalToGlobal
variable {X : Type*} [TopologicalSpace X]
abbrev Q (x y : X) := Path.Homotopic.Quotient x y
variable (R : ∀ x y : X, Q x y → Prop)

lemma cast {x y x' y' : X} {p : Q x y} (hx : x' = x) (hy : y' = y)
    (h : R x y p) : R x' y' (p.cast hx hy) := by
  subst x'; subst y'; simpa using h

/-- No subdivision or simplicial approximation assumption is made: the
partition is obtained from compactness of the actual unit interval. -/
theorem of_open_cover {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (cover : ∀ x, ∃ i, x ∈ U i)
    (hrefl : ∀ x, R x x (.refl x))
    (htrans : ∀ {x y z} {p : Q x y} {q : Q y z}, R x y p → R y z q → R x z (p.trans q))
    (hlocal : ∀ i {x y} (p : Path x y), (∀ t, p t ∈ U i) → R x y (.mk p))
    {x y : X} (p : Path x y) : R x y (.mk p) := by
  obtain ⟨t,ht0,hmono,⟨N,hN⟩,ht⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hU i).preimage p.continuous)
      (show univ ⊆ ⋃ i, p ⁻¹' U i from by
        intro s _
        obtain ⟨i,hi⟩ := cover (p s)
        exact mem_iUnion.mpr ⟨i,hi⟩)
  have hall (n : ℕ) : R (p (t 0)) (p (t n)) (.mk (p.subpath (t 0) (t n))) := by
    induction n with
    | zero => simpa using hrefl (p (t 0))
    | succ n ih =>
      obtain ⟨i,hi⟩ := ht n
      have hs : ∀ s, p.subpath (t n) (t (n+1)) s ∈ U i := by
        intro s
        have hr := mem_range_self (f := p.subpath (t n) (t (n+1))) s
        rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ n))] at hr
        obtain ⟨r,hr,he⟩ := hr
        exact he ▸ hi hr
      have hh := htrans ih (hlocal i _ hs)
      have he : Path.Homotopic.Quotient.mk ((p.subpath (t 0) (t n)).trans (p.subpath (t n) (t (n+1)))) =
          Path.Homotopic.Quotient.mk (p.subpath (t 0) (t (n+1))) :=
        Path.Homotopic.Quotient.eq.mpr ⟨Path.Homotopy.subpathTransSubpath p _ _ _⟩
      exact he ▸ hh
  have hlast := hall N
  rw [ht0,hN N le_rfl,Path.subpath_zero_one] at hlast
  have hh := cast R p.source.symm p.target.symm hlast
  simpa using hh

end HyperbolicObstruction.PathLocalToGlobal
end

end OAI
