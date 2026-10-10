import Mathlib

namespace OAI

namespace PiExponent.GeometrySupport.SerreDimensionShift

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_eq_zero_of_shortExact (A : C) {S : ShortComplex C} (hS : S.ShortExact)
    (q : ℕ) (hmid : ∀ x : Ext.{w} A S.X₂ q, x = 0)
    (hleft : ∀ x : Ext.{w} A S.X₁ (q + 1), x = 0)
    (x : Ext.{w} A S.X₃ q) : x = 0 := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ A hS x rfl (hleft _)
  rw [hmid y, Ext.zero_comp] at hy
  exact hy.symm

theorem ext_eq_zero_of_biproduct (A : C) {J : Type*} [Fintype J]
    {B : J → C} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ)
    (hzero : ∀ j, ∀ x : Ext.{w} A (B j) q, x = 0)
    (x : Ext.{w} A c.pt q) : x = 0 := by
  apply (Ext.addEquivBiproduct A hc q).injective
  ext j
  exact (hzero j _).trans ((map_zero (Ext.addEquivBiproduct A hc q)) ▸ rfl)

structure AcyclicPresentation {ι : Type t} (A : C) (F : ι → ℕ → C) (i : ι) where
  kernel : ι
  shift : ℕ
  middle : ℕ → C
  left : ∀ n, F kernel n ⟶ middle n
  right : ∀ n, middle n ⟶ F i (shift + n)
  comp_zero : ∀ n, left n ≫ right n = 0
  shortExact : ∀ n, (ShortComplex.mk (left n) (right n) (comp_zero n)).ShortExact
  acyclic : ∀ n q, 0 < q → ∀ x : Ext.{w} A (middle n) q, x = 0

theorem eventual_ext_zero_of_presentations {ι : Type t} (A : C) (F : ι → ℕ → C)
    (l : ℕ)
    (hbound : ∀ i n q, l ≤ q → ∀ x : Ext.{w} A (F i n) q, x = 0)
    (presentation : ∀ i, AcyclicPresentation A F i)
    (q : ℕ) (hq : 0 < q) (i : ι) :
    ∃ N, ∀ n, N ≤ n → ∀ x : Ext.{w} A (F i n) q, x = 0 := by
  have hstep : ∀ r q, 0 < q → l ≤ q + r → ∀ i,
      ∃ N, ∀ n, N ≤ n → ∀ x : Ext.{w} A (F i n) q, x = 0 := by
    intro r
    induction r with
    | zero =>
      intro q hq hl i
      exact ⟨0, fun n _ x => hbound i n q (by simpa using hl) x⟩
    | succ r ih =>
      intro q hq hl i
      let P := presentation i
      obtain ⟨N, hN⟩ := ih (q + 1) (by omega) (by omega) P.kernel
      refine ⟨P.shift + N, fun n hn => ?_⟩
      have hnshift : P.shift ≤ n := by omega
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnshift
      apply ext_eq_zero_of_shortExact A (P.shortExact t) q
      · exact P.acyclic t q hq
      · exact hN t (by omega)
  exact hstep l q hq (by omega) i

theorem eventual_all_positive_ext_zero_of_presentations {ι : Type t}
    (A : C) (F : ι → ℕ → C) (l : ℕ)
    (hbound : ∀ i n q, l ≤ q → ∀ x : Ext.{w} A (F i n) q, x = 0)
    (presentation : ∀ i, AcyclicPresentation A F i) (i : ι) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q → ∀ x : Ext.{w} A (F i n) q, x = 0 := by
  classical
  have h : ∀ q : Fin l, ∃ N, ∀ n, N ≤ n →
      ∀ x : Ext.{w} A (F i n) (q.val + 1), x = 0 :=
    fun q => eventual_ext_zero_of_presentations A F l hbound presentation
      (q.val + 1) (by omega) i
  choose N hN using h
  refine ⟨Finset.univ.sup N, fun n hn q hq x => ?_⟩
  cases q with
  | zero => omega
  | succ q =>
    by_cases hl : l ≤ q + 1
    · exact hbound i n (q + 1) hl x
    · exact hN ⟨q, by omega⟩ n
        (le_trans (Finset.le_sup (f := N) (Finset.mem_univ _)) hn) x

end
end PiExponent.GeometrySupport.SerreDimensionShift

end OAI
