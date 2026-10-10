import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.SubspacePointsEquiv
import OAI.Combinatorics.RamseyFive.Geometry.PlaneCommonNeighbors

namespace OAI

namespace SharpRamseyFive.RichPlaneOverlap
open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exceptional_centers (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (X : Finset (ℙ K V)) (D : ℕ) (hD : 8*(2*u+1) ≤ D) :
    ((X.filter fun x => D ≤ (F.filter fun A => x.submodule ≤ A).card).card:ℝ)*D^2 ≤
      16*(F.card:ℝ)^2 := by
  let Y := X.filter fun x => D ≤ (F.filter fun A => x.submodule ≤ A).card
  have hsub : Y ⊆ X.filter fun x => 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card := by
    intro x hx
    obtain ⟨hxX,hxD⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxX,hD.trans hxD⟩
  have h1 : (Y.card:ℝ)*D^2 ≤ ∑ x ∈ Y, ((F.filter fun A => x.submodule ≤ A).card:ℝ)^2 := by
    have h := Finset.sum_le_sum (s := Y) (f := fun _ => (D:ℝ)^2)
      (g := fun x => ((F.filter fun A => x.submodule ≤ A).card:ℝ)^2) (by
        intro x hx
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast (Finset.mem_filter.mp hx).2)
    simpa using h
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ =>
    sq_nonneg ((F.filter fun A => x.submodule ≤ A).card:ℝ))
  exact (h1.trans h2).trans (high_degree_second_moment F hF u hline hhyper X)

end SharpRamseyFive.RichPlaneOverlap

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma inf_eq_shared_line {A B L : Submodule K V}
    (hA : finrank K A = 3) (hB : finrank K B = 3) (hL : finrank K L = 2)
    (hAB : A ≠ B) (hLA : L ≤ A) (hLB : L ≤ B) : A ⊓ B = L := by
  have hle : L ≤ A ⊓ B := le_inf hLA hLB
  have he : A ⊓ B < A := lt_of_le_of_ne inf_le_left (by
    intro he
    have hab : A ≤ B := he ▸ inf_le_right
    exact hAB (Submodule.eq_of_le_of_finrank_eq hab (hA.trans hB.symm)))
  have hge := Submodule.finrank_mono hle
  have hlt := Submodule.finrank_lt_finrank_of_lt he
  rw [hA] at hlt
  rw [hL] at hge
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem rich_planes_through_line [Finite K]
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (L : Submodule K V) (hL : finrank K L = 2) :
    (F.filter fun A => L ≤ A).card*M ≤
      X.card + (F.filter fun A => L ≤ A).card*(Nat.card K+1) := by
  let : Finite V := Module.finite_of_finite K
  let G := F.filter fun A => L ≤ A
  let Y := X.filter fun x => x.submodule ≤ L
  let T (A : Submodule K V) := X.filter fun x => x.submodule ≤ A ∧ ¬x.submodule ≤ L
  have hY : Y.card ≤ Nat.card K+1 := by
    have hi : Function.Injective (fun x : Y => (⟨x.val,(Finset.mem_filter.mp x.property).2⟩ :
        {p : ℙ K V // p.submodule ≤ L})) := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : {p : ℙ K V // p.submodule ≤ L} => z.val) he)
    have hc := Nat.card_le_card_of_injective _ hi
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_subspacePoints, hL] at hc
    simpa [Finset.sum_range_succ, add_comm] using hc
  have hdis : (G : Set (Submodule K V)).PairwiseDisjoint T := by
    intro A hA B hB hAB
    obtain ⟨hAF,hLA⟩ := Finset.mem_filter.mp hA
    obtain ⟨hBF,hLB⟩ := Finset.mem_filter.mp hB
    have he := inf_eq_shared_line (hF A hAF) (hF B hBF) hL hAB hLA hLB
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨_,hxAA,hxL⟩ := Finset.mem_filter.mp hxA
    have hxBB := (Finset.mem_filter.mp hxB).2.1
    exact hxL (he ▸ le_inf hxAA hxBB)
  have hunion : G.biUnion T ⊆ X := by
    intro x hx
    obtain ⟨A,_,hxA⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxA).1
  have hsum : ∑ A ∈ G, (T A).card ≤ X.card := by
    rw [← Finset.card_biUnion hdis]
    exact Finset.card_le_card hunion
  have hrow (A : Submodule K V) (hA : A ∈ G) : M ≤ (T A).card + Y.card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := X.filter fun x => x.submodule ≤ A) (fun x => x.submodule ≤ L)
    have hsmall : ((X.filter fun x => x.submodule ≤ A).filter fun x => x.submodule ≤ L).card ≤ Y.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxA,hxL⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxA).1,hxL⟩
    have hn : (X.filter fun x => x.submodule ≤ A).filter (fun x => ¬x.submodule ≤ L) = T A := by
      simp only [T, Finset.filter_filter]
    rw [hn] at hpart
    have hm := hM A (Finset.mem_filter.mp hA).1
    omega
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hs
  have hm := Nat.mul_le_mul_left G.card hY
  dsimp [G] at hm hs hsum
  omega

theorem rich_planes_through_line_twice [Finite K]
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hlarge : 2*(Nat.card K+1) ≤ M)
    (L : Submodule K V) (hL : finrank K L = 2) :
    (F.filter fun A => L ≤ A).card*M ≤ 2*X.card := by
  have h := rich_planes_through_line F hF X M hM L hL
  have hm := Nat.mul_le_mul_left (F.filter fun A => L ≤ A).card hlarge
  nlinarith

noncomputable def dualOfHyperplane {d : ℕ} (hdim : finrank K V = d+1)
    (A : Submodule K V) (hA : finrank K A = d) : ℙ K (Module.Dual K V) :=
  Projectivization.mk'' A.dualAnnihilator (by
    have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq A
    rw [hA,hdim] at hh
    omega)

lemma ker_dualOfHyperplane {d : ℕ} (hdim : finrank K V = d+1)
    (A : Submodule K V) (hA : finrank K A = d) :
    LinearMap.ker (dualOfHyperplane hdim A hA).rep = A := by
  let b := dualOfHyperplane hdim A hA
  have he : b.submodule = A.dualAnnihilator := Projectivization.submodule_mk'' _ _
  have hmem : b.rep ∈ A.dualAnnihilator := by
    rw [← he, b.submodule_eq]
    exact Submodule.mem_span_singleton_self _
  have hle : A ≤ LinearMap.ker b.rep := by
    intro a ha
    exact ((Submodule.mem_dualAnnihilator b.rep).mp hmem) a ha
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hA]; omega)).symm

lemma dualOfHyperplane_injective {d : ℕ} (hdim : finrank K V = d+1) :
    Function.Injective (fun A : {A : Submodule K V // finrank K A = d} =>
      dualOfHyperplane hdim A.val A.property) := by
  intro A B hAB
  apply Subtype.ext
  have h := congrArg (fun b : ℙ K (Module.Dual K V) => LinearMap.ker b.rep) hAB
  simpa only [ker_dualOfHyperplane] using h

end SharpRamseyFive.RichPlaneGeometry

end OAI
