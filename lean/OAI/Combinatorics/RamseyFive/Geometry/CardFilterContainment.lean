import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.RichHyperplaneVariance

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma card_filter_containment_le (X : Finset (ℙ K V)) (A : Submodule K V) :
    (X.filter fun x => x.submodule ≤ A).card ≤ ∑ i ∈ Finset.range (finrank K A), Nat.card K^i := by
  let : Finite V := Module.finite_of_finite K
  let Y := X.filter fun x => x.submodule ≤ A
  have hi : Function.Injective (fun x : Y => (⟨x.val,(Finset.mem_filter.mp x.property).2⟩ :
      {p : ℙ K V // p.submodule ≤ A})) := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : {p : ℙ K V // p.submodule ≤ A} => z.val) he)
  have hc := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_subspacePoints] at hc
  exact hc

lemma card_filter_finrank_le_two (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A ≤ 2) :
    (X.filter fun x => x.submodule ≤ A).card ≤ Nat.card K+1 := by
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hA)
    (f := fun i => Nat.card K^i) (by intros; exact Nat.zero_le _)
  have hc := (card_filter_containment_le X A).trans hle
  simpa [Finset.sum_range_succ,add_comm] using hc

lemma card_filter_finrank_le_one (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A ≤ 1) :
    (X.filter fun x => x.submodule ≤ A).card ≤ 1 := by
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hA)
    (f := fun i => Nat.card K^i) (by intros; exact Nat.zero_le _)
  have hc := (card_filter_containment_le X A).trans hle
  simpa using hc

omit [Finite K] in
lemma finrank_inf_lt_of_not_le (A H : Submodule K V) (hn : ¬A ≤ H) :
    finrank K (A ⊓ H : Submodule K V) < finrank K A := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro he
  exact hn (he ▸ inf_le_right)

lemma plane_noncontaining_flat_cap (X : Finset (ℙ K V)) (A H : Submodule K V)
    (hA : finrank K A = 3) (hn : ¬A ≤ H) :
    (X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ H).card ≤ Nat.card K+1 := by
  have hh := finrank_inf_lt_of_not_le A H hn
  rw [hA] at hh
  simpa only [le_inf_iff] using card_filter_finrank_le_two X (A ⊓ H) (by omega)

lemma line_noncontaining_flat_cap (X : Finset (ℙ K V)) (A H : Submodule K V)
    (hA : finrank K A = 2) (hn : ¬A ≤ H) :
    (X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ H).card ≤ 1 := by
  have hh := finrank_inf_lt_of_not_le A H hn
  rw [hA] at hh
  simpa only [le_inf_iff] using card_filter_finrank_le_one X (A ⊓ H) (by omega)

lemma card_hyperplane_family {d : ℕ} (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d) :
    F.card ≤ Q (Nat.card K) d := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let f (A : F) := dualOfHyperplane hdim A.val (hF A.val A.property)
  have hf : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    have hk := congrArg (fun b : ℙ K (Module.Dual K V) => LinearMap.ker b.rep) he
    simpa only [f,ker_dualOfHyperplane] using hk
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, card_hyperplanes hdim] using hc

lemma card_hyperplanes_inside {d : ℕ} (H : Submodule K V) (hH : finrank K H = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d) :
    (F.filter fun A => A ≤ H).card ≤ Q (Nat.card K) d := by
  let G := F.filter fun A => A ≤ H
  let FH := G.image (fun A => A.comap H.subtype)
  have hc : FH.card = G.card := Finset.card_image_iff.mpr (by
    intro A hA B hB he
    exact comap_subtype_injOn H (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2 he)
  have hdimF (A : Submodule K H) (hA : A ∈ FH) : finrank K A = d := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [comap_subtype_finrank H B (Finset.mem_filter.mp hB).2]
    exact hF B (Finset.mem_filter.mp hB).1
  have hh := card_hyperplane_family hH FH hdimF
  rwa [hc] at hh

end SharpRamseyFive.RichPlaneGeometry

namespace SharpRamseyFive.HyperplaneOverlap
open Module ProjectiveIncidence RichPlaneGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma hyperplane_intersection_rank {d : ℕ} (hdim : finrank K V = d+1)
    (A B : Submodule K V) (hA : finrank K A = d) (hB : finrank K B = d) (hne : A ≠ B) :
    finrank K (A ⊓ B : Submodule K V) = d-1 := by
  have hn : ¬A ≤ B := fun h => hne (Submodule.eq_of_le_of_finrank_eq h (hA.trans hB.symm))
  have hlt := finrank_inf_lt_of_not_le A B hn
  have hs := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hle := Submodule.finrank_le (A ⊔ B : Submodule K V)
  rw [hA] at hlt
  rw [hA,hB] at hs
  rw [hdim] at hle
  omega

lemma card_hyperplanes_containing [Finite K] {d : ℕ} (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d) (W : Submodule K V) :
    (F.filter fun A => W ≤ A).card ≤
      ∑ i ∈ Finset.range (d+1-finrank K W), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let G := F.filter fun A => W ≤ A
  let f (A : G) : {b : ℙ K (Module.Dual K V) // b.submodule ≤ W.dualAnnihilator} :=
    ⟨dualOfHyperplane hdim A.val (hF _ (Finset.mem_filter.mp A.property).1), by
      rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem,Submodule.mem_dualAnnihilator]
      intro w hw
      have hk := (Finset.mem_filter.mp A.property).2 hw
      rw [← ker_dualOfHyperplane hdim A.val (hF _ (Finset.mem_filter.mp A.property).1)] at hk
      exact hk⟩
  have hf : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    have hv := congrArg (fun b : {b : ℙ K (Module.Dual K V) // b.submodule ≤ W.dualAnnihilator} =>
      LinearMap.ker b.val.rep) he
    simpa only [f,ker_dualOfHyperplane] using hv
  have hc := Fintype.card_le_of_injective f hf
  have he := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hr : finrank K W.dualAnnihilator = d+1-finrank K W := by omega
  rw [Fintype.card_coe,← Nat.card_eq_fintype_card,card_subspacePoints,hr] at hc
  exact hc

lemma pair_count_by_intersection {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (E : Finset (Submodule K V × Submodule K V))
    (hE : E ⊆ F ×ˢ F) (hEL : ∀ p ∈ E, p.1 ⊓ p.2 ∈ L) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
  let C (W : Submodule K V) := F.filter fun H => W ≤ H
  have hsub : E ⊆ L.biUnion (fun W => C W ×ˢ C W) := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (hE hp)
    exact Finset.mem_biUnion.mpr ⟨p.1 ⊓ p.2,hEL p hp,Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨ha,inf_le_left⟩,Finset.mem_filter.mpr ⟨hb,inf_le_right⟩⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (C W ×ˢ C W).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
    have hc := card_hyperplanes_containing hdim F hF W
    rw [hL W hW] at hc
    simpa only [Finset.card_product,pow_two] using Nat.pow_le_pow_left hc 2
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

lemma neighbor_count_by_intersection {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (H : Submodule K V) (E : Finset (Submodule K V))
    (hE : E ⊆ F) (hEL : ∀ A ∈ E, H ⊓ A ∈ L) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
  have hsub : E ⊆ L.biUnion (fun W => F.filter fun A => W ≤ A) := by
    intro A hA
    exact Finset.mem_biUnion.mpr ⟨H ⊓ A,hEL A hA,Finset.mem_filter.mpr ⟨hE hA,inf_le_right⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (F.filter fun A => W ≤ A).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
    simpa only [hL W hW] using card_hyperplanes_containing hdim F hF W
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

lemma pair_count_by_contained_witness {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (E : Finset (Submodule K V × Submodule K V))
    (hE : E ⊆ F ×ˢ F) (hEL : ∀ p ∈ E, ∃ W ∈ L, W ≤ p.1 ⊓ p.2) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
  let C (W : Submodule K V) := F.filter fun H => W ≤ H
  have hsub : E ⊆ L.biUnion (fun W => C W ×ˢ C W) := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (hE hp)
    obtain ⟨W,hW,hWp⟩ := hEL p hp
    exact Finset.mem_biUnion.mpr ⟨W,hW,Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨ha,hWp.trans inf_le_left⟩,
       Finset.mem_filter.mpr ⟨hb,hWp.trans inf_le_right⟩⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (C W ×ˢ C W).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
    have hc := card_hyperplanes_containing hdim F hF W
    rw [hL W hW] at hc
    simpa only [Finset.card_product,pow_two] using Nat.pow_le_pow_left hc 2
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

lemma neighbor_count_by_contained_witness {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (E : Finset (Submodule K V))
    (hE : E ⊆ F) (hEL : ∀ A ∈ E, ∃ W ∈ L, W ≤ A) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
  have hsub : E ⊆ L.biUnion (fun W => F.filter fun A => W ≤ A) := by
    intro A hA
    obtain ⟨W,hW,hWA⟩ := hEL A hA
    exact Finset.mem_biUnion.mpr ⟨W,hW,Finset.mem_filter.mpr ⟨hE hA,hWA⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (F.filter fun A => W ≤ A).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
    simpa only [hL W hW] using card_hyperplanes_containing hdim F hF W
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

lemma rich_radial_count {x : ℙ K V} [Fintype (RadialLine x)]
    (X : Finset {y : ℙ K V // x ≠ y}) (W : Submodule K V) (hx : x.submodule ≤ W)
    (L : Finset (RadialLine x)) (hL : L ⊆ RadialLine.inFlat W) (M : ℕ)
    (hM : ∀ l ∈ L, M ≤ (RadialLine.trainingOnLine X l).card) :
    L.card*M ≤ (X.filter fun y => y.val.submodule ≤ W).card := by
  have h := Finset.sum_le_sum hM
  simp only [Finset.sum_const_nat] at h
  apply h.trans
  rw [← RadialLine.sum_trainingOnLine X W hx]
  exact Finset.sum_le_sum_of_subset hL

lemma rich_radial_strength_count {x : ℙ K V} [Fintype (RadialLine x)]
    (X : Finset {y : ℙ K V // x ≠ y}) (q n : ℝ) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (W : Submodule K V) (hx : x.submodule ≤ W)
    (L : Finset (RadialLine x)) (hL : L ⊆ RadialLine.inFlat W) (a : ℝ)
    (ha : ∀ l ∈ L, a ≤ RadialLine.strength X q n l) :
    L.card*a ≤ q/n*(X.filter fun y => y.val.submodule ≤ W).card := by
  have h := Finset.sum_le_sum ha
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  apply h.trans
  rw [← RadialLine.sum_strength X q n W hx]
  exact Finset.sum_le_sum_of_subset_of_nonneg hL (fun l _ _ => by
    dsimp [RadialLine.strength]
    positivity)

end SharpRamseyFive.HyperplaneOverlap

end OAI
