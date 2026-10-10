import OAI.NumberTheory.JointDickman.Arithmetic.BrunFinitePopulation

namespace OAI

/-! # Products of even truncations over disjoint prime blocks -/
namespace JointDickman
open Finset

noncomputable def brunBlockChoices {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (r : ι → ℕ) : Finset (ι → Finset ℕ) := by
  classical
  exact Fintype.piFinset (fun i => (P i).powerset.filter (fun D => D.card ≤ 2*r i))

noncomputable def brunBlockUnion {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) : Finset ℕ :=
  univ.biUnion D

noncomputable def brunBlockSign {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) : ℝ :=
  ∏ i, (-1 : ℝ)^(D i).card

 theorem brunBlockChoices_mem {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (D : ι → Finset ℕ) : D ∈ brunBlockChoices P r ↔ ∀ i, D i ⊆ P i ∧ (D i).card ≤ 2*r i := by
  classical
  simp only [brunBlockChoices, Fintype.mem_piFinset, mem_filter, mem_powerset]

 theorem brunBlockSign_abs {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) : |brunBlockSign D| = 1 := by
  simp [brunBlockSign, abs_prod, abs_pow]

 theorem brunBlockUnion_inter {ι : Type*} [Fintype ι] (P D : ι → Finset ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (hD : ∀ i, D i ⊆ P i) (i : ι) :
    brunBlockUnion D ∩ P i = D i := by
  classical
  ext p
  simp only [mem_inter]
  constructor
  · rintro ⟨hp,hpi⟩
    obtain ⟨j,_,hpj⟩ := mem_biUnion.mp hp
    by_cases hji : j = i
    · simpa [hji] using hpj
    · exact False.elim (disjoint_left.mp (hP hji) (hD j hpj) hpi)
  · intro hp
    exact ⟨mem_biUnion.mpr ⟨i,mem_univ i,hp⟩,hD i hp⟩

 theorem brunBlockUnion_injOn {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Set.InjOn brunBlockUnion (brunBlockChoices P r : Set (ι → Finset ℕ)) := by
  intro D hD F hF he
  funext i
  rw [← brunBlockUnion_inter P D hP (fun i => (brunBlockChoices_mem P r D).mp hD i |>.1),
    ← brunBlockUnion_inter P F hP (fun i => (brunBlockChoices_mem P r F).mp hF i |>.1), he]

 theorem brunBlock_upper {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (E : Finset ℕ) : avoidsSelected (brunBlockUnion P) E ≤
      ∏ i, brunTruncation (P i ∩ E) (2*r i) := by
  classical
  by_cases hd : Disjoint (brunBlockUnion P) E
  · have he (i : ι) : P i ∩ E = ∅ := by
      apply disjoint_iff_inter_eq_empty.mp
      apply disjoint_left.mpr
      intro p hp hpe
      exact disjoint_left.mp hd (mem_biUnion.mpr ⟨i,mem_univ i,hp⟩) hpe
    simp [avoidsSelected,hd,he,brunTruncation_even]
  · simp only [avoidsSelected,hd,ite_false]
    exact prod_nonneg (fun i _ => brunTruncation_nonneg _ _)

 theorem brunBlock_expansion {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (E : Finset ℕ) :
    (∏ i, brunTruncation (P i ∩ E) (2*r i)) =
      ∑ D ∈ brunBlockChoices P r, if brunBlockUnion D ⊆ E then brunBlockSign D else 0 := by
  classical
  simp_rw [brunTruncation_inter]
  rw [prod_univ_sum]
  unfold brunBlockChoices
  apply sum_congr rfl
  intro D _
  rw [Fintype.prod_ite_zero]
  have he : (∀ i, D i ⊆ E) ↔ brunBlockUnion D ⊆ E := by
    simp only [brunBlockUnion, biUnion_subset, mem_univ, forall_true_left]
  simp only [he,brunBlockSign]

 theorem brunBlock_main {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (g : ℕ → ℝ) :
    (∑ D ∈ brunBlockChoices P r, brunBlockSign D * ∏ p ∈ brunBlockUnion D, g p) =
      ∏ i, brunMean (P i) g (r i) := by
  classical
  simp_rw [brunMean_eq]
  rw [prod_univ_sum]
  unfold brunBlockChoices
  apply sum_congr rfl
  intro D hD
  have hDP (i : ι) : D i ⊆ P i := ((brunBlockChoices_mem P r D).mp hD i).1
  have hd : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint D := by
    intro i _ j _ hij
    exact (hP hij).mono (hDP i) (hDP j)
  rw [brunBlockUnion, prod_biUnion hd, brunBlockSign, ← prod_mul_distrib]

end JointDickman

end OAI
