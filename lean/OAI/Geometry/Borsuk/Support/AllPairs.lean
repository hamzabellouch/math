import Mathlib
import OAI.Geometry.Borsuk.Projectors.TenPure

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section AllPairs
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)
lemma Admissible.all_pairs {f : E → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) {i j : ι} (hij : i ≠ j) :
    ∃ u : E, ‖u‖ = 1 ∧ 0 < f u i ∧ 0 < f u j := by
  classical
  let y : ι → ℝ := fun l => if l = i ∨ l = j then 1 else -1
  have hy : y ≠ 0 := by intro h; have hi := congrFun h i; simp [y] at hi
  obtain ⟨A,hA,t,ht,hAt⟩ := hf.signedExtension_ray hdim hy
  have hai : 0 < signedExtension f A i := by rw [hAt]; simpa [y] using ht
  have haj : 0 < signedExtension f A j := by rw [hAt]; simpa [y] using ht
  obtain ⟨u,huW,hu,hui⟩ := (hf.signedExtension_positive_support A i).mp hai
  obtain ⟨v,hvW,hv,hvj⟩ := (hf.signedExtension_positive_support A j).mp haj
  apply hf.two_labels_meet (LinearMap.range (op A⁺).toLinearMap) hij ?_ huW hu hui hvW hv hvj
  intro w hw hwn l hli hlj
  apply hf.signedExtension_range_labels (I := {i,j}) ?_ hw hwn (by simp [hli,hlj])
  intro l hl
  have hli : l ≠ i := by aesop
  have hlj : l ≠ j := by aesop
  rw [hAt]
  simp only [Pi.smul_apply,smul_eq_mul,y,ite_eq_right (not_or.mpr ⟨hli,hlj⟩),mul_neg_one]
  linarith
end AllPairs
end BorsukNine

namespace BorsukNine.SixCounting

variable {α : Type*} [DecidableEq α]
noncomputable local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable

noncomputable def triangles (C : Finset α) (T : Finset α → Prop) : Finset (Finset α) :=
  (C.powersetCard 3).filter T

omit [DecidableEq α] in
@[simp] lemma mem_triangles {C U : Finset α} {T : Finset α → Prop} :
    U ∈ triangles C T ↔ U ⊆ C ∧ U.card = 3 ∧ T U := by
  simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

lemma pair_incidence_count (C : Finset α) (T : Finset α → Prop) :
    ∑ P ∈ C.powersetCard 2, ((triangles C T).filter (P ⊆ ·)).card =
      3 * (triangles C T).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    ∑ U ∈ triangles C T, ∑ P ∈ C.powersetCard 2, (if P ⊆ U then (1 : ℕ) else 0) =
        ∑ U ∈ triangles C T, (U.powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [← Finset.card_filter]
      congr 1
      ext P
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨fun h => ⟨h.2, h.1.2⟩,
        fun h => ⟨⟨h.1.trans (mem_triangles.mp hU).1, h.2⟩, h.1⟩⟩
    _ = 3 * (triangles C T).card := by
      have he : ∀ U ∈ triangles C T, (U.powersetCard 2).card = 3 := by
        intro U hU
        rw [Finset.card_powersetCard, (mem_triangles.mp hU).2.1]
        decide
      rw [Finset.sum_congr rfl he]
      simp [mul_comm]

lemma complement_triangle {C U : Finset α} (hC : C.card = 6)
    (hU : U ∈ C.powersetCard 3) : C \ U ∈ C.powersetCard 3 := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.sdiff_subset, ?_⟩
  rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hU).1,
    hC, (Finset.mem_powersetCard.mp hU).2]

lemma triangle_count_upper {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U)) :
    (triangles C T).card ≤ 10 := by
  classical
  let A := triangles C T
  let B := C.powersetCard 3 \ A
  have hA : A ⊆ C.powersetCard 3 := Finset.filter_subset _ _
  have hi : (A.image (fun U => C \ U)) ⊆ B := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC (hA hV), ?_⟩
    intro hh
    exact hdisj V (hA hV) (mem_triangles.mp hV).2.2 (mem_triangles.mp hh).2.2
  have hinj : Set.InjOn (fun U => C \ U) (↑A : Set (Finset α)) := by
    intro U hU V hV he
    have hh := congrArg (fun W => C \ W) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hU).1,
      Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1] using hh
  have hc : A.card ≤ B.card := calc
    A.card = (A.image (fun U => C \ U)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ B.card := Finset.card_le_card hi
  have hB : B.card = 20 - A.card := by
    rw [Finset.card_sdiff_of_subset hA, Finset.card_powersetCard, hC]
    norm_num [Nat.choose]
  change A.card ≤ 10
  omega

lemma triangle_count_eq_ten {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card) :
    (triangles C T).card = 10 := by
  have hupper := triangle_count_upper hC hdisj
  have hlower : 30 ≤ ∑ P ∈ C.powersetCard 2,
      ((triangles C T).filter (P ⊆ ·)).card := by
    calc
      30 = ∑ _P ∈ C.powersetCard 2, 2 := by
        norm_num [Finset.card_powersetCard, hC, Nat.choose]
      _ ≤ _ := Finset.sum_le_sum hpairs
  rw [pair_incidence_count] at hlower
  omega

lemma pair_degree_eq_two {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card)
    {P : Finset α} (hP : P ∈ C.powersetCard 2) :
    ((triangles C T).filter (P ⊆ ·)).card = 2 := by
  have hsum : (∑ _P ∈ C.powersetCard 2, 2) =
      ∑ P ∈ C.powersetCard 2, ((triangles C T).filter (P ⊆ ·)).card := by
    rw [pair_incidence_count, triangle_count_eq_ten hC hdisj hpairs]
    norm_num [Finset.card_powersetCard, hC, Nat.choose]
  exact ((Finset.sum_eq_sum_iff_of_le hpairs).mp hsum P hP).symm

lemma complementary_iff {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card)
    {U : Finset α} (hU : U ∈ C.powersetCard 3) : T U ↔ ¬T (C \ U) := by
  classical
  refine ⟨hdisj U hU, ?_⟩
  intro hn
  let A := triangles C T
  let B := C.powersetCard 3 \ A
  have hA : A ⊆ C.powersetCard 3 := Finset.filter_subset _ _
  have hi : (A.image (fun U => C \ U)) ⊆ B := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC (hA hV), ?_⟩
    intro hh
    exact hdisj V (hA hV) (mem_triangles.mp hV).2.2 (mem_triangles.mp hh).2.2
  have hinj : Set.InjOn (fun U => C \ U) (↑A : Set (Finset α)) := by
    intro U hU V hV he
    have hh := congrArg (fun W => C \ W) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hU).1,
      Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1] using hh
  have he : A.image (fun U => C \ U) = B := by
    apply Finset.eq_of_subset_of_card_le hi
    rw [Finset.card_image_of_injOn hinj, Finset.card_sdiff_of_subset hA,
      Finset.card_powersetCard, hC]
    change Nat.choose 6 3 - (triangles C T).card ≤ (triangles C T).card
    rw [triangle_count_eq_ten hC hdisj hpairs]
    decide
  have hcU : C \ U ∈ B := by
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC hU, ?_⟩
    intro hh
    exact hn (mem_triangles.mp hh).2.2
  rw [← he] at hcU
  obtain ⟨V, hV, hVU⟩ := Finset.mem_image.mp hcU
  have hEq : V = U := by
    have hh := congrArg (fun W => C \ W) hVU
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powersetCard.mp hU).1] using hh
  exact hEq ▸ (mem_triangles.mp hV).2.2

end BorsukNine.SixCounting

end OAI
