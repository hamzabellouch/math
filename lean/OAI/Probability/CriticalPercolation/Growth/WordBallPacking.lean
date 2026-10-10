import Mathlib
import OAI.Probability.CriticalPercolation.Growth.WordLengthGeometry

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def around (a : A) (r : ℕ) : Finset A := (W.ball r).image (fun x => a*x)

lemma mem_around_iff {a x : A} {r : ℕ} : x∈W.around a r ↔ a⁻¹*x∈W.ball r := by
  constructor
  · intro h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
    simpa using hy
  · intro h
    exact Finset.mem_image.mpr ⟨a⁻¹*x,h,mul_inv_cancel_left a x⟩

lemma mem_ball_inv {x : A} {r : ℕ} (hx : x∈W.ball r) : x⁻¹∈W.ball r := by
  have hh := Finset.inv_mem_inv hx
  simpa [ball,←inv_pow,W.inv_eq] using hh

lemma self_mem_around (a : A) (r : ℕ) : a∈W.around a r := by
  rw [W.mem_around_iff]
  simp only [inv_mul_cancel]
  exact Finset.one_mem_pow W.one_mem

lemma card_around (a : A) (r : ℕ) : (W.around a r).card=(W.ball r).card := by
  unfold around
  exact Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel h)

lemma mem_around_symm {a x : A} {r : ℕ} (hx : x∈W.around a r) : a∈W.around x r := by
  rw [W.mem_around_iff] at hx ⊢
  simpa only [mul_inv_rev,inv_inv] using W.mem_ball_inv hx

lemma mem_around_add {a x y : A} {r s : ℕ}
    (hx : x∈W.around a r) (hy : y∈W.around x s) : y∈W.around a (r+s) := by
  rw [W.mem_around_iff] at hx hy ⊢
  rw [ball,pow_add]
  exact Finset.mem_mul.mpr ⟨a⁻¹*x,hx,x⁻¹*y,hy,by simp [mul_assoc]⟩

lemma around_subset_ball {a : A} {R r : ℕ} (ha : a∈W.ball R) :
    W.around a r⊆W.ball (R+r) := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  rw [ball,pow_add]
  exact Finset.mem_mul.mpr ⟨a,ha,y,hy,rfl⟩

lemma ball_card_pos (r : ℕ) : 0<(W.ball r).card :=
  Finset.card_pos.mpr ⟨1,Finset.one_mem_pow W.one_mem⟩

lemma packing_card_bound (J : Finset A) (r : ℕ)
    (hJ : (J:Set A).PairwiseDisjoint (fun a => W.around a r))
    (F : Finset A) (hF : ∀ a∈J, W.around a r⊆F) :
    J.card*(W.ball r).card≤F.card := by
  calc
    _ = ∑ a∈J, (W.around a r).card := by simp only [W.card_around,Finset.sum_const_nat]
    _ = (J.biUnion (fun a => W.around a r)).card := (Finset.card_biUnion hJ).symm
    _ ≤ _ := Finset.card_le_card (by
      intro x hx
      obtain ⟨a,ha,hx⟩ := Finset.mem_biUnion.mp hx
      exact hF a ha hx)

theorem exists_word_ball_packing (R r : ℕ) :
    ∃ J : Finset A, J⊆W.ball R ∧
      (J:Set A).PairwiseDisjoint (fun a => W.around a r) ∧
      J.card*(W.ball r).card≤(W.ball (R+r)).card ∧
      ∀ x∈W.ball R, ∃ a∈J, x∈W.around a (2*r) := by
  let C : Finset (Finset A) := (W.ball R).powerset.filter
    (fun (J : Finset A) => (J:Set A).PairwiseDisjoint (fun a => W.around a r))
  obtain ⟨J,hJmax⟩ := C.exists_maximal <| Finset.filter_nonempty_iff.mpr
    ⟨∅,Finset.empty_mem_powerset _,by simp⟩
  simp only [C,Finset.mem_filter,Finset.mem_powerset] at hJmax
  obtain ⟨hJR,hJ⟩ := hJmax.1
  refine ⟨J,hJR,hJ,W.packing_card_bound J r hJ _ (fun a ha => W.around_subset_ball (hJR ha)),?_⟩
  intro x hx
  by_cases hxJ : x∈J
  · exact ⟨x,hxJ,W.self_mem_around _ _⟩
  by_cases! hd : ∀ a∈J, Disjoint (W.around x r) (W.around a r)
  · exact False.elim (hJmax.not_gt
      ⟨Finset.insert_subset_iff.mpr ⟨hx,hJR⟩,by
        rw [Finset.coe_insert]
        exact hJ.insert (fun a ha _ => hd a ha)⟩
      (Finset.ssubset_insert hxJ))
  · obtain ⟨a,ha,hd⟩ := hd
    obtain ⟨y,hyx,hya⟩ := Finset.not_disjoint_iff.mp hd
    refine ⟨a,ha,?_⟩
    simpa only [show r+r=2*r by omega] using W.mem_around_add hya (W.mem_around_symm hyx)

lemma packing_overlap (J : Finset A) (r t K : ℕ)
    (hJ : (J:Set A).PairwiseDisjoint (fun a => W.around a r))
    (hvol : (W.ball (t+r)).card≤K*(W.ball r).card) (x : A) :
    (J.filter (fun a => x∈W.around a t)).card≤K := by
  let I := J.filter (fun a => x∈W.around a t)
  have hIJ : I⊆J := Finset.filter_subset _ _
  have hId : (I:Set A).PairwiseDisjoint (fun a => W.around a r) := fun a ha b hb hab => hJ (hIJ ha) (hIJ hb) hab
  have hsub (a : A) (ha : a∈I) : W.around a r⊆W.around x (t+r) := by
    intro y hy
    exact W.mem_around_add (W.mem_around_symm (Finset.mem_filter.mp ha).2) hy
  have hh := W.packing_card_bound I r hId (W.around x (t+r)) hsub
  rw [W.card_around] at hh
  exact le_of_mul_le_mul_right (hh.trans hvol) (W.ball_card_pos r)

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
