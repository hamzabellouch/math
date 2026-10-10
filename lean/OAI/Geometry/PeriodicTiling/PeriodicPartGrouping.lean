import OAI.Geometry.PeriodicTiling.FiniteMasks
import OAI.Geometry.PeriodicTiling.PlaneLattices
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

universe uG uι

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

theorem tileIndicator_finite_union_eq_sum {G : Type uG} {ι : Type uι} [Fintype ι]
    (parts : ι → Set G)
    (hbound : ∀ x, (∑ i, tileIndicator ℝ (parts i) x) ≤ 1)
    (s : Finset ι) (x : G) :
    tileIndicator ℝ {x | ∃ i ∈ s, x ∈ parts i} x =
      ∑ i ∈ s, tileIndicator ℝ (parts i) x := by
  classical
  by_cases hx : ∃ i ∈ s, x ∈ parts i
  · obtain ⟨i, hi, hix⟩ := hx
    have hlo : (1 : ℝ) ≤ ∑ j ∈ s, tileIndicator ℝ (parts j) x := by
      simpa only [tileIndicator, ite_eq_left hix] using
        (Finset.single_le_sum (fun j _ => tileIndicator_nonneg (parts j) x) hi)
    have hhi : (∑ j ∈ s, tileIndicator ℝ (parts j) x) ≤ 1 := by
      calc
        _ ≤ ∑ j, tileIndicator ℝ (parts j) x :=
          Finset.sum_le_univ_sum_of_nonneg (fun j => tileIndicator_nonneg (parts j) x)
        _ ≤ 1 := hbound x
    have hmem : x ∈ {x | ∃ j ∈ s, x ∈ parts j} := ⟨i, hi, hix⟩
    rw [tileIndicator, ite_eq_left hmem]
    exact le_antisymm hlo hhi
  · have hz : (∑ i ∈ s, tileIndicator ℝ (parts i) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hix : x ∉ parts i := fun h => hx ⟨i, hi, h⟩
      simp only [tileIndicator, ite_eq_right hix]
    rw [hz]
    simp only [tileIndicator, Set.mem_ofPred_eq, ite_eq_right hx]

theorem exists_grouped_periodic_parts {ι : Type uι} [Fintype ι]
    (parts : ι → Set Plane) (v : ι → Plane)
    (hv : ∀ i, v i ≠ 0) (hp : ∀ i, Period (parts i) (v i))
    {A : Set Plane}
    (hsum : ∀ x, (∑ i, tileIndicator ℝ (parts i) x) = tileIndicator ℝ A x) :
    ∃ (m : ℕ) (w : Fin m → Plane) (grouped : Fin m → Set Plane),
      (∀ j, w j ≠ 0) ∧
      (∀ i j, i ≠ j → planeDet (w i) (w j) ≠ 0) ∧
      (∀ x, (∑ j, tileIndicator ℝ (grouped j) x) = tileIndicator ℝ A x) ∧
      ∀ j, Period (grouped j) (w j) := by
  classical
  let r : Setoid ι :=
    { r := fun i j => planeDet (v i) (v j) = 0
      iseqv := ⟨fun i => planeDet_self (v i),
        fun {i j} hij => by rw [planeDet_swap, hij, neg_zero],
        fun {i j k} hij hjk => planeDet_zero_trans (hv j) hij hjk⟩ }
  let Q := Quotient r
  let : Fintype Q := Fintype.ofFinite Q
  let cls : ι → Q := Quotient.mk r
  let fiber (j : Q) : Finset ι := Finset.univ.filter (fun i => cls i = j)
  have mem_fiber (i : ι) (j : Q) : i ∈ fiber j ↔ cls i = j := by
    simp [fiber]
  have out_mem (j : Q) : j.out ∈ fiber j :=
    (mem_fiber _ _).2 (Quotient.out_eq j)
  have hex (j : Q) : ∃ w : Plane, w ≠ 0 ∧
      ∀ i ∈ fiber j, ∃ n : ℤ, w = n • v i := by
    have himage : ((fiber j).image v).Nonempty :=
      ⟨v j.out, Finset.mem_image_of_mem v (out_mem j)⟩
    obtain ⟨w, hw, hm⟩ := exists_common_collinear_multiple ((fiber j).image v) himage
      (by
        intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        exact hv i)
      (by
        intro z hz z' hz'
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hz'
        exact Quotient.exact (((mem_fiber i j).1 hi).trans ((mem_fiber i' j).1 hi').symm))
    exact ⟨w, hw, fun i hi => hm (v i) (Finset.mem_image_of_mem v hi)⟩
  choose w hw hm using hex
  let grouped : Q → Set Plane := fun j => {x | ∃ i ∈ fiber j, x ∈ parts i}
  have hbound (x : Plane) : (∑ i, tileIndicator ℝ (parts i) x) ≤ 1 := by
    rw [hsum]
    exact tileIndicator_le_one A x
  have hind (j : Q) (x : Plane) : tileIndicator ℝ (grouped j) x =
      ∑ i ∈ fiber j, tileIndicator ℝ (parts i) x :=
    tileIndicator_finite_union_eq_sum parts hbound (fiber j) x
  have htotal (x : Plane) : (∑ j, tileIndicator ℝ (grouped j) x) =
      tileIndicator ℝ A x := by
    simp_rw [hind]
    simp only [fiber, Finset.sum_filter]
    rw [Finset.sum_comm]
    calc
      (∑ i, ∑ j : Q, if cls i = j then tileIndicator ℝ (parts i) x else 0) =
          ∑ i, tileIndicator ℝ (parts i) x := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [ite_eq_left rfl, ite_true] using
          (Finset.sum_eq_single (s := Finset.univ)
            (f := fun j : Q => if cls i = j then tileIndicator ℝ (parts i) x else 0)
            (cls i) (fun j _ hji => ite_eq_right (Ne.symm hji))
            (fun h => (h (Finset.mem_univ (cls i))).elim))
      _ = tileIndicator ℝ A x := hsum x
  have hper (j : Q) : Period (grouped j) (w j) := by
    intro x
    change (∃ i ∈ fiber j, x + w j ∈ parts i) ↔ ∃ i ∈ fiber j, x ∈ parts i
    constructor
    · rintro ⟨i, hi, hx⟩
      obtain ⟨n, hn⟩ := hm j i hi
      refine ⟨i, hi, ?_⟩
      rw [hn] at hx
      exact ((hp i).zsmul n x).mp hx
    · rintro ⟨i, hi, hx⟩
      obtain ⟨n, hn⟩ := hm j i hi
      refine ⟨i, hi, ?_⟩
      rw [hn]
      exact ((hp i).zsmul n x).mpr hx
  have hpair (j k : Q) (hjk : j ≠ k) : planeDet (w j) (w k) ≠ 0 := by
    intro hdet
    obtain ⟨n, hn⟩ := hm j j.out (out_mem j)
    obtain ⟨m, hmk⟩ := hm k k.out (out_mem k)
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hw j (by simpa [hn0] using hn)
    have hm0 : m ≠ 0 := by
      intro hm0
      exact hw k (by simpa [hm0] using hmk)
    rw [hn, hmk, planeDet_zsmul_left, planeDet_zsmul_right] at hdet
    have hz : planeDet (v j.out) (v k.out) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left hn0)).resolve_left hm0
    apply hjk
    calc
      j = cls j.out := (Quotient.out_eq j).symm
      _ = cls k.out := Quotient.sound hz
      _ = k := Quotient.out_eq k
  let e : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
  refine ⟨Fintype.card Q, fun j => w (e j), fun j => grouped (e j),
    fun j => hw (e j), ?_, ?_, fun j => hper (e j)⟩
  · intro i j hij
    exact hpair (e i) (e j) (fun he => hij (e.injective he))
  · intro x
    rw [e.sum_comp (fun j => tileIndicator ℝ (grouped j) x)]
    exact htotal x

end PeriodicTilingThree

end

end OAI
