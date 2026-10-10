import Mathlib.Data.Finset.Sort
import OAI.NumberTheory.SiegelZeros.Determinants.DeterminantBridge

namespace OAI

namespace SiegelZeros


namespace SiegelZerosAwei.W30

open Module

variable {K : Type*} [Field K]
variable {ι n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem selected_card_eq (rows : ι → n → K) (s : Finset ι)
    (hlin : LinearIndepOn K rows (s : Set ι))
    (hspan : Submodule.span K (rows '' (s : Set ι)) = ⊤) :
    Fintype.card s = Fintype.card n := by
  have hset : Set.range (fun i : s => rows i) = rows '' (s : Set ι) := by
    ext x
    simp
  have h : Module.finrank K (Submodule.span K (Set.range (fun i : s => rows i))) =
      Fintype.card s :=
    _root_.finrank_span_eq_card (b := fun i : s => rows i) hlin.linearIndependent
  rw [hset, hspan, finrank_top, Module.finrank_pi] at h
  exact h.symm

theorem selected_equiv_det_ne_zero (rows : ι → n → K) (s : Finset ι)
    (hlin : LinearIndepOn K rows (s : Set ι))
    (hspan : Submodule.span K (rows '' (s : Set ι)) = ⊤) :
    ∃ e : n ≃ s, Matrix.det (fun i j => rows (e i) j) ≠ 0 := by
  classical
  let e : n ≃ s := (Fintype.equivOfCardEq (selected_card_eq rows s hlin hspan)).symm
  refine ⟨e, det_ne_zero_of_independent_rows _ ?_⟩
  exact hlin.linearIndependent.comp e e.injective

end SiegelZerosAwei.W30



namespace SiegelZerosAwei.W30

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [LinearOrder ι] {M : ℕ}

def orderedIndex (s : Finset ι) (hcard : s.card = M) : Fin M ↪o ι :=
  s.orderEmbOfFin hcard

theorem orderedIndex_mem (s : Finset ι) (hcard : s.card = M) (i : Fin M) :
    orderedIndex s hcard i ∈ s :=
  s.orderEmbOfFin_mem hcard i

theorem orderedIndex_strictMono (s : Finset ι) (hcard : s.card = M) :
    StrictMono (orderedIndex s hcard) :=
  (orderedIndex s hcard).strictMono

theorem orderedIndex_earlier_image (s : Finset ι) (hcard : s.card = M) (i : Fin M) :
    orderedIndex s hcard '' Set.Iio i =
      (s.filter (fun a => a < orderedIndex s hcard i) : Set ι) := by
  ext a
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨orderedIndex_mem s hcard j, (orderedIndex s hcard).strictMono hj⟩
  · intro ha
    obtain ⟨has, hai⟩ := Finset.mem_filter.mp ha
    let j := (s.orderIsoOfFin hcard).symm ⟨a, has⟩
    have hja : orderedIndex s hcard j = a := by
      exact congrArg Subtype.val ((s.orderIsoOfFin hcard).apply_symm_apply ⟨a, has⟩)
    refine ⟨j, ?_, hja⟩
    exact (orderedIndex s hcard).lt_iff_lt.mp (by simpa only [hja] using hai)

theorem ordered_rows_earlier_span (row : ι → V) (s : Finset ι)
    (hcard : s.card = M) (i : Fin M) :
    Submodule.span K ((fun j => row (orderedIndex s hcard j)) '' Set.Iio i) =
      Submodule.span K
        (row '' (s.filter (fun a => a < orderedIndex s hcard i) : Set ι)) := by
  rw [← orderedIndex_earlier_image s hcard i, Set.image_image]

theorem mem_ordered_rows_earlier_span (row : ι → V) (s : Finset ι)
    (hcard : s.card = M) (i : Fin M) (v : V)
    (hv : v ∈ Submodule.span K
      (row '' (s.filter (fun a => a < orderedIndex s hcard i) : Set ι))) :
    v ∈ Submodule.span K ((fun j => row (orderedIndex s hcard j)) '' Set.Iio i) := by
  rw [ordered_rows_earlier_span]
  exact hv

theorem ordered_rows_det_ne_zero (row : ι → Fin M → K) (s : Finset ι)
    (hcard : s.card = M) (hlin : LinearIndepOn K row (s : Set ι)) :
    Matrix.det (fun i j => row (orderedIndex s hcard i) j) ≠ 0 := by
  apply det_ne_zero_of_independent_rows
  exact hlin.linearIndependent.comp (s.orderIsoOfFin hcard)
    (s.orderIsoOfFin hcard).injective

theorem ordered_rows_det_of_spanning (row : ι → Fin M → K) (s : Finset ι)
    (hlin : LinearIndepOn K row (s : Set ι))
    (hspan : Submodule.span K (row '' (s : Set ι)) = ⊤) :
    ∃ hcard : s.card = M,
      Matrix.det (fun i j => row (orderedIndex s hcard i) j) ≠ 0 := by
  have hcard : s.card = M := by
    simpa using selected_card_eq row s hlin hspan
  exact ⟨hcard, ordered_rows_det_ne_zero row s hcard hlin⟩

end SiegelZerosAwei.W30


end SiegelZeros

end OAI
