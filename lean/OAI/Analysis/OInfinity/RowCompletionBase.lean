import OAI.Analysis.OInfinity.ConnectedRowCompletion

namespace OAI

/-! # The actual base path of the common-corner shrink

Binary completions chosen with connected left cocycles have a connected
base comparison. The proof identifies that base with compression of the
literal cocycle product by one fixed isometry. No general claim about a
corner stabilizer or about the ambient unitary group is used.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The cross product of two fillers with the same initial projection is
the standard compression of their middle unitary product. -/
lemma coisometry_filler_cross (A y : E) (hA : A * star A = 1)
    (hy : star y * y = 1) (hpy : (star A * A) * y = y) (u v : unitary E) :
    star (1 - star A * A + y * (star (v : E) * A)) *
        (1 - star A * A + y * (star (u : E) * A)) =
      (binaryCornerUnitary (star A) (by simpa only [star_star] using hA) (v * star u) : E) := by
  let p := star A * A
  let e := 1 - p
  have hp : star p = p := by simp only [p, star_mul, star_star]
  have hpp : p * p = p := by
    change (star A * A) * (star A * A) = star A * A
    calc
      _ = star A * (A * star A) * A := by noncomm_ring
      _ = _ := by rw [hA, mul_one]
  have he : star e = e := by simp only [e, star_sub, star_one, hp]
  have hee : e * e = e := by dsimp only [e]; noncomm_ring [hpp]
  have hey : e * y = 0 := by
    change (1 - star A * A) * y = 0
    rw [sub_mul, one_mul, hpy, sub_self]
  have hleft (w : unitary E) : e * (y * (star (w : E) * A)) = 0 := by
    rw [← mul_assoc, hey, zero_mul]
  have hright : star (y * (star (v : E) * A)) * e = 0 := by
    simpa only [star_mul, he, star_zero] using congrArg star (hleft v)
  have hmiddle : star (y * (star (v : E) * A)) * (y * (star (u : E) * A)) =
      star A * ((v : E) * star (u : E)) * A := by
    simp only [star_mul, star_star]
    calc
      _ = star A * (v : E) * (star y * y) * star (u : E) * A := by noncomm_ring
      _ = _ := by rw [hy, mul_one]; noncomm_ring
  change _ = cornerCompression (star A) ((v * star u : unitary E) : E)
  unfold cornerCompression
  rw [star_star]
  change star (e + y * (star (v : E) * A)) * (e + y * (star (u : E) * A)) =
    star A * ((v : E) * star (u : E)) * A + e
  rw [star_add, he, add_mul, mul_add, mul_add, hee, hleft, hright, hmiddle]
  abel

/-- Factoring the reference row out of the finite transfer keeps the
initial projection independent of the chosen completion cocycle. -/
lemma binaryShrinkValue_reference (r b : Fin 2 → E) (u : unitary E) :
    binaryShrinkValue r (fun i => star (u : E) * b i) 1 =
      1 - star (finiteCuntzTransfer r b 1) * finiteCuntzTransfer r b 1 +
        r 1 * (star (u : E) * finiteCuntzTransfer r b 1) := by
  let A := finiteCuntzTransfer r b 1
  have htransfer : finiteCuntzTransfer r (fun i => star (u : E) * b i) 1 =
      star (u : E) * A := by
    simp only [A, finiteCuntzTransfer, Finset.mul_sum, mul_one, mul_assoc]
  rw [binaryShrinkValue_one, htransfer]
  change 1 - star (star (u : E) * A) * (star (u : E) * A) +
    r 1 * (star (u : E) * A) = _
  have hg : star (star (u : E) * A) * (star (u : E) * A) = star A * A := by
    rw [star_mul, star_star]
    calc
      _ = star A * ((u : E) * star (u : E)) * A := by noncomm_ring
      _ = _ := by rw [u.property.2, mul_one]
  rw [hg]

/-- The fixed isometry and the full reference row give the exact base
identity used in the two common-corner comparisons. -/
lemma finiteCuntzTransfer_reference_coisometry (r b : Fin 2 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (hbs : (∑ i, b i * star (b i)) = 1) :
    finiteCuntzTransfer r b 1 * star (finiteCuntzTransfer r b 1) = 1 := by
  have hs : star (finiteCuntzTransfer r b 1) = finiteCuntzTransfer b r 1 := by
    simpa only [star_one] using finiteCuntzTransfer_star r b 1
  have hh := finiteCuntzTransfer_star_mul b r hr 1
  rw [← hs, star_star] at hh
  simpa only [star_one, one_mul, mul_one, hbs] using hh

lemma binaryShrinkValue_reference_cross (r b : Fin 2 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (hb : ∀ i j, star (b i) * b j = if i = j then 1 else 0)
    (hbs : (∑ i, b i * star (b i)) = 1) (u v : unitary E) :
    ∃ K : unitary E,
      (K : E) = star (binaryShrinkValue r (fun i => star (v : E) * b i) 1) *
        binaryShrinkValue r (fun i => star (u : E) * b i) 1 ∧
      K = binaryCornerUnitary (star (finiteCuntzTransfer r b 1))
        (by simpa only [star_star] using
          finiteCuntzTransfer_reference_coisometry r b hr hbs) (v * star u) := by
  let A := finiteCuntzTransfer r b 1
  have hAst : star A = finiteCuntzTransfer b r 1 := by
    simpa only [A, star_one] using finiteCuntzTransfer_star r b 1
  have hAA : A * star A = 1 := by
    have hh := finiteCuntzTransfer_star_mul b r hr 1
    rw [← hAst, star_star] at hh
    simpa only [star_one, one_mul, mul_one, hbs] using hh
  have hAp : star A * A = ∑ i, r i * star (r i) := by
    simpa only [A, star_one, one_mul, mul_one] using finiteCuntzTransfer_star_mul r b hb 1
  have hr1 : star (r 1) * r 1 = 1 := by simpa only [ite_true] using hr 1 1
  have hpy : (star A * A) * r 1 = r 1 := by
    rw [hAp]
    simpa only [finiteRowPermutation, Equiv.Perm.one_apply] using
      finiteRowPermutation_mul_row 1 r (by simp) (by simp) hr 1 1
  let K := binaryCornerUnitary (star A) (by simpa only [star_star] using hAA) (v * star u)
  refine ⟨K, ?_, rfl⟩
  rw [binaryShrinkValue_reference, binaryShrinkValue_reference]
  exact (coisometry_filler_cross A (r 1) hAA hr1 hpy u v).symm

/-- The base product is connected because its two prescribed cocycles
are connected. This is the concrete path, rather than an ambient K1 claim. -/
lemma binaryShrinkValue_reference_cross_joined (r b : Fin 2 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (hb : ∀ i j, star (b i) * b j = if i = j then 1 else 0)
    (hbs : (∑ i, b i * star (b i)) = 1)
    (u v : unitary E) (hu : Joined (1 : unitary E) u) (hv : Joined (1 : unitary E) v) :
    ∃ K : unitary E, Joined (1 : unitary E) K ∧
      (K : E) = star (binaryShrinkValue r (fun i => star (v : E) * b i) 1) *
        binaryShrinkValue r (fun i => star (u : E) * b i) 1 := by
  obtain ⟨K, hK, hKe⟩ := binaryShrinkValue_reference_cross r b hr hb hbs u v
  have hu' : Joined (1 : unitary E) (star u) := by
    simpa only [star_one] using hu.map (continuous_star : Continuous (star : unitary E → unitary E))
  have huv : Joined (1 : unitary E) (v * star u) := by
    simpa only [one_mul] using hv.mul hu'
  refine ⟨K, ?_, hK⟩
  rw [hKe]
  have hA : star (star (finiteCuntzTransfer r b 1)) * star (finiteCuntzTransfer r b 1) = 1 := by
    simpa only [star_star] using finiteCuntzTransfer_reference_coisometry r b hr hbs
  simpa only [binaryCornerUnitary_one] using
    huv.map (binaryCornerUnitary_continuous (star (finiteCuntzTransfer r b 1)) hA)

end WeakPureInfiniteness

end

end OAI
