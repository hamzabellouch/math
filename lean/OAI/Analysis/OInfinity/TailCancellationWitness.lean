import OAI.Analysis.OInfinity.BufferedRelativeWitness
import OAI.Analysis.OInfinity.CanonicalBufferAbsorption
import OAI.Analysis.PureInfiniteness.TailCancellationRows

namespace OAI

/-! # The zero corner containing the entire remaining source copy

The internal isometry `z` has range inside the absorption corner. Its
complement contains both the full residual source copy and a negative
part of the target copy. All data below are constructed in the first
buffer's commutant before applying the second-buffer comparison.
-/

noncomputable section
open Filter Topology
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def BufferAbsorptionCorner.map {F : Type*} [CStarAlgebra F]
    (D : BufferAbsorptionCorner E) (φ : E →⋆ₐ[ℂ] F) : BufferAbsorptionCorner F where
  q := φ D.q
  w := φ D.w
  a := φ D.a
  b := φ D.b
  projection := D.projection.map φ
  w_gram := by simpa only [map_mul, map_star, map_one] using congrArg φ D.w_gram
  w_range := by simpa only [map_mul, map_star, map_sub, map_one] using congrArg φ D.w_range
  w_orthogonal := by simpa only [map_mul, map_zero] using congrArg φ D.w_orthogonal
  a_gram := by simpa only [map_mul, map_star] using congrArg φ D.a_gram
  b_gram := by simpa only [map_mul, map_star] using congrArg φ D.b_gram
  orthogonal := by simpa only [map_mul, map_star, map_zero] using congrArg φ D.orthogonal
  ranges := by simpa only [map_add, map_mul, map_star] using congrArg φ D.ranges

local instance tailWitnessCentralizerClosed (R : ℕ → E) :
    IsClosed (StarSubalgebra.centralizer ℂ (Set.range R) : Set E) :=
  Set.isClosed_centralizer _

/-- The new comparison corner is genuinely a zero corner: its full
binary row comes from the internal isometry and two orthogonal copies
inside the original residual range. -/
lemma exists_tail_cancellation_reference [Nontrivial E]
    (D : BufferAbsorptionCorner E) (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (z : E) (hz : star z * z = 1) (hqz : D.q * z = z) :
    (1 - z * star z) ≠ 0 ∧ ∃ b : Fin 2 → E,
      (∀ i j, star (b i) * b j = if i = j then 1 - z * star z else 0) ∧
      (∑ i, b i * star (b i)) = 1 - z * star z := by
  let r : Fin 3 → E := ![z, D.w * s 0, D.w * s 1]
  have hzw : star z * D.w = 0 := by
    have hsq : star z * D.q = star z := by
      simpa only [star_mul, D.projection.isSelfAdjoint.star_eq] using congrArg star hqz
    calc
      _ = (star z * D.q) * D.w := by rw [hsq]
      _ = 0 := by rw [mul_assoc, D.w_orthogonal, mul_zero]
  have hwz : star D.w * z = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hzw
  have hsg (i j : ℕ) : star (D.w * s i) * (D.w * s j) = if i = j then 1 else 0 := by
    rw [star_mul]
    calc
      _ = star (s i) * (star D.w * D.w) * s j := by noncomm_ring
      _ = _ := by rw [D.w_gram, mul_one, hs]
  have hzws (j : ℕ) : star z * (D.w * s j) = 0 := by rw [← mul_assoc, hzw, zero_mul]
  have hwsz (j : ℕ) : star (D.w * s j) * z = 0 := by
    rw [star_mul, mul_assoc, hwz, mul_zero]
  have hr (i j : Fin 3) : star (r i) * r j = if i = j then 1 else 0 := by
    fin_cases i <;> fin_cases j
    · exact hz
    · exact hzws 0
    · exact hzws 1
    · exact hwsz 0
    · exact hsg 0 0
    · exact hsg 0 1
    · exact hwsz 1
    · exact hsg 1 0
    · exact hsg 1 1
  obtain ⟨hq0, b, hb, hbs, _⟩ := exists_buffer_shrink_range_pair r hr
  exact ⟨hq0, b, hb, hbs⟩

/-- The second buffer compares the entire residual source representation
with the complementary target corner, while fixing the retained full
subcorner pointwise. -/
lemma exists_buffered_tail_cancellation [Nontrivial E]
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (R : ℕ → E) (hR : ∀ i j, star (R i) * R j = if i = j then 1 else 0)
    (D : BufferAbsorptionCorner (StarSubalgebra.centralizer ℂ (Set.range R)))
    (s t : ℕ → StarSubalgebra.centralizer ℂ (Set.range R))
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (z : StarSubalgebra.centralizer ℂ (Set.range R))
    (hz : star z * z = 1) (hqz : D.q * z = z)
    (hqt : ∀ i, Commute D.q (t i))
    (hzt : ∀ i, Commute z (t i) ∧ Commute (star z) (t i))
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let d := NormUltra.QuotientAlgebra.diagonalHom (A := E) U
    ∃ v : unitary (NormUltra.QuotientAlgebra (fun _ : ℕ => E) U), Joined 1 v ∧
      ∀ i : Fin (n + 1),
        ‖(v : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) *
          d (t i * D.q + D.w * s i * star D.w) *
          star (v : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) - d (t i)‖ < ε := by
  intro d
  let C := StarSubalgebra.centralizer ℂ (Set.range R)
  let F := NormUltra.QuotientAlgebra (fun _ : ℕ => E) U
  let φ : C →⋆ₐ[ℂ] F := d.comp C.subtype
  let G := TailCancellation.geometry D z hz hqz
  have hpt (i : ℕ) : Commute (TailCancellation.full z) (t i) :=
    (hzt i).1.mul_left (hzt i).2
  let x : Fin (n + 2) → C := fun i => TailCancellation.sourceRow D z s t i
  let y : Fin (n + 2) → C := fun i => TailCancellation.targetRow z t i
  have hx (i j : Fin (n + 2)) : star (x i) * x j =
      if i = j then TailCancellation.support z else 0 := by
    simpa only [x, Fin.ext_iff] using TailCancellation.source_gram D z G s t hs ht hqt hpt i j
  have hy (i j : Fin (n + 2)) : star (y i) * y j =
      if i = j then TailCancellation.support z else 0 := by
    simpa only [y, Fin.ext_iff] using TailCancellation.target_gram z G.Q_proj t ht i j
  obtain ⟨hQ0, b, hb, hbs⟩ := exists_tail_cancellation_reference D s hs z hz hqz
  obtain ⟨v, hv, hvp, _, hvi⟩ := exists_buffered_relative_witness U R hR
    (TailCancellation.support z) G.Q_proj.isSelfAdjoint.star_eq G.Q_proj.isIdempotentElem.eq
    hQ0 n x y (fun i => TailCancellation.source_support D z G s t hpt i)
    (fun i => TailCancellation.target_support z G.Q_proj t hpt i) hx hy b hb hbs ε hε
  let D' := D.map φ
  have hz' : star (φ z) * φ z = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg φ hz
  have hqz' : D'.q * φ z = φ z := by
    simpa only [D', BufferAbsorptionCorner.map, map_mul] using congrArg φ hqz
  let G' := TailCancellation.geometry D' (φ z) hz' hqz'
  have hvp' : (v : F) * TailCancellation.full (φ z) = TailCancellation.full (φ z) := by
    change (v : F) * (1 - φ (TailCancellation.support z)) =
      1 - φ (TailCancellation.support z) at hvp
    simpa only [TailCancellation.support, TailCancellation.full, map_sub, map_mul,
      map_star, map_one, sub_sub_cancel] using hvp
  have hpt' (i : ℕ) : Commute (TailCancellation.full (φ z)) (φ (t i)) := by
    have h := congrArg φ (hpt i).eq
    change TailCancellation.full (φ z) * φ (t i) = φ (t i) * TailCancellation.full (φ z)
    simpa only [TailCancellation.full, map_mul, map_star] using h
  refine ⟨v, hv, fun i => ?_⟩
  have hi := hvi i
  have he := TailCancellation.recombination_norm D' (φ z) G'
    (fun j => φ (s j)) (fun j => φ (t j)) v hvp' hpt' i
  have hsource : TailCancellation.sourceRow D' (φ z) (fun j => φ (s j))
      (fun j => φ (t j)) i = φ (x i.castSucc) := by
    simp only [TailCancellation.sourceRow, TailCancellation.rest, TailCancellation.full,
      D', BufferAbsorptionCorner.map, x, map_add, map_mul, map_sub, map_star, Fin.val_castSucc]
  have htarget : TailCancellation.targetRow (φ z) (fun j => φ (t j)) i = φ (y i.castSucc) := by
    simp only [TailCancellation.targetRow, TailCancellation.support, TailCancellation.full,
      y, map_mul, map_sub, map_one, map_star, Fin.val_castSucc]
  rw [hsource, htarget] at he
  change ‖(v : F) * φ (t i * D.q + D.w * s i * star D.w) * star (v : F) - φ (t i)‖ < ε
  rw [show φ (t i * D.q + D.w * s i * star D.w) =
      φ (t i) * D'.q + D'.w * φ (s i) * star D'.w by
    simp only [map_add, map_mul, map_star, D', BufferAbsorptionCorner.map]]
  rw [he]
  exact hi

/-- Two commuting proper rows in the first buffer's commutant admit
actual connected finite conjugacy in the next norm ultrapower. -/
lemma exists_buffered_commuting_rows_conjugacy [Nontrivial E]
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (R : ℕ → E) (hR : ∀ i j, star (R i) * R j = if i = j then 1 else 0)
    (s t : ℕ → StarSubalgebra.centralizer ℂ (Set.range R))
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hst : bergRowsCommute s t) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let d := NormUltra.QuotientAlgebra.diagonalHom (A := E) U
    ∃ v : unitary (NormUltra.QuotientAlgebra (fun _ : ℕ => E) U), Joined 1 v ∧
      ∀ i : Fin (n + 1),
        ‖(v : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) * d (s i) *
          star (v : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) - d (t i)‖ < ε := by
  intro d
  let C := StarSubalgebra.centralizer ℂ (Set.range R)
  let F := NormUltra.QuotientAlgebra (fun _ : ℕ => E) U
  let φ : C →⋆ₐ[ℂ] F := d.comp C.subtype
  obtain ⟨D, hanchor, _, hspare, _, _, ⟨z, hz, hqz, hzcomm⟩, hcomm⟩ :=
    exists_canonical_connected_absorption_corner_with_commuting_isometry s hs (n + 1) 1
      (by norm_num)
  have htc (i : ℕ) : ∀ j, Commute (s j) (t i) ∧ Commute (star (s j)) (t i) := by
    intro j
    exact ⟨(hst j i).1, by simpa only [star_star] using (hst j i).2.star_star⟩
  have htcs (i : ℕ) : ∀ j, Commute (s j) (star (t i)) ∧
      Commute (star (s j)) (star (t i)) := by
    intro j
    exact ⟨(hst j i).2, (hst j i).1.star_star⟩
  have hqt (i : ℕ) := (hcomm (t i) (htc i)).1
  have hat (i : ℕ) : Commute (star D.a) (t i) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.2.1.star_star
  have hbt (i : ℕ) : Commute (star D.b) (t i) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.2.2.star_star
  have hzt (i : ℕ) : Commute z (t i) ∧ Commute (star z) (t i) := by
    exact ⟨hzcomm (t i) (htc i), by
      simpa only [star_star] using (hzcomm (star (t i)) (htcs i)).star_star⟩
  have heps : 0 < ε / 2 := by positivity
  obtain ⟨a, ha, hai⟩ := D.exists_proper_vacuum_absorption s t hs ht (n + 1)
    hspare hqt hat hbt (ε / 2) heps
  obtain ⟨v, hv, hvi⟩ := exists_buffered_tail_cancellation U R hR D s t hs ht
    z hz hqz hqt hzt n (ε / 2) heps
  let A : unitary F := Unitary.map (CStarConnectedLift.starMonoidHom φ) a
  have hA : Joined (1 : unitary F) A := by
    have h := (hanchor.trans ha).map (CStarAbsorption.continuous_unitaryMap φ)
    simpa only [map_one] using h
  refine ⟨v * A, by simpa only [one_mul] using hv.mul hA, fun i => ?_⟩
  let c := φ (t i * D.q + D.w * s i * star D.w)
  have hfirst : ‖(A : F) * φ (s i) * star (A : F) - c‖ < ε / 2 := by
    have hn := NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom
      ((a : C) * s i * star (a : C) - (t i * D.q + D.w * s i * star D.w))
    have he : φ ((a : C) * s i * star (a : C) -
        (t i * D.q + D.w * s i * star D.w)) =
        (A : F) * φ (s i) * star (A : F) - c := by
      change φ ((a : C) * s i * star (a : C) - _) =
        φ (a : C) * φ (s i) * star (φ (a : C)) - φ _
      simp only [map_sub, map_mul, map_star]
    change ‖φ ((a : C) * s i * star (a : C) -
      (t i * D.q + D.w * s i * star D.w))‖ ≤ _ at hn
    rw [he] at hn
    exact hn.trans_lt (hai i)
  have hsecond : ‖(v : F) * c * star (v : F) - φ (t i)‖ < ε / 2 := hvi i
  have hnorm : ‖(v : F) * ((A : F) * φ (s i) * star (A : F) - c) *
      star (v : F)‖ = ‖(A : F) * φ (s i) * star (A : F) - c‖ := by
    rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
    exact CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem v.property)
  have hsum := norm_add_le
    ((v : F) * ((A : F) * φ (s i) * star (A : F) - c) * star (v : F))
    ((v : F) * c * star (v : F) - φ (t i))
  rw [hnorm] at hsum
  have hid : ((v * A : unitary F) : F) * φ (s i) * star ((v * A : unitary F) : F) - φ (t i) =
      (v : F) * ((A : F) * φ (s i) * star (A : F) - c) * star (v : F) +
      ((v : F) * c * star (v : F) - φ (t i)) := by
    simp only [Submonoid.coe_mul, star_mul]
    noncomm_ring
  change ‖((v * A : unitary F) : F) * φ (s i) * star ((v * A : unitary F) : F) - φ (t i)‖ < ε
  rw [hid]
  exact hsum.trans_lt (by linarith)

end WeakPureInfiniteness

end

end OAI
