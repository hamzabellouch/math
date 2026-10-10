import OAI.Analysis.OInfinity.RelativeCompletedComparison
import OAI.Analysis.PureInfiniteness.ConnectedUltrapowerLift

namespace OAI

/-! # An actual relative witness after the second buffer

Both completion records and the common range row are constructed. The
only hypotheses concern the given finite proper rows in the first row's
commutant and their shared full binary reference corner.
-/

noncomputable section
open Filter Topology
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

local instance bufferedWitnessCentralizerClosed (R : ℕ → E) :
    IsClosed (StarSubalgebra.centralizer ℂ (Set.range R) : Set E) :=
  Set.isClosed_centralizer _

def RelativeBinaryCompletion.map {F : Type*} [CStarAlgebra F]
    {n : ℕ} {q : E} {b : Fin 2 → E} {x : Fin (n + 1) → E}
    (A : RelativeBinaryCompletion q b x) (f : E →⋆ₐ[ℂ] F) :
    RelativeBinaryCompletion (f q) (fun j => f (b j)) (fun i => f (x i)) := by
  let U := Unitary.map (CStarConnectedLift.starMonoidHom f)
  let P : Path (1 : unitary F) (U A.implementer) :=
    { toFun := fun t => U (A.deformation t)
      continuous_toFun := (CStarAbsorption.continuous_unitaryMap f).comp A.deformation.continuous
      source' := by rw [A.deformation.source, map_one]
      target' := by rw [A.deformation.target] }
  refine {
    row := fun j => f (A.row j)
    implementer := U A.implementer
    deformation := P
    fixes_complement := ?_
    support := ?_
    gram := ?_
    range_sum := ?_
    encoded_prefix := ?_
    cocycle := ?_ }
  · intro t
    constructor
    · change f (A.deformation t : E) * (1 - f q) = 1 - f q
      simpa only [map_mul, map_sub, map_one] using congrArg f (A.fixes_complement t).1
    · change (1 - f q) * f (A.deformation t : E) = 1 - f q
      simpa only [map_mul, map_sub, map_one] using congrArg f (A.fixes_complement t).2
  · intro j
    exact ⟨by simpa only [map_mul] using congrArg f (A.support j).1,
      by simpa only [map_mul] using congrArg f (A.support j).2⟩
  · intro i j
    have h := congrArg f (A.gram i j)
    simpa only [map_mul, map_star, apply_ite, map_zero] using h
  · simpa only [map_sum, map_mul, map_star] using congrArg f A.range_sum
  · intro i
    simpa only [map_mul, map_pow] using congrArg f (A.encoded_prefix i)
  · intro j
    change f (A.implementer : E) * f (A.row j) = f (b j)
    simpa only [map_mul] using congrArg f (A.cocycle j)

/-- The actual second-buffer construction removes the completion-record
hypotheses from the relative comparison. -/
lemma exists_buffered_relative_witness [Nontrivial E]
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (R : ℕ → E) (hR : ∀ i j, star (R i) * R j = if i = j then 1 else 0)
    (q : StarSubalgebra.centralizer ℂ (Set.range R))
    (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (n : ℕ) (x y : Fin (n + 2) → StarSubalgebra.centralizer ℂ (Set.range R))
    (hxs : ∀ i, q * x i = x i ∧ x i * q = x i)
    (hys : ∀ i, q * y i = y i ∧ y i * q = y i)
    (hx : ∀ i j, star (x i) * x j = if i = j then q else 0)
    (hy : ∀ i j, star (y i) * y j = if i = j then q else 0)
    (b : Fin 2 → StarSubalgebra.centralizer ℂ (Set.range R))
    (hb : ∀ i j, star (b i) * b j = if i = j then q else 0)
    (hbs : (∑ i, b i * star (b i)) = q)
    (ε : ℝ) (hε : 0 < ε) :
    let d := NormUltra.QuotientAlgebra.diagonalHom (A := E) U
    ∃ w : unitary (NormUltra.QuotientAlgebra (fun _ : ℕ => E) U), Joined 1 w ∧
      (w : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) * (1 - d q) = 1 - d q ∧
      (1 - d q) * (w : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) = 1 - d q ∧
      ∀ i : Fin (n + 1),
        ‖(w : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) * d (x i.castSucc) *
          star (w : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) - d (y i.castSucc)‖ < ε := by
  intro d
  let C := StarSubalgebra.centralizer ℂ (Set.range R)
  let F := NormUltra.QuotientAlgebra (fun _ : ℕ => E) U
  let D := StarSubalgebra.centralizer ℂ (Set.range (fun i => d (R i)))
  obtain ⟨⟨A⟩, ⟨B⟩⟩ := exists_buffer_preserving_pair_completions U R hR q hq hqq hq0
    n x y hxs hys hx hy b hb hbs
  let a := A.map D.subtype
  let c := B.map D.subtype
  let Q : F := d q
  have hQ : star Q = Q := by
    have h := congrArg C.subtype hq
    change star (q : E) = (q : E) at h
    change star (d (q : E)) = d (q : E)
    rw [← map_star, h]
  have hQQ : Q * Q = Q := by
    have h := congrArg C.subtype hqq
    change (q : E) * (q : E) = (q : E) at h
    change d (q : E) * d (q : E) = d (q : E)
    rw [← map_mul, h]
  have hQ0 : Q ≠ 0 := by
    intro he
    have hn : ‖Q‖ = ‖(q : E)‖ := by
      change ‖NormUltra.QuotientAlgebra.mk U (DirectComparison.boundedDiagonal (q : E))‖ = ‖(q : E)‖
      rw [NormUltra.QuotientAlgebra.norm_mk_eq_limsup]
      change Filter.limsup (fun _ : ℕ => ‖(q : E)‖) (U : Filter ℕ) = ‖(q : E)‖
      rw [Filter.limsup_const]
    rw [he, norm_zero] at hn
    apply hq0
    exact Subtype.ext (norm_eq_zero.mp hn.symm)
  have hqR (j : ℕ) : Commute Q (d (R j)) ∧ Commute Q (star (d (R j))) := by
    obtain ⟨h₁, h₂⟩ := (StarSubalgebra.mem_centralizer_iff ℂ).mp q.property (R j) ⟨j, rfl⟩
    constructor
    · change d (q : E) * d (R j) = d (R j) * d (q : E)
      simpa only [map_mul] using congrArg d h₁.symm
    · change d (q : E) * star (d (R j)) = star (d (R j)) * d (q : E)
      simpa only [map_mul, map_star] using congrArg d h₂.symm
  let r : Fin 3 → F := fun j => d (R j) * Q
  have hrs (j : Fin 3) : Q * r j = r j ∧ r j * Q = r j := by
    constructor
    · change Q * (d (R j) * Q) = d (R j) * Q
      rw [← mul_assoc, (hqR j).1.eq, mul_assoc, hQQ]
    · change (d (R j) * Q) * Q = d (R j) * Q
      rw [mul_assoc, hQQ]
  have hrg (i j : Fin 3) : star (r i) * r j = if i = j then Q else 0 := by
    have hdR : star (d (R i)) * d (R j) = if (i : ℕ) = (j : ℕ) then 1 else 0 := by
      rw [← map_star, ← map_mul, hR]
      split_ifs <;> simp only [map_one, map_zero]
    change star (d (R i) * Q) * (d (R j) * Q) = _
    rw [star_mul, hQ]
    calc
      _ = Q * (star (d (R i)) * d (R j)) * Q := by noncomm_ring
      _ = _ := by
        rw [hdR]
        by_cases hij : i = j
        · simpa only [hij, ite_true, mul_one] using hQQ
        · have hne : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Fin.ext he)
          simp only [hne, hij, ite_false, mul_zero, zero_mul]
  have hr_comm (z : D) (hz : Q * (z : F) = z ∧ (z : F) * Q = z) (j : Fin 3) :
      Commute (z : F) (r j) ∧ Commute (z : F) (star (r j)) := by
    obtain ⟨h₁, h₂⟩ := (StarSubalgebra.mem_centralizer_iff ℂ).mp z.property (d (R j)) ⟨j, rfl⟩
    have hzq : Commute (z : F) Q := hz.2.trans hz.1.symm
    constructor
    · exact (show Commute (z : F) (d (R j)) from h₁.symm).mul_right hzq
    · change Commute (z : F) (star (d (R j) * Q))
      rw [star_mul, hQ]
      exact hzq.mul_right (show Commute (z : F) (star (d (R j))) from h₂.symm)
  have hAR : bergRowsCommute a.row r := fun i j =>
    hr_comm (A.row i) (a.support i) j
  have hBR : bergRowsCommute c.row r := fun i j =>
    hr_comm (B.row i) (c.support i) j
  have hbF : ∀ i j, star (d (b i)) * d (b j) = if i = j then Q else 0 := by
    intro i j
    have h := congrArg (d.comp C.subtype) (hb i j)
    simpa only [map_mul, map_star, apply_ite, map_zero, StarAlgHom.comp_apply,
      StarSubalgebra.subtype_apply] using h
  have hbsF : (∑ i, d (b i) * star (d (b i))) = Q := by
    have h := congrArg (d.comp C.subtype) hbs
    simpa only [map_sum, map_mul, map_star, StarAlgHom.comp_apply,
      StarSubalgebra.subtype_apply] using h
  exact exists_relative_completed_row_comparison Q hQ hQQ hQ0 (fun j => d (b j)) hbF hbsF
    (fun i => d (x i.castSucc)) (fun i => d (y i.castSucc)) a c r hrs hrg hAR hBR ε hε

end WeakPureInfiniteness

end

end OAI
