import OAI.Analysis.OInfinity.ZeroUnitRows
import OAI.Analysis.OInfinity.CentralBufferImage
import OAI.Analysis.PureInfiniteness.ConnectedUltrapowerLift

namespace OAI

/-! # Mixed stabilization in the explicit zero-unit corner

The row `t₁ sᵢ t₁* + tᵢ₊₂ p` is the direct sum of the source row and the
negative target corner, with unit `1 - t₀t₀*`. Its Gram and support formulas
do not require the two rows to commute. The comparison below uses the actual
third buffer and retains the exact corner transport; it does not cancel the
negative summand or claim ambient half-flip.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def mixedNegativeRow (s t : ℕ → E) (i : ℕ) : E :=
  t 1 * s i * star (t 1) + t (i + 2) * canonicalNegativeProjection t

lemma mixedNegativeRow_self (t : ℕ → E) (i : ℕ) :
    mixedNegativeRow t t i = canonicalNegativeRow t i := rfl

lemma mixedNegativeRow_gram (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (i j : ℕ) :
    star (mixedNegativeRow s t i) * mixedNegativeRow s t j =
      if i = j then canonicalTailProjection t 1 else 0 := by
  let p := canonicalNegativeProjection t
  have hp : star p = p := canonicalTailProjection_star t 2
  have hpp : p * p = p := canonicalTailProjection_idempotent t ht 2
  have h11 : star (t 1) * t 1 = 1 := by simpa only [ite_true] using ht 1 1
  have hi1 : star (t 1) * t (j + 2) = 0 := by rw [ht, ite_eq_right (by omega)]
  have hj1 : star (t (i + 2)) * t 1 = 0 := by rw [ht, ite_eq_right (by omega)]
  have hA : star (t 1 * s i * star (t 1)) * (t 1 * s j * star (t 1)) =
      t 1 * (star (s i) * s j) * star (t 1) := by
    simp only [star_mul, star_star]
    calc
      _ = t 1 * star (s i) * (star (t 1) * t 1) * s j * star (t 1) := by noncomm_ring
      _ = _ := by rw [h11, mul_one]; noncomm_ring
  have hAB : star (t 1 * s i * star (t 1)) * (t (j + 2) * p) = 0 := by
    simp only [star_mul, star_star]
    calc
      _ = t 1 * star (s i) * (star (t 1) * t (j + 2)) * p := by noncomm_ring
      _ = 0 := by rw [hi1, mul_zero, zero_mul]
  have hBA : star (t (i + 2) * p) * (t 1 * s j * star (t 1)) = 0 := by
    simp only [star_mul, hp]
    calc
      _ = p * (star (t (i + 2)) * t 1) * s j * star (t 1) := by noncomm_ring
      _ = 0 := by rw [hj1, mul_zero, zero_mul, zero_mul]
  have hB : star (t (i + 2) * p) * (t (j + 2) * p) =
      p * (star (t (i + 2)) * t (j + 2)) * p := by rw [star_mul, hp]; noncomm_ring
  change star (t 1 * s i * star (t 1) + t (i + 2) * p) *
    (t 1 * s j * star (t 1) + t (j + 2) * p) = _
  rw [star_add, add_mul, mul_add, mul_add, hA, hAB, hBA, hB, add_zero, zero_add,
    hs, ht]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, mul_one, hpp]
    change t 1 * star (t 1) + canonicalTailProjection t 2 = canonicalTailProjection t 1
    rw [canonicalTailProjection_succ t 1]
    abel
  · have hij' : i + 2 ≠ j + 2 := by omega
    simp only [hij, hij', ite_false, mul_zero, zero_mul, add_zero]

lemma mixedNegativeRow_support (s t : ℕ → E)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (i : ℕ) :
    canonicalTailProjection t 1 * mixedNegativeRow s t i = mixedNegativeRow s t i ∧
    mixedNegativeRow s t i * canonicalTailProjection t 1 = mixedNegativeRow s t i := by
  have hq1 : canonicalTailProjection t 1 * t 1 = t 1 := by
    simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_mul_generator t ht 1 1
  have hq2 : canonicalTailProjection t 1 * t (i + 2) = t (i + 2) := by
    simpa only [show ¬i + 2 < 1 by omega, ite_false] using
      canonicalTailProjection_mul_generator t ht 1 (i + 2)
  have hsq : star (t 1) * canonicalTailProjection t 1 = star (t 1) := by
    simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_generator_star t ht 1 1
  obtain ⟨_, hpq⟩ := canonicalNegativeProjection_le_tail t ht
  constructor
  · simp only [mixedNegativeRow, mul_add, ← mul_assoc, hq1, hq2]
  · simp only [mixedNegativeRow, add_mul, mul_assoc, hsq, hpq]

lemma mixedNegativeRow_commutes (s t : ℕ → E) (x : E)
    (hs : ∀ i, Commute (s i) x)
    (ht : ∀ i, Commute (t i) x ∧ Commute (star (t i)) x) (i : ℕ) :
    Commute (mixedNegativeRow s t i) x := by
  exact (((ht 1).1.mul_left (hs i)).mul_left (ht 1).2).add_left
    ((ht (i + 2)).1.mul_left (canonicalTailProjection_commutes t x ht 2))

lemma mixedNegativeRow_coe (C : StarSubalgebra ℂ E) [IsClosed (C : Set E)]
    (s t : ℕ → C) (i : ℕ) :
    ((mixedNegativeRow s t i : C) : E) =
      mixedNegativeRow (fun j => (s j : E)) (fun j => (t j : E)) i := by
  change C.subtype (t 1 * s i * star (t 1) + t (i + 2) * canonicalTailProjection t 2) = _
  simp only [map_add, map_mul, map_star, StarSubalgebra.subtype_apply,
    canonicalTailProjection_coe, mixedNegativeRow, canonicalNegativeProjection]

lemma map_canonicalTailProjection {A : Type*} [CStarAlgebra A]
    (f : A →⋆ₐ[ℂ] E) (s : ℕ → A) (n : ℕ) :
    f (canonicalTailProjection s n) = canonicalTailProjection (fun i => f (s i)) n := by
  simp only [canonicalTailProjection, map_sub, map_one, map_sum, map_mul, map_star]

lemma map_mixedNegativeRow {A : Type*} [CStarAlgebra A]
    (f : A →⋆ₐ[ℂ] E) (s t : ℕ → A) (i : ℕ) :
    f (mixedNegativeRow s t i) = mixedNegativeRow (fun j => f (s j)) (fun j => f (t j)) i := by
  simp only [mixedNegativeRow, map_add, map_mul, map_star, canonicalNegativeProjection,
    map_canonicalTailProjection]

lemma map_canonicalNegativeRow {A : Type*} [CStarAlgebra A]
    (f : A →⋆ₐ[ℂ] E) (s : ℕ → A) (i : ℕ) :
    f (canonicalNegativeRow s i) = canonicalNegativeRow (fun j => f (s j)) i :=
  map_mixedNegativeRow f s s i

/-- Both rows are compared through the same actual buffer. The resulting
ambient connected unitary preserves the mixed row's unit exactly. -/
lemma exists_mixedNegative_buffer_comparison [Nontrivial E]
    (r : ℕ → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (s t : ℕ → StarSubalgebra.centralizer ℂ (Set.range r))
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * canonicalTailProjection (fun j => (t j : E)) 1 * star (u : E) =
        canonicalTailProjection (fun j => (t j : E)) 1 ∧
      ∀ i : Fin (n + 1),
        ‖(u : E) * mixedNegativeRow (fun j => (s j : E)) (fun j => (t j : E)) i *
          star (u : E) - canonicalNegativeRow (fun j => (t j : E)) i‖ < ε := by
  let C := StarSubalgebra.centralizer ℂ (Set.range r)
  let : IsClosed (C : Set E) := Set.isClosed_centralizer _
  let q : C := canonicalTailProjection t 1
  have hq : star q = q := canonicalTailProjection_star t 1
  have hqq : q * q = q := canonicalTailProjection_idempotent t ht 1
  have hq0 : q ≠ 0 := canonicalTailProjection_ne_zero t ht 1
  have hqdef : q = 1 - t 0 * star (t 0) := by
    dsimp only [q]
    rw [show (1 : ℕ) = 0 + 1 by rfl, canonicalTailProjection_succ, canonicalTailProjection_zero]
  have hw : star (t 0) * t 0 = 1 := by simpa only [ite_true] using ht 0 0
  have hz : star (t 1) * t 1 = 1 := by simpa only [ite_true] using ht 1 1
  have hw2 : star (t 2) * t 2 = 1 := by simpa only [ite_true] using ht 2 2
  have h01 : star (t 0) * t 1 = 0 := by simpa using ht 0 1
  have h02 : star (t 0) * t 2 = 0 := by simpa using ht 0 2
  have h12 : star (t 1) * t 2 = 0 := by simpa using ht 1 2
  have hww : t 0 * star (t 0) = 1 - q := by rw [hqdef]; abel
  have hqz : q * t 1 = t 1 := by
    exact (canonicalTailProjection_mul_generator t ht 1 1).trans (ite_eq_right (by omega))
  obtain ⟨a, b, v, _hv, _hae, _hbe, _hve, ha, hb, hab, hsum⟩ :=
    exists_zero_corner_cuntz_pair (t 0) (t 1) (t 2) hw hz hw2 h01 h02 h12
  rw [← hqdef] at ha hb hsum
  let x : Fin (n + 2) → C := fun i => mixedNegativeRow s t i
  let y : Fin (n + 2) → C := fun i => canonicalNegativeRow t i
  have hxs (i : Fin (n + 2)) : q * x i = x i ∧ x i * q = x i :=
    mixedNegativeRow_support s t ht i
  have hys (i : Fin (n + 2)) : q * y i = y i ∧ y i * q = y i :=
    canonicalNegativeRow_support t ht i
  have hx (i j : Fin (n + 2)) : star (x i) * x j = if i = j then q else 0 := by
    simpa only [x, q, Fin.ext_iff] using mixedNegativeRow_gram s t hs ht i j
  have hy (i j : Fin (n + 2)) : star (y i) * y j = if i = j then q else 0 := by
    simpa only [y, q, Fin.ext_iff] using canonicalNegativeRow_gram t ht i j
  obtain ⟨ux, hux, huxq, hex⟩ := exists_finite_zeroUnit_buffer_comparison
    r hr q (t 0) (t 1) hq hqq hq0 hw hww hz hqz n x hxs hx a b ha hb hab hsum
    (ε / 2) (by positivity)
  obtain ⟨uy, huy, huyq, hey⟩ := exists_finite_zeroUnit_buffer_comparison
    r hr q (t 0) (t 1) hq hqq hq0 hw hww hz hqz n y hys hy a b ha hb hab hsum
    (ε / 2) (by positivity)
  let u : unitary E := star uy * ux
  have hu : Joined (1 : unitary E) u := by
    simpa only [star_one, one_mul] using (huy.map continuous_star).mul hux
  have hqcoe : (q : E) = canonicalTailProjection (fun j => (t j : E)) 1 :=
    canonicalTailProjection_coe C t 1
  have huyback : star (uy : E) * canonicalTailProjection r 1 * (uy : E) = (q : E) := by
    rw [← huyq]
    calc
      _ = (star (uy : E) * (uy : E)) * (q : E) *
          (star (uy : E) * (uy : E)) := by noncomm_ring
      _ = _ := by rw [uy.property.1, one_mul, mul_one]
  refine ⟨u, hu, ?_, fun i => ?_⟩
  · rw [← hqcoe]
    change (star (uy : E) * (ux : E)) * (q : E) *
      star (star (uy : E) * (ux : E)) = (q : E)
    rw [star_mul, star_star]
    calc
      _ = star (uy : E) * ((ux : E) * (q : E) * star (ux : E)) * (uy : E) := by noncomm_ring
      _ = _ := by rw [huxq, huyback]
  · have he : ‖(ux : E) * (x i.castSucc : E) * star (ux : E) -
        (uy : E) * (y i.castSucc : E) * star (uy : E)‖ < ε := by
      calc
        _ ≤ ‖(ux : E) * (x i.castSucc : E) * star (ux : E) - canonicalNegativeRow r i‖ +
            ‖canonicalNegativeRow r i - (uy : E) * (y i.castSucc : E) * star (uy : E)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (hex i) (by simpa only [norm_sub_rev] using hey i)
        _ = ε := by ring
    have heq : (u : E) * (x i.castSucc : E) * star (u : E) - (y i.castSucc : E) =
        star (uy : E) * ((ux : E) * (x i.castSucc : E) * star (ux : E) -
          (uy : E) * (y i.castSucc : E) * star (uy : E)) * (uy : E) := by
      have hback : star (uy : E) * ((uy : E) * (y i.castSucc : E) * star (uy : E)) *
          (uy : E) = (y i.castSucc : E) := by
        calc
          _ = (star (uy : E) * (uy : E)) * (y i.castSucc : E) *
              (star (uy : E) * (uy : E)) := by noncomm_ring
          _ = _ := by rw [uy.property.1, one_mul, mul_one]
      change (star (uy : E) * (ux : E)) * (x i.castSucc : E) *
        star (star (uy : E) * (ux : E)) - (y i.castSucc : E) = _
      rw [star_mul, star_star, mul_sub, sub_mul, hback]
      noncomm_ring
    have hh : ‖(u : E) * (x i.castSucc : E) * star (u : E) - (y i.castSucc : E)‖ < ε := by
      rw [heq, mul_assoc]
      change ‖((star uy : unitary E) : E) *
        (((ux : E) * (x i.castSucc : E) * star (ux : E) -
          (uy : E) * (y i.castSucc : E) * star (uy : E)) * (uy : E))‖ < ε
      rw [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary]
      exact he
    simpa only [x, y, mixedNegativeRow_coe, canonicalNegativeRow_coe, Fin.val_castSucc] using hh

/-- The third row is constructed, not assumed: the two commuting factor
images admit mixed stabilization in their actual norm ultrapower. -/
lemma exists_mixedNegative_factor_ultrapower_comparison [Nontrivial E]
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]
    (f g : OInfinity →⋆ₐ[ℂ] E) (hfg : ∀ x y, Commute (f x) (g y))
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let d := NormUltra.QuotientAlgebra.diagonalHom (A := E) U
    let s := fun i => f (oInfinityIsometry i)
    let t := fun i => g (oInfinityIsometry i)
    ∃ u : unitary (NormUltra.QuotientAlgebra (fun _ : ℕ => E) U), Joined 1 u ∧
      (u : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) * d (canonicalTailProjection t 1) *
          star (u : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) = d (canonicalTailProjection t 1) ∧
      ∀ i : Fin (n + 1),
        ‖(u : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) * d (mixedNegativeRow s t i) *
          star (u : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) -
            d (canonicalNegativeRow t i)‖ < ε := by
  intro d s t
  let Q := NormUltra.QuotientAlgebra (fun _ : ℕ => E) U
  have hnorm : ‖(1 : Q)‖ = 1 := by
    change ‖NormUltra.QuotientAlgebra.mk U (DirectComparison.boundedDiagonal (1 : E))‖ = 1
    rw [NormUltra.QuotientAlgebra.norm_mk_eq_limsup]
    change Filter.limsup (fun _ : ℕ => ‖(1 : E)‖) (U : Filter ℕ) = 1
    rw [norm_one, Filter.limsup_const]
  let : Nontrivial Q := nontrivial_of_ne 0 1 (by
    intro he
    rw [← he, norm_zero] at hnorm
    exact zero_ne_one hnorm)
  obtain ⟨r, hr, hrf, hrg⟩ := exists_normUltrapower_factor_buffer U f g hfg
  let C := StarSubalgebra.centralizer ℂ (Set.range r)
  let : IsClosed (C : Set Q) := Set.isClosed_centralizer _
  let S : ℕ → C := fun i => ⟨d (s i), hrf (oInfinityIsometry i)⟩
  let T : ℕ → C := fun i => ⟨d (t i), hrg (oInfinityIsometry i)⟩
  have hrow (h : OInfinity →⋆ₐ[ℂ] E) (a : ℕ → C)
      (ha : ∀ i, (a i : Q) = d (h (oInfinityIsometry i))) :
      ∀ i j, star (a i) * a j = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      apply Subtype.ext
      change star (a i : Q) * (a j : Q) = 1
      rw [ha, ha, ← map_star, ← map_mul, ← map_star, ← map_mul,
        oInfinityIsometry_relations, ite_eq_left hij, map_one, map_one]
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (a i : Q) * (a j : Q) = 0
      rw [ha, ha, ← map_star, ← map_mul, ← map_star, ← map_mul,
        oInfinityIsometry_relations, ite_eq_right hij, map_zero, map_zero]
  have hS := hrow f S (fun _ => rfl)
  have hT := hrow g T (fun _ => rfl)
  obtain ⟨u, hu, hq, he⟩ := exists_mixedNegative_buffer_comparison r hr S T hS hT n ε hε
  refine ⟨u, hu, ?_, fun i => ?_⟩
  · simpa only [map_canonicalTailProjection] using hq
  · simpa only [map_mixedNegativeRow, map_canonicalNegativeRow] using he i

/-- Finite mixed comparison descends to a connected ambient unitary. The
corner is preserved to the requested tolerance; its complement is retained. -/
lemma exists_connected_mixedNegative_factor_comparison [Nontrivial E]
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]
    (f g : OInfinity →⋆ₐ[ℂ] E) (hfg : ∀ x y, Commute (f x) (g y))
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let s := fun i => f (oInfinityIsometry i)
    let t := fun i => g (oInfinityIsometry i)
    ∃ u : unitary E, Joined 1 u ∧
      ‖(u : E) * canonicalTailProjection t 1 * star (u : E) - canonicalTailProjection t 1‖ < ε ∧
      ∀ i : Fin (n + 1),
        ‖(u : E) * mixedNegativeRow s t i * star (u : E) - canonicalNegativeRow t i‖ < ε := by
  classical
  intro s t
  let q := canonicalTailProjection t 1
  let pair : Fin (n + 1) → E × E := fun i => (mixedNegativeRow s t i, canonicalNegativeRow t i)
  let F : Finset (E × E) := insert (q, q) (Finset.univ.image pair)
  obtain ⟨u, hu, hq, he⟩ := exists_mixedNegative_factor_ultrapower_comparison U f g hfg n ε hε
  have hall (p : E × E) (hp : p ∈ F) :
      ‖(u : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) *
        NormUltra.QuotientAlgebra.diagonalHom U p.1 *
        star (u : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) -
        NormUltra.QuotientAlgebra.diagonalHom U p.2‖ < ε := by
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst p
      change ‖(u : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) *
        NormUltra.QuotientAlgebra.diagonalHom U q *
        star (u : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) -
        NormUltra.QuotientAlgebra.diagonalHom U q‖ < ε
      rw [hq, sub_self, norm_zero]
      exact hε
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact he i
  obtain ⟨v, hv, hev⟩ := connected_finite_conjugacy_of_ultrapower U F u hu hall
  refine ⟨v, hv, hev (q, q) (Finset.mem_insert_self _ _), fun i => ?_⟩
  exact hev (pair i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

end WeakPureInfiniteness

end

end OAI
