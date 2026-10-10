import OAI.AlgebraicGeometry.PlaneCurves.CoefficientBlocks
import OAI.AlgebraicGeometry.PlaneCurves.LineGeometry

namespace OAI

/-!
# Integer and complex rows, slices, and exponent interpolation; Ordered integer rows of finite sets
-/

section

namespace Nagata.W29

def rowPositions (S : Finset (ℤ × ℤ)) (K : ℤ) : Finset ℤ :=
  (S.image Prod.fst).filter fun j => (j, K) ∈ S

def rowHeights (S : Finset (ℤ × ℤ)) : Finset ℤ := S.image Prod.snd

def largeRows (S : Finset (ℤ × ℤ)) (t : ℕ) : Finset ℤ :=
  (rowHeights S).filter fun K => t ≤ (rowPositions S K).card

@[simp] theorem mem_rowPositions (S : Finset (ℤ × ℤ)) (j K : ℤ) :
    j ∈ rowPositions S K ↔ (j, K) ∈ S := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(j, K), h, rfl⟩, h⟩

theorem rowPositions_eq_empty_of_not_mem (S : Finset (ℤ × ℤ)) (K : ℤ)
    (hK : K ∉ rowHeights S) : rowPositions S K = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply hK
  exact Finset.mem_image.mpr ⟨(j, K), (mem_rowPositions S j K).mp hj, rfl⟩

/-- Positive threshold rows automatically have a represented height. This
identifies the finite filter with the manuscript's quantification over all ℤ. -/
@[simp] theorem mem_largeRows (S : Finset (ℤ × ℤ)) (t : ℕ) (ht : 1 ≤ t)
    (K : ℤ) : K ∈ largeRows S t ↔ t ≤ (rowPositions S K).card := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hn : (rowPositions S K).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j, hj⟩ := hn
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr
      ⟨(j, K), (mem_rowPositions S j K).mp hj, rfl⟩, h⟩

/-- A slice of width at most `m λ < m` contains at most `m` integer positions. -/
theorem row_card_le (S : Finset (ℤ × ℤ)) (m : ℕ) (lam : ℝ)
    (hm : 0 < m) (hlam : lam < 1) (lo hi : ℤ → ℝ)
    (hinterval : ∀ K ∈ rowHeights S, lo K ≤ hi K)
    (hcontain : ∀ K, ∀ j ∈ rowPositions S K,
      lo K ≤ (j : ℝ) ∧ (j : ℝ) ≤ hi K)
    (hwidth : ∀ K ∈ rowHeights S, hi K - lo K ≤ (m : ℝ) * lam)
    (K : ℤ) : (rowPositions S K).card ≤ m := by
  by_cases hK : K ∈ rowHeights S
  · apply Nagata.W02.card_le_of_interval_length_lt (rowPositions S K)
      (lo K) (hi K) m (hinterval K hK) (hcontain K)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    nlinarith [hwidth K hK, mul_lt_mul_of_pos_left hlam hmR]
  · rw [rowPositions_eq_empty_of_not_mem S K hK]
    simp

/-- The spare endpoint in the lattice count is absorbed by `q(1-λ)m ≥ 1`. -/
theorem largeRows_card_le (S : Finset (ℤ × ℤ)) (q m : ℕ)
    (lam U A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : A + B = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (lo hi : ℤ → ℝ)
    (hinterval : ∀ K ∈ rowHeights S, lo K ≤ hi K)
    (hcontain : ∀ K, ∀ j ∈ rowPositions S K,
      lo K ≤ (j : ℝ) ∧ (j : ℝ) ≤ hi K)
    (hwidth : ∀ K ∈ rowHeights S, hi K - lo K ≤ (m : ℝ) * lam)
    (hprofile : ∀ s : ℝ, 0 ≤ s → s ≤ (m : ℝ) * lam →
      ∀ K ∈ rowHeights S, s ≤ hi K - lo K →
        U - A * ((m : ℝ) * lam - s) ≤ (K : ℝ) ∧
        (K : ℝ) ≤ U + B * ((m : ℝ) * lam - s))
    (t : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) :
    (largeRows S t).card ≤ q * (m - t + 1) := by
  have hforce : ∀ K ∈ largeRows S t, (t : ℝ) - 1 ≤ hi K - lo K := by
    intro K hK
    obtain ⟨hKr, hKt⟩ := Finset.mem_filter.mp hK
    exact Nagata.W02.sub_one_le_interval_length (rowPositions S K)
      (lo K) (hi K) t (hinterval K hKr) (hcontain K) hKt
  by_cases hfit : (t : ℝ) - 1 ≤ (m : ℝ) * lam
  · have hnonneg : 0 ≤ (m : ℝ) * lam - ((t : ℝ) - 1) := by linarith
    have hintervalH : U - A * ((m : ℝ) * lam - ((t : ℝ) - 1)) ≤
        U + B * ((m : ℝ) * lam - ((t : ℝ) - 1)) := by
      nlinarith [mul_nonneg hA hnonneg, mul_nonneg hB hnonneg]
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hcount := Nagata.W02.card_le_interval_length_add_one (largeRows S t)
      (U - A * ((m : ℝ) * lam - ((t : ℝ) - 1)))
      (U + B * ((m : ℝ) * lam - ((t : ℝ) - 1))) hintervalH
      (by
        intro K hK
        exact hprofile ((t : ℝ) - 1) (by linarith) hfit K
          (Finset.mem_filter.mp hK).1 (hforce K hK))
    have hlength :
        (U + B * ((m : ℝ) * lam - ((t : ℝ) - 1))) -
        (U - A * ((m : ℝ) * lam - ((t : ℝ) - 1))) =
        (q : ℝ) * ((m : ℝ) * lam - (t : ℝ) + 1) := by
      rw [← hAB]
      ring
    rw [hlength] at hcount
    have hcast : ((q * (m - t + 1) : ℕ) : ℝ) =
        (q : ℝ) * ((m : ℝ) - (t : ℝ) + 1) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub htm, Nat.cast_one]
    have hfinal : ((largeRows S t).card : ℝ) ≤ ((q * (m - t + 1) : ℕ) : ℝ) := by
      rw [hcast]
      nlinarith
    exact_mod_cast hfinal
  · have hempty : largeRows S t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro K hK
      have hw := hwidth K (Finset.mem_filter.mp hK).1
      have hf := hforce K hK
      exact hfit (hf.trans hw)
    rw [hempty]
    simp

end Nagata.W29

end

section

/-! Integer row inequalities for actual finite lattice subsets of the manuscript
polygon. This supplies the slice-to-count bridge in Lemma `integer-rows`. -/
namespace Nagata.W29

/-- Both integer-row estimates for a finite set enclosed in the translated
polygon. `a` is the manuscript's `ρ_*`; its defining numerical identity is the
explicit hypothesis `hcoef`. No row-count hypothesis occurs. -/
theorem integer_rows_of_polygon (S : Finset (ℤ × ℤ)) (q m : ℕ)
    (a lam U : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (hpolygon : ∀ p ∈ S,
      Nagata.W04.InPolygon a ((m : ℝ) * lam) (p.1 : ℝ) ((p.2 : ℝ) - U)) :
    (∀ K : ℤ, (rowPositions S K).card ≤ m) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ m → (largeRows S t).card ≤ q * (m - t + 1)) := by
  let scale : ℝ := (m : ℝ) * lam
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hscale : 0 < scale := mul_pos hmR hlam
  let lo : ℤ → ℝ := fun K =>
    scale * Nagata.W04.SliceLower a (((K : ℝ) - U) / scale)
  let hi : ℤ → ℝ := fun K =>
    scale * Nagata.W04.SliceUpper a (((K : ℝ) - U) / scale)
  have hcontain : ∀ K, ∀ j ∈ rowPositions S K,
      lo K ≤ (j : ℝ) ∧ (j : ℝ) ≤ hi K := by
    intro K j hj
    exact (Nagata.W04.scaled_slice_interval a scale U j K ha hscale).mp
      (hpolygon (j, K) ((mem_rowPositions S j K).mp hj))
  have hinterval : ∀ K ∈ rowHeights S, lo K ≤ hi K := by
    intro K hK
    obtain ⟨⟨j, k⟩, hp, hpK⟩ := Finset.mem_image.mp hK
    change k = K at hpK
    subst k
    have hr : j ∈ rowPositions S K := (mem_rowPositions S j K).mpr hp
    exact (hcontain K j hr).1.trans (hcontain K j hr).2
  have hwidth_id (K : ℤ) : hi K - lo K =
      Nagata.W04.ScaledSliceWidth a scale U K :=
    Nagata.W04.scaled_slice_width a scale U K ha
  have hwidth : ∀ K ∈ rowHeights S, hi K - lo K ≤ (m : ℝ) * lam := by
    intro K _
    rw [hwidth_id]
    exact Nagata.W04.scaled_width_le_scale a scale U K ha (le_of_lt hscale)
  constructor
  · exact row_card_le S m lam hm hlam1 lo hi hinterval hcontain hwidth
  · intro t ht htm
    apply largeRows_card_le S q m lam U (a * (1 + a / 9)) a
      (by positivity) (le_of_lt ha) (by nlinarith [hcoef]) hmargin
      lo hi hinterval hcontain hwidth ?_ t ht htm
    intro s hs hsu K _ hsw
    apply (Nagata.W04.scaled_width_threshold a scale U K s ha hscale hs hsu).mp
    rwa [hwidth_id] at hsw

end Nagata.W29

end

section

/-! The integer-to-complex bridge preserves the actual finite row cardinalities.
This makes the integer-row estimates applicable to complex polynomial interpolation. -/
noncomputable section
namespace Nagata.W29

/-- Coordinatewise standard inclusion ℤ² → ℂ². -/
def complexPoint (p : ℤ × ℤ) : ℂ × ℂ := ((p.1 : ℂ), (p.2 : ℂ))

def complexSet (S : Finset (ℤ × ℤ)) : Finset (ℂ × ℂ) := by
  classical
  exact S.image complexPoint

theorem complexPoint_injective : Function.Injective complexPoint := by
  intro p q hpq
  apply Prod.ext
  · have h := congrArg Prod.fst hpq
    change (p.1 : ℂ) = (q.1 : ℂ) at h
    exact_mod_cast h
  · have h := congrArg Prod.snd hpq
    change (p.2 : ℂ) = (q.2 : ℂ) at h
    exact_mod_cast h

/-- The standard inclusion preserves the entire finite column count. -/
theorem complexSet_card (S : Finset (ℤ × ℤ)) : (complexSet S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S complexPoint_injective

/-- Actual exponent columns and their complex-image columns are equivalent. -/
def complexColumnEquiv (S : Finset (ℤ × ℤ)) : S ≃ complexSet S := by
  classical
  let f : S → complexSet S := fun p =>
    ⟨complexPoint p.val, Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    apply Subtype.ext
    exact complexPoint_injective (congrArg Subtype.val hpq)
  · intro z
    obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨p, hp⟩, Subtype.ext hpz⟩

@[simp] theorem complexColumnEquiv_val (S : Finset (ℤ × ℤ)) (p : S) :
    (complexColumnEquiv S p).val = complexPoint p.val := rfl

theorem rowHeights_complexSet (S : Finset (ℤ × ℤ)) :
    Nagata.Workers.W10.rowHeights (complexSet S) =
      (rowHeights S).image (fun K : ℤ => (K : ℂ)) := by
  classical
  simp only [Nagata.Workers.W10.rowHeights, complexSet, rowHeights,
    Finset.image_image, Function.comp_def, complexPoint]

theorem rowXs_complexSet (S : Finset (ℤ × ℤ)) (K : ℤ) :
    Nagata.Workers.W10.rowXs (complexSet S) (K : ℂ) =
      (rowPositions S K).image (fun j : ℤ => (j : ℂ)) := by
  classical
  ext z
  constructor
  · intro hz
    have hp := Nagata.Workers.W10.mem_rowXs.mp hz
    obtain ⟨⟨j, k⟩, hjk, heq⟩ := Finset.mem_image.mp hp
    have hkC := congrArg Prod.snd heq
    change (k : ℂ) = (K : ℂ) at hkC
    have hk : k = K := by exact_mod_cast hkC
    subst k
    exact Finset.mem_image.mpr
      ⟨j, (mem_rowPositions S j K).mpr hjk, congrArg Prod.fst heq⟩
  · intro hz
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hz
    apply Nagata.Workers.W10.mem_rowXs.mpr
    exact Finset.mem_image.mpr
      ⟨(j, K), (mem_rowPositions S j K).mp hj, Prod.ext hjz rfl⟩

theorem row_card_complexSet (S : Finset (ℤ × ℤ)) (K : ℤ) :
    (Nagata.Workers.W10.rowXs (complexSet S) (K : ℂ)).card =
      (rowPositions S K).card := by
  classical
  rw [rowXs_complexSet]
  exact Finset.card_image_of_injective _ Int.cast_injective

/-- The threshold distributions agree, including threshold zero when restricted
to represented heights as in both finite-set definitions. -/
theorem distribution_card_complexSet (S : Finset (ℤ × ℤ)) (t : ℕ) :
    ((Nagata.Workers.W10.rowHeights (complexSet S)).filter
      fun K => t ≤ (Nagata.Workers.W10.rowXs (complexSet S) K).card).card =
    (largeRows S t).card := by
  classical
  symm
  apply Finset.card_bij (fun (K : ℤ) _ => (K : ℂ))
  · intro K hK
    obtain ⟨hheight, hcard⟩ := Finset.mem_filter.mp hK
    apply Finset.mem_filter.mpr
    constructor
    · rw [rowHeights_complexSet]
      exact Finset.mem_image.mpr ⟨K, hheight, rfl⟩
    · simpa only [row_card_complexSet] using hcard
  · intro K _ L _ heq
    exact_mod_cast heq
  · intro z hz
    obtain ⟨hzheight, hzcard⟩ := Finset.mem_filter.mp hz
    rw [rowHeights_complexSet] at hzheight
    obtain ⟨K, hK, hKz⟩ := Finset.mem_image.mp hzheight
    subst z
    refine ⟨K, Finset.mem_filter.mpr ⟨hK, ?_⟩, rfl⟩
    simpa only [row_card_complexSet] using hzcard

end Nagata.W29

end
end

section

/-! Arithmetic exponent enclosure to the finite integer-row estimates. The
geometric origin of the finite exponent set is not assumed or asserted. -/
namespace Nagata.W29

/-- Positive dilation of the actual enclosing polygon, retaining arbitrary λ. -/
theorem polygon_dilation (a lam c x y : ℝ) (hc : 0 < c) :
    Nagata.W04.InPolygon a (c * lam) (c * x) (c * y) ↔
      Nagata.W04.InPolygon a lam x y :=
  Nagata.W04.polygon_dilation a lam c x y hc

/-- Any finite set satisfying the explicit exponent interval conditions obeys
both manuscript row estimates. This is independent of the analytic/geometric
claim that those intervals index a basis of the required section space. -/
theorem integer_rows_of_raw_exponents (S : Finset (ℤ × ℤ)) (q m : ℕ)
    (d h rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hdegree : h = 3 * (d - 3 * (m : ℝ))) (hratio : h = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (hexponent : ∀ p ∈ S, Nagata.ExponentEnclosure.rawExponent
      d (m : ℝ) h a delta (p.1 : ℝ) (p.2 : ℝ)) :
    (∀ K : ℤ, (rowPositions S K).card ≤ m) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ m → (largeRows S t).card ≤ q * (m - t + 1)) := by
  apply integer_rows_of_polygon S q m a lam
    (h / 9 * (a - delta) + (m : ℝ) * a) ha hm hlam hlam1 hcoef hmargin
  intro p hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnormalized := Nagata.ExponentEnclosure.integer_exponent_enclosure
    hmR hrho hdelta hlam1.le hdegree hratio hslack (hexponent p hp)
  change Nagata.W04.InPolygon a lam ((p.1 : ℝ) / m)
    (((p.2 : ℝ) - (h / 9 * (a - delta) + (m : ℝ) * a)) / m) at hnormalized
  have hd := (polygon_dilation a lam (m : ℝ) ((p.1 : ℝ) / m)
    (((p.2 : ℝ) - (h / 9 * (a - delta) + (m : ℝ) * a)) / m) hmR).mpr hnormalized
  simpa only [mul_div_cancel₀ _ (ne_of_gt hmR)] using hd

end Nagata.W29

end

section

/-!
# Genuine finite subsets of the affine plane

Finite-set formulation of manuscript Section 4, Lemma `lem:interpolation`.
Rows are extracted from the actual second coordinates; their first coordinates
are exactly those occurring in the finite set.
-/
noncomputable section
namespace Nagata.Workers.W10
open Nagata.W01

/-- Interpolation of plane-valued data on a genuine finite plane set. -/
theorem interpolate_finset_plane_data (q m : ℕ) (S : Finset Plane)
    (hsize : ∀ K ∈ rowHeights S, (rowXs S K).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      ((rowHeights S).filter fun K => t ≤ (rowXs S K).card).card ≤ q * (m - t + 1))
    (v : Plane → ℂ) :
    ∃ p ∈ polynomialSpace q m, ∀ z ∈ S, planeEval p z = v z := by
  classical
  let e : Fin (rowHeights S).card ≃ rowHeights S := (rowHeights S).equivFin.symm
  let K : Fin (rowHeights S).card → ℂ := fun i => (e i).val
  let xs : Fin (rowHeights S).card → Finset ℂ := fun i => rowXs S (K i)
  have hK : Function.Injective K := fun i j h => e.injective (Subtype.ext h)
  have hpos : ∀ i, 1 ≤ (xs i).card := fun i =>
    Finset.card_pos.mpr (rowXs_nonempty (e i).property)
  have hcard : ∀ i, (xs i).card ≤ m := fun i => hsize (K i) (e i).property
  have hdist : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun i => t ≤ (xs i).card).card ≤ q * (m - t + 1) := by
    intro t ht htm
    change (Finset.univ.filter fun i => t ≤ (rowXs S (e i).val).card).card ≤ _
    rw [row_distribution_card S e t]
    exact hdistribution t ht htm
  obtain ⟨p, hp, hv⟩ := interpolate_distributed_rows_polynomial q m (rowHeights S).card
    K xs hK hpos hcard hdist v
  refine ⟨p, hp, ?_⟩
  intro z hz
  let k : rowHeights S := ⟨z.2, snd_mem_rowHeights hz⟩
  have he : K (e.symm k) = z.2 := congrArg Subtype.val (e.apply_symm_apply k)
  have hx : z.1 ∈ xs (e.symm k) := by
    change z.1 ∈ rowXs S (K (e.symm k))
    rw [he]
    exact mem_rowXs.mpr (by simpa only [Prod.eta] using hz)
  simpa only [he, Prod.eta] using hv (e.symm k) z.1 hx

/-- Every function on the actual finite set has a permitted polynomial extension. -/
theorem interpolate_finset_polynomial (q m : ℕ) (S : Finset Plane)
    (hsize : ∀ K ∈ rowHeights S, (rowXs S K).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      ((rowHeights S).filter fun K => t ≤ (rowXs S K).card).card ≤ q * (m - t + 1))
    (v : S → ℂ) :
    ∃ p ∈ polynomialSpace q m, ∀ z : S, planeEval p z.val = v z := by
  classical
  let v' : Plane → ℂ := fun z => if hz : z ∈ S then v ⟨z, hz⟩ else 0
  obtain ⟨p, hp, hv⟩ := interpolate_finset_plane_data q m S hsize hdistribution v'
  refine ⟨p, hp, ?_⟩
  intro z
  simpa only [v', dite_eq_left z.property] using hv z.val z.property

end Nagata.Workers.W10

end
end

section

namespace Nagata.W29

theorem finite_exponent_rows (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m) :
    let S := Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta
    (∀ K : ℤ, (rowPositions S K).card ≤ m) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ m → (largeRows S t).card ≤ q * (m - t + 1)) := by
  dsimp only
  apply integer_rows_of_raw_exponents
    (Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta) q m
    (d : ℝ) (3 * ((d : ℝ) - 3 * (m : ℝ))) rho a delta lam
    ha hm hrho hdelta hlam hlam1 rfl hratio hslack hcoef hmargin
  intro p hp
  have hraw := Nagata.FiniteExponents.mem_exponentSet_iff_raw.mp hp
  simpa only [Int.cast_natCast] using hraw

end Nagata.W29

end

section

noncomputable section
namespace Nagata.W29

/-- Genuine integer-point row bounds imply interpolation after the standard
coordinatewise inclusion in the complex affine plane. -/
theorem interpolate_integer_finset (q m : ℕ) (S : Finset (ℤ × ℤ))
    (hsize : ∀ K, (rowPositions S K).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (largeRows S t).card ≤ q * (m - t + 1))
    (v : complexSet S → ℂ) :
    ∃ p ∈ Nagata.W01.polynomialSpace q m,
      ∀ z : complexSet S, Nagata.W01.planeEval p z.val = v z := by
  classical
  apply Nagata.Workers.W10.interpolate_finset_polynomial q m (complexSet S) ?_ ?_ v
  · intro z hz
    rw [rowHeights_complexSet] at hz
    obtain ⟨K, _, hKz⟩ := Finset.mem_image.mp hz
    subst z
    simpa only [row_card_complexSet] using hsize K
  · intro t ht htm
    rw [distribution_card_complexSet]
    exact hdistribution t ht htm

end Nagata.W29

end
end

section

/-! Conversion from the source point exponents x_i to the actual scalar-product
arguments a_i=x₀−x_i, with x₀=1/2. -/
namespace Nagata.W29
open scoped BigOperators

/-- The exponents in Θ(τ^(x₀−x_i)e^x), not the point exponents x_i themselves. -/
noncomputable def sourceOffsets (x : Fin 9 → ℝ) : Fin 9 → ℝ := fun i => 1 / 2 - x i

theorem sourceOffsets_injective (x : Fin 9 → ℝ) (hx : Function.Injective x) :
    Function.Injective (sourceOffsets x) := by
  intro i j hij
  apply hx
  dsimp [sourceOffsets] at hij
  linarith

theorem sourceOffsets_bounds (x : Fin 9 → ℝ)
    (hx : ∀ i, 0 < x i ∧ x i < 1 / 2) :
    ∀ i, 0 < sourceOffsets x i ∧ sourceOffsets x i < 1 / 2 := by
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  dsimp [sourceOffsets]
  constructor <;> linarith

theorem sourceOffsets_sum (x : Fin 9 → ℝ) (delta : ℝ)
    (hsum : (∑ i : Fin 9, (1 / 2 - x i)) = delta) :
    (∑ i : Fin 9, sourceOffsets x i) = delta := hsum

end Nagata.W29

end

section

/-! Integer-row estimates and actual complex polynomial interpolation for the
finite exponent set defined by the manuscript's three explicit integer unions.
This finite result does not assert the geometric section-space identification. -/
noncomputable section
namespace Nagata.W29

/-- Section 4's interpolation conclusion on the actual finite integer exponent
set, viewed through the usual embedding in ℂ². All parameter hypotheses remain
explicit, and no geometric jet-space hypothesis is hidden in the statement. -/
theorem finite_exponent_interpolation (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (v : complexSet (Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta) → ℂ) :
    ∃ p ∈ Nagata.W01.polynomialSpace q m,
      ∀ z : complexSet (Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta),
        Nagata.W01.planeEval p z.val = v z := by
  have hrows := finite_exponent_rows d q m rho a delta lam ha hm hrho hdelta
    hlam hlam1 hratio hslack hcoef hmargin
  exact interpolate_integer_finset q m
    (Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta) hrows.1 hrows.2 v

end Nagata.W29

end
end

section

/-! Both nonzero-partial branches realize arbitrary normal displacements for
the actual two-variable polynomial equation. No preferred partial is required. -/
noncomputable section
namespace Nagata.W29
open Nagata.Workers.W28

theorem affinePolynomialGradient_surjective (G : MvPolynomial (Fin 2) ℂ)
    (p : ComplexPlane)
    (hgradient : planePolynomialEval (MvPolynomial.pderiv 0 G) p ≠ 0 ∨
      planePolynomialEval (MvPolynomial.pderiv 1 G) p ≠ 0) :
    Function.Surjective (polynomialGradient G p) := by
  apply Nagata.Workers.W14.nonzero_linearFunctional_surjective
    (polynomialGradient G p).toLinearMap
  intro hz
  rcases hgradient with h0 | h1
  · have h := LinearMap.congr_fun hz (1, 0)
    apply h0
    simpa [polynomialGradient] using h
  · have h := LinearMap.congr_fun hz (0, 1)
    apply h1
    simpa [polynomialGradient] using h

end Nagata.W29

end
end

end OAI
