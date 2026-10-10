import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Lattice.NodePolygon
import OAI.AlgebraicGeometry.Seshadri.Interpolation.LaurentJets

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
def nodeQuadrilateral (a b c : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(0, 0), (a, 0), (c, c), (0, b)}

def rowTriangle (a b c : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(-b, 0), (a, 0), (0, c)}

theorem mem_rowTriangle_of_inequalities (a b c q h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hh : 0 ≤ h)
    (hl : c * q + a * h ≤ a * c) (hr : -c * q + b * h ≤ b * c) :
    (q, h) ∈ rowTriangle a b c := by
  let D := c * (a + b)
  have hD : 0 < D := mul_pos hc (add_pos ha hb)
  let w : Fin 3 → ℝ := ![(a * c - a * h - c * q) / D,
    (b * c - b * h + c * q) / D, h / c]
  let z : Fin 3 → ℝ × ℝ := ![(-b, 0), (a, 0), (0, c)]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · exact div_nonneg (by linarith) hD.le
    · exact div_nonneg (by linarith) hD.le
    · exact div_nonneg hh hc.le
  have hsum : ∑ i : Fin 3, w i = 1 := by
    simp only [Fin.sum_univ_three]
    dsimp [w, D]
    field_simp
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)), z i ∈ rowTriangle a b c := by
    intro i _
    apply subset_convexHull ℝ _
    fin_cases i <;> simp [z]
  have hm := (convex_convexHull ℝ _).sum_mem hw hsum hz
  have heq : ∑ i : Fin 3, w i • z i = (q, h) := by
    simp only [Fin.sum_univ_three]
    apply Prod.ext <;> dsimp [w, z, D]
    · field_simp
      ring
    · field_simp
      ring
  rwa [heq] at hm

theorem nodeQuadrilateral_constraints (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b ≤ c * (a + b))
    (x y : ℝ) (h : (x, y) ∈ nodeQuadrilateral a b c) :
    0 ≤ x ∧ 0 ≤ y ∧ c * x + (a - c) * y ≤ a * c ∧
      (b - c) * x + c * y ≤ b * c := by
  have hx := planeForm_nonneg_on_hull 1 0 0
    {(0, 0), (a, 0), (c, c), (0, b)} (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [planeForm, ha.le, hc.le]) (x, y) h
  have hy := planeForm_nonneg_on_hull 0 1 0
    {(0, 0), (a, 0), (c, c), (0, b)} (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [planeForm, hb.le, hc.le]) (x, y) h
  have hl := planeForm_nonneg_on_hull (-c) (c - a) (a * c)
    {(0, 0), (a, 0), (c, c), (0, b)} (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> dsimp [planeForm] <;> nlinarith [mul_pos ha hc]) (x, y) h
  have hr := planeForm_nonneg_on_hull (c - b) (-c) (b * c)
    {(0, 0), (a, 0), (c, c), (0, b)} (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> dsimp [planeForm] <;> nlinarith [mul_pos hb hc]) (x, y) h
  dsimp [planeForm] at hx hy hl hr
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem diagonal_compress_mem (a b c x y h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b ≤ c * (a + b))
    (hxy : (x, y) ∈ nodeQuadrilateral a b c) (hh : 0 ≤ h) (hhx : h ≤ x) (hhy : h ≤ y) :
    (x - y, h) ∈ rowTriangle a b c := by
  obtain ⟨hx, hy, hl, hr⟩ := nodeQuadrilateral_constraints a b c ha hb hc hab x y hxy
  apply mem_rowTriangle_of_inequalities a b c (x - y) h ha hb hc hh
  · by_cases hq : y ≤ x
    · nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hhy)]
    · have hyx : x ≤ y := le_of_not_ge hq
      have hxc : x ≤ c := by
        by_contra hn
        have hx' : c < x := lt_of_not_ge hn
        nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hyx), mul_pos hb (sub_pos.mpr hx')]
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr (hhx.trans hxc)),
        mul_nonneg hc.le (sub_nonneg.mpr hyx)]
  · by_cases hq : x ≤ y
    · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hhx)]
    · have hyx : y ≤ x := le_of_not_ge hq
      have hyc : y ≤ c := by
        by_contra hn
        have hy' : c < y := lt_of_not_ge hn
        nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hyx), mul_pos ha (sub_pos.mpr hy')]
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr (hhy.trans hyc)),
        mul_nonneg hc.le (sub_nonneg.mpr hyx)]

def diagonalIndex (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2

noncomputable def diagonalRows (s : Finset (ℕ × ℕ)) : Finset ℤ := s.image diagonalIndex

noncomputable def diagonalRow (s : Finset (ℕ × ℕ)) (q : ℤ) : Finset (ℕ × ℕ) :=
  s.filter (fun p => diagonalIndex p = q)

noncomputable def rowStart (q : ℤ) : ℕ := (-q).toNat

noncomputable def rowHeight (s : Finset (ℕ × ℕ)) (q : ℤ) : ℕ :=
  (diagonalRow s q).sup (fun p => min p.1 p.2)

theorem diagonalRow_nonempty (s : Finset (ℕ × ℕ)) (q : diagonalRows s) :
    (diagonalRow s q).Nonempty := by
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp q.property
  exact ⟨p, Finset.mem_filter.mpr ⟨hp, he⟩⟩

theorem rowStart_add_min (p : ℕ × ℕ) :
    rowStart (diagonalIndex p) + min p.1 p.2 = p.2 := by
  simp only [rowStart, diagonalIndex]
  omega

noncomputable def rowEmbedding (s : Finset (ℕ × ℕ)) (p : s) :
    RowIndex (fun q : diagonalRows s => rowHeight s q) :=
  ⟨⟨diagonalIndex p, Finset.mem_image.mpr ⟨p, p.property, rfl⟩⟩,
    ⟨min p.val.1 p.val.2, Nat.lt_succ_of_le (by
      change min p.val.1 p.val.2 ≤ (diagonalRow s (diagonalIndex p.val)).sup _
      exact Finset.le_sup (f := fun t : ℕ × ℕ => min t.1 t.2)
        (b := p.val) (Finset.mem_filter.mpr ⟨p.property, rfl⟩))⟩⟩

theorem rowEmbedding_second (s : Finset (ℕ × ℕ)) (p : s) :
    rowStart (rowEmbedding s p).1 + ((rowEmbedding s p).2 : ℕ) = p.val.2 :=
  rowStart_add_min p

theorem rowEmbedding_first (s : Finset (ℕ × ℕ)) (p : s) :
    ((rowEmbedding s p).1 : ℤ) +
      ((rowStart (rowEmbedding s p).1 + ((rowEmbedding s p).2 : ℕ) : ℕ) : ℤ) = p.val.1 := by
  rw [rowEmbedding_second]
  change (p.val.1 : ℤ) - p.val.2 + p.val.2 = p.val.1
  omega

theorem rowEmbedding_injective (s : Finset (ℕ × ℕ)) : Function.Injective (rowEmbedding s) := by
  intro p p' h
  have hq := congrArg (fun i : RowIndex (fun q : diagonalRows s => rowHeight s q) => (i.1 : ℤ)) h
  have he := congrArg (fun i : RowIndex (fun q : diagonalRows s => rowHeight s q) =>
    rowStart i.1 + (i.2 : ℕ)) h
  rw [rowEmbedding_second, rowEmbedding_second] at he
  apply Subtype.ext
  apply Prod.ext
  · change (p.val.1 : ℤ) - p.val.2 = (p'.val.1 : ℤ) - p'.val.2 at hq
    omega
  · exact he

theorem rowEnvelope_dominated (s : Finset (ℕ × ℕ))
    (i : RowIndex (fun q : diagonalRows s => rowHeight s q)) :
    ∃ p ∈ s, diagonalIndex p = i.1 ∧ (i.2 : ℕ) ≤ min p.1 p.2 := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup (diagonalRow s i.1) (diagonalRow_nonempty s i.1)
    (fun p => min p.1 p.2)
  have hle : (i.2 : ℕ) ≤ rowHeight s i.1 := Nat.le_of_lt_succ i.2.isLt
  refine ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2, ?_⟩
  exact he ▸ hle

theorem compressed_row_exponent_injective {Q : Type*} (q : Q → ℤ)
    (hq : Function.Injective q) (n : Q → ℕ) :
    Function.Injective (fun i : RowIndex n => (q i.1, ((i.2 : ℕ) : ℤ))) := by
  intro i j h
  have hq' : i.1 = j.1 := hq (congrArg Prod.fst h)
  obtain ⟨i, a⟩ := i
  obtain ⟨j, b⟩ := j
  dsimp at hq'
  subst j
  have he : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := congrArg Prod.snd h
  have hh : a = b := Fin.ext (by exact_mod_cast he)
  subst b
  rfl

theorem rowEnvelope_mem_triangle (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b ≤ c * (a + b))
    (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ nodeQuadrilateral a b c)
    (i : RowIndex (fun q : diagonalRows s => rowHeight s q)) :
    (((i.1 : ℤ) : ℝ), ((i.2 : ℕ) : ℝ)) ∈ rowTriangle a b c := by
  obtain ⟨p, hp, hq, hh⟩ := rowEnvelope_dominated s i
  have hx : ((i.2 : ℕ) : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast hh.trans (min_le_left _ _)
  have hy : ((i.2 : ℕ) : ℝ) ≤ (p.2 : ℝ) := by
    exact_mod_cast hh.trans (min_le_right _ _)
  have he : (((i.1 : ℤ) : ℝ)) = (p.1 : ℝ) - p.2 := by
    rw [← hq]
    simp only [diagonalIndex, Int.cast_sub, Int.cast_natCast]
  rw [he]
  exact diagonal_compress_mem a b c _ _ _ ha hb hc hab (hs p hp) (Nat.cast_nonneg _) hx hy

theorem quadrilateral_jet_rank_of_triangle_test (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b ≤ c * (a + b))
    (r m : ℕ) (points : Fin r → ℂ × ℂ) (hi : Function.Injective points)
    (hnz : ∀ l, (points l).1 ≠ 0 ∧ (points l).2 ≠ 0)
    (htest : ∀ s : Finset (ℤ × ℤ), s.Nonempty →
      (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ rowTriangle a b c) →
      ∀ d : ℤ × ℤ → ℂ, (∀ p ∈ s, d p ≠ 0) →
        ∃ l : Fin r, ¬ MixedJetZero (laurentEval s d) (points l).1 (points l).2 m)
    (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ nodeQuadrilateral a b c) :
    ∃ p : Fin r → ℂ × ℂ, Function.Injective p ∧
      (∀ i, (p i).1 ≠ 0 ∧ (p i).2 ≠ 0) ∧
      LinearIndependent ℂ (fun e : s => finiteJetColumn r m p
        (fun x z => x ^ e.val.1 * z ^ e.val.2)) := by
  classical
  let q : diagonalRows s → ℤ := Subtype.val
  let n : diagonalRows s → ℕ := fun q => rowHeight s q
  have h₀ : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * z ^ (i.2 : ℕ))) := by
    have he := compressed_row_exponent_injective q Subtype.val_injective n
    have hh := monomial_jet_rank_of_test (rowTriangle a b c) r m points hnz htest
      (fun i : RowIndex n => (q i.1, ((i.2 : ℕ) : ℤ))) he
      (by simpa only [Int.cast_natCast] using rowEnvelope_mem_triangle a b c ha hb hc hab s hs)
    simpa only [zpow_natCast] using hh
  obtain ⟨p, hpi, hpn, hp⟩ := diagonal_row_compression q (fun q => rowStart q) n
    r m points hi (fun l => (hnz l).1) h₀
  refine ⟨p, hpi, hpn, ?_⟩
  have hres := hp.comp (rowEmbedding s) (rowEmbedding_injective s)
  convert hres using 1
  funext e
  congr 1
  funext x z
  dsimp only [q]
  rw [rowEmbedding_first, rowEmbedding_second, zpow_natCast]

open scoped BigOperators Topology
open Filter Set


end MaximalSeshadri.Interpolation
end

end OAI
