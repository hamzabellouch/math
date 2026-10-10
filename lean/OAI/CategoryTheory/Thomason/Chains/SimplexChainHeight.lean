import OAI.CategoryTheory.Thomason.Gray.CylinderAssembly
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization

namespace OAI

section

/-! # Support separation for simplex cones

The old simplex basis and the coned basis have disjoint images: their last
vertices are respectively before, and equal to, the new final vertex.
Consequently taking positive or negative parts commutes with the two basis
embeddings and with sums across these two images.
-/

namespace Thomason.Construction.SimplexComplex

/-- Embed a basis simplex into the old face. -/
def prefixBasis {m p : ℕ} (s : Basis m p) : Basis (m + 1) p :=
  s.trans Fin.castSuccOrderEmb

/-- Append the new final vertex to a basis simplex. -/
def coneBasis {m p : ℕ} (s : Basis m p) : Basis (m + 1) (p + 1) :=
  OrderEmbedding.ofStrictMono
    (Fin.snoc (fun i => (s i).castSucc) (Fin.last (m + 1))) (by
      intro i j hij
      obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
        · simpa only [Fin.snoc_castSucc, Fin.castSucc_lt_castSucc_iff] using s.strictMono hij
        · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using Fin.castSucc_lt_last (s i)
      · exact (not_lt_of_ge (Fin.le_last _) hij).elim)

@[simp]
theorem coneBasis_castSucc {m p : ℕ} (s : Basis m p) (i : Fin (p + 1)) :
    coneBasis s i.castSucc = (s i).castSucc := by
  change Fin.snoc (α := fun _ => Fin (m + 2)) (fun j => (s j).castSucc) (Fin.last (m + 1)) i.castSucc = _
  simp

@[simp]
theorem coneBasis_last {m p : ℕ} (s : Basis m p) :
    coneBasis s (Fin.last (p + 1)) = Fin.last (m + 1) := by
  change Fin.snoc (α := fun _ => Fin (m + 2)) (fun j => (s j).castSucc) (Fin.last (m + 1)) (Fin.last (p + 1)) = _
  simp

/-- Both changes of basis are injective. -/
theorem prefixBasis_injective (m p : ℕ) : Function.Injective (@prefixBasis m p) := by
  intro s t he
  apply DFunLike.ext
  intro i
  exact Fin.castSucc_injective _ (congrArg (fun b : Basis (m + 1) p => b i) he)

theorem coneBasis_injective (m p : ℕ) : Function.Injective (@coneBasis m p) := by
  intro s t he
  apply DFunLike.ext
  intro i
  apply Fin.castSucc_injective
  exact (coneBasis_castSucc s i).symm.trans
    ((congrArg (fun b : Basis (m + 1) (p + 1) => b i.castSucc) he).trans
      (coneBasis_castSucc t i))

def prefixBasisEmbedding (m p : ℕ) : Basis m p ↪ Basis (m + 1) p :=
  ⟨prefixBasis, prefixBasis_injective m p⟩

def coneBasisEmbedding (m p : ℕ) : Basis m p ↪ Basis (m + 1) (p + 1) :=
  ⟨coneBasis, coneBasis_injective m p⟩

/-- The old-face chain map is precisely extension along the basis embedding. -/
theorem mapChains_coneInclusion {m p : ℕ} (x : Chains m p) :
    mapChains (coneInclusion m) p x = Finsupp.embDomain (prefixBasisEmbedding m p) x := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add s z x _ _ ih =>
    have hs : mapBasis (coneInclusion m) p s = Finsupp.single (prefixBasis s) 1 := by
      have hmono : StrictMono (fun i => coneInclusion m (s i)) := by
        intro i j hij
        exact s.strictMono hij
      rw [mapBasis, dite_eq_left hmono]
      rfl
    simp only [map_add, mapChains_single, hs, ih, Finsupp.embDomain_add,
      Finsupp.embDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl

/-- A cone prism is a single basis embedding, without cancellations. -/
theorem prismBasis_cone {m p : ℕ} (s : Basis m p) :
    prismBasis (coneInclusion m) (coneVertex m) (cone_le m) p s =
      Finsupp.single (coneBasis s) 1 := by
  have he : append ((coneInclusion m).comp s.toOrderHom)
      ((coneVertex m) (s (Fin.last p))) (cone_le m _) = (coneBasis s).toOrderHom := by
    apply DFunLike.ext
    intro i
    induction i using Fin.lastCases with
    | last => exact (append_last _ _ _).trans (coneBasis_last s).symm
    | cast i => exact (append_castSucc _ _ _ i).trans (coneBasis_castSucc s i).symm
  calc
    _ = tuple (append ((coneInclusion m).comp s.toOrderHom)
      ((coneVertex m) (s (Fin.last p))) (cone_le m _)) := rfl
    _ = tuple (coneBasis s).toOrderHom := congrArg tuple he
    _ = _ := by
      have hmono : StrictMono (fun i => (coneBasis s).toOrderHom (top (p + 1) i)) := by
        intro i j hij
        exact (coneBasis s).strictMono hij
      rw [tuple, mapBasis, dite_eq_left hmono]
      rfl

/-- The cone operator is extension along the coned-basis embedding. -/
theorem prism_cone {m p : ℕ} (x : Chains m p) :
    prism (coneInclusion m) (coneVertex m) (cone_le m) p x =
      Finsupp.embDomain (coneBasisEmbedding m p) x := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add s z x _ _ ih =>
    simp only [map_add, prism_single, prismBasis_cone, ih, Finsupp.embDomain_add,
      Finsupp.embDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl

/-- Positive and negative parts commute with embedding a chain in the old face. -/
theorem signedPart_prefix {m p : ℕ} (a : Bool) (x : Chains m p) :
    signedPart a (mapChains (coneInclusion m) p x) =
      mapChains (coneInclusion m) p (signedPart a x) := by
  rw [mapChains_coneInclusion, mapChains_coneInclusion]
  exact (Finsupp.embDomain_mapRange _ _ _ _).symm

/-- Positive and negative parts commute with coning a chain. -/
theorem signedPart_cone {m p : ℕ} (a : Bool) (x : Chains m p) :
    signedPart a (prism (coneInclusion m) (coneVertex m) (cone_le m) p x) =
      prism (coneInclusion m) (coneVertex m) (cone_le m) p (signedPart a x) := by
  rw [prism_cone, prism_cone]
  exact (Finsupp.embDomain_mapRange _ _ _ _).symm

/-- An old-face basis simplex cannot contain the new final vertex. -/
theorem prefixBasis_ne_coneBasis {m p : ℕ} (s : Basis m (p + 1)) (t : Basis m p) :
    prefixBasis s ≠ coneBasis t := by
  intro he
  have hl := congrArg (fun b : Basis (m + 1) (p + 1) => b (Fin.last (p + 1))) he
  change (s (Fin.last (p + 1))).castSucc = coneBasis t (Fin.last (p + 1)) at hl
  rw [coneBasis_last] at hl
  exact Fin.castSucc_ne_last _ hl

/-- The two chain operators have disjoint coefficient support. -/
theorem prefix_cone_disjoint {m p : ℕ} (x : Chains m (p + 1)) (y : Chains m p)
    (b : Basis (m + 1) (p + 1)) :
    mapChains (coneInclusion m) (p + 1) x b = 0 ∨
      prism (coneInclusion m) (coneVertex m) (cone_le m) p y b = 0 := by
  classical
  by_cases hb : b ∈ Set.range (prefixBasisEmbedding m (p + 1))
  · right
    obtain ⟨s, rfl⟩ := hb
    rw [prism_cone]
    apply Finsupp.embDomain_of_notMem_range
    rintro ⟨t, ht⟩
    exact prefixBasis_ne_coneBasis s t ht.symm
  · left
    rw [mapChains_coneInclusion]
    exact Finsupp.embDomain_of_notMem_range _ _ _ hb

/-- Disjoint supports allow positive and negative parts to distribute. -/
theorem signedPart_add_of_disjoint {m p : ℕ} (a : Bool) (x y : Chains m p)
    (hxy : ∀ b, x b = 0 ∨ y b = 0) :
    signedPart a (x + y) = signedPart a x + signedPart a y := by
  apply Finsupp.ext
  intro b
  rcases hxy b with hx | hy
  · simp [signedPart, hx]
  · simp [signedPart, hy]

end Thomason.Construction.SimplexComplex

end

section

/-! # Height bounds propagate through signed positive-chain boundaries

A negative coefficient in the boundary of a positive chain has a negative
incidence witness in its support, and similarly for a positive coefficient.
The explicit basis height therefore controls the iterated sides of atoms.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

theorem differential_coefficient_sum {m p : ℕ} (x : Chains m (p+1)) (b : Basis m p) :
    differential m p x b = ∑ c ∈ x.support, x c * differentialBasis m p c b := by
  simp only [differential, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

/-- Negative boundary support comes from a negative basis incidence. -/
theorem negative_boundary_witness {m p : ℕ} (x : Chains m (p+1))
    (hx : x ∈ positive m (p+1)) (b : Basis m p)
    (hb : differential m p x b < 0) :
    ∃ c ∈ x.support, differentialBasis m p c b < 0 := by
  classical
  by_contra hn
  have hs : 0 ≤ ∑ c ∈ x.support, x c * differentialBasis m p c b := by
    apply Finset.sum_nonneg
    intro c hc
    apply mul_nonneg (hx c)
    exact le_of_not_gt (fun h => hn ⟨c, hc, h⟩)
  rw [← differential_coefficient_sum] at hs
  omega

/-- Positive boundary support comes from a positive basis incidence. -/
theorem positive_boundary_witness {m p : ℕ} (x : Chains m (p+1))
    (hx : x ∈ positive m (p+1)) (b : Basis m p)
    (hb : 0 < differential m p x b) :
    ∃ c ∈ x.support, 0 < differentialBasis m p c b := by
  classical
  by_contra hn
  have hs : (∑ c ∈ x.support, x c * differentialBasis m p c b) ≤ 0 := by
    apply Finset.sum_nonpos
    intro c hc
    apply mul_nonpos_of_nonneg_of_nonpos (hx c)
    exact le_of_not_gt (fun h => hn ⟨c, hc, h⟩)
  rw [← differential_coefficient_sum] at hs
  omega

/-- Taking a negative signed boundary lowers all supporting basis heights. -/
theorem negative_part_height {m p : ℕ} (x : Chains m (p+1))
    (hx : x ∈ positive m (p+1)) (R : ℤ)
    (hr : ∀ c ∈ x.support, basisHeight c ≤ R) (b : Basis m p)
    (hb : b ∈ (signedPart false (differential m p x)).support) : basisHeight b < R := by
  have hcoeff : differential m p x b < 0 := by
    have hh := Finsupp.mem_support_iff.mp hb
    change max 0 (-differential m p x b) ≠ 0 at hh
    omega
  obtain ⟨c, hc, hcb⟩ := negative_boundary_witness x hx b hcoeff
  exact (negative_boundary_height c b hcb).trans_le (hr c hc)

/-- Taking a positive signed boundary raises all supporting basis heights. -/
theorem positive_part_height {m p : ℕ} (x : Chains m (p+1))
    (hx : x ∈ positive m (p+1)) (R : ℤ)
    (hr : ∀ c ∈ x.support, R ≤ basisHeight c) (b : Basis m p)
    (hb : b ∈ (signedPart true (differential m p x)).support) : R < basisHeight b := by
  have hcoeff : 0 < differential m p x b := by
    have hh := Finsupp.mem_support_iff.mp hb
    change max 0 (differential m p x b) ≠ 0 at hh
    omega
  obtain ⟨c, hc, hcb⟩ := positive_boundary_witness x hx b hcoeff
  exact (hr c hc).trans_lt (positive_boundary_height c b hcb)

/-- The two entire iterated sides of a basis atom remain on their specified
side of its height. -/
theorem basisAtom_side_bounds {h : NormalizedSimplexIdentities} {m p : ℕ}
    {b : Basis m p} {x : h.object m} (hx : IsBasisAtom h b x)
    (side : Bool) (n : ℕ) (hn : n ≤ p) (c : Basis m n) (hc : c ∈ (x.table side n).support) :
    if side then basisHeight b ≤ basisHeight c else basisHeight c ≤ basisHeight b := by
  induction hn using Nat.decreasingInduction with
  | self =>
    have he : c = b := by
      by_contra hne
      have hh := Finsupp.mem_support_iff.mp hc
      rw [hx.1 side, Finsupp.single_eq_of_ne hne] at hh
      exact hh rfl
    subst c
    cases side <;> exact le_rfl
  | of_succ k hk ih =>
    rw [hx.2.1 side k hk] at hc
    cases side with
    | false =>
      exact (negative_part_height (x.table false (k+1)) (x.positive false (k+1))
        (basisHeight b) ih c hc).le
    | true =>
      exact (positive_part_height (x.table true (k+1)) (x.positive true (k+1))
        (basisHeight b) ih c hc).le

/-- Below the atom's dimension the height inequalities are strict. -/
theorem basisAtom_side_height {h : NormalizedSimplexIdentities} {m p : ℕ}
    {b : Basis m p} {x : h.object m} (hx : IsBasisAtom h b x)
    (side : Bool) (n : ℕ) (hn : n < p) (c : Basis m n) (hc : c ∈ (x.table side n).support) :
    if side then basisHeight b < basisHeight c else basisHeight c < basisHeight b := by
  rw [hx.2.1 side n hn] at hc
  cases side with
  | false =>
    exact negative_part_height (x.table false (n+1)) (x.positive false (n+1))
      (basisHeight b) (fun c hc => basisAtom_side_bounds hx false (n+1) hn c hc) c hc
  | true =>
    exact positive_part_height (x.table true (n+1)) (x.positive true (n+1))
      (basisHeight b) (fun c hc => basisAtom_side_bounds hx true (n+1) hn c hc) c hc

/-- Increasingly ordered atoms have precisely the disjoint boundary supports
required by the positive binary splitting construction. -/
theorem ordered_basisAtoms_disjoint {h : NormalizedSimplexIdentities} {m p q r : ℕ}
    {a : Basis m p} {b : Basis m q} {A B : h.object m}
    (hA : IsBasisAtom h a A) (hB : IsBasisAtom h b B)
    (hp : r < p) (hq : r < q) (hab : basisHeight a ≤ basisHeight b) (c : Basis m r) :
    A.table false r c = 0 ∨ B.table true r c = 0 := by
  by_cases ha : A.table false r c = 0
  · exact Or.inl ha
  · right
    by_contra hb
    have hca := basisAtom_side_height hA false r hp c (Finsupp.mem_support_iff.mpr ha)
    have hbc := basisAtom_side_height hB true r hq c (Finsupp.mem_support_iff.mpr hb)
    exact (not_lt_of_ge hab) (hbc.trans hca)

end Thomason.Construction.SimplexComplex

end

end OAI
