import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import OAI.Computability.UniqueGames.Quadratic.Block

namespace OAI

section

/-!
The spanning clause of Lemma `latent-block`.  Three coordinate lines
already suffice.  Horizontal coordinate vectors lie in their own block;
vertical coordinate vectors lie in either of the other two blocks.
-/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F]

/-- The three standard coordinate vectors of the quadratic block. -/
def basisCoord (i : Fin 3) : Vec F := Pi.single i 1

theorem basisCoord_ne_zero (i : Fin 3) : (basisCoord i : Vec F) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [basisCoord] at hi

@[simp] theorem Q_smul_basisCoord (t : F) (i : Fin 3) :
    Q (t • (basisCoord i : Vec F)) = 0 := by
  ext k
  fin_cases i <;> fin_cases k <;> simp [Q, basisCoord]

theorem dot_smul_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    dot (basisCoord j : Vec F) (t • (basisCoord i : Vec F)) = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [dot, basisCoord]

/-- The explicit coordinate decomposition, over the field rather than only
over the binary scalars of the block spaces. -/
theorem basisCoord_decomposition (x : Vec F) :
    x = x 0 • basisCoord 0 + x 1 • basisCoord 1 + x 2 • basisCoord 2 := by
  ext i
  fin_cases i <;> simp [basisCoord]

variable [CharP F 2] [Algebra (ZMod 2) F]

theorem horizontal_mem_U_basisCoord (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈ U (basisCoord i) := by
  refine ⟨(mem_line_iff _ _).mpr ⟨t, rfl⟩, ?_⟩
  change dot (basisCoord i) (0 + Q (t • basisCoord i)) = 0
  simp

theorem vertical_mem_U_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    ((0 : Vec F), t • basisCoord i) ∈ U (basisCoord j) := by
  refine ⟨(line _).zero_mem, ?_⟩
  change dot (basisCoord j) (t • basisCoord i + Q 0) = 0
  simpa using dot_smul_basisCoord_of_ne t i j hij

/-- The binary span of the three coordinate block spaces. -/
def coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F) :=
  (U (basisCoord 0) ⊔ U (basisCoord 1)) ⊔ U (basisCoord 2)

theorem U_basisCoord_le_coordinateBlockSpan (i : Fin 3) :
    U (basisCoord i) ≤ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  fin_cases i
  · exact le_trans le_sup_left le_sup_left
  · exact le_trans le_sup_right le_sup_left
  · exact le_sup_right

theorem horizontal_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
  U_basisCoord_le_coordinateBlockSpan i (horizontal_mem_U_basisCoord t i)

theorem vertical_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    ((0 : Vec F), t • basisCoord i) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  have h (j : Fin 3) (hij : i ≠ j) :
      ((0 : Vec F), t • basisCoord i) ∈
        (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
    U_basisCoord_le_coordinateBlockSpan j (vertical_mem_U_basisCoord_of_ne t i j hij)
  fin_cases i
  · exact h 1 (by decide)
  · exact h 0 (by decide)
  · exact h 0 (by decide)

/-- Every pair is a sum of three horizontal and three vertical coordinate
pairs, all already in the sum of the coordinate blocks. -/
theorem mem_coordinateBlockSpan (p : Vec F × Vec F) :
    p ∈ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  let S : Submodule (ZMod 2) (Vec F × Vec F) := coordinateBlockSpan
  have hh : (p.1, (0 : Vec F)) ∈ S := by
    have h := S.add_mem
      (S.add_mem (horizontal_mem_coordinateBlockSpan (p.1 0) 0)
        (horizontal_mem_coordinateBlockSpan (p.1 1) 1))
      (horizontal_mem_coordinateBlockSpan (p.1 2) 2)
    convert h using 1
    ext i <;> fin_cases i <;> simp [basisCoord]
  have hv : ((0 : Vec F), p.2) ∈ S := by
    have h := S.add_mem
      (S.add_mem (vertical_mem_coordinateBlockSpan (p.2 0) 0)
        (vertical_mem_coordinateBlockSpan (p.2 1) 1))
      (vertical_mem_coordinateBlockSpan (p.2 2) 2)
    convert h using 1
    ext i <;> fin_cases i <;> simp [basisCoord]
  have h := S.add_mem hh hv
  simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using h

theorem coordinateBlockSpan_eq_top :
    (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) = ⊤ := by
  apply top_unique
  intro p _
  exact mem_coordinateBlockSpan p

/-- The block spaces for all nonzero line generators span the whole ambient
binary vector space.  The proof uses just the three coordinate generators. -/
theorem iSup_U_nonzero_eq_top :
    (⨆ v : {v : Vec F // v ≠ 0}, U v.1) = ⊤ := by
  apply top_unique
  rw [← coordinateBlockSpan_eq_top (F := F)]
  unfold coordinateBlockSpan
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 0, basisCoord_ne_zero 0⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 1, basisCoord_ne_zero 1⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 2, basisCoord_ne_zero 2⟩

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

/-- A coordinate-stable subspace containing the coordinates is the whole
function space when the coordinates separate points and exclude the zero
point. The proof constructs each point indicator by successively removing
the other points. -/
theorem eq_top_of_binary_coordinates
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F) (W : Submodule F (X → F))
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (hcoordinate : ∀ i, c i ∈ W)
    (hstable : ∀ i f, f ∈ W → (fun x => c i x * f x) ∈ W) :
    W = ⊤ := by
  classical
  have hindicator : ∀ x : X, (fun y => if x = y then (1 : F) else 0) ∈ W := by
    intro x
    have hfilter : ∀ s : Finset X,
        ∃ f : X → F, f ∈ W ∧ f x = 1 ∧ ∀ y ∈ s, y ≠ x → f y = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          obtain ⟨i, hi⟩ := hnonzero x
          refine ⟨c i, hcoordinate i, (hbinary i x).resolve_left hi, ?_⟩
          simp
      | @insert y s hy ih =>
          obtain ⟨f, hf, hfx, hfzero⟩ := ih
          by_cases hyx : y = x
          · refine ⟨f, hf, hfx, ?_⟩
            intro z hz hzx
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact (hzx hyx).elim
            · exact hfzero z hz hzx
          · obtain ⟨i, hi⟩ := hseparate x y (Ne.symm hyx)
            rcases hbinary i x with hix | hix <;>
              rcases hbinary i y with hiy | hiy
            · exact (hi (hix.trans hiy.symm)).elim
            · refine ⟨fun z => f z - c i z * f z,
                W.sub_mem hf (hstable i f hf), ?_, ?_⟩
              · simp [hfx, hix]
              · intro z hz hzx
                rcases Finset.mem_insert.mp hz with rfl | hz
                · simp [hiy]
                · simp [hfzero z hz hzx]
            · refine ⟨fun z => c i z * f z, hstable i f hf, ?_, ?_⟩
              · simp [hfx, hix]
              · intro z hz hzx
                rcases Finset.mem_insert.mp hz with rfl | hz
                · simp [hiy]
                · simp [hfzero z hz hzx]
            · exact (hi (hix.trans hiy.symm)).elim
    obtain ⟨f, hf, hfx, hfzero⟩ := hfilter Finset.univ
    have heq : f = fun y => if x = y then (1 : F) else 0 := by
      funext y
      by_cases hxy : x = y
      · subst y
        simp [hfx]
      · simp [hxy, hfzero y (Finset.mem_univ y) (Ne.symm hxy)]
    rwa [← heq]
  apply top_unique
  intro f _
  rw [pi_eq_sum_univ f]
  exact W.sum_mem fun x _ => W.smul_mem (f x) (hindicator x)

/-- Degree-two evaluation space. Repeated indices are allowed, so on binary
points this also contains every degree-one evaluation. -/
def quadraticEvaluationSpan {F X I : Type*} [Field F]
    (c : I → X → F) : Submodule F (X → F) :=
  Submodule.span F (Set.range fun ij : I × I => fun x => c ij.1 x * c ij.2 x)

/-- Degree-three evaluation space. Repeated indices recover all lower
positive degrees on binary points. -/
def cubicEvaluationSpan {F X I : Type*} [Field F]
    (c : I → X → F) : Submodule F (X → F) :=
  Submodule.span F
    (Set.range fun ijk : I × I × I => fun x => c ijk.1 x * c ijk.2.1 x * c ijk.2.2 x)

theorem eq_top_of_cubic_le_of_le_quadratic
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F) (W : Submodule F (X → F))
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (hcubic : cubicEvaluationSpan c ≤ W)
    (hquadratic : W ≤ quadraticEvaluationSpan c) : W = ⊤ := by
  apply eq_top_of_binary_coordinates c W hbinary hseparate hnonzero
  · intro i
    have hi : (fun x => c i x * c i x * c i x) ∈ cubicEvaluationSpan c :=
      Submodule.subset_span ⟨(i, i, i), rfl⟩
    have heq : (fun x => c i x * c i x * c i x) = c i := by
      funext x
      rcases hbinary i x with h | h <;> simp [h]
    rw [heq] at hi
    exact hcubic hi
  · intro k f hf
    have hf' : f ∈ Submodule.span F
        (Set.range fun ij : I × I => fun x => c ij.1 x * c ij.2 x) :=
      hquadratic hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨⟨i, j⟩, rfl⟩ := hf
        have h : (fun x => c k x * c i x * c j x) ∈ cubicEvaluationSpan c :=
          Submodule.subset_span ⟨(k, i, j), rfl⟩
        simpa only [mul_assoc] using hcubic h
    | zero =>
        have heq : (fun x => c k x * (0 : X → F) x) = (0 : X → F) := by
          funext x
          exact mul_zero _
        rw [heq]
        exact W.zero_mem
    | add f g hf hg ihf ihg =>
        have heq : (fun x => c k x * ((f + g) x)) =
            (fun x => c k x * f x) + (fun x => c k x * g x) := by
          funext x
          exact mul_add _ _ _
        rw [heq]
        exact W.add_mem ihf ihg
    | smul a f hf ih =>
        have heq : (fun x => c k x * ((a • f) x)) =
            a • (fun x => c k x * f x) := by
          funext x
          exact mul_left_comm _ _ _
        rw [heq]
        exact W.smul_mem a ih

/-- Equality of the quadratic and cubic evaluation spaces can occur only
when both are already the full function space. -/
theorem quadraticEvaluationSpan_eq_top_of_cubic_le
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F)
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (h : cubicEvaluationSpan c ≤ quadraticEvaluationSpan c) :
    quadraticEvaluationSpan c = ⊤ :=
  eq_top_of_cubic_le_of_le_quadratic c _ hbinary hseparate hnonzero h le_rfl

/-- Every element of the binary field is either zero or one. -/
theorem binary_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The exact evaluation-space form used for the genericity argument.
`φ` embeds the binary coordinates into the field of rational functions (or
any other field of characteristic two). -/
theorem eq_top_of_binary_evaluation_stable
    {F : Type*} [Field F] {r : ℕ}
    (E : Finset (Fin r → ZMod 2))
    (hzero : (0 : Fin r → ZMod 2) ∉ E)
    (φ : ZMod 2 →+* F)
    (W : Submodule F (E → F))
    (hcoordinate : ∀ i : Fin r, (fun t : E => φ (t.val i)) ∈ W)
    (hstable : ∀ (i : Fin r) (f : E → F), f ∈ W →
      (fun t : E => φ (t.val i) * f t) ∈ W) : W = ⊤ := by
  classical
  have hφ : Function.Injective φ := by
    intro a b h
    rcases binary_eq_zero_or_one a with rfl | rfl <;>
      rcases binary_eq_zero_or_one b with rfl | rfl <;> simp_all
  apply eq_top_of_binary_coordinates (fun i (t : E) => φ (t.val i)) W
      _ _ _ hcoordinate hstable
  · intro i t
    rcases binary_eq_zero_or_one (t.val i) with h | h
    · left
      simp [h]
    · right
      simp [h]
  · intro t u htu
    have hne : t.val ≠ u.val := fun h => htu (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, fun h => hi (hφ h)⟩
  · intro t
    have hne : t.val ≠ 0 := by
      intro h
      exact hzero (h ▸ t.property)
    have hi : ∃ i : Fin r, t.val i ≠ 0 := by
      by_contra h
      apply hne
      funext i
      exact Classical.not_not.mp (fun hi => h ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hi
    exact ⟨i, fun h => hi (hφ (by simpa using h))⟩

end UniqueGamesTheorem.Quadratic

end

section

/-! The low-dimension obstruction used by the all-lifts genericity proof. -/

namespace UniqueGamesTheorem.Quadratic

/-- A proper-dimensional subspace of the quadratic evaluation space misses
at least one cubic evaluation. This supplies a concrete coefficient vector
outside the alignment-column span. -/
theorem exists_cubic_not_mem_of_finrank_lt
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F) (W : Submodule F (X → F))
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (hquadratic : W ≤ quadraticEvaluationSpan c)
    (hdim : Module.finrank F W < Fintype.card X) :
    ∃ i j k, (fun x => c i x * c j x * c k x) ∉ W := by
  classical
  by_contra h
  have hcubic : cubicEvaluationSpan c ≤ W := by
    apply Submodule.span_le.mpr
    rintro f ⟨⟨i, j, k⟩, rfl⟩
    by_contra hn
    exact h ⟨i, j, k, hn⟩
  have htop := eq_top_of_cubic_le_of_le_quadratic c W hbinary hseparate
    hnonzero hcubic hquadratic
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hdim
  exact (lt_irrefl _) hdim

end UniqueGamesTheorem.Quadratic

end

section

/-!
A concrete mathematical family of finite binary fields of unbounded size.
The extension degree is chosen from numerical thresholds alone, before the
logical output dimension of the latent gadget is selected.
-/

namespace UniqueGamesTheorem.Quadratic

/-- The degree-`d` binary Galois field.  Cardinality statements below require
`d > 0`; the degenerate exponent zero is deliberately excluded. -/
abbrev BinaryField (d : ℕ) := GaloisField 2 d

theorem card_binaryField (d : ℕ) (hd : 0 < d) :
    Nat.card (BinaryField d) = 2 ^ d :=
  GaloisField.card 2 d (Nat.ne_of_gt hd)

theorem finrank_binaryField (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (BinaryField d) = d :=
  GaloisField.finrank 2 (Nat.ne_of_gt hd)

theorem finrank_binaryField_triple (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (Fin 3 → BinaryField d) = 3 * d := by
  rw [← Module.finrank_mul_finrank (ZMod 2) (BinaryField d) (Fin 3 → BinaryField d),
    finrank_binaryField d hd, Module.finrank_fin_fun, mul_comm]

/-- A deliberately simple explicit upper choice; optimization of the field
size is irrelevant because these thresholds are fixed before the input. -/
def fieldDegree (cardThreshold rankThreshold : ℕ) : ℕ :=
  cardThreshold + rankThreshold + 1

theorem fieldDegree_pos (N r : ℕ) : 0 < fieldDegree N r := by
  simp [fieldDegree]

theorem threshold_lt_two_pow_fieldDegree (N r : ℕ) : N < 2 ^ fieldDegree N r := by
  have h : N ≤ fieldDegree N r := by unfold fieldDegree; omega
  exact lt_of_le_of_lt h Nat.lt_two_pow_self

theorem rankThreshold_le_triple_fieldDegree (N r : ℕ) : r ≤ 3 * fieldDegree N r := by
  unfold fieldDegree
  omega

theorem exists_binary_field_degree (N r : ℕ) :
    ∃ d : ℕ, 0 < d ∧ N < 2 ^ d ∧ r ≤ 3 * d :=
  ⟨fieldDegree N r, fieldDegree_pos N r, threshold_lt_two_pow_fieldDegree N r,
    rankThreshold_le_triple_fieldDegree N r⟩

/-- Simultaneous cardinality and rank threshold attainment by the same field. -/
theorem chosen_binaryField_thresholds (N r : ℕ) :
    N < Nat.card (BinaryField (fieldDegree N r)) ∧
      r ≤ Module.finrank (ZMod 2) (Fin 3 → BinaryField (fieldDegree N r)) := by
  rw [card_binaryField _ (fieldDegree_pos N r),
    finrank_binaryField_triple _ (fieldDegree_pos N r)]
  exact ⟨threshold_lt_two_pow_fieldDegree N r, rankThreshold_le_triple_fieldDegree N r⟩

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Separation of polynomial parity classes

The genericity argument uses monomials with distinct squarefree
exponent vectors. Polynomial coefficients in the original variables become
polynomials in squares after adjoining their square roots. The lemmas below
prove the resulting coefficient separation directly, without assuming an
algebraic independence witness.
-/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped BigOperators

variable {σ ι R : Type*} [CommSemiring R]

/-- Exponents zero or one represent parity classes. -/
def SquarefreeExponent (a : σ →₀ ℕ) : Prop := ∀ k, a k < 2

/-- Two different squarefree shifts have disjoint expanded supports. -/
theorem coeff_expand_mul_monomial_of_ne
    (p : MvPolynomial σ R) (a b n : σ →₀ ℕ)
    (ha : SquarefreeExponent a) (hb : SquarefreeExponent b) (hab : a ≠ b) :
    (expand 2 p * monomial b 1).coeff (2 • n + a) = 0 := by
  classical
  rw [coeff_mul_monomial']
  split_ifs with hle
  · obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra h
      push Not at h
      exact hab (Finsupp.ext h)
    have hcoeff : (expand 2 p).coeff (2 • n + a - b) = 0 := by
      apply coeff_expand_of_not_dvd (i := k)
      intro hdiv
      obtain ⟨m, hm⟩ := hdiv
      have hle' := hle k
      have ha' := ha k
      have hb' := hb k
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul] at hm hle'
      omega
    simp [hcoeff]
  · rfl

/-- Within one parity class coefficient extraction recovers the coefficient
before expansion. -/
theorem coeff_expand_mul_monomial_self
    (p : MvPolynomial σ R) (a n : σ →₀ ℕ) :
    (expand 2 p * monomial a 1).coeff (2 • n + a) = p.coeff n := by
  rw [coeff_mul_monomial, coeff_expand_smul 2 (by decide), mul_one]

/-- Extraction from a finite sum isolates its unique parity class. -/
theorem coeff_sum_expand_mul_monomial [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R)
    (i : ι) (n : σ →₀ ℕ) :
    (∑ j, expand 2 (p j) * monomial (e j) 1).coeff (2 • n + e i) =
      (p i).coeff n := by
  classical
  rw [coeff_sum]
  rw [Finset.sum_eq_single i]
  · exact coeff_expand_mul_monomial_self _ _ _
  · intro j _ hji
    exact coeff_expand_mul_monomial_of_ne _ _ _ _ (he i) (he j)
      (fun h => hji (hinj h).symm)
  · simp

/-- A polynomial dependence between distinct squarefree parity classes is
trivial, even when each coefficient is itself an arbitrary polynomial in the
squared variables. -/
theorem sum_expand_mul_monomial_eq_zero_iff [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R) :
    (∑ i, expand 2 (p i) * monomial (e i) 1) = 0 ↔ ∀ i, p i = 0 := by
  constructor
  · intro h i
    ext n
    have hc := congrArg (fun q : MvPolynomial σ R => q.coeff (2 • n + e i)) h
    simpa only [coeff_sum_expand_mul_monomial e he hinj,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc
  · intro h
    simp [h]

noncomputable def blockExponent {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : (κ × J) →₀ ℕ := by
  classical
  exact Finsupp.equivFunOnFinite.symm (fun x => if x.2 = v x.1 then 1 else 0)

@[simp] theorem blockExponent_apply {κ J : Type*} [Finite κ] [Finite J] [DecidableEq J]
    (v : κ → J) (x : κ × J) :
    blockExponent v x = if x.2 = v x.1 then 1 else 0 := by
  classical
  by_cases h : x.2 = v x.1 <;> simp [blockExponent, h]

theorem blockExponent_squarefree {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : SquarefreeExponent (blockExponent v) := by
  classical
  intro x
  simp only [blockExponent_apply]
  split_ifs <;> decide

theorem blockExponent_injective {κ J : Type*} [Finite κ] [Finite J] :
    Function.Injective (blockExponent (κ := κ) (J := J)) := by
  classical
  intro v w h
  funext i
  have hc := congrArg (fun e : (κ × J) →₀ ℕ => e (i, v i)) h
  by_contra hne
  simp [hne] at hc

theorem blockExponent_eq_sum {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    blockExponent v = ∑ i, Finsupp.single (i, v i) 1 := by
  classical
  ext x
  rw [blockExponent_apply, Finsupp.finsetSum_apply]
  symm
  rw [Finset.sum_eq_single x.1]
  · simp [Finsupp.single_apply, Prod.ext_iff, eq_comm]
  · intro i _ hi
    have hix : (i, v i) ≠ x := fun h => hi (congrArg Prod.fst h)
    simp [hix]
  · simp

theorem monomial_blockExponent {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    (monomial (blockExponent v) 1 : MvPolynomial (κ × J) R) =
      ∏ i, X (i, v i) := by
  rw [blockExponent_eq_sum, monomial_sum_one]
  rfl

/-- In particular the three-block monomials have independent polynomial
coefficients after squaring the variables. -/
theorem sum_expand_mul_blockMonomial_eq_zero_iff {J : Type*} [Fintype J]
    (p : (Fin 3 → J) → MvPolynomial (Fin 3 × J) R) :
    (∑ v, expand 2 (p v) * monomial (blockExponent v) 1) = 0 ↔
      ∀ v, p v = 0 :=
  sum_expand_mul_monomial_eq_zero_iff blockExponent blockExponent_squarefree
    blockExponent_injective p

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Polynomial parity obstruction

This supplies the algebraic obstruction step in the genericity proof.
Squaring a cleared dual row exposes its distinct squarefree parity classes.
No genericity or minor-existence conclusion is assumed here.
-/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped BigOperators
open scoped nonZeroDivisors

variable {σ : Type*}

/-- Every coefficient in the binary prime field is fixed by squaring. -/
theorem zmodTwo_sq (a : ZMod 2) : a ^ 2 = a := by
  classical
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl
  · exact zero_pow (by decide)
  · exact one_pow 2

theorem expand_two_eq_sq (p : MvPolynomial σ (ZMod 2)) : expand 2 p = p ^ 2 := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a => simp only [expand_monomial, monomial_pow, zmodTwo_sq]
  | add p q hp hq => rw [map_add, CharTwo.add_sq, hp, hq]

/-- A separating linear functional written in coordinate form. -/
theorem exists_coordinate_separator {X K : Type*} [Field K] [Fintype X]
    (W : Submodule K (X → K)) (v : X → K) (hv : v ∉ W) :
    ∃ a : X → K, (∀ w ∈ W, ∑ x, a x * w x = 0) ∧
      (∑ x, a x * v x) ≠ 0 := by
  classical
  obtain ⟨f, hfv, hfW⟩ := W.exists_dual_map_eq_bot_of_notMem hv inferInstance
  let a : X → K := fun x => f (fun y => if x = y then 1 else 0)
  have hrepr (w : X → K) : f w = ∑ x, a x * w x := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  refine ⟨a, ?_, ?_⟩
  · intro w hw
    have hmem : f w ∈ W.map f := ⟨w, hw, rfl⟩
    rw [hfW, Submodule.mem_bot, hrepr] at hmem
    exact hmem
  · rwa [← hrepr]

section Obstruction

variable {J X : Type*} [Fintype J] [Fintype X]

/-- The universal coordinate `z_i(t)` with the `x_ij` as indeterminates. -/
noncomputable def universalLinearForm (t : J → ZMod 2) (i : Fin 3) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ j, C (t j) * MvPolynomial.X (i, j)

/-- Polynomial alignment columns; every lift is one linear combination of
these columns. -/
noncomputable def universalAlignmentColumn (t : X → J → ZMod 2)
    (ij : Fin 3 × J) (x : X) : MvPolynomial (Fin 3 × J) (ZMod 2) :=
  C (t x ij.2) * universalLinearForm (t x) ij.1

theorem universalLinearForm_prod (t : J → ZMod 2) :
    (∏ i, universalLinearForm t i) =
      ∑ v : Fin 3 → J, C (∏ i, t (v i)) * monomial (blockExponent v) 1 := by
  classical
  unfold universalLinearForm
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.prod_mul_distrib, ← map_prod, monomial_blockExponent]

/-- Coefficient obtained by pairing a polynomial row with a cubic binary
evaluation. -/
noncomputable def cubicPairing (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) (v : Fin 3 → J) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ x, p x * C (∏ i, t x (v i))

/-- Clearing the rational dual's denominator and squaring gives this one
polynomial obstruction to simultaneous alignment. Its degree is finite and
depends only on the fixed set of inputs. -/
noncomputable def alignmentObstruction (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ x, p x ^ 2 * ∏ i, universalLinearForm (t x) i

theorem alignmentObstruction_parity_expansion (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) :
    alignmentObstruction t p = ∑ v : Fin 3 → J,
      cubicPairing t p v ^ 2 * monomial (blockExponent v) 1 := by
  classical
  unfold alignmentObstruction
  simp_rw [universalLinearForm_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  unfold cubicPairing
  rw [CharTwo.sum_sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_pow, ← map_pow, zmodTwo_sq, mul_assoc]

theorem alignmentObstruction_ne_zero (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2))
    (v : Fin 3 → J) (hv : cubicPairing t p v ≠ 0) :
    alignmentObstruction t p ≠ 0 := by
  intro h
  rw [alignmentObstruction_parity_expansion] at h
  have hzero : ∀ w, cubicPairing t p w = 0 := by
    apply (sum_expand_mul_blockMonomial_eq_zero_iff _).mp
    simpa only [expand_two_eq_sq] using h
  exact hv (hzero v)

end Obstruction

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped nonZeroDivisors

/-- A polynomial row annihilates all alignment columns and detects a cubic
evaluation. The row is constructed from a rational dual separator; there is
no assumed algebraic genericity certificate. -/
theorem exists_polynomial_alignment_annihilator
    {J X : Type*} [Fintype J] [Fintype X]
    (t : X → J → ZMod 2) (ht : Function.Injective t)
    (hnonzero : ∀ x, t x ≠ 0) (hcard : 3 * Fintype.card J < Fintype.card X) :
    ∃ p : X → MvPolynomial (Fin 3 × J) (ZMod 2),
      (∀ ij, ∑ x, p x * universalAlignmentColumn t ij x = 0) ∧
      ∃ v : Fin 3 → J, cubicPairing t p v ≠ 0 := by
  classical
  let P := MvPolynomial (Fin 3 × J) (ZMod 2)
  let K := FractionRing P
  let f : P →+* K := algebraMap P K
  let φ : ZMod 2 →+* K := f.comp C
  let c : J → X → K := fun j x => φ (t x j)
  let M : Matrix X (Fin 3 × J) K := fun x ij => f (universalAlignmentColumn t ij x)
  let W := LinearMap.range M.mulVecLin
  have hquadratic : W ≤ quadraticEvaluationSpan c := by
    change LinearMap.range M.mulVecLin ≤ _
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    have heq : M.col ij = ∑ j, f (MvPolynomial.X (ij.1, j)) •
        (fun x => c ij.2 x * c j x) := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change f (C (t x ij.2) * ∑ j, C (t x j) * MvPolynomial.X (ij.1, j)) =
        ∑ j, f (MvPolynomial.X (ij.1, j)) * (f (C (t x ij.2)) * f (C (t x j)))
      simp only [map_mul, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ac_rfl
    rw [heq]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(ij.2, j), rfl⟩
  have hbinary : ∀ j x, c j x = 0 ∨ c j x = 1 := by
    intro j x
    rcases binary_eq_zero_or_one (t x j) with h | h
    · left
      simp [c, h]
    · right
      simp [c, h]
  have hseparate : ∀ x y, x ≠ y → ∃ j, c j x ≠ c j y := by
    intro x y hxy
    have hfun : t x ≠ t y := fun h => hxy (ht h)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hfun
    exact ⟨j, fun h => hj (φ.injective h)⟩
  have hnz : ∀ x, ∃ j, c j x ≠ 0 := by
    intro x
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hnonzero x)
    refine ⟨j, ?_⟩
    intro h
    exact hj (φ.injective (by simpa [c] using h))
  have hdim : Module.finrank K W < Fintype.card X := by
    have hle : Module.finrank K W ≤ 3 * Fintype.card J := by
      calc
        Module.finrank K W ≤ Module.finrank K ((Fin 3 × J) → K) :=
          LinearMap.finrank_range_le M.mulVecLin
        _ = 3 * Fintype.card J := by
          rw [Module.finrank_fintype_fun_eq_card]
          simp
    exact hle.trans_lt hcard
  obtain ⟨i, j, k, hijk⟩ := exists_cubic_not_mem_of_finrank_lt
    c W hbinary hseparate hnz hquadratic hdim
  let v : Fin 3 → J := ![i, j, k]
  have hcubic : (fun x => ∏ b : Fin 3, c (v b) x) ∉ W := by
    simpa [v, Fin.prod_univ_succ, mul_assoc] using hijk
  obtain ⟨a, ha, hav⟩ := exists_coordinate_separator W _ hcubic
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite P⁰ a
  choose p hp using hb
  have hp' (x : X) : f (p x) = f (b : P) * a x := by
    simpa only [Algebra.smul_def] using hp x
  have hbne : f (b : P) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  refine ⟨p, ?_, v, ?_⟩
  · intro ij
    apply IsFractionRing.injective P K
    change f (∑ x, p x * universalAlignmentColumn t ij x) = f 0
    rw [map_sum, map_zero]
    simp only [map_mul, hp', mul_assoc]
    rw [← Finset.mul_sum]
    have hcol : M.col ij ∈ W := by
      change M.col ij ∈ LinearMap.range M.mulVecLin
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨ij, rfl⟩
    have hsum := ha (M.col ij) hcol
    change (∑ x, a x * f (universalAlignmentColumn t ij x)) = 0 at hsum
    rw [hsum, mul_zero]
  · have heq : f (cubicPairing t p v) =
        f (b : P) * ∑ x, a x * ∏ i : Fin 3, c (v i) x := by
      unfold cubicPairing
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp [hp', c, φ, map_prod, mul_assoc]
    intro hz
    have : f (b : P) * (∑ x, a x * ∏ i : Fin 3, c (v i) x) = 0 := by
      rw [← heq, hz, map_zero]
    exact (mul_ne_zero hbne hav) this

/-- Every specialization of the polynomial row obstructs every alignment
column combination simultaneously. -/
theorem alignmentObstruction_eval_eq_zero
    {J X F : Type*} [Fintype J] [Fintype X] [Field F] [CharP F 2]
    (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2))
    (hann : ∀ ij, ∑ x, p x * universalAlignmentColumn t ij x = 0)
    (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F)
    (c : X → F) (a : (Fin 3 × J) → F)
    (hc : ∀ x, c x ^ 2 = ρ (∏ i, universalLinearForm (t x) i))
    (ha : ∀ x, c x = ∑ ij, ρ (universalAlignmentColumn t ij x) * a ij) :
    ρ (alignmentObstruction t p) = 0 := by
  classical
  have hann' (ij : Fin 3 × J) :
      (∑ x, ρ (p x) * ρ (universalAlignmentColumn t ij x)) = 0 := by
    have h := congrArg ρ (hann ij)
    simpa only [map_sum, map_mul, map_zero] using h
  have hpair : (∑ x, ρ (p x) * c x) = 0 := by
    simp_rw [ha, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro ij _
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, hann', zero_mul]
  calc
    ρ (alignmentObstruction t p) = ∑ x, ρ (p x) ^ 2 *
        ρ (∏ i, universalLinearForm (t x) i) := by
          simp only [alignmentObstruction, map_sum, map_mul, map_pow]
    _ = (∑ x, ρ (p x) * c x) ^ 2 := by
      rw [CharTwo.sum_sq]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_pow, hc]
    _ = 0 := by rw [hpair, zero_pow (by decide)]

/-- The uniform algebraic obstruction exists for every set of more than
three times the binary dimension many distinct nonzero inputs. Its one
polynomial works for all lifts over every characteristic-two field. -/
theorem exists_nonzero_alignment_obstruction
    {J X : Type*} [Fintype J] [Fintype X]
    (t : X → J → ZMod 2) (ht : Function.Injective t)
    (hnonzero : ∀ x, t x ≠ 0) (hcard : 3 * Fintype.card J < Fintype.card X) :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [CharP F 2]
        (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F)
        (c : X → F) (a : (Fin 3 × J) → F),
        (∀ x, c x ^ 2 = ρ (∏ i, universalLinearForm (t x) i)) →
        (∀ x, c x = ∑ ij, ρ (universalAlignmentColumn t ij x) * a ij) →
        ρ P = 0 := by
  obtain ⟨p, hann, v, hv⟩ := exists_polynomial_alignment_annihilator t ht hnonzero hcard
  refine ⟨alignmentObstruction t p, alignmentObstruction_ne_zero t p v hv, ?_⟩
  intro F _ _ ρ c a hc ha
  exact alignmentObstruction_eval_eq_zero t p hann ρ c a hc ha

end UniqueGamesTheorem.Quadratic

end

end OAI
