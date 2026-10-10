import Mathlib
import OAI.Computability.MaxCut.Games.OrientedBlockKernel
import OAI.Computability.MaxCut.PCP.ParityIndependence

namespace OAI

noncomputable section

/-!
# Polynomial parity obstruction

This supplies the algebraic obstruction step in the v2 genericity proof.
Squaring a cleared dual row exposes its distinct squarefree parity classes.
No genericity or minor-existence conclusion is assumed here.
-/

namespace MaxCutGames.Quadratic

section

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

end

section

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

/-- The exact evaluation-space form used for the v2 genericity argument.
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

end

/-! The low-dimension obstruction used by the v2 all-lifts genericity proof. -/

section

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

end

/-! The actual random binary-linear parametrization used in the genericity proof. -/

section

open Module
open scoped BigOperators

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

/-- Independent field entries specify a binary-linear map into `F³`. -/
def parameterMap (x : (Fin 3 × J) → F) : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) :=
  (Pi.basisFun (ZMod 2) J).constr (ZMod 2) (fun j i => x (i, j))

omit [CharP F 2] in
theorem parameterMap_apply (x : (Fin 3 × J) → F) (t : J → ZMod 2) (i : Fin 3) :
    parameterMap x t i = ∑ j, algebraMap (ZMod 2) F (t j) * x (i, j) := by
  classical
  simp [parameterMap, Basis.constr_apply_fintype, Algebra.smul_def]

omit [CharP F 2] in
theorem parameterMap_basis (x : (Fin 3 × J) → F) (j : J) (i : Fin 3) :
    parameterMap x ((Pi.basisFun (ZMod 2) J) j) i = x (i, j) := by
  exact congrFun ((Pi.basisFun (ZMod 2) J).constr_basis (ZMod 2)
    (fun j i => x (i, j)) j) i

omit [CharP F 2] in
/-- Evaluation of the universal polynomial is the actual linear map. -/
theorem eval_universalLinearForm (x : (Fin 3 × J) → F) (t : J → ZMod 2) (i : Fin 3) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t i) =
      parameterMap x t i := by
  rw [parameterMap_apply]
  simp [universalLinearForm]

omit [CharP F 2] in
/-- All linear lifts have the prescribed universal alignment columns, with
their arbitrary values on the binary basis as column coefficients. -/
theorem dot_parameter_lift (x : (Fin 3 × J) → F)
    (g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) (t : J → ZMod 2) :
    (∑ i, parameterMap x t i * g t i) =
      ∑ ij : Fin 3 × J,
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x
          (universalAlignmentColumn (fun t : J → ZMod 2 => t) ij t) *
          g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1 := by
  have h := dot_lift_eq_alignment_mulVec (Pi.basisFun (ZMod 2) J)
    (fun t : J → ZMod 2 => t) (parameterMap x) g t
  simpa [Matrix.mulVec, dotProduct, alignmentMatrix, Pi.basisFun_repr,
    universalAlignmentColumn, eval_universalLinearForm] using h

variable [Fintype F]

/-- The unique square-root value satisfies the universal cubic equation. -/
theorem alignmentRightHandSide_sq (x : (Fin 3 × J) → F) (t : J → ZMod 2) :
    alignmentRightHandSide (parameterMap x t) ^ 2 =
      MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x
        (∏ i : Fin 3, universalLinearForm t i) := by
  simp [alignmentRightHandSide, Fin.prod_univ_succ, eval_universalLinearForm, mul_assoc]

end

/-!
# One polynomial controls all binary linear lifts

For fixed binary dimension, multiply the nonzero obstructions for the finitely
many sets of `3r + 1` nonzero inputs.  A nonvanishing specialization then obeys
the alignment bound simultaneously for every binary linear map.  The resulting
polynomial and its degree are chosen before the extension field.
-/

section

open scoped BigOperators

/-- An unconditional polynomial exceptional-set certificate for the complete
all-lifts alignment condition.  There is no quantified bound on the maps `g`
outside the conclusion, and no choice of extension field enters `P`. -/
theorem exists_all_lifts_alignment_polynomial (J : Type*) [Fintype J] [DecidableEq J] :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (x : (Fin 3 × J) → F),
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x P ≠ 0 →
        ∀ g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F),
          (alignmentEvent (R := ZMod 2) (parameterMap x) g
            (fun t => alignmentRightHandSide (parameterMap x t))).card ≤
              3 * Fintype.card J := by
  classical
  let V := J → ZMod 2
  let Esets := {E : Finset V // (0 : V) ∉ E ∧ E.card = 3 * Fintype.card J + 1}
  have hex (E : Esets) := exists_nonzero_alignment_obstruction
    (fun t : E.val => (t : V)) Subtype.val_injective
    (fun t : E.val => by
      intro hz
      apply E.property.1
      simpa only [hz] using t.property)
    (show 3 * Fintype.card J < Fintype.card E.val by
      simpa only [Fintype.card_coe, E.property.2] using
        Nat.lt_succ_self (3 * Fintype.card J))
  choose p hp hvanish using hex
  let P : MvPolynomial (Fin 3 × J) (ZMod 2) := ∏ E : Esets, p E
  refine ⟨P, Finset.prod_ne_zero_iff.mpr (fun E _ => hp E), ?_⟩
  intro F _ _ _ _ x hP g
  by_contra hbad
  have hlarge : 3 * Fintype.card J + 1 ≤
      (alignmentEvent (R := ZMod 2) (parameterMap x) g
        (fun t => alignmentRightHandSide (parameterMap x t))).card := by omega
  obtain ⟨E, hsub, hcard⟩ := Finset.exists_subset_card_eq hlarge
  have hzero : (0 : V) ∉ E := by
    intro hz
    have hmem := hsub hz
    simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.1 rfl
  let E' : Esets := ⟨E, hzero, hcard⟩
  let ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F :=
    MvPolynomial.eval₂Hom (algebraMap (ZMod 2) F) x
  let c : E → F := fun t => alignmentRightHandSide (parameterMap x (t : V))
  let a : (Fin 3 × J) → F :=
    fun ij => g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1
  have hc (t : E) :
      c t ^ 2 = ρ (∏ i : Fin 3, universalLinearForm (t : V) i) := by
    exact alignmentRightHandSide_sq x t
  have ha (t : E) : c t = ∑ ij, ρ
      (universalAlignmentColumn (fun t : E => (t : V)) ij t) * a ij := by
    have hmem := hsub t.property
    simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have ht := hmem.2
    calc
      c t = ∑ i, parameterMap x (t : V) i * g (t : V) i := ht.symm
      _ = _ := dot_parameter_lift x g t
  have hz : ρ (p E') = 0 := hvanish E' F ρ c a hc ha
  apply hP
  change ρ P = 0
  simp only [P, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ E') hz

end

/-!
# Polynomial obstructions to collapsed or proportional binary inputs

One linear polynomial detects each nonzero input. One quadratic polynomial
detects each pair of distinct nonzero binary inputs. The witnesses are proved
nonzero by explicit coordinate-selector evaluations. Together with the
alignment obstruction they yield a finite product whose zero set contains
every failure of v2 genericity. An `O_r(1/q)` bound suffices here.
-/

open MvPolynomial

theorem exists_binary_coordinate_one {J : Type*} (t : J → ZMod 2) (ht : t ≠ 0) :
    ∃ j, t j = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ht
  exact ⟨j, (binary_eq_zero_or_one (t j)).resolve_left hj⟩

/-- Distinct nonzero vectors over the binary field have a nonzero two-column
minor. Since the coefficient field is binary, the minor equals one. -/
theorem exists_binary_minor_one {J : Type*} (t u : J → ZMod 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) :
    ∃ j k, t j * u k + t k * u j = 1 := by
  obtain ⟨j, hj⟩ := exists_binary_coordinate_one t ht
  by_cases huj : u j = 0
  · obtain ⟨k, hk⟩ := exists_binary_coordinate_one u hu
    exact ⟨j, k, by simp [hj, huj, hk]⟩
  · have huj' : u j = 1 := (binary_eq_zero_or_one (u j)).resolve_left huj
    obtain ⟨k, hk⟩ := Function.ne_iff.mp htu
    refine ⟨j, k, ?_⟩
    rcases binary_eq_zero_or_one (t k) with htk | htk <;>
      rcases binary_eq_zero_or_one (u k) with huk | huk
    · exact (hk (htk.trans huk.symm)).elim
    · simp [hj, huj', htk, huk]
    · simp [hj, huj', htk, huk]
    · exact (hk (htk.trans huk.symm)).elim

variable {J : Type*} [Fintype J]

/-- Set the first two rows of the indeterminate matrix to coordinate
selectors. The third row is zero. -/
noncomputable def selectorAssignment (j k : J) : (Fin 3 × J) → ZMod 2 := by
  classical
  exact fun x => if x.1 = 0 then (if x.2 = j then 1 else 0)
    else if x.1 = 1 then (if x.2 = k then 1 else 0) else 0

theorem eval_universalLinearForm_selector_zero (t : J → ZMod 2) (j k : J) :
    eval (selectorAssignment j k) (universalLinearForm t 0) = t j := by
  classical
  simp [universalLinearForm, selectorAssignment]

theorem eval_universalLinearForm_selector_one (t : J → ZMod 2) (j k : J) :
    eval (selectorAssignment j k) (universalLinearForm t 1) = t k := by
  classical
  simp [universalLinearForm, selectorAssignment]

theorem universalLinearForm_zero_ne_zero (t : J → ZMod 2) (ht : t ≠ 0) :
    universalLinearForm t 0 ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_binary_coordinate_one t ht
  intro h
  have hc := congrArg (eval (selectorAssignment j j)) h
  rw [eval_universalLinearForm_selector_zero, map_zero, hj] at hc
  exact one_ne_zero hc

/-- A two-row determinant, with subtraction equal to addition in
characteristic two. -/
noncomputable def universalPairMinor (t u : J → ZMod 2) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  universalLinearForm t 0 * universalLinearForm u 1 +
    universalLinearForm t 1 * universalLinearForm u 0

theorem universalPairMinor_ne_zero (t u : J → ZMod 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) :
    universalPairMinor t u ≠ 0 := by
  obtain ⟨j, k, hjk⟩ := exists_binary_minor_one t u ht hu htu
  intro h
  have hc := congrArg (eval (selectorAssignment j k)) h
  simp only [universalPairMinor, map_add, map_mul,
    eval_universalLinearForm_selector_zero, eval_universalLinearForm_selector_one,
    map_zero] at hc
  rw [hjk] at hc
  exact one_ne_zero hc

/-- Proportional specialized image vectors force the fixed pair minor to
vanish, for every value of the proportionality scalar. -/
theorem universalPairMinor_eq_zero_of_proportional
    {F : Type*} [Field F] [CharP F 2]
    (t u : J → ZMod 2)
    (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F) (a : F)
    (h : ∀ i, ρ (universalLinearForm t i) = a * ρ (universalLinearForm u i)) :
    ρ (universalPairMinor t u) = 0 := by
  simp only [universalPairMinor, map_add, map_mul, h]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (CharTwo.add_self_eq_zero
      (a * ρ (universalLinearForm u 0) * ρ (universalLinearForm u 1)))

end MaxCutGames.Quadratic

end

end OAI
