import OAI.Analysis.OInfinity.IncompleteBinaryPath

namespace OAI

/-! # Finite stabilization inside a genuinely fixed spare corner

The first corner is the support of the original unitary. Additional equivalent
corners lie in its fixed complement. A cyclic permutation of these corners
turns a diagonal of path samples into adjacent increments. All finite corners
and the uncovered complement are retained explicitly.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

/-- A diagonal block sum in a row of partial isometries. -/
def fixedSpareBlock (r : I → E) (x : I → E) : E := ∑ i, r i * x i * star (r i)

def fixedSpareRange (r : I → E) : E := ∑ i, r i * star (r i)

omit [DecidableEq I] in
lemma fixedSpareBlock_one (r : I → E) : fixedSpareBlock r (fun _ => 1) = fixedSpareRange r := by
  simp only [fixedSpareBlock, fixedSpareRange, mul_one]

omit [DecidableEq I] in
lemma fixedSpareBlock_star (r : I → E) (x : I → E) :
    star (fixedSpareBlock r x) = fixedSpareBlock r (fun i => star (x i)) := by
  simp only [fixedSpareBlock, star_sum, star_mul, star_star, mul_assoc]

omit [DecidableEq I] in
lemma fixedSpareBlock_sub (r : I → E) (x y : I → E) :
    fixedSpareBlock r x - fixedSpareBlock r y = fixedSpareBlock r (fun i => x i - y i) := by
  simp only [fixedSpareBlock, mul_sub, sub_mul, Finset.sum_sub_distrib]

section Row

variable (q : E) (r : I → E) (hqstar : star q = q) (hqq : q * q = q)
variable (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)

include hqstar hqq hr in
omit [Fintype I] in
lemma fixedSpareRow_right (i : I) : r i * q = r i :=
  finiteRow_right_support q r hqstar hqq hr i

include hqstar hqq hr in
omit [Fintype I] in
lemma fixedSpareRow_star_left (i : I) : q * star (r i) = star (r i) := by
  simpa only [star_mul, star_star, hqstar] using congrArg star
    (fixedSpareRow_right q r hqstar hqq hr i)

include hqstar hqq hr in
lemma fixedSpareBlock_mul (x y : I → E) (hx : ∀ i, Commute q (x i)) :
    fixedSpareBlock r x * fixedSpareBlock r y = fixedSpareBlock r (fun i => x i * y i) := by
  have hterm (i j : I) : (r i * x i * star (r i)) * (r j * y j * star (r j)) =
      if i = j then r i * (x i * y i) * star (r i) else 0 := by
    calc
      _ = r i * x i * (star (r i) * r j) * y j * star (r j) := by noncomm_ring
      _ = _ := by
        rw [hr]
        split_ifs with hij
        · subst j
          rw [mul_assoc (r i) (x i) q, ← (hx i).eq, ← mul_assoc (r i) q,
            fixedSpareRow_right q r hqstar hqq hr]
          simp only [mul_assoc]
        · simp
  simp only [fixedSpareBlock, Finset.sum_mul, Finset.mul_sum, hterm,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [DecidableEq I] in
lemma fixedSpareRange_star : star (fixedSpareRange r) = fixedSpareRange r := by
  simp only [fixedSpareRange, star_sum, star_mul, star_star]

include hqstar hqq hr in
lemma fixedSpareRange_sq : fixedSpareRange r * fixedSpareRange r = fixedSpareRange r := by
  simpa only [fixedSpareBlock_one, one_mul] using
    fixedSpareBlock_mul q r hqstar hqq hr (fun _ => 1) (fun _ => 1)
      (fun _ => Commute.one_right _)

include hqstar hqq hr in
lemma fixedSpareBlock_range (x : I → E) (hx : ∀ i, Commute q (x i)) :
    fixedSpareRange r * fixedSpareBlock r x = fixedSpareBlock r x ∧
      fixedSpareBlock r x * fixedSpareRange r = fixedSpareBlock r x := by
  constructor
  · simpa only [fixedSpareBlock_one, one_mul] using
      fixedSpareBlock_mul q r hqstar hqq hr (fun _ => 1) x (fun _ => Commute.one_right _)
  · simpa only [fixedSpareBlock_one, mul_one] using
      fixedSpareBlock_mul q r hqstar hqq hr x (fun _ => 1) hx

include hqstar hqq hr in
lemma fixedSpareBlock_gram (x : I → unitary E) (hx : ∀ i, Commute q (x i : E)) :
    star (fixedSpareBlock r (fun i => (x i : E))) * fixedSpareBlock r (fun i => (x i : E)) =
        fixedSpareRange r ∧
      fixedSpareBlock r (fun i => (x i : E)) * star (fixedSpareBlock r (fun i => (x i : E))) =
        fixedSpareRange r := by
  have hxstar (i : I) : Commute q (star (x i : E)) := by
    simpa only [hqstar] using (hx i).star_star
  constructor
  · rw [fixedSpareBlock_star, fixedSpareBlock_mul q r hqstar hqq hr _ _ hxstar]
    simp only [Unitary.coe_star_mul_self, fixedSpareBlock_one]
  · rw [fixedSpareBlock_star, fixedSpareBlock_mul q r hqstar hqq hr _ _ hx]
    convert fixedSpareBlock_one r using 2
    funext i
    exact (x i).prop.2

include hqstar hqq hr in
def fixedSpareDiagonalUnitary (x : I → unitary E) (hx : ∀ i, Commute q (x i : E)) : unitary E :=
  ⟨relativeUnitaryExtension (fixedSpareRange r) (fixedSpareBlock r (fun i => (x i : E))),
    relativeUnitaryExtension_mem (fixedSpareRange r) _
      (fixedSpareRange_star r) (fixedSpareRange_sq q r hqstar hqq hr)
      (fixedSpareBlock_range q r hqstar hqq hr _ hx).1
      (fixedSpareBlock_range q r hqstar hqq hr _ hx).2
      (fixedSpareBlock_gram q r hqstar hqq hr x hx).1
      (fixedSpareBlock_gram q r hqstar hqq hr x hx).2⟩

include hqstar hqq hr in
lemma fixedSpareDiagonalUnitary_mul (x y : I → unitary E)
    (hx : ∀ i, Commute q (x i : E)) (hy : ∀ i, Commute q (y i : E)) :
    fixedSpareDiagonalUnitary q r hqstar hqq hr x hx *
      fixedSpareDiagonalUnitary q r hqstar hqq hr y hy =
    fixedSpareDiagonalUnitary q r hqstar hqq hr (fun i => x i * y i)
      (fun i => (hx i).mul_right (hy i)) := by
  apply Subtype.ext
  change (fixedSpareBlock r (fun i => (x i : E)) + (1 - fixedSpareRange r)) *
    (fixedSpareBlock r (fun i => (y i : E)) + (1 - fixedSpareRange r)) =
    fixedSpareBlock r (fun i => (x i : E) * (y i : E)) + (1 - fixedSpareRange r)
  have hxP := (fixedSpareBlock_range q r hqstar hqq hr _ hx).2
  have hPy := (fixedSpareBlock_range q r hqstar hqq hr _ hy).1
  have hPP := fixedSpareRange_sq q r hqstar hqq hr
  rw [← fixedSpareBlock_mul q r hqstar hqq hr _ _ hx]
  noncomm_ring [hxP, hPy, hPP]

include hqstar hqq hr in
lemma fixedSpareRange_mul_row (i : I) : fixedSpareRange r * r i = r i := by
  change finiteRowPermutation r 1 * r i = r i
  exact finiteRowPermutation_mul_row q r hqstar hqq hr 1 i

include hqstar hqq hr in
lemma fixedSparePermutation_support (σ : Equiv.Perm I) :
    fixedSpareRange r * finiteRowPermutation r σ = finiteRowPermutation r σ ∧
      finiteRowPermutation r σ * fixedSpareRange r = finiteRowPermutation r σ := by
  have he : fixedSpareRange r = finiteRowPermutation r 1 := by
    simp only [finiteRowPermutation, Equiv.Perm.one_apply, fixedSpareRange]
  rw [he]
  constructor <;> simp only [finiteRowPermutation_mul q r hqstar hqq hr, one_mul, mul_one]

include hqstar hqq hr in
lemma fixedSparePermutation_gram (σ : Equiv.Perm I) :
    star (finiteRowPermutation r σ) * finiteRowPermutation r σ = fixedSpareRange r ∧
      finiteRowPermutation r σ * star (finiteRowPermutation r σ) = fixedSpareRange r := by
  constructor
  · rw [finiteRowPermutation_star, finiteRowPermutation_mul q r hqstar hqq hr, inv_mul_cancel]
    rfl
  · rw [finiteRowPermutation_star, finiteRowPermutation_mul q r hqstar hqq hr, mul_inv_cancel]
    rfl

include hqstar hqq hr in
def fixedSparePermutationUnitary (σ : Equiv.Perm I) : unitary E :=
  ⟨relativeUnitaryExtension (fixedSpareRange r) (finiteRowPermutation r σ),
    relativeUnitaryExtension_mem (fixedSpareRange r) _
      (fixedSpareRange_star r) (fixedSpareRange_sq q r hqstar hqq hr)
      (fixedSparePermutation_support q r hqstar hqq hr σ).1
      (fixedSparePermutation_support q r hqstar hqq hr σ).2
      (fixedSparePermutation_gram q r hqstar hqq hr σ).1
      (fixedSparePermutation_gram q r hqstar hqq hr σ).2⟩

include hqstar hqq hr in
lemma fixedSparePermutationUnitary_mul (σ τ : Equiv.Perm I) :
    fixedSparePermutationUnitary q r hqstar hqq hr (σ * τ) =
      fixedSparePermutationUnitary q r hqstar hqq hr σ *
        fixedSparePermutationUnitary q r hqstar hqq hr τ := by
  apply Subtype.ext
  have hσ := (fixedSparePermutation_support q r hqstar hqq hr σ).2
  have hτ := (fixedSparePermutation_support q r hqstar hqq hr τ).1
  have hPP := fixedSpareRange_sq q r hqstar hqq hr
  change finiteRowPermutation r (σ * τ) + (1 - fixedSpareRange r) =
    (finiteRowPermutation r σ + (1 - fixedSpareRange r)) *
      (finiteRowPermutation r τ + (1 - fixedSpareRange r))
  rw [← finiteRowPermutation_mul q r hqstar hqq hr]
  noncomm_ring [hσ, hτ, hPP]

include hqstar hqq hr in
lemma fixedSparePermutationUnitary_involution (σ : Equiv.Perm I) (hσ : σ * σ = 1) :
    star (fixedSparePermutationUnitary q r hqstar hqq hr σ : E) =
      (fixedSparePermutationUnitary q r hqstar hqq hr σ : E) := by
  have hinv : σ⁻¹ = σ := by
    calc
      σ⁻¹ = σ⁻¹ * (σ * σ) := by rw [hσ, mul_one]
      _ = σ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  change star (finiteRowPermutation r σ + (1 - fixedSpareRange r)) = _
  rw [star_add, star_sub, star_one, fixedSpareRange_star r,
    finiteRowPermutation_star, hinv]
  rfl

include hqstar hqq hr in
omit [Fintype I] in
lemma fixedSpareRow_norm_le (i : I) : ‖r i‖ ≤ 1 := by
  have hq : ‖q‖ ≤ 1 := IsStarProjection.norm_le q (isStarProjection_iff'.mpr ⟨hqq, hqstar⟩)
  have he := congrArg norm (hr i i)
  simp only [ite_true, CStarRing.norm_star_mul_self] at he
  nlinarith [norm_nonneg (r i)]

include hqstar hqq hr in
lemma fixedSpareBlock_sub_norm_le (x y : I → E) (C : ℝ) (hC : 0 ≤ C)
    (hxy : ∀ i, ‖x i - y i‖ ≤ C) : ‖fixedSpareBlock r x - fixedSpareBlock r y‖ ≤ C := by
  rw [fixedSpareBlock_sub]
  apply bergOrthogonal_sum_norm_le _ Finset.univ C hC
  · intro i hi j hj hij
    have hz : star (r i) * r j = 0 := by rw [hr, ite_eq_right hij]
    constructor
    · simp only [star_mul, star_star]
      calc
        _ = r i * star (x i - y i) * (star (r i) * r j) * (x j - y j) * star (r j) := by noncomm_ring
        _ = 0 := by rw [hz]; simp
    · simp only [star_mul, star_star]
      calc
        _ = r i * (x i - y i) * (star (r i) * r j) * star (x j - y j) * star (r j) := by noncomm_ring
        _ = 0 := by rw [hz]; simp
  · intro i hi
    calc
      ‖r i * (x i - y i) * star (r i)‖ ≤ ‖r i‖ * ‖x i - y i‖ * ‖r i‖ := by
        simpa only [norm_star] using (norm_mul₃_le (a := r i) (b := x i - y i) (c := star (r i)))
      _ ≤ 1 * C * 1 := by
        gcongr
        · exact fixedSpareRow_norm_le q r hqstar hqq hr i
        · exact hxy i
        · exact fixedSpareRow_norm_le q r hqstar hqq hr i
      _ = C := by ring

include hqstar hqq hr in
lemma fixedSpareDiagonalUnitary_deviation (x : I → unitary E)
    (hx : ∀ i, Commute q (x i : E)) :
    (fixedSpareDiagonalUnitary q r hqstar hqq hr x hx : E) =
      1 + fixedSpareBlock r (fun i => (x i : E) - 1) := by
  rw [← fixedSpareBlock_sub, fixedSpareBlock_one]
  change fixedSpareBlock r (fun i => (x i : E)) + (1 - fixedSpareRange r) = _
  abel

include hqstar hqq hr in
lemma fixedSparePermutationUnitary_mul_row (σ : Equiv.Perm I) (i : I) :
    (fixedSparePermutationUnitary q r hqstar hqq hr σ : E) * r i = r (σ i) := by
  change (finiteRowPermutation r σ + (1 - fixedSpareRange r)) * r i = _
  rw [add_mul, sub_mul, one_mul, fixedSpareRange_mul_row q r hqstar hqq hr,
    sub_self, add_zero, finiteRowPermutation_mul_row q r hqstar hqq hr]

include hqstar hqq hr in
lemma fixedSparePermutation_conjugate_block (σ : Equiv.Perm I) (x : I → E) :
    (fixedSparePermutationUnitary q r hqstar hqq hr σ : E) * fixedSpareBlock r x *
      star (fixedSparePermutationUnitary q r hqstar hqq hr σ : E) =
        fixedSpareBlock r (fun i => x (σ.symm i)) := by
  let c := fixedSparePermutationUnitary q r hqstar hqq hr σ
  have hm (i : I) : (c : E) * r i = r (σ i) :=
    fixedSparePermutationUnitary_mul_row q r hqstar hqq hr σ i
  have hms (i : I) : star (r i) * star (c : E) = star (r (σ i)) := by
    simpa only [star_mul] using congrArg star (hm i)
  change (c : E) * (∑ i, r i * x i * star (r i)) * star (c : E) = _
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, r (σ i) * x i * star (r (σ i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ((c : E) * r i) * x i * (star (r i) * star (c : E)) := by noncomm_ring
        _ = _ := by rw [hm, hms]
    _ = _ := by
      apply Fintype.sum_equiv σ
      intro i
      simp only [Equiv.symm_apply_apply]

end Row

section Cycle
variable (N : ℕ)

def fixedSpareReflection (a : ZMod N) : Equiv.Perm (ZMod N) := Equiv.subLeft a

lemma fixedSpareReflection_sq (a : ZMod N) :
    fixedSpareReflection N a * fixedSpareReflection N a = 1 := by
  ext i
  change a - (a - i) = i
  ring

lemma fixedSpareCycle_factor :
    (Equiv.addRight (1 : ZMod N)) = fixedSpareReflection N 1 * fixedSpareReflection N 0 := by
  ext i
  change i + 1 = 1 - (0 - i)
  ring

/-- The cycle of arbitrary equivalent corners, including its uncovered
complement, has a path whose bound is independent of the number of corners. -/
lemma exists_fixedSpareCycle_path [NeZero N] [Nontrivial E]
    (q : E) (r : ZMod N → E) (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0) :
    ∃ p : Path (1 : unitary E)
        (fixedSparePermutationUnitary q r hqstar hqq hr (Equiv.addRight (1 : ZMod N))),
      ∀ a b, ‖(p a : E) - p b‖ ≤ (4 * Real.pi) * |(a : ℝ) - b| := by
  let a := fixedSparePermutationUnitary q r hqstar hqq hr (fixedSpareReflection N 1)
  let b := fixedSparePermutationUnitary q r hqstar hqq hr (fixedSpareReflection N 0)
  obtain ⟨pa, hpa⟩ := exists_controlled_selfadjoint_unitary_path a
    (fixedSparePermutationUnitary_involution q r hqstar hqq hr _ (fixedSpareReflection_sq N 1))
  obtain ⟨pb, hpb⟩ := exists_controlled_selfadjoint_unitary_path b
    (fixedSparePermutationUnitary_involution q r hqstar hqq hr _ (fixedSpareReflection_sq N 0))
  have hab : fixedSparePermutationUnitary q r hqstar hqq hr (Equiv.addRight (1 : ZMod N)) = a * b := by
    rw [fixedSpareCycle_factor, fixedSparePermutationUnitary_mul]
  let p := (pa.mul pb).cast (one_mul _).symm hab
  refine ⟨p, ?_⟩
  intro x y
  change ‖((pa.mul pb) x : E) - (pa.mul pb) y‖ ≤ _
  simpa only [show 2 * Real.pi + 2 * Real.pi = 4 * Real.pi by ring] using
    unitaryPath_mul_sub_norm_le pa pb (2 * Real.pi) (2 * Real.pi) hpa hpb x y

end Cycle

/-- A near-identity finite stabilization gives a path for the original
unitary. Only the cycle path contributes to the bound; the diagonal does not. -/
lemma exists_controlled_path_of_near_commutator (u d c : unitary E) (L : ℝ)
    (p : Path (1 : unitary E) c)
    (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b|)
    (hnear : ‖((u * (d * c * star d * star c) : unitary E) : E) - 1‖ < 2) :
    ∃ q : Path (1 : unitary E) u,
      ∀ a b, ‖(q a : E) - q b‖ ≤ (Real.pi + 2 * L) * |(a : ℝ) - b| := by
  let k := d * c * star d * star c
  let a : Path (1 : unitary E) (d * c * star d) :=
    (p.map (show Continuous (fun x : unitary E => d * x * star d) by fun_prop)).cast
      (by simp) rfl
  let b : Path (1 : unitary E) (star c) :=
    (p.map (continuous_star : Continuous (star : unitary E → unitary E))).cast (by simp) rfl
  have ha : ∀ s t, ‖(a s : E) - a t‖ ≤ L * |(s : ℝ) - t| := by
    intro s t
    change ‖((d : E) * (p s : E)) * star (d : E) -
      ((d : E) * (p t : E)) * star (d : E)‖ ≤ _
    rw [← sub_mul, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem d.prop),
      ← mul_sub, CStarRing.norm_coe_unitary_mul]
    exact hp s t
  have hb : ∀ s t, ‖(b s : E) - b t‖ ≤ L * |(s : ℝ) - t| := by
    intro s t
    change ‖star (p s : E) - star (p t : E)‖ ≤ _
    rw [← star_sub, norm_star]
    exact hp s t
  let pk : Path (1 : unitary E) k := (a.mul b).cast (by simp) rfl
  have hpk : ∀ s t, ‖(pk s : E) - pk t‖ ≤ (2 * L) * |(s : ℝ) - t| := by
    intro s t
    change ‖((a.mul b) s : E) - (a.mul b) t‖ ≤ _
    simpa only [show L + L = 2 * L by ring] using
      unitaryPath_mul_sub_norm_le a b L L ha hb s t
  let X := u * k
  let px : Path (1 : unitary E) X := Unitary.path 1 X hnear
  let pki : Path (1 : unitary E) (star k) :=
    (pk.map (continuous_star : Continuous (star : unitary E → unitary E))).cast (by simp) rfl
  have hpki : ∀ s t, ‖(pki s : E) - pki t‖ ≤ (2 * L) * |(s : ℝ) - t| := by
    intro s t
    change ‖star (pk s : E) - star (pk t : E)‖ ≤ _
    rw [← star_sub, norm_star]
    exact hpk s t
  have hend : X * star k = u := by simp only [X, mul_assoc, Unitary.mul_star_self, mul_one]
  let q : Path (1 : unitary E) u := (px.mul pki).cast (by simp) hend.symm
  refine ⟨q, ?_⟩
  intro s t
  change ‖((px.mul pki) s : E) - (px.mul pki) t‖ ≤ _
  exact unitaryPath_mul_sub_norm_le px pki Real.pi (2 * L)
    (unitary_shortPath_sub_norm_le 1 X hnear) hpki s t

end WeakPureInfiniteness

end

end OAI
