import OAI.Analysis.OInfinity.NegativeBinary
import OAI.Analysis.OInfinity.JointRohlinWitness

namespace OAI

/-! # Comparison of stabilized canonical rows on their common corner

The finite binary encodings are constructed inside the two closed row
algebras. Restriction to the product of their units gives commuting full
binary rows, so the proved connected binary comparison applies. The two
complementary corners are retained; this is not yet the global half-flip.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma zeroCornerRow_castSucc (q a b : E) :
    ∀ n (i : Fin n), zeroCornerRow q a b n i.castSucc = a ^ (i : ℕ) * b := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [zeroCornerRow, Fin.castSucc_zero, Fin.cases_zero, Fin.val_zero,
        pow_zero, one_mul]
    · change a * zeroCornerRow q a b n j.castSucc = a ^ ((j : ℕ) + 1) * b
      rw [ih, pow_succ', mul_assoc]

/-- Multiplication by a commuting projection is a genuine nonunital star hom. -/
def commutingProjectionRestriction (C : StarSubalgebra ℂ E) (q : E)
    (hq : star q = q) (hqq : q * q = q) (hc : ∀ x : C, Commute (x : E) q) :
    C →⋆ₙₐ[ℂ] E where
  toFun x := (x : E) * q
  map_zero' := zero_mul q
  map_add' x y := add_mul _ _ _
  map_smul' r x := smul_mul_assoc r (x : E) q
  map_mul' x y := by
    change (x : E) * (y : E) * q = ((x : E) * q) * ((y : E) * q)
    calc
      _ = (x : E) * (y : E) * (q * q) := by rw [hqq]
      _ = (x : E) * ((y : E) * q) * q := by noncomm_ring
      _ = (x : E) * (q * (y : E)) * q := by rw [(hc y).eq]
      _ = _ := by noncomm_ring
  map_star' x := by
    change (star (x : E)) * q = star ((x : E) * q)
    rw [star_mul, hq]
    exact (hc (star x)).eq

lemma nonunital_map_pow_mul {A : Type*} [CStarAlgebra A] (f : A →⋆ₙₐ[ℂ] E)
    (a b : A) (n : ℕ) : f (a ^ n * b) = f a ^ n * f b := by
  induction n with
  | zero => simp only [pow_zero, one_mul]
  | succ n ih => rw [pow_succ', mul_assoc, map_mul, ih, pow_succ', mul_assoc]

lemma canonicalTailProjection_coe (C : StarSubalgebra ℂ E) [IsClosed (C : Set E)] (s : ℕ → C) (n : ℕ) :
    ((canonicalTailProjection s n : C) : E) =
      canonicalTailProjection (fun i => (s i : E)) n := by
  change C.subtype (1 - ∑ i : Fin n, s i * star (s i)) = _
  simp only [map_sub, map_one, map_sum, map_mul, map_star, StarSubalgebra.subtype_apply, canonicalTailProjection]

lemma canonicalNegativeRow_coe (C : StarSubalgebra ℂ E) [IsClosed (C : Set E)] (s : ℕ → C) (i : ℕ) :
    ((canonicalNegativeRow s i : C) : E) =
      canonicalNegativeRow (fun j => (s j : E)) i := by
  change C.subtype (s 1 * s i * star (s 1) + s (i + 2) * canonicalTailProjection s 2) = _
  simp only [map_add, map_mul, map_star, StarSubalgebra.subtype_apply, canonicalTailProjection_coe,
    canonicalNegativeRow, canonicalNegativeProjection]

lemma exists_relative_binary_power_conjugacy
    (q : E) (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (a b : Fin 2 → E)
    (ha : ∀ i j, star (a i) * a j = if i = j then q else 0)
    (hb : ∀ i j, star (b i) * b j = if i = j then q else 0)
    (has : (∑ i, a i * star (a i)) = q)
    (hbs : (∑ i, b i * star (b i)) = q)
    (hab : bergRowsCommute a b) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * (1 - q) = 1 - q ∧ (1 - q) * (u : E) = 1 - q ∧
      ∀ i ≤ m, ‖(u : E) * (a 0 ^ i * a 1) * star (u : E) - (b 0 ^ i * b 1)‖ < ε := by
  obtain ⟨u, hu, hur, hul, hclose⟩ :=
    exists_relative_binary_leaf_conjugacy q hq hqq hq0 a b ha hb has hbs hab (m + 1) ε hε
  refine ⟨u, hu, hur, hul, fun i hi => ?_⟩
  have h := hclose (Fin.castSucc (⟨i, by omega⟩ : Fin (m + 1)))
  simpa only [zeroCornerRow_castSucc, Fin.val_mk] using h

/-- The product of the two first-tail units is nonzero: it contains the
range of the literal isometry `s₁t₁`. -/
lemma canonicalCommonCorner_nonzero [Nontrivial E]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) :
    canonicalTailProjection s 1 * canonicalTailProjection t 1 ≠ 0 := by
  let p := canonicalTailProjection s 1
  let q := canonicalTailProjection t 1
  have hsp : p * s 1 = s 1 := by
    simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_mul_generator s hs 1 1
  have htq : q * t 1 = t 1 := by
    simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_mul_generator t ht 1 1
  have hsq : Commute (s 1) q :=
    (canonicalTailProjection_commutes t (s 1)
      (fun j => ⟨(hc 1 j).1.symm, (hc 1 j).2.symm⟩) 1).symm
  have hunit : star (s 1 * t 1) * (s 1 * t 1) = 1 := by
    calc
      _ = star (t 1) * (star (s 1) * s 1) * t 1 := by rw [star_mul]; noncomm_ring
      _ = 1 := by simp only [hs, ht, ite_true, mul_one]
  have hsupport : (p * q) * (s 1 * t 1) = s 1 * t 1 := by
    calc
      _ = p * (q * s 1) * t 1 := by noncomm_ring
      _ = s 1 * (q * t 1) := by rw [← hsq.eq, ← mul_assoc, hsp]; noncomm_ring
      _ = _ := by rw [htq]
  intro hz
  change p * q = 0 at hz
  have hr : s 1 * t 1 = 0 := by simpa only [hz, zero_mul] using hsupport.symm
  have h10 : (1 : E) = 0 := by simpa only [hr, mul_zero] using hunit.symm
  exact one_ne_zero h10

/-- Restrict two full binary rows in commuting algebras to the product
of their units. Both the Gram relations and cross commutation are exact. -/
lemma restrict_commuting_binary_rows
    (C D : StarSubalgebra ℂ E) [IsClosed (C : Set E)] [IsClosed (D : Set E)]
    (hc : ∀ x : C, ∀ y : D, Commute (x : E) (y : E))
    (p : C) (q : D) (hp : star p = p) (hpp : p * p = p)
    (hq : star q = q) (hqq : q * q = q)
    (a : Fin 2 → C) (b : Fin 2 → D)
    (ha : ∀ i j, star (a i) * a j = if i = j then p else 0)
    (hb : ∀ i j, star (b i) * b j = if i = j then q else 0)
    (has : (∑ i, a i * star (a i)) = p)
    (hbs : (∑ i, b i * star (b i)) = q) :
    let f := commutingProjectionRestriction C (q : E)
      (congrArg (fun z : D => (z : E)) hq) (congrArg (fun z : D => (z : E)) hqq) (fun x => hc x q)
    let g := commutingProjectionRestriction D (p : E)
      (congrArg (fun z : C => (z : E)) hp) (congrArg (fun z : C => (z : E)) hpp) (fun y => (hc p y).symm)
    (∀ i j, star (f (a i)) * f (a j) = if i = j then (p : E) * (q : E) else 0) ∧
    (∀ i j, star (g (b i)) * g (b j) = if i = j then (p : E) * (q : E) else 0) ∧
    (∑ i, f (a i) * star (f (a i))) = (p : E) * (q : E) ∧
    (∑ i, g (b i) * star (g (b i))) = (p : E) * (q : E) ∧
    bergRowsCommute (fun i => f (a i)) (fun i => g (b i)) := by
  intro f g
  have hfg (i j : Fin 2) : star (f (a i)) * f (a j) =
      if i = j then (p : E) * (q : E) else 0 := by
    rw [← map_star, ← map_mul, ha]
    split_ifs
    · rfl
    · exact map_zero f
  have hgg (i j : Fin 2) : star (g (b i)) * g (b j) =
      if i = j then (p : E) * (q : E) else 0 := by
    rw [← map_star, ← map_mul, hb]
    split_ifs
    · exact (hc p q).eq.symm
    · exact map_zero g
  have hfs : (∑ i, f (a i) * star (f (a i))) = (p : E) * (q : E) := by
    simp only [← map_star, ← map_mul, ← map_sum, has]
    rfl
  have hgs : (∑ i, g (b i) * star (g (b i))) = (p : E) * (q : E) := by
    simp only [← map_star, ← map_mul, ← map_sum, hbs]
    exact (hc p q).eq.symm
  refine ⟨hfg, hgg, hfs, hgs, fun i j => ?_⟩
  have hap : Commute (a i : E) (p : E) := by
    have hl := finiteRow_left_support p a hp hpp ha has i
    have hr := finiteRow_right_support p a hp hpp ha i
    change (a i : E) * (p : E) = (p : E) * (a i : E)
    exact congrArg (fun z : C => (z : E)) (hr.trans hl.symm)
  have hbq : Commute (q : E) (b j : E) := by
    have hl := finiteRow_left_support q b hq hqq hb hbs j
    have hr := finiteRow_right_support q b hq hqq hb j
    change (q : E) * (b j : E) = (b j : E) * (q : E)
    exact congrArg (fun z : D => (z : E)) (hl.trans hr.symm)
  constructor
  · change Commute ((a i : E) * (q : E)) ((b j : E) * (p : E))
    exact ((hc (a i) (b j)).mul_right hap).mul_left
      (hbq.mul_right (hc p q).symm)
  · change Commute ((a i : E) * (q : E)) (star ((b j : E) * (p : E)))
    have hpe : star (p : E) = (p : E) := congrArg (fun z : C => (z : E)) hp
    have hqe : star (q : E) = (q : E) := congrArg (fun z : D => (z : E)) hq
    rw [star_mul, hpe]
    have hqb : Commute (q : E) (star (b j : E)) := by
      change (q : E) * star (b j : E) = star (b j : E) * (q : E)
      have h := congrArg star hbq.eq
      simpa only [star_mul, hqe] using h.symm
    exact (hap.mul_right (hc (a i) (star (b j)))).mul_left
      ((hc p q).symm.mul_right hqb)

/-- Actual finite stabilized-row comparison on the common corner. The
unitary is connected to one and fixes the complementary identity exactly. -/
lemma exists_canonicalNegative_common_comparison [Nontrivial E]
    (C D : StarSubalgebra ℂ E) [IsClosed (C : Set E)] [IsClosed (D : Set E)]
    (hc : ∀ x : C, ∀ y : D, Commute (x : E) (y : E))
    (s : ℕ → C) (t : ℕ → D)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let S : ℕ → E := fun i => s i
    let T : ℕ → E := fun i => t i
    let P := canonicalTailProjection S 1
    let Q := canonicalTailProjection T 1
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * (1 - P * Q) = 1 - P * Q ∧
      (1 - P * Q) * (u : E) = 1 - P * Q ∧
      ∀ i ≤ m, ‖(u : E) * (canonicalNegativeRow S i * Q) * star (u : E) -
        canonicalNegativeRow T i * P‖ < ε := by
  intro S T P Q
  let p := canonicalTailProjection s 1
  let q := canonicalTailProjection t 1
  have hp : star p = p := canonicalTailProjection_star s 1
  have hpp : p * p = p := canonicalTailProjection_idempotent s hs 1
  have hq : star q = q := canonicalTailProjection_star t 1
  have hqq : q * q = q := canonicalTailProjection_idempotent t ht 1
  have hpc : (p : E) = P := canonicalTailProjection_coe C s 1
  have hqc : (q : E) = Q := canonicalTailProjection_coe D t 1
  have hPQ : Commute P Q := by simpa only [hpc, hqc] using hc p q
  have hP : star P = P := by
    have h : star (p : E) = (p : E) := congrArg (fun z : C => (z : E)) hp
    simpa only [hpc] using h
  have hQ : star Q = Q := by
    have h : star (q : E) = (q : E) := congrArg (fun z : D => (z : E)) hq
    simpa only [hqc] using h
  have hPP : P * P = P := by
    have h : (p : E) * (p : E) = (p : E) := congrArg (fun z : C => (z : E)) hpp
    simpa only [hpc] using h
  have hQQ : Q * Q = Q := by
    have h : (q : E) * (q : E) = (q : E) := congrArg (fun z : D => (z : E)) hqq
    simpa only [hqc] using h
  have hPQstar : star (P * Q) = P * Q := by rw [star_mul, hP, hQ, hPQ.eq]
  have hPQsq : (P * Q) * (P * Q) = P * Q := by
    calc
      _ = P * (Q * P) * Q := by noncomm_ring
      _ = P * Q := by rw [← hPQ.eq, ← mul_assoc, hPP, mul_assoc, hQQ]
  have hS (i j : ℕ) : star (S i) * S j = if i = j then 1 else 0 := by
    have h := congrArg C.subtype (hs i j)
    simp only [map_mul, map_star, apply_ite, map_one, map_zero,
      StarSubalgebra.subtype_apply] at h
    change star (s i : E) * (s j : E) = _
    simpa only [apply_ite] using h
  have hT (i j : ℕ) : star (T i) * T j = if i = j then 1 else 0 := by
    have h := congrArg D.subtype (ht i j)
    simp only [map_mul, map_star, apply_ite, map_one, map_zero,
      StarSubalgebra.subtype_apply] at h
    change star (t i : E) * (t j : E) = _
    simpa only [apply_ite] using h
  have hST : bergRowsCommute S T := fun i j => ⟨hc (s i) (t j), hc (s i) (star (t j))⟩
  have hPQ0 : P * Q ≠ 0 := canonicalCommonCorner_nonzero S T hS hT hST
  obtain ⟨a0, a1, ha0, ha1, haa, has, hae⟩ := exists_canonicalNegative_binary_encoding s hs m
  obtain ⟨b0, b1, hb0, hb1, hbb, hbs, hbe⟩ := exists_canonicalNegative_binary_encoding t ht m
  let a : Fin 2 → C := ![a0, a1]
  let b : Fin 2 → D := ![b0, b1]
  have haa' : star a1 * a0 = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star haa
  have hbb' : star b1 * b0 = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hbb
  have ha : ∀ i j, star (a i) * a j = if i = j then p else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [a, p, ha0, ha1, haa, haa']
  have hb : ∀ i j, star (b i) * b j = if i = j then q else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [b, q, hb0, hb1, hbb, hbb']
  have has' : (∑ i, a i * star (a i)) = p := by simpa only [Fin.sum_univ_two, a,
    Matrix.cons_val_zero, Matrix.cons_val_one] using has
  have hbs' : (∑ i, b i * star (b i)) = q := by simpa only [Fin.sum_univ_two, b,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hbs
  let f := commutingProjectionRestriction C (q : E)
    (congrArg (fun z : D => (z : E)) hq) (congrArg (fun z : D => (z : E)) hqq) (fun x => hc x q)
  let g := commutingProjectionRestriction D (p : E)
    (congrArg (fun z : C => (z : E)) hp) (congrArg (fun z : C => (z : E)) hpp) (fun y => (hc p y).symm)
  obtain ⟨hf, hg, hfs, hgs, hfg⟩ := restrict_commuting_binary_rows C D hc p q hp hpp hq hqq
    a b ha hb has' hbs'
  simp only [hpc, hqc] at hf hg hfs hgs
  obtain ⟨u, hu, hur, hul, hclose⟩ := exists_relative_binary_power_conjugacy
    (P * Q) hPQstar hPQsq hPQ0 (fun i => f (a i)) (fun i => g (b i))
    hf hg hfs hgs hfg m ε hε
  refine ⟨u, hu, hur, hul, fun i hi => ?_⟩
  have heA : f (a 0) ^ i * f (a 1) = canonicalNegativeRow S i * Q := by
    rw [← nonunital_map_pow_mul]
    change f (a0 ^ i * a1) = _
    rw [hae i hi]
    change ((canonicalNegativeRow s i : C) : E) * (q : E) = _
    rw [canonicalNegativeRow_coe, hqc]
  have heB : g (b 0) ^ i * g (b 1) = canonicalNegativeRow T i * P := by
    rw [← nonunital_map_pow_mul]
    change g (b0 ^ i * b1) = _
    rw [hbe i hi]
    change ((canonicalNegativeRow t i : D) : E) * (p : E) = _
    rw [canonicalNegativeRow_coe, hpc]
  simpa only [heA, heB] using hclose i hi

/-- The closed unital algebra generated by the complete canonical row. -/
def closedCanonicalRowAlgebra (s : ℕ → E) : StarSubalgebra ℂ E :=
  (StarAlgebra.adjoin ℂ (Set.range s)).topologicalClosure

instance closedCanonicalRowAlgebra_isClosed (s : ℕ → E) :
    IsClosed (closedCanonicalRowAlgebra s : Set E) :=
  StarSubalgebra.isClosed_topologicalClosure _

lemma mem_closedCanonicalRowAlgebra (s : ℕ → E) (i : ℕ) :
    s i ∈ closedCanonicalRowAlgebra s :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)

lemma closedCanonicalRowAlgebras_commute (s t : ℕ → E) (hc : bergRowsCommute s t)
    (x : closedCanonicalRowAlgebra s) (y : closedCanonicalRowAlgebra t) :
    Commute (x : E) (y : E) := by
  have hD : closedCanonicalRowAlgebra t ≤ StarSubalgebra.centralizer ℂ (Set.range s) := by
    apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨j, rfl⟩
      apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
      rintro _ ⟨i, rfl⟩
      refine ⟨(hc i j).1.eq, ?_⟩
      simpa only [star_star] using (hc i j).2.star_star.eq
    · exact Set.isClosed_centralizer _
  have hxc : (x : E) ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (Set.range s) : Set E) :=
    StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer ℂ (Set.range s) x.property
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hxc) y (hD y.property)).1.symm

/-- No chosen binary encodings or commutant assumptions remain in this
application to the original two commuting canonical rows. -/
lemma exists_canonicalNegative_comparison [Nontrivial E]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let P := canonicalTailProjection s 1
    let Q := canonicalTailProjection t 1
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * (1 - P * Q) = 1 - P * Q ∧
      (1 - P * Q) * (u : E) = 1 - P * Q ∧
      ∀ i ≤ m, ‖(u : E) * (canonicalNegativeRow s i * Q) * star (u : E) -
        canonicalNegativeRow t i * P‖ < ε := by
  let S : ℕ → closedCanonicalRowAlgebra s := fun i => ⟨s i, mem_closedCanonicalRowAlgebra s i⟩
  let T : ℕ → closedCanonicalRowAlgebra t := fun i => ⟨t i, mem_closedCanonicalRowAlgebra t i⟩
  have hS (i j : ℕ) : star (S i) * S j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      apply Subtype.ext
      change star (s i) * s j = 1
      simpa only [ite_eq_left hij] using hs i j
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (s i) * s j = 0
      simpa only [ite_eq_right hij] using hs i j
  have hT (i j : ℕ) : star (T i) * T j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      apply Subtype.ext
      change star (t i) * t j = 1
      simpa only [ite_eq_left hij] using ht i j
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (t i) * t j = 0
      simpa only [ite_eq_right hij] using ht i j
  exact exists_canonicalNegative_common_comparison
    (closedCanonicalRowAlgebra s) (closedCanonicalRowAlgebra t)
    (closedCanonicalRowAlgebras_commute s t hc) S T hS hT m ε hε

end WeakPureInfiniteness

end

end OAI
