import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeChains
import OAI.CategoryTheory.Thomason.Gray.RightCylinderPrism

namespace OAI

section

/-! # Literal coefficients of the pasted-globe right cylinder

The formal endpoint and mixed bases are identified with the actual two or
three Finsupp factors of each chain group. Coefficients detect equality and
positivity; the basis vectors are the top chains of the constructed atoms.
-/

namespace Thomason.Construction.PastingGlobeCylinderBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

abbrev Basis (n k p : ℕ) :=
  RightCylinderBasis.Basis (PastingGlobeBasis.Basis n k) p

instance basisDecidableEq (n k p : ℕ) : DecidableEq (Basis n k p) := Classical.decEq _

abbrev Cylinder {n k : ℕ} (hkn : k < n) := rightCylinder (PastingGlobeBasis.complex n k hkn)

/-- The coefficient in either endpoint copy. -/
def endpointCoefficient {n k : ℕ} (hkn : k < n) :
    (p : ℕ) → Bool → PastingGlobeBasis.Basis n k p → (Cylinder hkn).group p → ℤ
  | 0, a, b, x => if a then DFunLike.coe (F := PastingGlobeBasis.Chains n k 0) x.2 b
      else DFunLike.coe (F := PastingGlobeBasis.Chains n k 0) x.1 b
  | p+1, a, b, x =>
      if a then DFunLike.coe (F := PastingGlobeBasis.Chains n k (p+1)) x.2.1 b
      else DFunLike.coe (F := PastingGlobeBasis.Chains n k (p+1)) x.1 b

/-- Coefficients in the actual tuple-of-Finsupp chain group. -/
def coefficient {n k p : ℕ} (hkn : k < n) : Basis n k p → (Cylinder hkn).group p → ℤ
  | .endpoint a b, x => endpointCoefficient hkn p a b x
  | .mixed b, x => DFunLike.coe (F := PastingGlobeBasis.Chains n k _) x.2.2 b

/-- The actual chain vector associated to each formal tensor basis. -/
def vector {n k p : ℕ} (hkn : k < n) : Basis n k p → (Cylinder hkn).group p
  | .endpoint a b =>
    (RightCylinder.endpoint (PastingGlobeBasis.complex n k hkn) a).app p (Finsupp.single b 1)
  | .mixed b => (0, 0, Finsupp.single b 1)

/-- Endpoint maps retain precisely the coefficient in their own copy. -/
theorem coefficient_endpoint {n k p : ℕ} (hkn : k < n) (s t : Bool)
    (b : PastingGlobeBasis.Basis n k p) (x : PastingGlobeBasis.Chains n k p) :
    coefficient hkn (.endpoint t b)
        ((RightCylinder.endpoint (PastingGlobeBasis.complex n k hkn) s).app p x) =
      if t = s then x b else 0 := by
  cases p <;> cases s <;> cases t <;> rfl

/-- The formal tensor coefficients jointly detect chain equality. -/
theorem coefficient_ext {n k p : ℕ} (hkn : k < n) {x y : (Cylinder hkn).group p}
    (h : ∀ b, coefficient hkn b x = coefficient hkn b y) : x = y := by
  cases p with
  | zero =>
    apply Prod.ext
    · apply Finsupp.ext
      intro b
      exact h (.endpoint false b)
    · apply Finsupp.ext
      intro b
      exact h (.endpoint true b)
  | succ p =>
    apply Prod.ext
    · apply Finsupp.ext
      intro b
      exact h (.endpoint false b)
    · apply Prod.ext
      · apply Finsupp.ext
        intro b
        exact h (.endpoint true b)
      · apply Finsupp.ext
        intro b
        exact h (.mixed b)

/-- The actual positive cone is exactly coordinatewise nonnegativity. -/
theorem positive_iff {n k p : ℕ} (hkn : k < n) (x : (Cylinder hkn).group p) :
    x ∈ (Cylinder hkn).positive p ↔ ∀ b, 0 ≤ coefficient hkn b x := by
  cases p with
  | zero =>
    constructor
    · intro hx b
      cases b with
      | endpoint a b => cases a; exact hx.1 b; exact hx.2 b
    · intro hx
      exact ⟨fun b => hx (.endpoint false b), fun b => hx (.endpoint true b)⟩
  | succ p =>
    constructor
    · intro hx b
      cases b with
      | endpoint a b => cases a; exact hx.1 b; exact hx.2.1 b
      | mixed b => exact hx.2.2 b
    · intro hx
      exact ⟨(fun b => hx (.endpoint false b)), (fun b => hx (.endpoint true b)),
        (fun b => hx (.mixed b))⟩

/-- Basis vectors have their literal Kronecker coefficients. -/
theorem coefficient_vector {n k p : ℕ} (hkn : k < n) (b c : Basis n k p) :
    coefficient hkn b (vector hkn c) = if b = c then 1 else 0 := by
  classical
  cases p with
  | zero =>
    cases b with
    | endpoint a b =>
      cases c with
      | endpoint d c =>
        cases a <;> cases d
        all_goals first
          | change (Finsupp.single c (1 : ℤ)) b = _
            simp [Finsupp.single_apply, eq_comm]
          | change (0 : PastingGlobeBasis.Chains n k 0) b = _
            simp
  | succ p =>
    cases b with
    | endpoint a b =>
      cases c with
      | endpoint d c =>
        cases a <;> cases d
        all_goals first
          | change (Finsupp.single c (1 : ℤ)) b = _
            simp [Finsupp.single_apply, eq_comm]
          | change (0 : PastingGlobeBasis.Chains n k (p+1)) b = _
            simp
      | mixed c =>
        cases a <;>
          change (0 : PastingGlobeBasis.Chains n k (p+1)) b = _ <;> simp
    | mixed b =>
      cases c with
      | endpoint d c =>
        cases d <;> change (0 : PastingGlobeBasis.Chains n k p) b = _ <;> simp
      | mixed c =>
        change (Finsupp.single c (1 : ℤ)) b = _
        simp [Finsupp.single_apply, eq_comm]

/-- An actual bounded cell for every formal tensor basis vector. -/
def atom {n k p : ℕ} (hkn : k < n) : Basis n k p → Cell (Cylinder hkn)
  | .endpoint a b => PastingGlobeBasis.endpointAtom hkn a b
  | .mixed b => PastingGlobeBasis.mixedAtom hkn b

/-- The atom's complete top row is exactly its tensor basis vector. -/
theorem atom_top {n k p : ℕ} (hkn : k < n) (b : Basis n k p) (a : Bool) :
    (atom hkn b).table a p = vector hkn b := by
  cases b with
  | endpoint s b => exact PastingGlobeBasis.endpointAtom_top hkn s b a
  | mixed b => exact PastingGlobeBasis.mixedAtom_top hkn b a

/-- Every chosen tensor atom is bounded by the degree of its basis vector. -/
theorem atom_dimension {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    (Cylinder hkn).realization.DimensionLE p (atom hkn b) := by
  cases b with
  | endpoint s b => exact PastingGlobeBasis.endpointAtom_dimension hkn s b
  | mixed b => exact PastingGlobeBasis.mixedAtom_dimension hkn b

end

end Thomason.Construction.PastingGlobeCylinderBasis

end

section

/-! # Ordered atoms of the four-globe interchange complex -/

namespace Thomason.Construction.GridGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

def atom {n k l p : ℕ} (hkl : k < l) (hln : l < n) (b : Basis n k l p) :
    Cell (complex hkl hln) :=
  (inclusion hkl hln b.val.1).realization.toFun
    (PastingGlobeBasis.atom (hkl.trans hln) b.val.2)

theorem atom_top {n k l p : ℕ} (hkl : k < l) (hln : l < n)
    (b : Basis n k l p) (a : Bool) :
    (atom hkl hln b).table a p = Finsupp.single b 1 := by
  change embedApp hkl hln b.val.1 p
    ((PastingGlobeBasis.atom (hkl.trans hln) b.val.2).table a p) = _
  rw [PastingGlobeBasis.atom_top, embedApp_single, embed_self]

theorem atom_above {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (b : Basis n k l p) (hpq : p < q) (a : Bool) :
    (atom hkl hln b).table a q = 0 := by
  change embedApp hkl hln b.val.1 q
    ((PastingGlobeBasis.atom (hkl.trans hln) b.val.2).table a q) = _
  rw [PastingGlobeBasis.atom_above _ _ hpq a]
  exact map_zero _

theorem atom_below {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (b : Basis n k l p) (hqp : q < p) (a : Bool) :
    (atom hkl hln b).table a q = Finsupp.single
      (embed hkl hln b.val.1 (PastingGlobeBasis.embed (hkl.trans hln) b.val.2.val.1
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) 1 := by
  change embedApp hkl hln b.val.1 q
    ((PastingGlobeBasis.atom (hkl.trans hln) b.val.2).table a q) = _
  rw [PastingGlobeBasis.atom_below _ _ hqp a, embedApp_single]

private theorem height_lower_false_false_false {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (hv : p < n ∨ (p = n ∧ false = false))
    (hc : false = false ∨ k < p ∨ (p = k ∧ false = true))
    (hr : false = false ∨ l < p ∨ (p = l ∧ false = true))
    (hqp : q < p) (a : Bool) :
    let b : Basis n k l p := ⟨(false, ⟨(false, false), hv, hc⟩), hr⟩
    if a then height b < height (embed hkl hln false
      (PastingGlobeBasis.embed (hkl.trans hln) false
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩))
    else height (embed hkl hln false
      (PastingGlobeBasis.embed (hkl.trans hln) false
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) < height b := by
  dsimp only
  cases a
  all_goals
    simp_all [height, embed, left, PastingGlobeBasis.embed,
      PastingGlobeBasis.left]
    all_goals omega

private theorem height_lower_false_false_true {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (hv : p < n ∨ (p = n ∧ true = false))
    (hc : false = false ∨ k < p ∨ (p = k ∧ true = true))
    (hr : false = false ∨ l < p ∨ (p = l ∧ true = true))
    (hqp : q < p) (a : Bool) :
    let b : Basis n k l p := ⟨(false, ⟨(false, true), hv, hc⟩), hr⟩
    if a then height b < height (embed hkl hln false
      (PastingGlobeBasis.embed (hkl.trans hln) false
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩))
    else height (embed hkl hln false
      (PastingGlobeBasis.embed (hkl.trans hln) false
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) < height b := by
  dsimp only
  cases a
  all_goals
    simp_all [height, embed, left, PastingGlobeBasis.embed,
      PastingGlobeBasis.left]
    all_goals omega

private theorem height_lower_false_true_false {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (hv : p < n ∨ (p = n ∧ false = false))
    (hc : true = false ∨ k < p ∨ (p = k ∧ false = true))
    (hr : false = false ∨ l < p ∨ (p = l ∧ false = true))
    (hqp : q < p) (a : Bool) :
    let b : Basis n k l p := ⟨(false, ⟨(true, false), hv, hc⟩), hr⟩
    if a then height b < height (embed hkl hln false
      (PastingGlobeBasis.embed (hkl.trans hln) true
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩))
    else height (embed hkl hln false
      (PastingGlobeBasis.embed (hkl.trans hln) true
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) < height b := by
  dsimp only
  cases a
  all_goals
    simp_all [height, embed, left, PastingGlobeBasis.embed,
      PastingGlobeBasis.left, PastingGlobeBasis.right]
    all_goals first | omega | (split_ifs <;> simp_all <;> omega)

private theorem height_lower_false_true_true {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (hv : p < n ∨ (p = n ∧ true = false))
    (hc : true = false ∨ k < p ∨ (p = k ∧ true = true))
    (hr : false = false ∨ l < p ∨ (p = l ∧ true = true))
    (hqp : q < p) (a : Bool) :
    let b : Basis n k l p := ⟨(false, ⟨(true, true), hv, hc⟩), hr⟩
    if a then height b < height (embed hkl hln false
      (PastingGlobeBasis.embed (hkl.trans hln) true
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩))
    else height (embed hkl hln false
      (PastingGlobeBasis.embed (hkl.trans hln) true
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) < height b := by
  dsimp only
  cases a
  all_goals
    simp_all [height, embed, left, PastingGlobeBasis.embed,
      PastingGlobeBasis.left, PastingGlobeBasis.right]
    all_goals first | omega | (split_ifs <;> simp_all <;> omega)

private theorem height_lower_true_false_false {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (hv : p < n ∨ (p = n ∧ false = false))
    (hc : false = false ∨ k < p ∨ (p = k ∧ false = true))
    (hr : true = false ∨ l < p ∨ (p = l ∧ false = true))
    (hqp : q < p) (a : Bool) :
    let b : Basis n k l p := ⟨(true, ⟨(false, false), hv, hc⟩), hr⟩
    if a then height b < height (embed hkl hln true
      (PastingGlobeBasis.embed (hkl.trans hln) false
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩))
    else height (embed hkl hln true
      (PastingGlobeBasis.embed (hkl.trans hln) false
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) < height b := by
  dsimp only
  cases a
  all_goals
    simp_all [height, embed, targetBasis, left, PastingGlobeBasis.embed,
      PastingGlobeBasis.left]
    all_goals first | omega | (split_ifs <;> simp_all <;> omega)

private theorem height_lower_true_false_true {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (hv : p < n ∨ (p = n ∧ true = false))
    (hc : false = false ∨ k < p ∨ (p = k ∧ true = true))
    (hr : true = false ∨ l < p ∨ (p = l ∧ true = true))
    (hqp : q < p) (a : Bool) :
    let b : Basis n k l p := ⟨(true, ⟨(false, true), hv, hc⟩), hr⟩
    if a then height b < height (embed hkl hln true
      (PastingGlobeBasis.embed (hkl.trans hln) false
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩))
    else height (embed hkl hln true
      (PastingGlobeBasis.embed (hkl.trans hln) false
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) < height b := by
  dsimp only
  cases a
  all_goals
    simp_all [height, embed, targetBasis, left, PastingGlobeBasis.embed,
      PastingGlobeBasis.left]
    all_goals first | omega | (split_ifs <;> simp_all <;> omega)

private theorem height_lower_true_true_false {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (hv : p < n ∨ (p = n ∧ false = false))
    (hc : true = false ∨ k < p ∨ (p = k ∧ false = true))
    (hr : true = false ∨ l < p ∨ (p = l ∧ false = true))
    (hqp : q < p) (a : Bool) :
    let b : Basis n k l p := ⟨(true, ⟨(true, false), hv, hc⟩), hr⟩
    if a then height b < height (embed hkl hln true
      (PastingGlobeBasis.embed (hkl.trans hln) true
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩))
    else height (embed hkl hln true
      (PastingGlobeBasis.embed (hkl.trans hln) true
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) < height b := by
  have hpl : l ≤ p := by
    rcases hr with h | h | ⟨h, _⟩
    · cases h
    · exact h.le
    · exact h.ge
  have hpn : p ≤ n := by rcases hv with h | ⟨h, _⟩ <;> omega
  have hpk : ¬ p < k := by omega
  have hpl' : ¬ p < l := by omega
  dsimp only
  by_cases hqk : q < k
  · have hql : q < l := hqk.trans hkl
    cases a <;> simp [height, embed, left, PastingGlobeBasis.embed,
      PastingGlobeBasis.left, PastingGlobeBasis.right, hqk, hql] <;> omega
  · by_cases hqke : q = k
    · subst q
      have hkl' : ¬ l < k := by omega
      cases a <;> simp [height, embed, left, PastingGlobeBasis.embed,
        PastingGlobeBasis.left, PastingGlobeBasis.right, hkl] <;> omega
    · by_cases hql : q < l
      · cases a <;> simp [height, embed, left, PastingGlobeBasis.embed, PastingGlobeBasis.right, hqk, hqke, hql] <;> omega
      · by_cases hqle : q = l
        · subst q
          cases a <;> simp [height, embed, targetBasis, left, PastingGlobeBasis.embed, PastingGlobeBasis.right, hqk, hqke] <;> omega
        · cases a <;> simp [height, embed, PastingGlobeBasis.embed, PastingGlobeBasis.right, hqk, hqke, hql, hqle] <;> omega

private theorem height_lower_true_true_true {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (hv : p < n ∨ (p = n ∧ true = false))
    (hc : true = false ∨ k < p ∨ (p = k ∧ true = true))
    (hr : true = false ∨ l < p ∨ (p = l ∧ true = true))
    (hqp : q < p) (a : Bool) :
    let b : Basis n k l p := ⟨(true, ⟨(true, true), hv, hc⟩), hr⟩
    if a then height b < height (embed hkl hln true
      (PastingGlobeBasis.embed (hkl.trans hln) true
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩))
    else height (embed hkl hln true
      (PastingGlobeBasis.embed (hkl.trans hln) true
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) < height b := by
  have hpl : l ≤ p := by
    rcases hr with h | h | ⟨h, _⟩
    · cases h
    · exact h.le
    · exact h.ge
  have hpn : p ≤ n := by rcases hv with h | ⟨h, _⟩ <;> omega
  have hpk : ¬ p < k := by omega
  have hpl' : ¬ p < l := by omega
  dsimp only
  by_cases hqk : q < k
  · have hql : q < l := hqk.trans hkl
    cases a <;> simp [height, embed, left, PastingGlobeBasis.embed,
      PastingGlobeBasis.left, PastingGlobeBasis.right, hqk, hql, hpk] <;> omega
  · by_cases hqke : q = k
    · subst q
      have hkl' : ¬ l < k := by omega
      cases a <;> simp [height, embed, left, PastingGlobeBasis.embed,
        PastingGlobeBasis.left, PastingGlobeBasis.right, hkl, hpk] <;> omega
    · by_cases hql : q < l
      · cases a <;> simp [height, embed, left, PastingGlobeBasis.embed, PastingGlobeBasis.right, hqk, hqke, hql, hpk] <;> omega
      · by_cases hqle : q = l
        · subst q
          cases a <;> simp [height, embed, targetBasis, left, PastingGlobeBasis.embed, PastingGlobeBasis.right, hqk, hqke, hpk] <;> omega
        · cases a <;> simp [height, embed, PastingGlobeBasis.embed, PastingGlobeBasis.right, hqk, hqke, hql, hqle, hpk] <;> omega

theorem height_lower {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (b : Basis n k l p) (hqp : q < p) (a : Bool) :
    if a then height b < height (embed hkl hln b.val.1
      (PastingGlobeBasis.embed (hkl.trans hln) b.val.2.val.1
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩))
    else height (embed hkl hln b.val.1
      (PastingGlobeBasis.embed (hkl.trans hln) b.val.2.val.1
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩)) < height b := by
  rcases b with ⟨⟨row, ⟨⟨col, pole⟩, hv, hc⟩⟩, hr⟩
  cases row <;> cases col <;> cases pole

  · exact height_lower_false_false_false hkl hln hv hc hr hqp a

  · exact height_lower_false_false_true hkl hln hv hc hr hqp a

  · exact height_lower_false_true_false hkl hln hv hc hr hqp a

  · exact height_lower_false_true_true hkl hln hv hc hr hqp a

  · exact height_lower_true_false_false hkl hln hv hc hr hqp a

  · exact height_lower_true_false_true hkl hln hv hc hr hqp a

  · exact height_lower_true_true_false hkl hln hv hc hr hqp a

  · exact height_lower_true_true_true hkl hln hv hc hr hqp a

theorem atom_sideHeight {n k l p q : ℕ} (hkl : k < l) (hln : l < n)
    (b : Basis n k l p) (hqp : q < p) (a : Bool) (c : Basis n k l q)
    (hc : DFunLike.coe (F := Chains n k l q) ((atom hkl hln b).table a q) c ≠ 0) :
    if a then height b < height c else height c < height b := by
  rw [atom_below hkl hln b hqp a] at hc
  have he : c = embed hkl hln b.val.1
      (PastingGlobeBasis.embed (hkl.trans hln) b.val.2.val.1
        ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩) := by
    by_contra he
    exact hc (Finsupp.single_eq_of_ne he)
  subst c
  exact height_lower hkl hln b hqp a

def orderedAtomBasis {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    OrderedAtomBasis (complex hkl hln) where
  Index p := Basis n k l p
  coordinates _ := AddEquiv.refl _
  positive_iff _ _ := Iff.rfl
  augmentation := by
    change ∀ x : Chains n k l 0, weight n k l 0 x = x.sum (fun _ z => z)
    intro x
    simp [weight, Finsupp.linearCombination_apply]
  atom _ := atom hkl hln
  atom_top _ := atom_top hkl hln
  atom_above _ b q h a := atom_above hkl hln b h a
  height _ := height
  disjoint {p q r} b c hrp hrq hbc e := by
    by_cases he : DFunLike.coe (F := Chains n k l r) ((atom hkl hln b).table false r) e = 0
    · exact Or.inl he
    · right
      by_contra hf
      have h1 := atom_sideHeight hkl hln b hrp false e he
      have h2 := atom_sideHeight hkl hln c hrq true e hf
      simp only [Bool.false_eq_true, ite_false, ite_true] at h1 h2
      exact (lt_irrefl _) (h2.trans (h1.trans_le hbc))

theorem orderedAtomBasis_sideHeight {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    (orderedAtomBasis hkl hln).SideHeight :=
  fun _ b _ h a c hc => atom_sideHeight hkl hln b h a c hc

def cylinderOrderedAtomBasis {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    OrderedAtomBasis (rightCylinder (complex hkl hln)) :=
  (orderedAtomBasis hkl hln).cylinderOrderedAtomBasis (orderedAtomBasis_sideHeight hkl hln)

end
end Thomason.Construction.GridGlobeBasis

end

section

/-! # The strict order of the literal cylinder differential

The signed endpoint and mixed incidences are checked on the actual tuple
chain groups. Thus every nonzero boundary coefficient points strictly in
the expected direction for the previously constructed integer height.
-/

namespace Thomason.Construction.PastingGlobeCylinderBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- Endpoint boundaries stay in their chosen endpoint copy. -/
theorem endpoint_boundary_coefficient {n k p : ℕ} (hkn : k < n) (s t : Bool)
    (b : PastingGlobeBasis.Basis n k (p+1)) (c : PastingGlobeBasis.Basis n k p) :
    coefficient hkn (.endpoint t c)
        ((Cylinder hkn).differential p (vector hkn (.endpoint s b))) =
      if t = s then PastingGlobeBasis.boundary hkn b c else 0 := by
  let f := RightCylinder.endpoint (PastingGlobeBasis.complex n k hkn) s
  have hf := f.differential p
    (show (PastingGlobeBasis.complex n k hkn).group (p+1) from Finsupp.single b 1)
  calc
    _ = coefficient hkn (.endpoint t c) (f.app p
        ((PastingGlobeBasis.complex n k hkn).differential p
          (show (PastingGlobeBasis.complex n k hkn).group (p+1) from Finsupp.single b 1))) :=
      congrArg (coefficient hkn (.endpoint t c)) hf.symm
    _ = if t = s then
        DFunLike.coe (F := PastingGlobeBasis.Chains n k p)
          ((PastingGlobeBasis.complex n k hkn).differential p
            (show (PastingGlobeBasis.complex n k hkn).group (p+1) from Finsupp.single b 1)) c
        else 0 := coefficient_endpoint hkn s t c _
    _ = _ := by
      change (if t = s then PastingGlobeBasis.differential hkn p (Finsupp.single b 1) c
        else 0) = _
      simp

/-- An endpoint boundary has no mixed component. -/
theorem endpoint_mixed_boundary_coefficient {n k p : ℕ} (hkn : k < n) (s : Bool)
    (b : PastingGlobeBasis.Basis n k (p+2)) (c : PastingGlobeBasis.Basis n k p) :
    coefficient hkn (.mixed c)
        ((Cylinder hkn).differential (p+1) (vector hkn (.endpoint s b))) = 0 := by
  cases s <;> change (0 : PastingGlobeBasis.Chains n k p) c = 0 <;> rfl

/-- The endpoint part of a mixed boundary has the right-tensor sign. -/
theorem mixed_endpoint_boundary_coefficient {n k p : ℕ} (hkn : k < n) (t : Bool)
    (b c : PastingGlobeBasis.Basis n k p) :
    coefficient hkn (.endpoint t c)
        ((Cylinder hkn).differential p (vector hkn (.mixed b))) =
      (if t then (-1 : ℤ)^p else -((-1 : ℤ)^p)) * (if b = c then 1 else 0) := by
  classical
  cases p with
  | zero =>
    cases t
    · change (0 : ℤ) - (Finsupp.single b (1 : ℤ)) c = _
      by_cases hbc : b = c <;> simp [hbc]
    · change (0 : ℤ) + (Finsupp.single b (1 : ℤ)) c = _
      simp [Finsupp.single_apply]
  | succ p =>
    cases t
    · change (0 : ℤ) - (-1 : ℤ)^(p+1) • (Finsupp.single b (1 : ℤ)) c = _
      by_cases hbc : b = c <;> simp [hbc]
    · change (0 : ℤ) + (-1 : ℤ)^(p+1) • (Finsupp.single b (1 : ℤ)) c = _
      simp [Finsupp.single_apply]

/-- The mixed part retains the original boundary coefficients. -/
theorem mixed_boundary_coefficient {n k p : ℕ} (hkn : k < n)
    (b : PastingGlobeBasis.Basis n k (p+1)) (c : PastingGlobeBasis.Basis n k p) :
    coefficient hkn (.mixed c)
        ((Cylinder hkn).differential (p+1) (vector hkn (.mixed b))) =
      PastingGlobeBasis.boundary hkn b c := by
  change PastingGlobeBasis.differential hkn p (Finsupp.single b 1) c = _
  simp

/-- The actual finite strong height, on all tensor degrees at once. -/
def height {n k p : ℕ} (b : Basis n k p) : ℤ :=
  RightCylinderBasis.height (fun _ => PastingGlobeBasis.height) b

private theorem endpoint_height_lt {n k p q : ℕ} (s t : Bool)
    (b : PastingGlobeBasis.Basis n k p) (c : PastingGlobeBasis.Basis n k q)
    (h : PastingGlobeBasis.height b < PastingGlobeBasis.height c) :
    height (.endpoint s b) < height (.endpoint t c) := by
  simp only [height, RightCylinderBasis.height]
  split_ifs <;> omega

/-- All negative coefficients decrease height and all positive coefficients
increase it, for the literal directed-complex differential. -/
theorem differential_height {n k p : ℕ} (hkn : k < n) (a : Bool)
    (b : Basis n k (p+1)) (c : Basis n k p)
    (hc : if a then 0 < coefficient hkn c ((Cylinder hkn).differential p (vector hkn b))
      else coefficient hkn c ((Cylinder hkn).differential p (vector hkn b)) < 0) :
    if a then height b < height c else height c < height b := by
  cases b with
  | endpoint s b =>
    cases p with
    | zero =>
      cases c with
      | endpoint t c =>
        rw [endpoint_boundary_coefficient] at hc
        by_cases hts : t = s
        · simp only [hts, ite_true] at hc
          cases a with
          | false =>
            exact endpoint_height_lt _ _ _ _
              (PastingGlobeBasis.height_lt_of_boundary_neg hkn b c hc)
          | true =>
            exact endpoint_height_lt _ _ _ _
              (PastingGlobeBasis.height_lt_of_boundary_pos hkn b c hc)
        · simp [hts] at hc
    | succ p =>
      cases c with
      | endpoint t c =>
        rw [endpoint_boundary_coefficient] at hc
        by_cases hts : t = s
        · simp only [hts, ite_true] at hc
          cases a with
          | false =>
            exact endpoint_height_lt _ _ _ _
              (PastingGlobeBasis.height_lt_of_boundary_neg hkn b c hc)
          | true =>
            exact endpoint_height_lt _ _ _ _
              (PastingGlobeBasis.height_lt_of_boundary_pos hkn b c hc)
        · simp [hts] at hc
      | mixed c =>
        have hz := endpoint_mixed_boundary_coefficient hkn s b c
        cases a
        · exact False.elim ((ne_of_lt hc) hz)
        · exact False.elim ((ne_of_gt hc) hz)
  | mixed b =>
    cases p with
    | zero =>
      cases c with
      | endpoint t c =>
        rw [mixed_endpoint_boundary_coefficient] at hc
        by_cases hbc : b = c
        · subst c
          cases a <;> cases t <;> simp [height, RightCylinderBasis.height,
            RightCylinderBasis.sourceEndpoint] at hc ⊢
        · simp [hbc] at hc
    | succ p =>
      cases c with
      | endpoint t c =>
        rw [mixed_endpoint_boundary_coefficient] at hc
        by_cases hbc : b = c
        · subst c
          cases a <;> cases t <;> cases hb : p.bodd <;>
            simp [height, RightCylinderBasis.height, RightCylinderBasis.sourceEndpoint,
              RightCylinder.sign_bodd, Nat.mod_two_of_bodd, hb] at hc ⊢
        · simp [hbc] at hc
      | mixed c =>
        rw [mixed_boundary_coefficient] at hc
        cases a with
        | false =>
          have hh := PastingGlobeBasis.height_lt_of_boundary_neg hkn b c hc
          simp only [Bool.false_eq_true, ite_false, height, RightCylinderBasis.height]
          omega
        | true =>
          have hh := PastingGlobeBasis.height_lt_of_boundary_pos hkn b c hc
          simp only [ite_true, height, RightCylinderBasis.height]
          omega

end

end Thomason.Construction.PastingGlobeCylinderBasis

end

section

/-! # The full signed tables of the actual cylinder atoms

The source and target rows below each atom's top degree have disjoint
supports. Positivity and the boundary equation therefore recover each row
as the corresponding signed part, giving the concrete unital atom data.
-/

namespace Thomason.Construction.PastingGlobeCylinderBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

private theorem endpoint_atom_coefficient {n k p q : ℕ} (hkn : k < n)
    (s : Bool) (b : PastingGlobeBasis.Basis n k p) (a t : Bool)
    (c : PastingGlobeBasis.Basis n k q) :
    coefficient hkn (.endpoint t c) ((atom hkn (.endpoint s b)).table a q) =
      if t = s then DFunLike.coe (F := PastingGlobeBasis.Chains n k q)
        ((PastingGlobeBasis.atom hkn b).table a q) c else 0 :=
  coefficient_endpoint hkn s t c _

private theorem mixed_atom_endpoint_coefficient {n k p q : ℕ} (hkn : k < n)
    (b : PastingGlobeBasis.Basis n k p) (a t : Bool)
    (c : PastingGlobeBasis.Basis n k q) :
    coefficient hkn (.endpoint t c) ((atom hkn (.mixed b)).table a q) =
      if t = RightCylinder.prismSide q a then
        DFunLike.coe (F := PastingGlobeBasis.Chains n k q)
          ((PastingGlobeBasis.atom hkn b).table a q) c else 0 := by
  cases q with
  | zero => cases a <;> cases t <;> rfl
  | succ q =>
    change coefficient hkn (.endpoint t c)
      (if RightCylinder.prismSide (q+1) a then
        (0, (PastingGlobeBasis.atom hkn b).table a (q+1),
          (PastingGlobeBasis.atom hkn b).table a q)
       else ((PastingGlobeBasis.atom hkn b).table a (q+1), 0,
          (PastingGlobeBasis.atom hkn b).table a q)) = _
    cases hs : RightCylinder.prismSide (q+1) a <;> cases t <;> rfl

private theorem mixed_atom_mixed_coefficient {n k p q : ℕ} (hkn : k < n)
    (b : PastingGlobeBasis.Basis n k p) (a : Bool)
    (c : PastingGlobeBasis.Basis n k q) :
    coefficient hkn (.mixed c) ((atom hkn (.mixed b)).table a (q+1)) =
      DFunLike.coe (F := PastingGlobeBasis.Chains n k q)
        ((PastingGlobeBasis.atom hkn b).table a q) c := by
  change coefficient hkn (.mixed c)
      (if RightCylinder.prismSide (q+1) a then
        (0, (PastingGlobeBasis.atom hkn b).table a (q+1),
          (PastingGlobeBasis.atom hkn b).table a q)
       else ((PastingGlobeBasis.atom hkn b).table a (q+1), 0,
          (PastingGlobeBasis.atom hkn b).table a q)) = _
  split_ifs <;> rfl

/-- The two lower rows of every endpoint or mixed atom are disjoint. -/
theorem atom_lower_disjoint {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (hqp : q < p) (c : Basis n k q) :
    coefficient hkn c ((atom hkn b).table false q) = 0 ∨
      coefficient hkn c ((atom hkn b).table true q) = 0 := by
  cases b with
  | endpoint s b =>
    cases c with
    | endpoint t c =>
      rw [endpoint_atom_coefficient, endpoint_atom_coefficient]
      by_cases hts : t = s
      · simpa only [hts, ite_true] using PastingGlobeBasis.atom_lower_disjoint hkn b hqp c
      · simp [hts]
    | mixed c =>
      left
      cases s <;> rfl
  | mixed b =>
    cases c with
    | endpoint t c =>
      rw [mixed_atom_endpoint_coefficient, mixed_atom_endpoint_coefficient]
      have hs : RightCylinder.prismSide q false ≠ RightCylinder.prismSide q true := by
        simp only [RightCylinder.prismSide, Bool.false_eq_true, ite_false, ite_true]
        cases q.bodd <;> decide
      by_cases hf : t = RightCylinder.prismSide q false
      · right
        have ht : t ≠ RightCylinder.prismSide q true := fun h => hs (hf.symm.trans h)
        simp [ht]
      · left
        simp [hf]
    | mixed c =>
      rw [mixed_atom_mixed_coefficient, mixed_atom_mixed_coefficient]
      exact PastingGlobeBasis.atom_lower_disjoint hkn b (Nat.lt_of_succ_lt_succ hqp) c

private theorem coefficient_sub {n k q : ℕ} (hkn : k < n) (b : Basis n k q)
    (x y : (Cylinder hkn).group q) :
    coefficient hkn b (x-y) = coefficient hkn b x - coefficient hkn b y := by
  cases q with
  | zero => cases b with | endpoint a b => cases a <;> rfl
  | succ q =>
    cases b with
    | endpoint a b => cases a <;> rfl
    | mixed b => rfl

/-- The complete downward-recursive signed-part formula holds for every
constructed cylinder atom. -/
theorem atom_signed_table {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (hqp : q < p) (a : Bool) (c : Basis n k q) :
    coefficient hkn c ((atom hkn b).table a q) = max 0
      (if a then coefficient hkn c
          ((Cylinder hkn).differential q ((atom hkn b).table a (q+1)))
       else -coefficient hkn c
          ((Cylinder hkn).differential q ((atom hkn b).table a (q+1)))) := by
  have hp := (positive_iff hkn _).mp ((atom hkn b).positive false q) c
  have ht := (positive_iff hkn _).mp ((atom hkn b).positive true q) c
  have hd := atom_lower_disjoint hkn b hqp c
  rw [(atom hkn b).boundary, coefficient_sub]
  cases a <;> rcases hd with hd | hd <;> simp only [hd, sub_zero, zero_sub,
    neg_neg, Bool.false_eq_true, ite_false, ite_true] <;> omega

end

end Thomason.Construction.PastingGlobeCylinderBasis

end

end OAI
