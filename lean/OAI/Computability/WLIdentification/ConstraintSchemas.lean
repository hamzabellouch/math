import OAI.Computability.WLIdentification.RowOffsets

namespace OAI

namespace WLIdentification

structure ComparisonSchemas (r : ℕ) (P E : Type) where
  pointIndex : P ↪ ℕ
  edgeIndex : E ↪ ℕ
  dimension : P → ℕ
  dimension_bound : ∀ p, dimension p = 1 ∨ dimension p = 2
  source : E → P
  target : E → P
  domain : E → Fin r → Finset Bool
  domain_nonempty : ∀ e i, (domain e i).Nonempty
  mapping : (e : E) → (i : Fin r) → {a // a ∈ domain e i} → Bool
  mapping_injective : ∀ e i, Function.Injective (mapping e i)
  left : (e : E) → (Fin (dimension (source e)) → Bit) →ₗ[Bit] Bit
  right : (e : E) → (Fin (dimension (target e)) → Bit) →ₗ[Bit] Bit

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

abbrev InternalType (_S : ComparisonSchemas r P E) (n : ℕ) := P ⊕ (E × Fin (n + 1))
abbrev Link (_S : ComparisonSchemas r P E) (n : ℕ) := E ⊕ ((E × Fin n) ⊕ E)

def first (n : ℕ) : S.Link n → S.InternalType n
  | .inl e => .inl (S.source e)
  | .inr (.inl (e, i)) => .inr (e, i.castSucc)
  | .inr (.inr e) => .inr (e, Fin.last n)

def second (n : ℕ) : S.Link n → S.InternalType n
  | .inl e => .inr (e, 0)
  | .inr (.inl (e, i)) => .inr (e, i.succ)
  | .inr (.inr e) => .inl (S.target e)

def wire (n : ℕ) : S.Link n → E
  | .inl e => e
  | .inr (.inl (e, _)) => e
  | .inr (.inr e) => e

def layoutDimension (n : ℕ) : S.InternalType n → ℕ
  | .inl p => S.dimension p
  | .inr _ => 1

def layoutLabels (n : ℕ) : S.InternalType n → Fin r → Finset Bool
  | .inl _, _ => Finset.univ
  | .inr (e, _), i => S.domain e i

def firstLabel (n : ℕ) (l : S.Link n) (i : Fin r) :
    {a // a ∈ S.domain (S.wire n l) i} → {a // a ∈ S.layoutLabels n (S.first n l) i} := by
  cases l with
  | inl e => exact fun a => ⟨a.val, Finset.mem_univ _⟩
  | inr l => cases l with
    | inl p => exact id
    | inr e => exact id

def secondLabel (n : ℕ) (l : S.Link n) (i : Fin r) :
    {a // a ∈ S.domain (S.wire n l) i} → {a // a ∈ S.layoutLabels n (S.second n l) i} := by
  cases l with
  | inl e => exact id
  | inr l => cases l with
    | inl p => exact id
    | inr e => exact fun a => ⟨S.mapping e i a, Finset.mem_univ _⟩

def firstForm (n : ℕ) (l : S.Link n) :
    (Fin (S.layoutDimension n (S.first n l)) → Bit) →ₗ[Bit] Bit := by
  cases l with
  | inl e => exact S.left e
  | inr l => cases l with
    | inl p => exact (LinearMap.proj (0 : Fin 1))
    | inr e => exact (LinearMap.proj (0 : Fin 1))

def secondForm (n : ℕ) (l : S.Link n) :
    (Fin (S.layoutDimension n (S.second n l)) → Bit) →ₗ[Bit] Bit := by
  cases l with
  | inl e => exact (LinearMap.proj (0 : Fin 1))
  | inr l => cases l with
    | inl p => exact (LinearMap.proj (0 : Fin 1))
    | inr e => exact S.right e

def layout (n : ℕ) : RingLayout r (S.InternalType n) (S.Link n) where
  typeIndex := NaturalCode.sum S.pointIndex (NaturalCode.prod S.edgeIndex (NaturalCode.fin _))
  linkIndex := NaturalCode.sum S.edgeIndex (NaturalCode.sum (NaturalCode.prod S.edgeIndex (NaturalCode.fin _)) S.edgeIndex)
  dimension := S.layoutDimension n
  dimension_bound t := by cases t with
    | inl p => exact S.dimension_bound p
    | inr p => exact Or.inl rfl
  labels := S.layoutLabels n
  labels_nonempty t i := by cases t with
    | inl p => exact ⟨false, Finset.mem_univ _⟩
    | inr p => exact S.domain_nonempty p.1 i
  first := S.first n
  second := S.second n
  endpoints_ne l := by
    cases l with
    | inl e => intro h; cases h
    | inr l => cases l with
      | inl p =>
        intro h
        have hi := congrArg (fun t : S.InternalType n =>
          match t with | .inl _ => 0 | .inr p => p.2.val) h
        change p.2.val = p.2.val + 1 at hi
        omega
      | inr e => intro h; cases h
  internal_endpoint l := by
    cases l with
    | inl e => exact Or.inr rfl
    | inr l => cases l <;> exact Or.inl rfl
  matchLabels l i := S.domain (S.wire n l) i
  matchLabels_nonempty l i := S.domain_nonempty (S.wire n l) i
  firstLabel := S.firstLabel n
  secondLabel := S.secondLabel n
  firstLabel_injective l i := by
    cases l with
    | inl e =>
      intro a b h
      apply Subtype.ext
      exact congrArg (fun x : {a // a ∈ S.layoutLabels n (S.first n (.inl e)) i} => x.val) h
    | inr l => cases l <;> exact Function.injective_id
  secondLabel_injective l i := by
    cases l with
    | inl e => exact Function.injective_id
    | inr l => cases l with
      | inl p => exact Function.injective_id
      | inr e => exact fun a b h => S.mapping_injective e i (congrArg Subtype.val h)
  firstForm := S.firstForm n
  secondForm := S.secondForm n

end ComparisonSchemas

namespace CycleRows.RowSum
variable {r : ℕ} {A : Fin r → Type} {V : Type} [AddCommMonoid V]

protected theorem sum {I : Type} (s : Finset I)
    (h : I → ((i : Fin r) → A i) → V) (hh : ∀ j ∈ s, RowSum A V (h j)) :
    RowSum A V (fun a => ∑ j ∈ s, h j a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (RowSum.zero (A := A) (V := V))
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (hh j (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hh i (Finset.mem_insert_of_mem hi)))

protected theorem pi {J : Type} {W : J → Type} [∀ j, AddCommMonoid (W j)]
    (h : ((i : Fin r) → A i) → (j : J) → W j)
    (hh : ∀ j, RowSum A (W j) (fun a => h a j)) : RowSum A ((j : J) → W j) h := by
  choose f hf using hh
  refine ⟨fun i u v j => f j i u v, ?_⟩
  intro a
  funext j
  simpa only [Finset.sum_apply] using hf j a

end CycleRows.RowSum

namespace WireAlgebra

def prefixSum {n : ℕ} (c : Fin n → Bit) (j : Fin (n + 1)) : Bit :=
  ∑ i : Fin n, if i.val < j.val then c i else 0

@[simp]
theorem prefix_zero {n : ℕ} (c : Fin n → Bit) : prefixSum c 0 = 0 := by
  simp [prefixSum]

@[simp]
theorem prefix_last {n : ℕ} (c : Fin n → Bit) : prefixSum c (Fin.last n) = ∑ i, c i := by
  simp [prefixSum]

theorem prefix_succ {n : ℕ} (c : Fin n → Bit) (j : Fin n) :
    prefixSum c j.succ = prefixSum c j.castSucc + c j := by
  have hi (i : Fin n) : (if i.val < j.val + 1 then c i else 0) =
      (if i.val < j.val then c i else 0) + (if i = j then c i else 0) := by
    by_cases h : i.val < j.val
    · have hne : i ≠ j := fun hh => by subst i; omega
      simp [h, hne, show i.val < j.val + 1 by omega]
    · by_cases he : i = j
      · subst i; simp
      · have hn : ¬i.val < j.val + 1 := by
          intro hh
          exact he (Fin.ext (by omega))
        simp [h, he, hn]
  simp only [prefixSum, Fin.val_succ, Fin.val_castSucc, hi, Finset.sum_add_distrib]
  simp

theorem sum_adjacent {n : ℕ} (h : Fin (n + 1) → Bit) :
    ∑ i : Fin n, (h i.castSucc + h i.succ) = h 0 + h (Fin.last n) := by
  have ha := Fin.sum_univ_castSucc h
  have hb := Fin.sum_univ_succ h
  have hab : (∑ i : Fin n, h i.castSucc) + h (Fin.last n) =
      h 0 + ∑ i : Fin n, h i.succ := ha.symm.trans hb
  rw [Finset.sum_add_distrib]
  calc
    _ = ((∑ i : Fin n, h i.castSucc) + (∑ i : Fin n, h i.succ)) +
        (h (Fin.last n) + h (Fin.last n)) := by
      rw [CharTwo.add_self_eq_zero, add_zero]
    _ = ((∑ i : Fin n, h i.castSucc) + h (Fin.last n)) +
        (∑ i : Fin n, h i.succ) + h (Fin.last n) := by abel
    _ = _ := by
      rw [hab]
      simp only [add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- A wire's internal scalars cancel; the converse uses explicit prefixSum sums. -/
theorem chain_lifting {n : ℕ} (left right first last : Bit) (middle : Fin n → Bit) :
    (∃ h : Fin (n + 1) → Bit,
      left + h 0 = first ∧
      (∀ i, h i.castSucc + h i.succ = middle i) ∧
      h (Fin.last n) + right = last) ↔
    left + right = first + (∑ i, middle i) + last := by
  constructor
  · rintro ⟨h, hfirst, hmiddle, hlast⟩
    rw [← hfirst, ← hlast, ← funext hmiddle, sum_adjacent]
    symm
    calc
      _ = left + right + (h 0 + h 0) + (h (Fin.last n) + h (Fin.last n)) := by abel
      _ = _ := by simp only [CharTwo.add_self_eq_zero, add_zero]
  · intro he
    refine ⟨fun j => left + first + prefixSum middle j, ?_, ?_, ?_⟩
    · simp only [prefix_zero, add_zero]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · intro i
      dsimp only
      rw [prefix_succ]
      calc
        _ = ((left + first + prefixSum middle i.castSucc) +
          (left + first + prefixSum middle i.castSucc)) + middle i := by abel
        _ = middle i := by rw [CharTwo.add_self_eq_zero, zero_add]
    · dsimp only
      rw [prefix_last]
      calc
        _ = (left + right) + first + (∑ i, middle i) := by abel
        _ = last := by
          rw [he]
          calc
            _ = (first + first) + ((∑ i, middle i) + (∑ i, middle i)) + last := by abel
            _ = last := by simp only [CharTwo.add_self_eq_zero, zero_add]

end WireAlgebra

namespace WireAlgebra

theorem prefix_equations {n : ℕ} (left right first last : Bit) (middle : Fin n → Bit)
    (he : left + right = first + (∑ i, middle i) + last) :
    let h := fun j => left + first + prefixSum middle j
    (left + h 0 = first) ∧ (∀ i, h i.castSucc + h i.succ = middle i) ∧
      (h (Fin.last n) + right = last) := by
  dsimp only
  constructor
  · simp only [prefix_zero, add_zero]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  constructor
  · intro i
    rw [prefix_succ]
    calc
      _ = ((left + first + prefixSum middle i.castSucc) +
        (left + first + prefixSum middle i.castSucc)) + middle i := by abel
      _ = middle i := by rw [CharTwo.add_self_eq_zero, zero_add]
  · rw [prefix_last]
    calc
      _ = (left + right) + first + (∑ i, middle i) := by abel
      _ = last := by
        rw [he]
        calc
          _ = (first + first) + ((∑ i, middle i) + (∑ i, middle i)) + last := by abel
          _ = last := by simp only [CharTwo.add_self_eq_zero, zero_add]

end WireAlgebra

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

abbrev Address (_S : ComparisonSchemas r P E) :=
  Fin r → {a : Bool // a ∈ (Finset.univ : Finset Bool)}
abbrev DomainAddress (e : E) := (i : Fin r) → {a // a ∈ S.domain e i}

def sourceAddress (e : E) (a : S.DomainAddress e) : S.Address :=
  fun i => ⟨(a i).val, Finset.mem_univ _⟩
def targetAddress (e : E) (a : S.DomainAddress e) : S.Address :=
  fun i => ⟨S.mapping e i (a i), Finset.mem_univ _⟩

def firstShift (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E)
    (a : S.DomainAddress e) : Bit := (S.layout n).linkShift beta (.inl e) a

def middleShift (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E) (j : Fin n)
    (a : S.DomainAddress e) : Bit := (S.layout n).linkShift beta (.inr (.inl (e, j))) a

def lastShift (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E)
    (a : S.DomainAddress e) : Bit := (S.layout n).linkShift beta (.inr (.inr e)) a

def wireShift (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E)
    (a : S.DomainAddress e) : Bit :=
  S.firstShift n beta e a + (∑ j, S.middleShift n beta e j a) + S.lastShift n beta e a

theorem wireShift_rowSum (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E) :
    CycleRows.RowSum (fun i => {a // a ∈ S.domain e i}) Bit (S.wireShift n beta e) := by
  exact ((S.layout n).linkShift_rowSum beta (.inl e)).add
    (CycleRows.RowSum.sum Finset.univ (S.middleShift n beta e)
      (fun j _ => (S.layout n).linkShift_rowSum beta (.inr (.inl (e, j))))) |>.add
        ((S.layout n).linkShift_rowSum beta (.inr (.inr e)))

variable [Fintype P] [Fintype E]

theorem offsets_iff_real_rowSums (hr : 3 ≤ r) (n : ℕ)
    (beta : (S.layout n).Block → Bit) :
    (∃ z, ((S.layout n).affine (by omega)).Solves beta z) ↔
    ∃ h : (p : P) → S.Address → Fin (S.dimension p) → Bit,
      (∀ p, CycleRows.RowSum (fun _ : Fin r => {a : Bool // a ∈ (Finset.univ : Finset Bool)})
        (Fin (S.dimension p) → Bit) (h p)) ∧
      ∀ e (a : S.DomainAddress e),
        S.left e (h (S.source e) (S.sourceAddress e a)) +
        S.right e (h (S.target e) (S.targetAddress e a)) = S.wireShift n beta e a := by
  rw [(S.layout n).offsets_iff_rowSums hr beta]
  constructor
  · rintro ⟨h, hs, he⟩
    refine ⟨fun p => h (.inl p), fun p => hs (.inl p), ?_⟩
    intro e a
    apply (WireAlgebra.chain_lifting _ _ _ _ _).mp
    refine ⟨fun j => h (.inr (e, j)) a (0 : Fin 1), ?_, ?_, ?_⟩
    · exact he (.inl e) a
    · intro j
      exact he (.inr (.inl (e, j))) a
    · exact he (.inr (.inr e)) a
  · rintro ⟨h, hs, he⟩
    let g (e : E) (j : Fin (n + 1)) (a : S.DomainAddress e) : Bit :=
      S.left e (h (S.source e) (S.sourceAddress e a)) + S.firstShift n beta e a +
        WireAlgebra.prefixSum (fun i => S.middleShift n beta e i a) j
    let q : (t : S.InternalType n) → (S.layout n).Address t →
        Fin ((S.layout n).dimension t) → Bit := fun t => match t with
      | .inl p => h p
      | .inr (e, j) => fun a _ => g e j a
    have hg (e : E) (a : S.DomainAddress e) :
        (S.left e (h (S.source e) (S.sourceAddress e a)) + g e 0 a = S.firstShift n beta e a) ∧
        (∀ j, g e j.castSucc a + g e j.succ a = S.middleShift n beta e j a) ∧
        (g e (Fin.last n) a + S.right e (h (S.target e) (S.targetAddress e a)) = S.lastShift n beta e a) :=
      WireAlgebra.prefix_equations _ _ _ _ _ (he e a)
    refine ⟨q, ?_, ?_⟩
    · intro t
      cases t with
      | inl p => exact hs p
      | inr p =>
        apply CycleRows.RowSum.pi
        intro j
        have hf := ((hs (S.source p.1)).map (S.left p.1).toAddMonoidHom).pullback
          (fun i (a : {a // a ∈ S.domain p.1 i}) => (⟨a.val, Finset.mem_univ _⟩ : {b : Bool // b ∈ (Finset.univ : Finset Bool)}))
        have hb := (S.layout n).linkShift_rowSum beta (.inl p.1)
        have hc : CycleRows.RowSum (fun i => {a // a ∈ S.domain p.1 i}) Bit
            (fun a => WireAlgebra.prefixSum (fun i => S.middleShift n beta p.1 i a) p.2) := by
          apply CycleRows.RowSum.sum
          intro i _
          by_cases hi : i.val < p.2.val
          · simpa only [hi, ite_true, middleShift, RingLayout.Match, layout, wire] using
              (S.layout n).linkShift_rowSum beta (.inr (.inl (p.1, i)))
          · simpa only [hi, ite_false] using
              (CycleRows.RowSum.zero (A := fun i => {a // a ∈ S.domain p.1 i}) (V := Bit))
        exact (hf.add hb).add hc
    · intro l a
      cases l with
      | inl e => exact (hg e a).1
      | inr l => cases l with
        | inl p => exact (hg p.1 a).2.1 p.2
        | inr e => exact (hg e a).2.2

end ComparisonSchemas

end WLIdentification

end OAI
