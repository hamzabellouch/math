import OAI.Computability.MeanPayoff.Probability

namespace OAI

section
namespace MeanPayoff

abbrev Vec (V : Type) := V → ℤ

def shift {V : Type} (p : Vec V) (c : ℤ) : Vec V := fun i => p i + c

def clip {V : Type} (a b p : Vec V) : Vec V :=
  fun i => min (b i) (max (a i) (p i))

def InBox {V : Type} (a b p : Vec V) : Prop := a ≤ p ∧ p ≤ b

def Subsolution {V : Type} (F : Vec V → Vec V) (a b y : Vec V) : Prop :=
  InBox a b y ∧ ∀ i, a i < y i → y i ≤ F y i

def Supersolution {V : Type} (F : Vec V → Vec V) (a b z : Vec V) : Prop :=
  InBox a b z ∧ ∀ i, z i < b i → F z i ≤ z i

def subSupport {V : Type} (a y : Vec V) : Set V := {i | a i < y i}
def superSupport {V : Type} (b z : Vec V) : Set V := {i | z i < b i}

structure OperatorLaws {V : Type} (F : Vec V → Vec V) : Prop where
  mono : Monotone F
  translation : ∀ p c, F (shift p c) = shift (F p) c

def transformed (G : Game) (e : Fin G.m) : ℤ := (G.n + 1 : ℤ) * G.weight e + 1

def outgoing (G : Game) (v : Fin G.n) : Finset (Fin G.m) :=
  Finset.univ.filter (fun e => G.tail e = v)

theorem outgoing_nonempty (G : Game) (v : Fin G.n) : (outgoing G v).Nonempty := by
  obtain ⟨e, he⟩ := G.total v
  exact ⟨e, by simp [outgoing, he]⟩

def operator (G : Game) (p : Vec (Fin G.n)) : Vec (Fin G.n) := fun i =>
  if G.maxOwner i then
    (outgoing G i).sup' (outgoing_nonempty G i) (fun e => transformed G e + p (G.head e))
  else
    (outgoing G i).inf' (outgoing_nonempty G i) (fun e => transformed G e + p (G.head e))

theorem operator_laws (G : Game) : OperatorLaws (operator G) := by
  constructor
  · intro p q hpq i
    simp only [operator]
    split
    · apply (Finset.sup'_le_iff _ _).2
      intro e he
      exact le_trans (add_le_add_right (hpq (G.head e)) _)
        (Finset.le_sup' (fun e => transformed G e + q (G.head e)) he)
    · apply (Finset.le_inf'_iff _ _).2
      intro e he
      exact le_trans (Finset.inf'_le (fun e => transformed G e + p (G.head e)) he)
        (add_le_add_right (hpq (G.head e)) _)
  · intro p c
    funext i
    simp only [operator, shift]
    split
    · simpa only [add_assoc] using
        (Finset.sup'_add (outgoing G i)
          (fun e => transformed G e + p (G.head e)) c (outgoing_nonempty G i)).symm
    · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_inf' (outgoing_nonempty G i)
        (fun e => transformed G e + p (G.head e))
      obtain ⟨f, hf, hfq⟩ := Finset.exists_mem_eq_inf' (outgoing_nonempty G i)
        (fun e => transformed G e + (p (G.head e) + c))
      have hlo := Finset.inf'_le (fun e => transformed G e + p (G.head e)) hf
      have hup := Finset.inf'_le (fun e => transformed G e + (p (G.head e) + c)) he
      rw [heq] at hlo ⊢
      rw [hfq] at hup ⊢
      omega

section Projections
variable {V : Type} {F : Vec V → Vec V}

theorem subsolution_raise_floor (laws : OperatorLaws F) {a b a' y : Vec V}
    (hy : Subsolution F a b y) (haa' : a ≤ a') (ha'b : a' ≤ b) :
    Subsolution F a' b (fun i => max (y i) (a' i)) ∧
    subSupport a' (fun i => max (y i) (a' i)) ⊆ subSupport a y := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i; exact le_max_right _ _
  · intro i; exact max_le (hy.1.2 i) (ha'b i)
  · intro i hi
    have hiy : a' i < y i := by simpa using hi
    have heq : max (y i) (a' i) = y i := max_eq_left (le_of_lt hiy)
    dsimp only
    rw [heq]
    exact le_trans (hy.2 i (lt_of_le_of_lt (haa' i) hiy))
      (laws.mono (fun j => le_max_left (y j) (a' j)) i)
  · intro i hi
    have hiy : a' i < y i := by simpa [subSupport] using hi
    exact lt_of_le_of_lt (haa' i) hiy

theorem supersolution_lower_ceiling (laws : OperatorLaws F) {a b b' z : Vec V}
    (hz : Supersolution F a b z) (hab' : a ≤ b') (hb'b : b' ≤ b) :
    Supersolution F a b' (fun i => min (z i) (b' i)) ∧
    superSupport b' (fun i => min (z i) (b' i)) ⊆ superSupport b z := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i; exact le_min (hz.1.1 i) (hab' i)
  · intro i; exact min_le_right _ _
  · intro i hi
    have hiz : z i < b' i := by simpa using hi
    have heq : min (z i) (b' i) = z i := min_eq_left (le_of_lt hiz)
    dsimp only
    rw [heq]
    exact le_trans (laws.mono (fun j => min_le_left (z j) (b' j)) i)
      (hz.2 i (lt_of_lt_of_le hiz (hb'b i)))
  · intro i hi
    have hiz : z i < b' i := by simpa [superSupport] using hi
    exact lt_of_lt_of_le hiz (hb'b i)

def centerSub (y q : Vec V) (d A : ℤ) : Vec V :=
  fun i => max (y i - d + A) (q i - A)

def centerSuper (z q : Vec V) (e A : ℤ) : Vec V :=
  fun i => min (z i + e - A) (q i + A)

theorem centerSub_support (y q : Vec V) (d A : ℤ) :
    subSupport (fun i => q i - A) (centerSub y q d A) =
      {i | d - 2 * A < y i - q i} := by
  ext i
  simp only [subSupport, centerSub, Set.mem_ofPred_eq, lt_max_iff, lt_self_iff_false,
    or_false]
  omega

theorem centerSuper_support (z q : Vec V) (e A : ℤ) :
    superSupport (fun i => q i + A) (centerSuper z q e A) =
      {i | e - 2 * A < q i - z i} := by
  ext i
  simp only [superSupport, centerSuper, Set.mem_ofPred_eq, min_lt_iff,
    lt_self_iff_false, or_false]
  omega

theorem centered_subsolution (laws : OperatorLaws F) {a b y q : Vec V} {d A : ℤ}
    (hy : Subsolution F a b y) (hq : InBox a b q)
    (hA : 0 < A) (hdev : ∀ i, y i - q i ≤ d) (hd : 2 * A ≤ d) :
    Subsolution F (fun i => q i - A) (fun i => q i + A) (centerSub y q d A) ∧
    subSupport (fun i => q i - A) (centerSub y q d A) ⊆ subSupport a y := by
  have hs : subSupport (fun i => q i - A) (centerSub y q d A) ⊆
      subSupport a y := by
    rw [centerSub_support]
    intro i hi
    have hqi : a i ≤ q i := hq.1 i
    change a i < y i
    change d - 2 * A < y i - q i at hi
    omega
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hs⟩
  · intro i; exact le_max_right _ _
  · intro i
    change max (y i - d + A) (q i - A) ≤ q i + A
    apply max_le
    · have := hdev i; omega
    · omega
  · intro i hi
    have hiy : y i ≤ F y i := hy.2 i (hs hi)
    have hlarge : q i - A < y i - d + A := by
      simpa only [centerSub, lt_max_iff, lt_self_iff_false, or_false] using hi
    have heq : centerSub y q d A i = y i - d + A :=
      max_eq_left (le_of_lt hlarge)
    rw [heq]
    have hmono : F (shift y (-d + A)) i ≤ F (centerSub y q d A) i := by
      apply laws.mono
      intro j
      have := le_max_left (y j - d + A) (q j - A)
      simp [shift, centerSub, sub_eq_add_neg, add_assoc]
    rw [laws.translation] at hmono
    simp only [shift] at hmono
    omega

theorem centered_supersolution (laws : OperatorLaws F) {a b z q : Vec V} {e A : ℤ}
    (hz : Supersolution F a b z) (hq : InBox a b q)
    (hA : 0 < A) (hdev : ∀ i, q i - z i ≤ e) (he : 2 * A ≤ e) :
    Supersolution F (fun i => q i - A) (fun i => q i + A) (centerSuper z q e A) ∧
    superSupport (fun i => q i + A) (centerSuper z q e A) ⊆ superSupport b z := by
  have hs : superSupport (fun i => q i + A) (centerSuper z q e A) ⊆
      superSupport b z := by
    rw [centerSuper_support]
    intro i hi
    have hqi : q i ≤ b i := hq.2 i
    change z i < b i
    change e - 2 * A < q i - z i at hi
    omega
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hs⟩
  · intro i
    change q i - A ≤ min (z i + e - A) (q i + A)
    apply le_min
    · have := hdev i; omega
    · omega
  · intro i; exact min_le_right _ _
  · intro i hi
    have hiz : F z i ≤ z i := hz.2 i (hs hi)
    have hsmall : z i + e - A < q i + A := by
      simpa only [centerSuper, min_lt_iff, lt_self_iff_false, or_false] using hi
    have heq : centerSuper z q e A i = z i + e - A :=
      min_eq_left (le_of_lt hsmall)
    rw [heq]
    have hmono : F (centerSuper z q e A) i ≤ F (shift z (e - A)) i := by
      apply laws.mono
      intro j
      have := min_le_left (z j + e - A) (q j + A)
      simp [shift, centerSuper, sub_eq_add_neg, add_assoc]
    rw [laws.translation] at hmono
    simp only [shift] at hmono
    omega

end Projections

def averageStep {V : Type} (a b r₁ r₂ : Vec V) : Vec V :=
  clip a b (fun i => (r₁ i + r₂ i) / 2)

theorem high_deviation_step {V : Type} {a b y q r₁ r₂ : Vec V} {d D : ℤ}
    (hyb : y ≤ b) (hD : 0 < D) (hd : 2 * D ≤ d)
    (hdev : ∀ i, y i - q i ≤ d)
    (hr₁ : ∀ i, q i - D ≤ r₁ i)
    (hr₂ : centerSub y q d D ≤ r₂) :
    ∀ i, y i - averageStep a b r₁ r₂ i ≤ d := by
  intro i
  have hq := hdev i
  have h1 := hr₁ i
  have h2 := le_trans (le_max_left (y i - d + D) (q i - D)) (hr₂ i)
  have hb : y i ≤ b i := hyb i
  have havg : y i - d ≤ (r₁ i + r₂ i) / 2 := by omega
  have hclip : y i - d ≤ min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) :=
    le_min (by omega) (le_trans havg (le_max_right _ _))
  change y i - min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) ≤ d
  omega

theorem high_bad_step {V : Type} {a b y q r₁ r₂ : Vec V} {d D : ℤ}
    (hyb : y ≤ b) (hD : 0 < D) (hd : 2 * D ≤ d)
    (hr₁ : centerSub y q d D ≤ r₁) (hr₂ : centerSub y q d D ≤ r₂) :
    ∀ i, y i - averageStep a b r₁ r₂ i ≤ d - D := by
  intro i
  have h1 := le_trans (le_max_left (y i - d + D) (q i - D)) (hr₁ i)
  have h2 := le_trans (le_max_left (y i - d + D) (q i - D)) (hr₂ i)
  have hb : y i ≤ b i := hyb i
  have havg : y i - d + D ≤ (r₁ i + r₂ i) / 2 := by omega
  have hclip : y i - d + D ≤ min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) :=
    le_min (by omega) (le_trans havg (le_max_right _ _))
  change y i - min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) ≤ d - D
  omega

theorem low_deviation_step {V : Type} {a b z q r₁ r₂ : Vec V} {e D : ℤ}
    (haz : a ≤ z) (hD : 0 < D) (he : 2 * D ≤ e)
    (hdev : ∀ i, q i - z i ≤ e)
    (hr₁ : r₁ ≤ centerSuper z q e D)
    (hr₂ : ∀ i, r₂ i ≤ q i + D) :
    ∀ i, averageStep a b r₁ r₂ i - z i ≤ e := by
  intro i
  have hq := hdev i
  have h1 : r₁ i ≤ z i + e - D := le_trans (hr₁ i) (min_le_left (z i + e - D) (q i + D))
  have h2 := hr₂ i
  have ha : a i ≤ z i := haz i
  have havg : (r₁ i + r₂ i) / 2 ≤ z i + e := by omega
  have hclip : min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) ≤ z i + e :=
    le_trans (min_le_right _ _) (max_le (by omega) havg)
  change min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) - z i ≤ e
  omega

theorem low_bad_step {V : Type} {a b z q r₁ r₂ : Vec V} {e D : ℤ}
    (haz : a ≤ z) (hD : 0 < D) (he : 2 * D ≤ e)
    (hr₁ : r₁ ≤ centerSuper z q e D) (hr₂ : r₂ ≤ centerSuper z q e D) :
    ∀ i, averageStep a b r₁ r₂ i - z i ≤ e - D := by
  intro i
  have h1 : r₁ i ≤ z i + e - D := le_trans (hr₁ i) (min_le_left (z i + e - D) (q i + D))
  have h2 : r₂ i ≤ z i + e - D := le_trans (hr₂ i) (min_le_left (z i + e - D) (q i + D))
  have ha : a i ≤ z i := haz i
  have havg : (r₁ i + r₂ i) / 2 ≤ z i + e - D := by omega
  have hclip : min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) ≤ z i + e - D :=
    le_trans (min_le_right _ _) (max_le (by omega) havg)
  change min (b i) (max (a i) ((r₁ i + r₂ i) / 2)) - z i ≤ e - D
  omega

theorem no_tight_sequence (G : Game) (p : Vec (Fin G.n))
    (v : ℕ → Fin G.n) (w : ℕ → ℤ)
    (h : ∀ k, p (v k) = (G.n + 1 : ℤ) * w k + 1 + p (v (k + 1))) : False := by
  have hmod : ∀ k : ℕ,
      p (v k) + (k : ℤ) ≡ p (v 0) [ZMOD (G.n + 1 : ℤ)] := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      apply Int.ModEq.trans _ ih
      apply Int.modEq_iff_dvd.mpr
      use w k
      have hk := h k
      push_cast
      linarith
  have hinj : Function.Injective (fun k : Fin (G.n + 1) => v k.val) := by
    intro i j hij
    change v i.val = v j.val at hij
    apply Fin.ext
    have hm := (hmod i.val).trans (hmod j.val).symm
    rw [hij] at hm
    have hc := Int.ModEq.add_left_cancel' (p (v j.val)) hm
    have hn : i.val ≡ j.val [MOD (G.n + 1)] :=
      Int.natCast_modEq_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using hc)
    exact hn.eq_of_lt_of_lt i.isLt j.isLt
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

theorem comparison_step (G : Game) {a b y z : Vec (Fin G.n)}
    (hy : Subsolution (operator G) a b y)
    (hz : Supersolution (operator G) a b z)
    {d : ℤ} (hd : 0 < d) (hdev : ∀ j, y j - z j ≤ d)
    (i : Fin G.n) (hi : y i - z i = d) :
    ∃ e : Fin G.m, G.tail e = i ∧
      y (G.head e) - z (G.head e) = d ∧
      y i = transformed G e + y (G.head e) := by
  have hay : a i < y i := by have hzi : a i ≤ z i := hz.1.1 i; omega
  have hzb : z i < b i := by have hyi : y i ≤ b i := hy.1.2 i; omega
  have hys := hy.2 i hay
  have hzs := hz.2 i hzb
  have hmono : operator G y i ≤ operator G z i + d := by
    have hm := (operator_laws G).mono (a := y) (b := shift z d)
      (fun j => by have := hdev j; dsimp [shift]; omega) i
    rw [(operator_laws G).translation] at hm
    exact hm
  have hyeq : y i = operator G y i := by omega
  have hzeq : z i = operator G z i := by omega
  by_cases ho : G.maxOwner i = true
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup' (outgoing_nonempty G i)
      (fun e => transformed G e + y (G.head e))
    have htail : G.tail e = i := (Finset.mem_filter.mp he).2
    have hye : y i = transformed G e + y (G.head e) := by
      rw [hyeq, operator, ite_eq_left ho]; exact heq
    have hzle : transformed G e + z (G.head e) ≤ z i := by
      rw [hzeq, operator, ite_eq_left ho]
      exact Finset.le_sup' (fun e => transformed G e + z (G.head e)) he
    exact ⟨e, htail, by have := hdev (G.head e); omega, hye⟩
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_inf' (outgoing_nonempty G i)
      (fun e => transformed G e + z (G.head e))
    have htail : G.tail e = i := (Finset.mem_filter.mp he).2
    have hze : z i = transformed G e + z (G.head e) := by
      rw [hzeq, operator, ite_eq_right ho]; exact heq
    have hyle : y i ≤ transformed G e + y (G.head e) := by
      rw [hyeq, operator, ite_eq_right ho]
      exact Finset.inf'_le (fun e => transformed G e + y (G.head e)) he
    have hj := hdev (G.head e)
    exact ⟨e, htail, by omega, by omega⟩

theorem box_comparison (G : Game) {a b y z : Vec (Fin G.n)}
    (hy : Subsolution (operator G) a b y)
    (hz : Supersolution (operator G) a b z) : y ≤ z := by
  classical
  let : Nonempty (Fin G.n) := ⟨⟨0, G.positive⟩⟩
  let d : ℤ := Finset.univ.sup' Finset.univ_nonempty (fun i => y i - z i)
  have hdev : ∀ i, y i - z i ≤ d := fun i =>
    Finset.le_sup' (fun j => y j - z j) (Finset.mem_univ i)
  by_contra h
  change ¬ (∀ i, y i ≤ z i) at h
  obtain ⟨k, hk⟩ := not_forall.mp h
  have hd : 0 < d := by have := hdev k; omega
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin G.n))
    (fun i => y i - z i)
  let S := {i : Fin G.n // y i - z i = d}
  let s₀ : S := ⟨v, hv.symm⟩
  have hs : ∀ s : S, ∃ e : Fin G.m, G.tail e = s.val ∧
      y (G.head e) - z (G.head e) = d ∧
      y s.val = transformed G e + y (G.head e) :=
    fun s => comparison_step G hy hz hd hdev s.val s.property
  choose edge hedge using hs
  let next : S → S := fun s => ⟨G.head (edge s), (hedge s).2.1⟩
  let path : ℕ → S := fun k => next^[k] s₀
  apply no_tight_sequence G y (fun k => (path k).val)
    (fun k => G.weight (edge (path k)))
  intro k
  have heq := (hedge (path k)).2.2
  simpa only [path, Function.iterate_succ_apply', next, transformed] using heq

def boxStep {V : Type} (F : Vec V → Vec V) (a b p : Vec V) : Vec V :=
  clip a b (F p)

theorem boxStep_in_box {V : Type} (F : Vec V → Vec V)
    {a b : Vec V} (hab : a ≤ b) (p : Vec V) : InBox a b (boxStep F a b p) := by
  constructor
  · intro i
    exact le_min (hab i) (le_max_left _ _)
  · intro i; exact min_le_left _ _

theorem boxStep_mono {V : Type} {F : Vec V → Vec V} (hF : Monotone F)
    (a b : Vec V) : Monotone (boxStep F a b) := by
  intro p q hpq i
  exact min_le_min_left _ (max_le_max_left _ (hF hpq i))

theorem fixed_iff_comparisons {V : Type} (F : Vec V → Vec V)
    {a b p : Vec V} (hab : a ≤ b) :
    boxStep F a b p = p ↔ Subsolution F a b p ∧ Supersolution F a b p := by
  constructor
  · intro heq
    have hp := boxStep_in_box F hab p
    rw [heq] at hp
    have hc : ∀ i, min (b i) (max (a i) (F p i)) = p i := congrFun heq
    constructor
    · refine ⟨hp, ?_⟩
      intro i hi
      have := hc i
      omega
    · refine ⟨hp, ?_⟩
      intro i hi
      have := hc i
      omega
  · rintro ⟨hy, hz⟩
    funext i
    have ha : a i ≤ p i := hy.1.1 i
    have hb : p i ≤ b i := hy.1.2 i
    have hs := hy.2 i
    have ht := hz.2 i
    change min (b i) (max (a i) (F p i)) = p i
    omega

def volume {n : ℕ} (b p : Vec (Fin n)) : ℕ := ∑ i, (b i - p i).toNat

theorem volume_decreases {n : ℕ} {b p q : Vec (Fin n)}
    (hpq : p ≤ q) (hqb : q ≤ b) (hne : p ≠ q) : volume b q < volume b p := by
  apply Finset.sum_lt_sum
  · intro i _
    exact Int.toNat_le_toNat (sub_le_sub_left (hpq i) _)
  · have hx : ∃ i, p i ≠ q i := Function.ne_iff.mp hne
    obtain ⟨i, hi⟩ := hx
    have hpi : p i ≤ q i := hpq i
    have hqi : q i ≤ b i := hqb i
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply (Int.toNat_lt_toNat (by omega)).mpr
    omega

def basicFrom {n : ℕ} (F : Vec (Fin n) → Vec (Fin n)) (hF : Monotone F)
    (a b : Vec (Fin n)) (hab : a ≤ b) (p : Vec (Fin n))
    (hp : InBox a b p) (hinc : p ≤ boxStep F a b p) :
    {r : Vec (Fin n) × ℕ // InBox a b r.1 ∧ boxStep F a b r.1 = r.1 ∧
      r.2 ≤ volume b p + 1} := by
  by_cases heq : boxStep F a b p = p
  · exact ⟨(p, 1), hp, heq, by omega⟩
  · have hq := boxStep_in_box F hab p
    have hnext : boxStep F a b p ≤ boxStep F a b (boxStep F a b p) :=
      boxStep_mono hF a b hinc
    have hvol : volume b (boxStep F a b p) < volume b p :=
      volume_decreases hinc hq.2 (Ne.symm heq)
    let r := basicFrom F hF a b hab (boxStep F a b p) hq hnext
    exact ⟨(r.val.1, r.val.2 + 1), r.property.1, r.property.2.1, by
      have := r.property.2.2; dsimp only; omega⟩
termination_by volume b p

def basic (G : Game) (a b : Vec (Fin G.n)) (hab : a ≤ b) : Vec (Fin G.n) × ℕ :=
  (basicFrom (operator G) (operator_laws G).mono a b hab a
    ⟨le_refl a, hab⟩ (boxStep_in_box (operator G) hab a).1).val

theorem basic_spec (G : Game) (a b : Vec (Fin G.n)) (hab : a ≤ b) :
    Subsolution (operator G) a b (basic G a b hab).1 ∧
    Supersolution (operator G) a b (basic G a b hab).1 ∧
    (basic G a b hab).2 ≤ volume b a + 1 := by
  have h := (basicFrom (operator G) (operator_laws G).mono a b hab a
    ⟨le_refl a, hab⟩ (boxStep_in_box (operator G) hab a).1).property
  have hc := (fixed_iff_comparisons (operator G) hab).mp h.2.1
  exact ⟨hc.1, hc.2, h.2.2⟩

theorem box_solution_exists_unique (G : Game) (a b : Vec (Fin G.n)) (hab : a ≤ b) :
    ∃! x, Subsolution (operator G) a b x ∧ Supersolution (operator G) a b x := by
  refine ⟨(basic G a b hab).1, ⟨(basic_spec G a b hab).1,
    (basic_spec G a b hab).2.1⟩, ?_⟩
  intro y hy
  apply le_antisymm
  · exact box_comparison G hy.1 (basic_spec G a b hab).2.1
  · exact box_comparison G (basic_spec G a b hab).1 hy.2

theorem no_tight_segment (G : Game) (p : Vec (Fin G.n))
    (v : ℕ → Fin G.n) (w : ℕ → ℤ)
    (h : ∀ k < G.n, p (v k) = (G.n + 1 : ℤ) * w k + 1 + p (v (k + 1))) : False := by
  have hmod : ∀ k : ℕ, k ≤ G.n →
      p (v k) + (k : ℤ) ≡ p (v 0) [ZMOD (G.n + 1 : ℤ)] := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      apply Int.ModEq.trans _ (ih (by omega))
      apply Int.modEq_iff_dvd.mpr
      use w k
      have hstep := h k (by omega)
      push_cast
      linarith
  have hinj : Function.Injective (fun k : Fin (G.n + 1) => v k.val) := by
    intro i j hij
    change v i.val = v j.val at hij
    apply Fin.ext
    have hm := (hmod i.val (by omega)).trans (hmod j.val (by omega)).symm
    rw [hij] at hm
    have hc := Int.ModEq.add_left_cancel' (p (v j.val)) hm
    have hn : i.val ≡ j.val [MOD (G.n + 1)] :=
      Int.natCast_modEq_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using hc)
    exact hn.eq_of_lt_of_lt i.isLt j.isLt
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

theorem operator_attained (G : Game) (p : Vec (Fin G.n)) (i : Fin G.n) :
    ∃ e : Fin G.m, G.tail e = i ∧ operator G p i = transformed G e + p (G.head e) := by
  by_cases ho : G.maxOwner i = true
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup' (outgoing_nonempty G i)
      (fun e => transformed G e + p (G.head e))
    exact ⟨e, (Finset.mem_filter.mp he).2, by simpa [operator, ho] using heq⟩
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_inf' (outgoing_nonempty G i)
      (fun e => transformed G e + p (G.head e))
    exact ⟨e, (Finset.mem_filter.mp he).2, by simpa [operator, ho] using heq⟩

theorem solution_near_boundary (G : Game) {x : Vec (Fin G.n)} {B W : ℤ}
    (hW : 0 ≤ W) (hweights : ∀ e, |transformed G e| ≤ W)
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => B) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => B) x) :
    ∀ i, x i ≤ G.n * W ∨ B - G.n * W ≤ x i := by
  classical
  choose edge hedge using operator_attained G x
  let next : Fin G.n → Fin G.n := fun i =>
    if 0 < x i ∧ x i < B then G.head (edge i) else i
  have hstep : ∀ i, |x (next i) - x i| ≤ W := by
    intro i
    by_cases hi : 0 < x i ∧ x i < B
    · have hsub := hx.1.2 i hi.1
      have hsuper := hx.2.2 i hi.2
      have he := (hedge i).2
      have hw := hweights (edge i)
      simp only [next, ite_eq_left hi]
      rw [show x (G.head (edge i)) - x i = -transformed G (edge i) by omega,
        abs_neg]
      exact hw
    · simp only [next, ite_eq_right hi, sub_self, abs_zero]; exact hW
  intro start
  let path : ℕ → Fin G.n := fun k => next^[k] start
  have hmove : ∀ k, |x (path k) - x start| ≤ k * W := by
    intro k
    induction k with
    | zero => simp [path]
    | succ k ih =>
      have hs := hstep (path k)
      have hp : path (k + 1) = next (path k) := Function.iterate_succ_apply' next k start
      rw [← hp] at hs
      calc
        |x (path (k + 1)) - x start| =
          |(x (path (k + 1)) - x (path k)) + (x (path k) - x start)| := by congr 1; ring
        _ ≤ |x (path (k + 1)) - x (path k)| + |x (path k) - x start| := abs_add_le _ _
        _ ≤ W + k * W := add_le_add hs ih
        _ = (↑(k + 1) : ℤ) * W := by push_cast; ring
  have hboundary : ∃ k < G.n, ¬ (0 < x (path k) ∧ x (path k) < B) := by
    by_contra h
    push Not at h
    apply no_tight_segment G x path (fun k => G.weight (edge (path k)))
    intro k hk
    have hi := h k hk
    have hsub := hx.1.2 (path k) hi.1
    have hsuper := hx.2.2 (path k) hi.2
    have hp : path (k + 1) = G.head (edge (path k)) := by
      change next^[k + 1] start = _
      rw [Function.iterate_succ_apply']
      exact ite_eq_left hi
    rw [hp]
    have he := (hedge (path k)).2
    change x (path k) = transformed G (edge (path k)) + x (G.head (edge (path k)))
    omega
  obtain ⟨k, hk, hbound⟩ := hboundary
  have hlo : 0 ≤ x (path k) := hx.1.1.1 (path k)
  have hhi : x (path k) ≤ B := hx.1.1.2 (path k)
  have hm := hmove k
  have hk' : (k : ℤ) ≤ G.n := by omega
  have hkn := mul_le_mul_of_nonneg_right hk' hW
  have ha := (abs_le.mp hm)
  by_cases he : x (path k) = 0
  · left; omega
  · right; have he' : x (path k) = B := by omega
    omega

theorem exists_rounding_shift {n : ℕ} (p : Vec (Fin n)) :
    ∃ c : ℤ, ∀ i, (p i - c) % (n + 1 : ℤ) ≠ 0 := by
  classical
  have hN : (0 : ℤ) < n + 1 := by omega
  let residue : Fin n → Fin (n + 1) := fun i =>
    ⟨(p i % (n + 1 : ℤ)).toNat,
      (Int.toNat_lt (Int.emod_nonneg _ (ne_of_gt hN))).mpr (by
        simpa only [Nat.cast_add, Nat.cast_one] using Int.emod_lt_of_pos (p i) hN)⟩
  have hns : ¬ Function.Surjective residue := by
    intro hs
    have hc := Fintype.card_le_of_surjective residue hs
    simp only [Fintype.card_fin] at hc
    omega
  have hex : ∃ c : Fin (n + 1), ∀ i, residue i ≠ c := by
    simpa only [Function.Surjective, not_forall, not_exists] using hns
  obtain ⟨c, hc⟩ := hex
  refine ⟨c.val, ?_⟩
  intro i hi
  apply hc i
  apply Fin.ext
  change (p i % (n + 1 : ℤ)).toNat = c.val
  have hm : (c.val : ℤ) ≡ p i [ZMOD (n + 1 : ℤ)] :=
    Int.modEq_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hi)
  have hcmod : (c.val : ℤ) % (n + 1 : ℤ) = c.val :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast c.isLt)
  change (c.val : ℤ) % (n + 1 : ℤ) = p i % (n + 1 : ℤ) at hm
  rw [hcmod] at hm
  rw [← hm]
  simp

theorem rounded_high_edge {N a b w c : ℤ} (hN : 0 < N)
    (hgap : (a - c) % N ≠ 0) (h : a ≤ N * w + 1 + b) :
    (a - c) / N ≤ w + (b - c) / N := by
  have ha := Int.ediv_emod_unique (a := a - c) (b := N)
    (r := (a - c) % N) (q := (a - c) / N) hN
  have hb := Int.ediv_emod_unique (a := b - c) (b := N)
    (r := (b - c) % N) (q := (b - c) / N) hN
  have hqa := ha.mp ⟨rfl, rfl⟩
  have hqb := hb.mp ⟨rfl, rfl⟩
  by_contra hn
  have hq : w + (b - c) / N + 1 ≤ (a - c) / N := by omega
  have hp := mul_le_mul_of_nonneg_left hq (le_of_lt hN)
  have hra : 1 ≤ (a - c) % N := by omega
  have hrb : (b - c) % N ≤ N - 1 := by omega
  nlinarith [hqa.1, hqb.1]

def weightBound (G : Game) : ℤ :=
  max 1 ((Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) : ℕ) : ℤ)

def topWidth (G : Game) : ℤ := 8 * G.n * weightBound G

theorem weightBound_positive (G : Game) : 0 < weightBound G := by
  have := le_max_left (1 : ℤ) ((Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) : ℕ) : ℤ)
  change 0 < max 1 _
  omega

theorem transformed_le_bound (G : Game) (e : Fin G.m) : |transformed G e| ≤ weightBound G := by
  have h := Finset.le_sup (f := fun e : Fin G.m => (transformed G e).natAbs) (Finset.mem_univ e)
  have hc : ((transformed G e).natAbs : ℤ) ≤
      ((Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) : ℕ) : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hc
  exact hc.trans (le_max_right _ _)

theorem top_bands (G : Game) {x : Vec (Fin G.n)}
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => topWidth G) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => topWidth G) x) :
    ∀ i, x i ≤ G.n * weightBound G ∨ 7 * G.n * weightBound G ≤ x i := by
  intro i
  have h := solution_near_boundary G (le_of_lt (weightBound_positive G))
    (transformed_le_bound G) hx i
  simpa only [topWidth, show 8 * (G.n : ℤ) * weightBound G - G.n * weightBound G =
    7 * G.n * weightBound G by ring] using h

theorem max_edge_le_operator (G : Game) (p : Vec (Fin G.n))
    {i : Fin G.n} (ho : G.maxOwner i = true) {e : Fin G.m} (he : G.tail e = i) :
    transformed G e + p (G.head e) ≤ operator G p i := by
  rw [operator, ite_eq_left ho]
  exact Finset.le_sup' (fun e => transformed G e + p (G.head e)) (by simp [outgoing, he])

theorem operator_le_min_edge (G : Game) (p : Vec (Fin G.n))
    {i : Fin G.n} (ho : G.maxOwner i ≠ true) {e : Fin G.m} (he : G.tail e = i) :
    operator G p i ≤ transformed G e + p (G.head e) := by
  rw [operator, ite_eq_right ho]
  exact Finset.inf'_le (fun e => transformed G e + p (G.head e)) (by simp [outgoing, he])

theorem move_tail (G : Game) (σ τ : Strategy G) (v : Fin G.n)
    (history : List (Fin G.m)) : G.tail (move G σ τ v history) = v := by
  unfold move
  split
  · exact (σ history v).property
  · exact (τ history v).property

theorem next_position (G : Game) (σ τ : Strategy G) (v : Fin G.n) (t : ℕ) :
    (position G σ τ v (t + 1)).1 = G.head (play G σ τ v t) := rfl

theorem high_edge_stays_high (G : Game) {x : Vec (Fin G.n)}
    (hbands : ∀ i, x i ≤ G.n * weightBound G ∨ 7 * G.n * weightBound G ≤ x i)
    {i : Fin G.n} {e : Fin G.m}
    (hi : 7 * G.n * weightBound G ≤ x i)
    (he : x i ≤ transformed G e + x (G.head e)) :
    7 * G.n * weightBound G ≤ x (G.head e) := by
  rcases hbands (G.head e) with hl | hh
  · have hw := (abs_le.mp (transformed_le_bound G e)).2
    have hn : (1 : ℤ) ≤ G.n := by exact_mod_cast G.positive
    have hW := weightBound_positive G
    have hnW : weightBound G ≤ G.n * weightBound G := by nlinarith
    nlinarith
  · exact hh

theorem low_edge_stays_low (G : Game) {x : Vec (Fin G.n)}
    (hbands : ∀ i, x i ≤ G.n * weightBound G ∨ 7 * G.n * weightBound G ≤ x i)
    {i : Fin G.n} {e : Fin G.m}
    (hi : x i ≤ G.n * weightBound G)
    (he : transformed G e + x (G.head e) ≤ x i) :
    x (G.head e) ≤ G.n * weightBound G := by
  rcases hbands (G.head e) with hl | hh
  · exact hl
  · have hw := (abs_le.mp (transformed_le_bound G e)).1
    have hn : (1 : ℤ) ≤ G.n := by exact_mod_cast G.positive
    have hW := weightBound_positive G
    have hnW : weightBound G ≤ G.n * weightBound G := by nlinarith
    nlinarith

theorem high_strategy (G : Game) {x : Vec (Fin G.n)}
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => topWidth G) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => topWidth G) x) :
    ∃ σ : Strategy G, ∀ τ : Strategy G, ∀ start : Fin G.n,
      7 * G.n * weightBound G ≤ x start → ∀ t : ℕ,
      7 * G.n * weightBound G ≤ x (position G σ τ start t).1 ∧
      x (position G σ τ start t).1 ≤
        transformed G (play G σ τ start t) + x (position G σ τ start (t + 1)).1 := by
  classical
  choose edge hedge using operator_attained G x
  let σ : Strategy G := fun _ i => ⟨edge i, (hedge i).1⟩
  refine ⟨σ, ?_⟩
  intro τ start hstart
  have hlocal (i : Fin G.n) (history : List (Fin G.m))
      (hi : 7 * G.n * weightBound G ≤ x i) :
      x i ≤ transformed G (move G σ τ i history) + x (G.head (move G σ τ i history)) := by
    have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
    have hW := weightBound_positive G
    have hpos : 0 < x i := by nlinarith
    have hsub := hx.1.2 i hpos
    by_cases ho : G.maxOwner i = true
    · simpa only [move, ite_eq_left ho, σ] using hsub.trans_eq (hedge i).2
    · exact hsub.trans (operator_le_min_edge G x ho (move_tail G σ τ i history))
  have hstay : ∀ t : ℕ, 7 * G.n * weightBound G ≤ x (position G σ τ start t).1 := by
    intro t
    induction t with
    | zero => exact hstart
    | succ t ih =>
      rw [next_position]
      exact high_edge_stays_high G (top_bands G hx) ih
        (hlocal (position G σ τ start t).1 (position G σ τ start t).2 ih)
  intro t
  refine ⟨hstay t, ?_⟩
  rw [next_position]
  exact hlocal (position G σ τ start t).1 (position G σ τ start t).2 (hstay t)

theorem low_strategy (G : Game) {x : Vec (Fin G.n)}
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => topWidth G) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => topWidth G) x) :
    ∃ τ : Strategy G, ∀ σ : Strategy G, ∀ start : Fin G.n,
      x start ≤ G.n * weightBound G → ∀ t : ℕ,
      x (position G σ τ start t).1 ≤ G.n * weightBound G ∧
      transformed G (play G σ τ start t) + x (position G σ τ start (t + 1)).1 ≤
        x (position G σ τ start t).1 := by
  classical
  choose edge hedge using operator_attained G x
  let τ : Strategy G := fun _ i => ⟨edge i, (hedge i).1⟩
  refine ⟨τ, ?_⟩
  intro σ start hstart
  have hlocal (i : Fin G.n) (history : List (Fin G.m))
      (hi : x i ≤ G.n * weightBound G) :
      transformed G (move G σ τ i history) + x (G.head (move G σ τ i history)) ≤ x i := by
    have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
    have hW := weightBound_positive G
    have hlt : x i < topWidth G := by unfold topWidth; nlinarith
    have hsuper := hx.2.2 i hlt
    by_cases ho : G.maxOwner i = true
    · exact (max_edge_le_operator G x ho (move_tail G σ τ i history)).trans hsuper
    · simpa only [move, ite_eq_right ho, τ] using (hedge i).2.symm.trans_le hsuper
  have hstay : ∀ t : ℕ, x (position G σ τ start t).1 ≤ G.n * weightBound G := by
    intro t
    induction t with
    | zero => exact hstart
    | succ t ih =>
      rw [next_position]
      exact low_edge_stays_low G (top_bands G hx) ih
        (hlocal (position G σ τ start t).1 (position G σ τ start t).2 ih)
  intro t
  refine ⟨hstay t, ?_⟩
  rw [next_position]
  exact hlocal (position G σ τ start t).1 (position G σ τ start t).2 (hstay t)

def vectorBound {n : ℕ} (p : Fin n → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (p i).natAbs)

theorem le_vectorBound {n : ℕ} (p : Fin n → ℤ) (i : Fin n) :
    |p i| ≤ (vectorBound p : ℤ) := by
  have h := Finset.le_sup (f := fun i => (p i).natAbs) (Finset.mem_univ i)
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

noncomputable def average (w : ℕ → ℝ) (T : ℕ) : ℝ := (∑ j ∈ Finset.range T, w j) / T

theorem average_bounds {w : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ t, |w t| ≤ M) (T : ℕ) : -M ≤ average w T ∧ average w T ≤ M := by
  by_cases hT : T = 0
  · simp [hT, average, hM, neg_nonpos.mpr hM]
  have ht : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT
  constructor
  · apply (le_div_iff₀ ht).2
    calc
      -M * (T : ℝ) = ∑ j ∈ Finset.range T, -M := by simp; ring
      _ ≤ ∑ j ∈ Finset.range T, w j :=
        Finset.sum_le_sum (fun j _ => (abs_le.mp (hw j)).1)
  · apply (div_le_iff₀ ht).2
    calc
      (∑ j ∈ Finset.range T, w j) ≤ ∑ j ∈ Finset.range T, M :=
        Finset.sum_le_sum (fun j _ => (abs_le.mp (hw j)).2)
      _ = M * (T : ℝ) := by simp; ring

theorem payoff_bounded (G : Game) (π : ℕ → Fin G.m) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (average (fun t => (G.weight (π t) : ℝ))) ∧
    Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (average (fun t => (G.weight (π t) : ℝ))) := by
  let M : ℝ := vectorBound G.weight
  have hM : 0 ≤ M := by positivity
  have hw (t : ℕ) : |(G.weight (π t) : ℝ)| ≤ M := by
    dsimp [M]
    exact_mod_cast le_vectorBound G.weight (π t)
  exact ⟨Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun t => (average_bounds hM hw t).2),
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun t => (average_bounds hM hw t).1)⟩

theorem lower_average_from_potential {w p : ℕ → ℝ} {K : ℝ}
    (hp : ∀ t, |p t| ≤ K) (he : ∀ t, p t - p (t + 1) ≤ w t) (T : ℕ) :
    (-2 * K) / (T : ℝ) ≤ average w T := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
  calc
    -2 * K ≤ p 0 - p T := by
      have h0 := (abs_le.mp (hp 0)).1
      have hT := (abs_le.mp (hp T)).2
      linarith
    _ = ∑ j ∈ Finset.range T, (p j - p (j + 1)) := (Finset.sum_range_sub' p T).symm
    _ ≤ ∑ j ∈ Finset.range T, w j := Finset.sum_le_sum fun j _ => he j

theorem upper_average_from_potential {w p : ℕ → ℝ} {K N δ : ℝ}
    (hN : 0 < N) (hp : ∀ t, |p t| ≤ K)
    (he : ∀ t, N * w t + δ ≤ p t - p (t + 1))
    {T : ℕ} (hT : 0 < T) :
    average w T ≤ (2 * K / N) / (T : ℝ) - δ / N := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : N * (∑ j ∈ Finset.range T, w j) + (T : ℝ) * δ ≤ 2 * K := by
    calc
      N * (∑ j ∈ Finset.range T, w j) + (T : ℝ) * δ =
          ∑ j ∈ Finset.range T, (N * w j + δ) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range T, (p j - p (j + 1)) :=
        Finset.sum_le_sum fun j _ => he j
      _ = p 0 - p T := Finset.sum_range_sub' p T
      _ ≤ 2 * K := by
        have h0 := (abs_le.mp (hp 0)).2
        have hT := (abs_le.mp (hp T)).1
        linarith
  have hd := div_le_div_of_nonneg_right hs (le_of_lt (mul_pos hN ht))
  have hleft : (N * (∑ j ∈ Finset.range T, w j) + (T : ℝ) * δ) / (N * T) =
      average w T + δ / N := by
    unfold average
    field_simp
  have hright : 2 * K / (N * (T : ℝ)) = (2 * K / N) / T := by ring
  rw [hleft, hright] at hd
  linarith

theorem high_payoff (G : Game) {x : Vec (Fin G.n)} (σ τ : Strategy G)
    (start : Fin G.n)
    (he : ∀ t, x (position G σ τ start t).1 ≤
      transformed G (play G σ τ start t) + x (position G σ τ start (t + 1)).1) :
    0 ≤ meanPayoff G (play G σ τ start) := by
  obtain ⟨c, hc⟩ := exists_rounding_shift x
  let q (i : Fin G.n) : ℤ := (x i - c) / (G.n + 1 : ℤ)
  let p (t : ℕ) : ℝ := q (position G σ τ start t).1
  let K : ℝ := vectorBound q
  have hp (t : ℕ) : |p t| ≤ K := by
    dsimp [p, K]
    exact_mod_cast le_vectorBound q (position G σ τ start t).1
  have hedge (t : ℕ) : p t - p (t + 1) ≤ (G.weight (play G σ τ start t) : ℝ) := by
    have hN : (0 : ℤ) < G.n + 1 := by omega
    have h := rounded_high_edge hN (hc (position G σ τ start t).1) (he t)
    change q (position G σ τ start t).1 ≤
      G.weight (play G σ τ start t) + q (position G σ τ start (t + 1)).1 at h
    have hr : p t ≤ (G.weight (play G σ τ start t) : ℝ) + p (t + 1) := by
      dsimp [p]
      exact_mod_cast h
    linarith
  have hl := lower_average_from_potential hp hedge
  have ht := tendsto_const_div_atTop_nhds_zero_nat (-2 * K)
  have hb := (payoff_bounded G (play G σ τ start)).1
  have hcb : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (average (fun t => (G.weight (play G σ τ start t) : ℝ))) :=
    Filter.IsBounded.isCobounded_flip hb
  have hm := Filter.liminf_le_liminf (Filter.Eventually.of_forall hl)
    ht.isBoundedUnder_ge hcb
  rw [ht.liminf_eq] at hm
  exact hm

theorem low_payoff (G : Game) {x : Vec (Fin G.n)} (σ τ : Strategy G)
    (start : Fin G.n)
    (he : ∀ t, transformed G (play G σ τ start t) +
      x (position G σ τ start (t + 1)).1 ≤ x (position G σ τ start t).1) :
    meanPayoff G (play G σ τ start) ≤ -1 / (G.n + 1 : ℝ) := by
  let p (t : ℕ) : ℝ := x (position G σ τ start t).1
  let K : ℝ := vectorBound x
  have hp (t : ℕ) : |p t| ≤ K := by
    dsimp [p, K]
    exact_mod_cast le_vectorBound x (position G σ τ start t).1
  have hedge (t : ℕ) : (G.n + 1 : ℝ) * G.weight (play G σ τ start t) + 1 ≤
      p t - p (t + 1) := by
    have h := he t
    unfold transformed at h
    have hr : (G.n + 1 : ℝ) * G.weight (play G σ τ start t) + 1 + p (t + 1) ≤ p t := by
      dsimp [p]
      exact_mod_cast h
    linarith
  have hN : (0 : ℝ) < G.n + 1 := by positivity
  have hev : ∀ᶠ T : ℕ in Filter.atTop,
      average (fun t => (G.weight (play G σ τ start t) : ℝ)) T ≤
        (2 * K / (G.n + 1 : ℝ)) / T - 1 / (G.n + 1 : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with T hT
    exact upper_average_from_potential hN hp hedge hT
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (2 * K / (G.n + 1 : ℝ))).sub_const
    (1 / (G.n + 1 : ℝ))
  have hcb : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun T : ℕ => (2 * K / (G.n + 1 : ℝ)) / T - 1 / (G.n + 1 : ℝ)) :=
    Filter.IsBounded.isCobounded_flip ht.isBoundedUnder_le
  have hm := Filter.liminf_le_liminf hev (payoff_bounded G (play G σ τ start)).2 hcb
  rw [ht.liminf_eq] at hm
  change meanPayoff G (play G σ τ start) ≤ (0 : ℝ) - 1 / (G.n + 1 : ℝ) at hm
  rw [show (-1 : ℝ) / (G.n + 1 : ℝ) = 0 - 1 / (G.n + 1 : ℝ) by ring]
  exact hm

theorem winning_iff_high (G : Game) {x : Vec (Fin G.n)}
    (hx : Subsolution (operator G) (fun _ => 0) (fun _ => topWidth G) x ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => topWidth G) x) (v : Fin G.n) :
    Winning G v ↔ topWidth G / 2 < x v := by
  have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
  have hW := weightBound_positive G
  have hhalf : topWidth G / 2 = 4 * G.n * weightBound G := by
    unfold topWidth
    rw [show 8 * (G.n : ℤ) * weightBound G = (4 * G.n * weightBound G) * 2 by ring]
    omega
  constructor
  · rintro ⟨σ, hσ⟩
    rcases top_bands G hx v with hl | hh
    · obtain ⟨τ, hτ⟩ := low_strategy G hx
      have he := fun t => (hτ σ v hl t).2
      have hp := low_payoff G σ τ v he
      have hneg : (-1 : ℝ) / (G.n + 1 : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
      exact False.elim (not_lt_of_ge ((hσ τ).trans hp) hneg)
    · rw [hhalf]
      nlinarith
  · intro hv
    obtain ⟨σ, hσ⟩ := high_strategy G hx
    refine ⟨σ, fun τ => ?_⟩
    have hh : 7 * G.n * weightBound G ≤ x v := by
      rcases top_bands G hx v with hl | hh
      · rw [hhalf] at hv
        nlinarith
      · exact hh
    exact high_payoff G σ τ v fun t => (hσ τ v hh t).2

def mass {n : ℕ} (a : Fin n → ℚ) (S : Finset (Fin n)) : ℚ := ∑ i ∈ S, a i

def lowerActive {n : ℕ} (a y : Vec (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a i < y i)

def upperActive {n : ℕ} (b z : Vec (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => z i < b i)

theorem mass_nonneg {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, 0 ≤ a i) (S : Finset (Fin n)) :
    0 ≤ mass a S := Finset.sum_nonneg (fun i _ => ha i)

theorem mass_mono {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, 0 ≤ a i)
    {S T : Finset (Fin n)} (hST : S ⊆ T) : mass a S ≤ mass a T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST (fun i _ _ => ha i)

theorem weight_le_mass {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, 0 ≤ a i)
    {S : Finset (Fin n)} {i : Fin n} (hi : i ∈ S) : a i ≤ mass a S :=
  Finset.single_le_sum (fun i _ => ha i) hi

end MeanPayoff

end

end OAI
