import OAI.Computability.StarHeight.Markers

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uι uι2 uι3

namespace LocalMarkers

variable {Alphabet : Type uAlphabet}

def AgreesOn (f g : ℤ → Alphabet) (l r : ℤ) : Prop :=
  ∀ x : ℤ, l ≤ x → x < r → f x = g x

def ShortContinuation (d K : ℕ) (w : ℤ → Alphabet) (z : ℤ) (v : ℤ → Alphabet) : Prop :=
  (∃ a : ℕ, 0 < a ∧ a < d ∧ Function.Periodic v (a : ℤ)) ∧
    AgreesOn w v z (z + K)

lemma short_continuation_exists {d K : ℕ} (hK : d ≤ K) (w : ℤ → Alphabet) (z : ℤ)
    (hp : ∃ a : ℕ, 0 < a ∧ a < d ∧ Period (fun i : Fin K => w (z + i.val)) a) :
    ∃ v : ℤ → Alphabet, ShortContinuation d K w z v := by
  obtain ⟨a, ha, had, hp⟩ := hp
  obtain ⟨v, hv, he⟩ := exists_continuation z ha (by omega) hp
  refine ⟨v, ⟨a, ha, had, hv⟩, ?_⟩
  intro x hx hx'
  have hn : ((x - z).toNat : ℤ) = x - z := Int.toNat_of_nonneg (by omega)
  let i : Fin K := ⟨(x - z).toNat, by omega⟩
  have hi : z + (i.val : ℤ) = x := by dsimp [i]; omega
  simpa only [hi] using (he i).symm

lemma short_continuations_equal {d K : ℕ} {w v v' : ℤ → Alphabet} {z z' : ℤ}
    (hv : ShortContinuation d K w z v) (hv' : ShortContinuation d K w z' v')
    (hover : (d : ℤ) ^ 2 ≤ (K : ℤ) - |z - z'|) : v = v' := by
  obtain ⟨⟨a, ha, had, hva⟩, he⟩ := hv
  obtain ⟨⟨b, hb, hbd, hvb⟩, he'⟩ := hv'
  have haZ : 0 < (a : ℤ) := by omega
  have hbZ : 0 < (b : ℤ) := by omega
  have hadZ : (a : ℤ) < d := by omega
  have hbdZ : (b : ℤ) < d := by omega
  have hab : (a : ℤ) * b ≤ (d : ℤ) ^ 2 := by nlinarith
  apply periodic_agree haZ hbZ hva hvb (max z z')
  intro x hx hx'
  have hz : z ≤ x := (le_max_left z z').trans hx
  have hz' : z' ≤ x := (le_max_right z z').trans hx
  have hu : x < z + K := by
    have hmax : max z z' = if z ≤ z' then z' else z := max_def _ _
    split_ifs at hmax with hzz
    · rw [abs_of_nonpos (by omega)] at hover
      omega
    · rw [abs_of_nonneg (by omega)] at hover
      omega
  have hu' : x < z' + K := by
    have hmax : max z z' = if z ≤ z' then z' else z := max_def _ _
    split_ifs at hmax with hzz
    · rw [abs_of_nonpos (by omega)] at hover
      omega
    · rw [abs_of_nonneg (by omega)] at hover
      omega
  exact (he x hz hu).symm.trans (he' x hz' hu')

lemma common_continuation {d K : ℕ} (w : ℤ → Alphabet) (S : Finset ℤ)
    (hne : S.Nonempty) (v : ℤ → ℤ → Alphabet)
    (hv : ∀ z ∈ S, ShortContinuation d K w z (v z))
    (hover : ∀ z ∈ S, ∀ z' ∈ S, (d : ℤ) ^ 2 ≤ (K : ℤ) - |z - z'|) :
    ∃ u : ℤ → Alphabet, (∃ a : ℕ, 0 < a ∧ a < d ∧ Function.Periodic u (a : ℤ)) ∧
      ∀ z ∈ S, v z = u ∧ AgreesOn w u z (z + K) := by
  obtain ⟨z, hz⟩ := hne
  refine ⟨v z, (hv z hz).1, ?_⟩
  intro z' hz'
  have he := short_continuations_equal (hv z' hz') (hv z hz) (hover z' hz' z hz)
  exact ⟨he, he ▸ (hv z' hz').2⟩

lemma periodic_run {d K : ℕ} (hd : 2 ≤ d) (hK : 3 * d ^ 2 < K)
    (w : ℤ → Alphabet) (l u : ℤ) (hlu : l ≤ u)
    (hp : ∀ x : ℤ, l ≤ x → x ≤ u →
      ∃ a : ℕ, 0 < a ∧ a < d ∧ Period (fun i : Fin K => w (x + i.val)) a) :
    ∃ v : ℤ → Alphabet, (∃ a : ℕ, 0 < a ∧ a < d ∧ Function.Periodic v (a : ℤ)) ∧
      AgreesOn w v l (u + K) := by
  classical
  have hdK : d ≤ K := by nlinarith
  have hex : ∀ x : {x : ℤ // l ≤ x ∧ x ≤ u},
      ∃ v : ℤ → Alphabet, ShortContinuation d K w x.val v := by
    intro x
    exact short_continuation_exists hdK w x.val (hp x.val x.2.1 x.2.2)
  choose v hv using hex
  let x₀ : {x : ℤ // l ≤ x ∧ x ≤ u} := ⟨l, le_refl _, hlu⟩
  have heq : ∀ (n : ℕ) (hn : l + n ≤ u),
      v ⟨l + n, by omega, hn⟩ = v x₀ := by
    intro n
    induction n with
    | zero => intro hn; congr 1; apply Subtype.ext; simp [x₀]
    | succ n ih =>
      intro hn
      have hn' : l + (n : ℤ) ≤ u := by omega
      have hover : (d : ℤ) ^ 2 ≤ (K : ℤ) - |(l + (n + 1 : ℕ)) - (l + n)| := by
        have hh : (n + 1 : ℕ) = n + 1 := rfl
        have hcast : (3 : ℤ) * (d : ℤ) ^ 2 < K := by exact_mod_cast hK
        have habs : |(l + (n + 1 : ℕ)) - (l + n)| = 1 := by
          rw [Nat.cast_add, Nat.cast_one]
          ring_nf
          norm_num
        rw [habs]
        nlinarith [sq_nonneg (d : ℤ)]
      exact (short_continuations_equal (hv ⟨l + ((n + 1 : ℕ) : ℤ), by omega, hn⟩)
        (hv ⟨l + n, by omega, hn'⟩) hover).trans (ih hn')
  refine ⟨v x₀, (hv x₀).1, ?_⟩
  intro i hi hi'
  let x : ℤ := min i u
  have hx : l ≤ x ∧ x ≤ u := ⟨le_min hi hlu, min_le_right _ _⟩
  have hn : ((x - l).toNat : ℤ) = x - l := Int.toNat_of_nonneg (by omega)
  have he : v ⟨x, hx⟩ = v x₀ := by
    have hh := heq (x - l).toNat (by omega)
    have hxval : l + (((x - l).toNat : ℕ) : ℤ) = x := by omega
    simpa only [hxval] using hh
  rw [← he]
  apply (hv ⟨x, hx⟩).2 i (min_le_left _ _)
  dsimp [x]
  rcases le_total i u with h | h
  · rw [min_eq_left h]
    have : (0 : ℤ) < K := by omega
    omega
  · rwa [min_eq_right h]

end LocalMarkers

namespace MarkerSearch

def Separated (S : Set ℤ) (d : ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|

def FirstAfter (S : Set ℤ) (l m : ℤ) : Prop :=
  m ∈ S ∧ l ≤ m ∧ ∀ m' ∈ S, l ≤ m' → m ≤ m'

lemma firstAfter_unique {S : Set ℤ} {l m m' : ℤ}
    (h : FirstAfter S l m) (h' : FirstAfter S l m') : m = m' :=
  le_antisymm (h.2.2 m' h'.1 h'.2.1) (h'.2.2 m h.1 h.2.1)

noncomputable def search (S : Set ℤ) (l r : ℤ) : Option ℤ := by
  classical
  let F := (Finset.Icc l r).filter (· ∈ S)
  exact if h : F.Nonempty then some (F.min' h) else none

lemma search_none {S : Set ℤ} {l r : ℤ} :
    search S l r = none ↔ ∀ m ∈ S, l ≤ m → m ≤ r → False := by
  classical
  dsimp only [search]
  split_ifs with h
  · simp only [false_iff]
    obtain ⟨m, hm⟩ := h
    have hh := Finset.mem_filter.mp hm
    have hb := Finset.mem_Icc.mp hh.1
    exact fun hn => hn m hh.2 hb.1 hb.2
  · simp only [true_iff]
    intro m hm hl hr
    exact h ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl, hr⟩, hm⟩⟩

lemma search_some {S : Set ℤ} {l r m : ℤ} :
    search S l r = some m ↔ FirstAfter S l m ∧ m ≤ r := by
  classical
  let F := (Finset.Icc l r).filter (· ∈ S)
  constructor
  · dsimp only [search]
    split_ifs with h
    · intro he
      have hm : F.min' h = m := Option.some.inj he
      have hmem : m ∈ F := hm ▸ F.min'_mem h
      obtain ⟨hb, hS⟩ := Finset.mem_filter.mp hmem
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hb
      refine ⟨⟨hS, hl, ?_⟩, hr⟩
      intro m' hm' hl'
      by_cases hr' : m' ≤ r
      · rw [← hm]
        exact F.min'_le m' (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl', hr'⟩, hm'⟩)
      · omega
    · simp
  · rintro ⟨h, hr⟩
    have hf : F.Nonempty := ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h.2.1, hr⟩, h.1⟩⟩
    have hmem := F.min'_mem hf
    obtain ⟨hb, hS⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hl, _⟩ := Finset.mem_Icc.mp hb
    have he : F.min' hf = m := le_antisymm
      (F.min'_le m (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h.2.1, hr⟩, h.1⟩))
      (h.2.2 _ hS hl)
    dsimp only [search]
    rw [dite_eq_left hf]
    exact congrArg some he

lemma search_some_or_none (S : Set ℤ) (l r : ℤ) :
    (∀ m ∈ S, l ≤ m → m ≤ r → False) ∨
      ∃ m, FirstAfter S l m ∧ m ≤ r := by
  cases h : search S l r with
  | none => exact Or.inl (search_none.mp h)
  | some m => exact Or.inr ⟨m, search_some.mp h⟩

lemma search_ext {S : Set ℤ} {l r l' r' : ℤ}
    (he : ∀ m ∈ S, (l ≤ m ∧ m ≤ r) ↔ (l' ≤ m ∧ m ≤ r')) :
    search S l r = search S l' r' := by
  classical
  have hf : (Finset.Icc l r).filter (· ∈ S) = (Finset.Icc l' r').filter (· ∈ S) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h, hS⟩
      exact ⟨(he m hS).mp h, hS⟩
    · rintro ⟨h, hS⟩
      exact ⟨(he m hS).mpr h, hS⟩
  dsimp only [search]
  simp only [hf]

lemma firstAfter_shift {S : Set ℤ} {l v m w : ℤ} (_hw : 0 ≤ w) (hv : |v| ≤ w)
    (hleft : ∀ m ∈ S, w < |m - l|) :
    FirstAfter S (l + v) m ↔ FirstAfter S l m := by
  have hv' := abs_le.mp hv
  constructor
  · intro h
    have hml := h.2.1
    have hdist := hleft m h.1
    have hl : l ≤ m := by
      by_contra hn
      rw [abs_of_neg (by omega)] at hdist
      omega
    refine ⟨h.1, hl, ?_⟩
    intro m' hm' hl'
    have hdist' := hleft m' hm'
    rw [abs_of_nonneg (by omega)] at hdist'
    exact h.2.2 m' hm' (by omega)
  · intro h
    have hml := h.2.1
    have hdist := hleft m h.1
    rw [abs_of_nonneg (by omega)] at hdist
    refine ⟨h.1, by omega, ?_⟩
    intro m' hm' hl'
    have hdist' := hleft m' hm'
    have hl'' : l ≤ m' := by
      by_contra hn
      rw [abs_of_neg (by omega)] at hdist'
      omega
    exact h.2.2 m' hm' hl''

lemma instability_charge {S : Set ℤ} {l r v w : ℤ} (hw : 0 ≤ w) (hv : |v| ≤ w)
    (hne : search S l r ≠ search S (l + v) (r + v)) :
    (∃ m ∈ S, |m - l| ≤ w) ∨
      ∃ m, FirstAfter S l m ∧ |m - r| ≤ w := by
  classical
  by_cases hn : ∃ m ∈ S, |m - l| ≤ w
  · exact Or.inl hn
  · right
    have hleft : ∀ m ∈ S, w < |m - l| := by
      intro m hm
      exact lt_of_not_ge (fun he => hn ⟨m, hm, he⟩)
    have hv' := abs_le.mp hv
    cases h₀ : search S l r with
    | none =>
      cases h₁ : search S (l + v) (r + v) with
      | none => exact False.elim (hne (h₀.trans h₁.symm))
      | some m =>
        obtain ⟨hm, hmr⟩ := search_some.mp h₁
        have hm' := (firstAfter_shift hw hv hleft).mp hm
        have hlarge : r < m := by
          by_contra he
          exact search_none.mp h₀ m hm'.1 hm'.2.1 (le_of_not_gt he)
        refine ⟨m, hm', ?_⟩
        rw [abs_of_pos (by omega)]
        omega
    | some m =>
      obtain ⟨hm, hmr⟩ := search_some.mp h₀
      cases h₁ : search S (l + v) (r + v) with
      | none =>
        have hm' := (firstAfter_shift hw hv hleft).mpr hm
        have hlarge : r + v < m := by
          by_contra he
          exact search_none.mp h₁ m hm'.1 hm'.2.1 (le_of_not_gt he)
        refine ⟨m, hm, ?_⟩
        rw [abs_of_nonpos (by omega)]
        omega
      | some m' =>
        have hm' := (firstAfter_shift hw hv hleft).mp (search_some.mp h₁).1
        have he := firstAfter_unique hm hm'
        exact False.elim (hne (h₀.trans ((congrArg some he).trans h₁.symm)))

lemma extension_charge {S : Set ℤ} {l r H : ℤ}
    (hn : search S l r = none) (he : ∃ m ∈ S, l ≤ m ∧ m ≤ r + H) :
    ∃ m, FirstAfter S l m ∧ 0 < m - r ∧ m - r ≤ H := by
  have hsome : search S l (r + H) ≠ none := by
    intro h
    obtain ⟨m, hm, hl, hr⟩ := he
    exact search_none.mp h m hm hl hr
  cases h : search S l (r + H) with
  | none => exact False.elim (hsome h)
  | some m =>
    obtain ⟨hm, hr⟩ := search_some.mp h
    have hlo : r < m := by
      by_contra he
      exact search_none.mp hn m hm.1 hm.2.1 (le_of_not_gt he)
    exact ⟨m, hm, by omega, by omega⟩

end MarkerSearch

namespace MarkerSearch

open scoped Classical

lemma close_unique {a b c w : ℤ} (ha : |a - c| ≤ w) (hb : |b - c| ≤ w)
    (hgap : 2 * w < |a - b|) : False := by
  have h := abs_sub_le a c b
  rw [abs_sub_comm c b] at h
  omega

lemma separated_interval_unique {S : Set ℤ} {d l r x y : ℤ}
    (hS : Separated S d) (hlen : r - l < d)
    (hx : x ∈ S) (hy : y ∈ S) (hxl : l ≤ x) (hxr : x ≤ r)
    (hyl : l ≤ y) (hyr : y ≤ r) : x = y := by
  by_contra hn
  have h := hS x hx y hy hn
  have hxy : |x - y| ≤ r - l := abs_le.mpr ⟨by omega, by omega⟩
  omega

lemma firstAfter_same_side {S : Set ℤ} {d l r z z' m m' : ℤ}
    (hS : Separated S d) (hlen : r - l < d)
    (hz : l ≤ z ∧ z ≤ r) (hz' : l ≤ z' ∧ z' ≤ r)
    (hm : FirstAfter S z m) (hm' : FirstAfter S z' m')
    (hside : (m ≤ r) ↔ (m' ≤ r)) : m = m' := by
  by_cases h : m ≤ r
  · exact separated_interval_unique hS hlen hm.1 hm'.1
      (hz.1.trans hm.2.1) h (hz'.1.trans hm'.2.1) (hside.mp h)
  · have h' : r < m' := lt_of_not_ge (fun hh => h (hside.mpr hh))
    exact le_antisymm (hm.2.2 m' hm'.1 (by omega))
      (hm'.2.2 m hm.1 (by omega))

lemma left_charge_card {ι : Type uι} (s : Finset ι) {S : Set ℤ}
    {d z h w : ℤ} (δ : ι → ℤ)
    (hS : Separated S d) (hsep : 2 * h + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 * w < |δ i - δ j|) :
    (s.filter fun i => ∃ m ∈ S, |m - (z + δ i)| ≤ w).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, m, hm, hmclose⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, m', hm', hmclose'⟩ := Finset.mem_filter.mp hj
  have hiδ := abs_le.mp (hδ i hi)
  have hjδ := abs_le.mp (hδ j hj)
  have hmδ := abs_le.mp hmclose
  have hmδ' := abs_le.mp hmclose'
  have he : m = m' := separated_interval_unique hS (by omega) hm hm'
    (show z - h - w ≤ m by omega) (show m ≤ z + h + w by omega)
    (by omega) (by omega)
  subst m'
  by_contra hij
  have ha : |δ i - (m - z)| ≤ w := by
    rw [abs_sub_comm]
    convert hmclose using 1
    congr 1
    ring
  have hb : |δ j - (m - z)| ≤ w := by
    rw [abs_sub_comm]
    convert hmclose' using 1
    congr 1
    ring
  exact close_unique ha hb (hgap i hi j hj hij)

lemma right_charge_card {ι : Type uι2} (s : Finset ι) {S : Set ℤ}
    {d z h w : ℤ} (δ H : ι → ℤ)
    (hS : Separated S d) (hsep : 2 * h < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      2 * w < |(z + δ i + H i) - (z + δ j + H j)|) :
    (s.filter fun i => ∃ m, FirstAfter S (z + δ i) m ∧
      |m - (z + δ i + H i)| ≤ w).card ≤ 2 := by
  classical
  let F := s.filter fun i => ∃ m, FirstAfter S (z + δ i) m ∧
    |m - (z + δ i + H i)| ≤ w
  have hp : ∀ i : {i // i ∈ F}, ∃ m, FirstAfter S (z + δ i.val) m ∧
      |m - (z + δ i.val + H i.val)| ≤ w :=
    fun i => (Finset.mem_filter.mp i.2).2
  choose m hm using hp
  have hinj : Function.Injective (fun i => decide (m i ≤ z + h)) := by
    intro i j he
    have hi := (Finset.mem_filter.mp i.2).1
    have hj := (Finset.mem_filter.mp j.2).1
    have hiδ := abs_le.mp (hδ i.val hi)
    have hjδ := abs_le.mp (hδ j.val hj)
    have hside : (m i ≤ z + h) ↔ (m j ≤ z + h) := by simpa using he
    have hme := firstAfter_same_side hS (show z + h - (z - h) < d by omega)
      (show z - h ≤ z + δ i.val ∧ z + δ i.val ≤ z + h by omega)
      (show z - h ≤ z + δ j.val ∧ z + δ j.val ≤ z + h by omega)
      (hm i).1 (hm j).1 hside
    apply Subtype.ext
    by_contra hij
    have hc := (hm j).2
    rw [← hme] at hc
    exact close_unique (by simpa [abs_sub_comm] using (hm i).2)
      (by simpa [abs_sub_comm] using hc) (hgap i.val hi j.val hj hij)
  simpa [F] using Fintype.card_le_of_injective _ hinj

def InnerFailure (S : Set ℤ) (z H w E : ℤ) : Prop :=
  (∃ v, |v| ≤ w ∧ search S z (z + H) ≠ search S (z + v) (z + H + v)) ∨
  (search S z (z + H) = none ∧ ∃ m ∈ S, z ≤ m ∧ m ≤ z + H + E)

lemma innerFailure_charge {S : Set ℤ} {z H w E : ℤ} (hw : 0 ≤ w)
    (hf : InnerFailure S z H w E) :
    (∃ m ∈ S, |m - z| ≤ w) ∨
      ∃ m, FirstAfter S z m ∧ |m - (z + H)| ≤ max E w := by
  rcases hf with ⟨v, hv, hne⟩ | ⟨hn, he⟩
  · rcases instability_charge hw hv hne with h | ⟨m, hm, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨m, hm, hc.trans (le_max_right _ _)⟩
  · obtain ⟨m, hm, hlo, hhi⟩ := extension_charge hn he
    exact Or.inr ⟨m, hm, by rw [abs_of_pos hlo]; exact hhi.trans (le_max_left _ _)⟩

lemma innerFailure_card {ι : Type uι3} (s : Finset ι) {S : Set ℤ}
    {d z h w E : ℤ} (δ H : ι → ℤ)
    (hS : Separated S d) (hw : 0 ≤ w) (hsep : 2 * h + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 * w < |δ i - δ j|)
    (hrgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      2 * max E w < |(z + δ i + H i) - (z + δ j + H j)|) :
    (s.filter fun i => InnerFailure S (z + δ i) (H i) w E).card ≤ 3 := by
  classical
  let A := s.filter fun i => ∃ m ∈ S, |m - (z + δ i)| ≤ w
  let B := s.filter fun i => ∃ m, FirstAfter S (z + δ i) m ∧
    |m - (z + δ i + H i)| ≤ max E w
  have hs : (s.filter fun i => InnerFailure S (z + δ i) (H i) w E) ⊆ A ∪ B := by
    intro i hi
    obtain ⟨hi, hf⟩ := Finset.mem_filter.mp hi
    rcases innerFailure_charge hw hf with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hb⟩)
  have ha : A.card ≤ 1 := left_charge_card s δ hS hsep hδ hgap
  have hb : B.card ≤ 2 := right_charge_card s δ H hS (by omega) hδ hrgap
  exact (Finset.card_le_card hs).trans ((Finset.card_union_le A B).trans (show A.card + B.card ≤ 3 by omega))

end MarkerSearch

end GeneralizedStarHeight

end OAI
