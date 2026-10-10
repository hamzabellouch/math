import OAI.Computability.Scheduling.RunCertificates

namespace OAI

section

namespace ThreeMachine.Structure
section PriorityEncoding
variable {J : Type}

theorem pairCode_lt {B i j rx ry : ℕ} (hx : rx < B) (hy : ry < B) :
    i * B + rx < j * B + ry ↔ i < j ∨ i = j ∧ rx < ry := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hm := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hij)
    rw [Nat.succ_mul] at hm
    constructor
    · exact fun _ => Or.inl hij
    · omega
  · simp only [lt_self_iff_false, true_and, false_or, Nat.add_lt_add_iff_left]
  · have hm := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hji)
    rw [Nat.succ_mul] at hm
    constructor
    · omega
    · rintro (h | ⟨h, _⟩) <;> omega

namespace GlobalList

noncomputable def keyValue (K : GlobalList J) (rank : J → ℕ) (B : ℕ) (x : J) : ℕ :=
  K.lastIndex x * B + rank x

theorem keyValue_lt_iff {K : GlobalList J} {rank : J → ℕ} {B : ℕ} {x y : J}
    (hx : rank x < B) (hy : rank y < B) :
    K.keyValue rank B x < K.keyValue rank B y ↔ K.KeyLT rank x y :=
  pairCode_lt hx hy

theorem keyValue_injective {K : GlobalList J} {rank : J → ℕ} {B : ℕ}
    (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank) :
    Function.Injective (K.keyValue rank B) := by
  intro x y he
  apply hinj
  have hn1 : ¬K.KeyLT rank x y := by
    rw [← keyValue_lt_iff (hrank x) (hrank y), he]
    exact lt_irrefl _
  have hn2 : ¬K.KeyLT rank y x := by
    rw [← keyValue_lt_iff (hrank y) (hrank x), he]
    exact lt_irrefl _
  unfold KeyLT at hn1 hn2
  omega

theorem lastIndex_le_sup (K : GlobalList J) (x : J) :
    K.lastIndex x ≤ K.indices.sup id := by
  apply Finset.sup_le
  intro i hi
  exact Finset.le_sup (f := id) ((mem_memberships K x i).mp hi).1

theorem keyValue_bound {K : GlobalList J} {rank : J → ℕ} {B : ℕ}
    (hrank : ∀ x, rank x < B) (x : J) :
    K.keyValue rank B x < (K.indices.sup id + 1) * B := by
  have hm := Nat.mul_le_mul_right B (K.lastIndex_le_sup x)
  have hx := hrank x
  unfold keyValue
  rw [Nat.add_mul]
  simp only [one_mul]
  omega

theorem carryNumeric_selection {K : GlobalList J} {rank : J → ℕ} {B t : ℕ}
    (hB : 0 < B) (hrank : ∀ x, rank x < B) (x : J) :
    x ∈ (K.carry rank (t/B) (t%B)).Qual ↔
      x ∈ K.Qual ∧ t ≤ K.keyValue rank B x := by
  rw [carry_selection]
  have htmod : t % B < B := Nat.mod_lt _ hB
  have hdiv : t / B * B + t % B = t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t B
  have hlt := pairCode_lt (hrank x) htmod (i := K.lastIndex x) (j := t/B)
  unfold keyValue
  rw [hdiv] at hlt
  constructor
  · rintro ⟨hx, hgt | ⟨he, hr⟩⟩
    · refine ⟨hx, ?_⟩
      by_contra hn
      rcases hlt.mp (by omega) with h | ⟨h, _⟩ <;> omega
    · exact ⟨hx, by omega⟩
  · rintro ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    by_cases he : K.lastIndex x = t/B
    · right
      refine ⟨he, ?_⟩
      rw [he] at ht
      omega
    · left
      by_contra hn
      have hless : K.lastIndex x < t/B := by omega
      have hcode := hlt.mpr (Or.inl hless)
      omega

noncomputable def samePriority (K : GlobalList J) (rank : J → ℕ) (B : ℕ)
    (P : Set J) (x : J) : ℕ := by
  classical
  exact if x ∈ K.Qual then B + K.keyValue rank B x
    else if x ∈ P then rank x else B + (K.indices.sup id + 1) * B + rank x

theorem samePriority_injective {K : GlobalList J} {rank : J → ℕ} {B : ℕ} {P : Set J}
    (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank) :
    Function.Injective (K.samePriority rank B P) := by
  classical
  intro x y he
  have hx := hrank x
  have hy := hrank y
  have hkx := K.keyValue_bound hrank x
  have hky := K.keyValue_bound hrank y
  by_cases hqx : x ∈ K.Qual
  · by_cases hqy : y ∈ K.Qual
    · simp only [samePriority, ite_eq_left hqx, ite_eq_left hqy] at he
      exact keyValue_injective hrank hinj (Nat.add_left_cancel he)
    · by_cases hpy : y ∈ P
      · simp only [samePriority, ite_eq_left hqx, ite_eq_right hqy, ite_eq_left hpy] at he
        omega
      · simp only [samePriority, ite_eq_left hqx, ite_eq_right hqy, ite_eq_right hpy] at he
        omega
  · by_cases hqy : y ∈ K.Qual
    · by_cases hpx : x ∈ P
      · simp only [samePriority, ite_eq_right hqx, ite_eq_left hqy, ite_eq_left hpx] at he
        omega
      · simp only [samePriority, ite_eq_right hqx, ite_eq_left hqy, ite_eq_right hpx] at he
        omega
    · by_cases hpx : x ∈ P <;> by_cases hpy : y ∈ P
      · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_left hpx, ite_eq_left hpy] at he
        exact hinj he
      · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_left hpx, ite_eq_right hpy] at he
        omega
      · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_right hpx, ite_eq_left hpy] at he
        omega
      · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_right hpx, ite_eq_right hpy] at he
        exact hinj (Nat.add_left_cancel he)

theorem samePriority_extends {K : GlobalList J} {rank : J → ℕ} {B : ℕ}
    {P W : Set J} {r : J → J → Prop}
    (hrank : ∀ x, rank x < B) (hstrict : ∀ x y, r x y → rank x < rank y)
    (hup : K.Upsets r) (hP : ∀ x y, r x y → y ∈ P → x ∈ P)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P) :
    ∀ x ∈ W, ∀ y ∈ W, r x y → K.samePriority rank B P x < K.samePriority rank B P y := by
  classical
  intro x hx y hy hxy
  have hr := hstrict x y hxy
  have hrx := hrank x
  have hry := hrank y
  have hkx := K.keyValue_bound hrank x
  have hky := K.keyValue_bound hrank y
  by_cases hqx : x ∈ K.Qual
  · have hqy := K.qual_upset hup hxy hqx
    simp only [samePriority, ite_eq_left hqx, ite_eq_left hqy, Nat.add_lt_add_iff_left]
    exact (keyValue_lt_iff hrx hry).mpr (K.key_extends hup hstrict hqx hxy)
  · by_cases hqy : y ∈ K.Qual
    · have hpx := hP x y hxy (hqual y hy hqy)
      simp only [samePriority, ite_eq_right hqx, ite_eq_left hqy, ite_eq_left hpx]
      omega
    · by_cases hpy : y ∈ P
      · have hpx := hP x y hxy hpy
        simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_left hpx, ite_eq_left hpy]
        exact hr
      · by_cases hpx : x ∈ P
        · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_right hpy, ite_eq_left hpx]
          omega
        · simp only [samePriority, ite_eq_right hqx, ite_eq_right hqy, ite_eq_right hpy, ite_eq_right hpx]
          omega

theorem samePriority_key {K : GlobalList J} {rank : J → ℕ} {B : ℕ} {P : Set J}
    (hrank : ∀ x, rank x < B) {x y : J} (hx : x ∈ K.Qual) (hy : y ∈ K.Qual) :
    K.samePriority rank B P x < K.samePriority rank B P y ↔ K.KeyLT rank x y := by
  classical
  simp only [samePriority, ite_eq_left hx, ite_eq_left hy, Nat.add_lt_add_iff_left]
  exact keyValue_lt_iff (hrank x) (hrank y)

theorem samePriority_cut {K : GlobalList J} {rank : J → ℕ} {B t : ℕ} {P W : Set J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P)
    (ht : t ≤ (K.indices.sup id + 1) * B) :
    ∀ x ∈ W, x ∈ PriorityCut (K.samePriority rank B P) (B+t) ↔
      x ∈ P \ (K.carry rank (t/B) (t%B)).Qual := by
  classical
  intro x hx
  rw [Set.mem_sdiff, carryNumeric_selection hB hrank]
  change K.samePriority rank B P x < B+t ↔ x ∈ P ∧ ¬(x ∈ K.Qual ∧ _)
  by_cases hqx : x ∈ K.Qual
  · have hpx := hqual x hx hqx
    simp only [samePriority, hpx, hqx, ite_true, true_and]
    omega
  · by_cases hpx : x ∈ P
    · simp only [samePriority, hpx, hqx, ite_false, ite_true, false_and, not_false_eq_true,
        and_self, iff_true]
      have := hrank x
      omega
    · simp only [samePriority, hpx, hqx, ite_false, false_and, iff_false]
      omega

end GlobalList
end PriorityEncoding
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SwitchedPriorities
variable {J : Type}

noncomputable def switchPriority (rank : J → ℕ) (B : ℕ) (D : Set J) (x : J) : ℕ := by
  classical
  exact if x ∈ D then B + rank x else rank x

theorem switchPriority_injective {rank : J → ℕ} {B : ℕ} {D : Set J}
    (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank) :
    Function.Injective (switchPriority rank B D) := by
  classical
  intro x y he
  have hx := hrank x
  have hy := hrank y
  by_cases hxD : x ∈ D <;> by_cases hyD : y ∈ D <;>
    simp only [switchPriority, hxD, hyD, ite_true, ite_false] at he
  · exact hinj (Nat.add_left_cancel he)
  · omega
  · omega
  · exact hinj he

theorem switchPriority_extends {r : J → J → Prop} {rank : J → ℕ} {B : ℕ} {D : Set J}
    (hrank : ∀ x, rank x < B) (hstrict : ∀ x y, r x y → rank x < rank y)
    (hup : GlobalUpset r D) :
    ∀ x y, r x y → switchPriority rank B D x < switchPriority rank B D y := by
  classical
  intro x y hxy
  have hlt := hstrict x y hxy
  by_cases hxD : x ∈ D
  · have hyD := hup hxy hxD
    simp only [switchPriority, ite_eq_left hxD, ite_eq_left hyD, Nat.add_lt_add_iff_left]
    exact hlt
  · by_cases hyD : y ∈ D
    · simp only [switchPriority, ite_eq_right hxD, ite_eq_left hyD]
      have := hrank x
      omega
    · simp only [switchPriority, ite_eq_right hxD, ite_eq_right hyD]
      exact hlt

theorem switchPriority_cut {rank : J → ℕ} {B t : ℕ} {D : Set J}
    (ht : t ≤ B) :
    PriorityCut (switchPriority rank B D) t = Dᶜ \ RankTail rank t := by
  classical
  ext x
  change (if x ∈ D then B + rank x else rank x) < t ↔ x ∉ D ∧ ¬t ≤ rank x
  by_cases hx : x ∈ D
  · simp only [hx, ite_true, not_true_eq_false, false_and, iff_false]
    omega
  · simp only [hx, ite_false, not_false_eq_true, true_and, not_le]

namespace GlobalList

theorem pair_lastIndex_right {A D : Set J} {x : J} (hx : x ∈ D) :
    (pair A D).lastIndex x = 1 := by
  have hx1 : x ∈ (pair A D).entry 1 := by simpa [pair] using hx
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have := ((mem_memberships (pair A D) x i).mp hi).1
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl <;> simp
  · exact le_lastIndex (by simp [pair]) hx1

theorem pair_lastIndex_left {A D : Set J} {x : J} (hx : x ∉ D) :
    (pair A D).lastIndex x = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro i hi
  obtain ⟨hi, hxi⟩ := (mem_memberships (pair A D) x i).mp hi
  simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact le_rfl
  · exact (hx (by simpa [pair] using hxi)).elim

theorem switchPair_agreement {rank : J → ℕ} {B t : ℕ} {W G D : Set J}
    (ht : t ≤ B) (hcover : ∀ x ∈ W, x ∉ D → x ∈ G) :
    ∀ x ∈ W, x ∈ (pair (G ∩ RankTail rank t) D).Qual ↔
      x ∉ PriorityCut (switchPriority rank B D) t := by
  rw [switchPriority_cut ht, qual_pair]
  intro x hx
  change (x ∈ G ∧ t ≤ rank x) ∨ x ∈ D ↔ ¬(x ∉ D ∧ ¬t ≤ rank x)
  by_cases hD : x ∈ D
  · simp [hD]
  · have hG := hcover x hx hD
    simp [hD, hG]

theorem switchPair_key {rank : J → ℕ} {B t : ℕ} {G D : Set J}
    (hrank : ∀ x, rank x < B) (x y : J) :
    (pair (G ∩ RankTail rank t) D).KeyLT rank x y ↔
      switchPriority rank B D x < switchPriority rank B D y := by
  classical
  have hx := hrank x
  have hy := hrank y
  unfold KeyLT
  by_cases hxD : x ∈ D <;> by_cases hyD : y ∈ D
  · rw [pair_lastIndex_right hxD, pair_lastIndex_right hyD]
    simp only [lt_self_iff_false, true_and, false_or, switchPriority, ite_eq_left hxD,
      ite_eq_left hyD, Nat.add_lt_add_iff_left]
  · rw [pair_lastIndex_right hxD, pair_lastIndex_left hyD]
    simp only [Nat.not_lt_zero, Nat.one_ne_zero, false_and, false_or, switchPriority,
      ite_eq_left hxD, ite_eq_right hyD, false_iff]
    omega
  · rw [pair_lastIndex_left hxD, pair_lastIndex_right hyD]
    simp only [Nat.zero_lt_one, true_or, switchPriority, ite_eq_right hxD, ite_eq_left hyD, true_iff]
    omega
  · rw [pair_lastIndex_left hxD, pair_lastIndex_left hyD]
    simp only [lt_self_iff_false, true_and, false_or, switchPriority, ite_eq_right hxD, ite_eq_right hyD]

end GlobalList
end SwitchedPriorities
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ReverseSeeds
variable {J A : Type}

structure ReverseSeed (r : J → J → Prop) (time : J → ℕ) (atoms : A → Set J)
    (W : Set J) (B : Boundary J) (b : ℕ) where
  predicate : Set J
  downset : GlobalUpset (fun x y => r y x) predicate
  small : Described atoms predicate 24
  cover : ∀ x ∈ W, x ∉ B.pred r → x ∈ predicate
  earlier : ∀ x ∈ predicate, time x < b

variable {r : J → J → Prop} {time : J → ℕ} {atoms : A → Set J}

theorem reverse_seed_at_edge {T a b ap bp v : ℕ} {B B' V : Boundary J}
    {W E W' S Sstar Hext : Set J}
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hrespect : ∀ x y, r x y → time x < time y)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hB : B.At time T b) (hB' : B'.At time T bp) (hV : V.At time T v)
    (hW : W = Window time a b) (hE : E = Window time a v)
    (hW' : W' = Window time ap bp)
    (hapos : a ≤ ap) (hab : ap < bp) (hbv : bp ≤ v) (hvb : v < b)
    (hhigh : ∀ x ∈ W', x ∉ S → x ∈ B'.pred r)
    (hcovers : ∀ x ∈ W, x ∈ S → x ∈ B.pred r)
    (hbelow : ∀ x ∈ W, x ∈ S → x ∈ Sstar)
    (hcenter : V.Separates r time W Sstar v)
    (hsep : B'.Separates r time E S bp)
    (hH : GlobalUpset (fun x y => r y x) Hext)
    (hagrees : ∀ x ∈ W, x ∈ Hext ↔ x ∈ S)
    (hsmall : Described atoms Hext 21)
    (hPsmall : Described atoms (B.pred r) 1)
    (hDbsmall : Described atoms (B'.weakDesc r) 1)
    (hDvsmall : Described atoms (V.weakDesc r) 1) :
    Nonempty (ReverseSeed r time atoms W' B' bp) := by
  let G := ((B.pred r \ B'.weakDesc r) \ V.weakDesc r) ∩ Hext
  have hup : GlobalUpset (fun x y => r y x) G := by
    intro x y hyx hx
    refine ⟨⟨⟨Boundary.pred_downset htrans B hyx hx.1.1.1, ?_⟩, ?_⟩, hH hyx hx.2⟩
    · intro hy
      exact hx.1.1.2 (Boundary.weakDesc_upset htrans B' hyx hy)
    · intro hy
      exact hx.1.2 (Boundary.weakDesc_upset htrans V hyx hy)
  have hGsmall : Described atoms G 24 := by
    exact ((hPsmall.diff hDbsmall).diff hDvsmall).inter hsmall
  refine ⟨⟨G, hup, hGsmall, ?_, ?_⟩⟩
  · intro x hx hnP
    have hxt : x ∈ Window time ap bp := hW' ▸ hx
    change ap < time x ∧ time x < bp at hxt
    have hxW : x ∈ W := hW ▸ show x ∈ Window time a b from ⟨by omega, by omega⟩
    have hxS : x ∈ S := by by_contra hn; exact hnP (hhigh x hx hn)
    refine ⟨⟨⟨hcovers x hxW hxS, ?_⟩, ?_⟩, (hagrees x hxW).mpr hxS⟩
    · intro hD
      have := Boundary.weakDesc_time hrespect hbound hB' hD
      omega
    · intro hD
      have := Boundary.weakDesc_time hrespect hbound hV hD
      omega
  · intro x hx
    have hxb := Boundary.pred_time hrespect hbound hB hx.1.1.1
    by_contra hn
    have hxW : x ∈ W := hW ▸ show x ∈ Window time a b from ⟨by omega, hxb⟩
    have hxS := (hagrees x hxW).mp hx.2
    have hxv : time x < v := by
      by_contra hnv
      rcases (show v ≤ time x by omega).eq_or_lt with he | hl
      · exact hx.1.2 (Boundary.mem_weak_at_time hbound hV he.symm).2
      · exact hx.1.2 (V.desc_subset_weakDesc r (hcenter.2 x hxW hl (hbelow x hxW hxS)))
    have hxE : x ∈ E := hE ▸ show x ∈ Window time a v from ⟨by omega, hxv⟩
    rcases (show bp ≤ time x by omega).eq_or_lt with he | hl
    · exact hx.1.1.2 (Boundary.mem_weak_at_time hbound hB' he.symm).2
    · exact hx.1.1.2 (B'.desc_subset_weakDesc r (hsep.2 x hxE hl hxS))

variable [Fintype J]

def ReverseSeed.reorder {p q : Layout J} {W : Set J} {B : Boundary J} {a b : ℕ}
    (D : ReverseSeed r p.time atoms W B b)
    (hW : W = Window p.time a b) (hfix : p.FixedOutside q W) :
    ReverseSeed r q.time atoms W B b := by
  refine { D with earlier := ?_ }
  intro x hx
  by_cases hxW : x ∈ W
  · exact ((hfix.time_range (fun z hz => hW ▸ hz) hxW)).2
  · rw [hfix.time hxW]
    exact D.earlier x hx

end ReverseSeeds
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section DescriptionInterface
variable {J A : Type} {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}

structure AtomSupport (atoms : A → Set J) (r : J → J → Prop) (rank : J → ℕ) : Prop where
  truth : Described atoms Set.univ 1
  falsity : Described atoms ∅ 1
  rankTail : ∀ k, Described atoms (RankTail rank k) 1
  pred : ∀ B : Boundary J, Described atoms (B.pred r) 1
  desc : ∀ B : Boundary J, Described atoms (B.desc r) 1
  weakPred : ∀ B : Boundary J, Described atoms (B.weakPred r) 1
  weakDesc : ∀ B : Boundary J, Described atoms (B.weakDesc r) 1
  triple : ∀ Z : Triple J, Described atoms (Z.val : Set J) 1

namespace RunData
variable {K : GlobalList J} {W : Set J}

theorem qual_small (D : RunData K rank atoms W) (hA : AtomSupport atoms r rank)
    (hcard : K.indices.card ≤ 5) : Described atoms K.Qual 195 := by
  classical
  by_cases hne : K.indices.Nonempty
  · have hd := Described.finite_union K.indices K.entry (fun _ => 25) hne
      (fun i hi => D.entry_small hA.rankTail hi)
    apply hd.mono
    simp only [Finset.sum_const, smul_eq_mul]
    omega
  · have hzero : K.indices = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have he : K.Qual = ∅ := by ext x; simp [GlobalList.Qual, hzero]
    rw [he]
    exact hA.falsity.mono (by omega)

theorem carry_cutoff_small (D : RunData K rank atoms W) (hA : AtomSupport atoms r rank)
    (hcard : K.indices.card ≤ 5) (B : Boundary J) (d k : ℕ) :
    Described atoms (B.pred r \ (K.carry rank d k).Qual) 205 := by
  have hc : (K.carry rank d k).indices.card ≤ 5 := by
    exact (Finset.card_filter_le _ _).trans hcard
  exact ((hA.pred B).diff ((D.carry d k).qual_small hA hc)).mono (by omega)

theorem carry_low_extension (D : RunData K rank atoms W)
    (hA : AtomSupport atoms r rank) (hcard : K.indices.card ≤ 5)
    (hK : K.Upsets r) (hsecond : GlobalUpset r D.second)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (B : Boundary J) (d k : ℕ) :
    ∃ H : Set J, GlobalUpset (fun x y => r y x) H ∧ Described atoms H 21 ∧
      ∀ x ∈ W, x ∈ H ↔ x ∈ B.pred r \ (K.carry rank d k).Qual := by
  have hc : (K.carry rank d k).indices.card ≤ 5 :=
    (Finset.card_filter_le _ _).trans hcard
  obtain ⟨U, hUup, hUsmall, hUagree⟩ := (D.carry d k).short_upset_extension
    (GlobalList.carry_upsets hK hstrict) hsecond hstrict hA.rankTail hA.falsity hc
  refine ⟨B.pred r \ U, ?_, (hA.pred B).diff hUsmall, ?_⟩
  · intro x y hyx hx
    exact ⟨Boundary.pred_downset htrans B hyx hx.1, fun hyU => hx.2 (hUup hyx hyU)⟩
  · intro x hx
    simp only [Set.mem_sdiff, hUagree x hx]

end RunData

theorem global_child_small
    {A' B B' V : Boundary J} {W' S Stilde : Set J} {K' : GlobalList J}
    (hA : AtomSupport atoms r rank)
    (hqual : Described atoms K'.Qual 195)
    (hcut : Described atoms Stilde 205)
    (hhigh : W' \ S = (K'.Qual ∩ B'.pred r) \ A'.weakPred r)
    (hlow : W' ∩ S = (((A'.desc r ∩ B.pred r) \ B'.weakDesc r) \ V.weakDesc r) ∩ Stilde) :
    Described atoms W' 406 := by
  have hh : Described atoms (W' \ S) 197 := by
    rw [hhigh]
    exact (hqual.inter (hA.pred B')).diff (hA.weakPred A')
  have hl : Described atoms (W' ∩ S) 209 := by
    rw [hlow]
    exact ((((hA.desc A').inter (hA.pred B)).diff (hA.weakDesc B')).diff (hA.weakDesc V)).inter hcut
  have he : W' = (W' \ S) ∪ (W' ∩ S) := by ext x; simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [he]
  exact hh.union hl

end DescriptionInterface
end ThreeMachine.Structure

namespace ThreeMachine.Structure
namespace GlobalList
section SameUpdate
variable {J : Type} {K : GlobalList J} {rank : J → ℕ}

noncomputable def sameUpdate (K : GlobalList J) (rank : J → ℕ) (B t : ℕ)
    (D P : Set J) : GlobalList J :=
  (K.carry rank (t/B) (t%B)).append (D \ P)

theorem carry_qual_subset (K : GlobalList J) (rank : J → ℕ) (d k : ℕ) :
    (K.carry rank d k).Qual ⊆ K.Qual := by
  intro x hx
  exact ((carry_selection K rank d k x).mp hx).1

theorem sameUpdate_agreement {B t : ℕ} {W D P : Set J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P)
    (hcover : ∀ x ∈ W, x ∈ D ∨ x ∈ P)
    (ht : t ≤ (K.indices.sup id + 1) * B) :
    ∀ x ∈ W, x ∈ (K.sameUpdate rank B t D P).Qual ↔
      x ∉ PriorityCut (K.samePriority rank B P) (B+t) := by
  intro x hx
  rw [samePriority_cut hB hrank hqual ht x hx]
  change x ∈ ((K.carry rank (t/B) (t%B)).append (D \ P)).Qual ↔ _
  rw [append_qual]
  have hc : x ∈ (K.carry rank (t/B) (t%B)).Qual → x ∈ P :=
    fun h => hqual x hx (carry_qual_subset K rank _ _ h)
  have hd := hcover x hx
  simp only [Set.mem_union, Set.mem_sdiff]
  tauto

theorem sameUpdate_disjoint {B t : ℕ} {W D P : Set J}
    (hdisj : K.InjectionDisjoint W)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P) :
    (K.sameUpdate rank B t D P).InjectionDisjoint W := by
  apply (hdisj.carry _ _).append
  intro x hx hI hC
  exact hI.2 (hqual x hx (carry_qual_subset K rank _ _ hC))

theorem sameUpdate_upsets {B t : ℕ} {D P : Set J} {r : J → J → Prop}
    (hK : K.Upsets r) (hD : GlobalUpset r D)
    (hP : GlobalUpset (fun x y => r y x) P)
    (hstrict : ∀ x y, r x y → rank x < rank y) :
    (K.sameUpdate rank B t D P).Upsets r := by
  apply append_upsets (carry_upsets hK hstrict)
  intro x y hxy hx
  exact ⟨hD hxy hx.1, fun hyP => hx.2 (hP hxy hyP)⟩

theorem sameUpdate_key {B t : ℕ} {W D P : Set J}
    (hrank : ∀ x, rank x < B)
    (hqual : ∀ x ∈ W, x ∈ K.Qual → x ∈ P)
    {x y : J} (hxW : x ∈ W) (hyW : y ∈ W)
    (hx : x ∈ (K.sameUpdate rank B t D P).Qual)
    (hy : y ∈ (K.sameUpdate rank B t D P).Qual) :
    (K.sameUpdate rank B t D P).KeyLT rank x y ↔
      K.samePriority rank B P x < K.samePriority rank B P y := by
  classical
  let C := K.carry rank (t/B) (t%B)
  let I := D \ P
  change x ∈ (C.append I).Qual at hx
  change y ∈ (C.append I).Qual at hy
  change (C.append I).KeyLT rank x y ↔ _
  have hCx : x ∈ C.Qual → x ∈ K.Qual := fun hx => carry_qual_subset K rank _ _ hx
  have hCy : y ∈ C.Qual → y ∈ K.Qual := fun hy => carry_qual_subset K rank _ _ hy
  have hvx := K.keyValue_bound hrank x
  have hvy := K.keyValue_bound hrank y
  by_cases hxI : x ∈ I <;> by_cases hyI : y ∈ I
  · have hxP : x ∉ P := hxI.2
    have hyP : y ∉ P := hyI.2
    have hxK : x ∉ K.Qual := fun h => hxP (hqual x hxW h)
    have hyK : y ∉ K.Qual := fun h => hyP (hqual y hyW h)
    simp only [KeyLT, append_lastIndex_of_mem hxI, append_lastIndex_of_mem hyI,
      lt_self_iff_false, true_and, false_or, samePriority, ite_eq_right hxK, ite_eq_right hyK,
      ite_eq_right hxP, ite_eq_right hyP, Nat.add_lt_add_iff_left]
  · have hyC : y ∈ C.Qual := by rw [append_qual] at hy; exact hy.resolve_right hyI
    have hxP : x ∉ P := hxI.2
    have hxK : x ∉ K.Qual := fun h => hxP (hqual x hxW h)
    have hbefore := lt_nextIndex (lastIndex_mem hyC).1
    simp only [KeyLT, append_lastIndex_of_mem hxI, append_lastIndex_of_not_mem hyI,
      samePriority, ite_eq_right hxK, ite_eq_right hxP, ite_eq_left (hCy hyC)]
    constructor <;> intro h <;> omega
  · have hxC : x ∈ C.Qual := by rw [append_qual] at hx; exact hx.resolve_right hxI
    have hyP : y ∉ P := hyI.2
    have hyK : y ∉ K.Qual := fun h => hyP (hqual y hyW h)
    have hbefore := lt_nextIndex (lastIndex_mem hxC).1
    simp only [KeyLT, append_lastIndex_of_not_mem hxI, append_lastIndex_of_mem hyI,
      samePriority, ite_eq_left (hCx hxC), ite_eq_right hyK, ite_eq_right hyP]
    constructor
    · intro _
      omega
    · intro _
      exact Or.inl hbefore
  · have hxC : x ∈ C.Qual := by rw [append_qual] at hx; exact hx.resolve_right hxI
    have hyC : y ∈ C.Qual := by rw [append_qual] at hy; exact hy.resolve_right hyI
    rw [append_key_of_not_mem hxI hyI, carry_key hxC hyC]
    exact (samePriority_key hrank (hCx hxC) (hCy hyC)).symm

end SameUpdate
end GlobalList
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SameBoundaryUpdate
variable {J : Type} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
theorem Boundary.desc_eq_of_interior {r : J → J → Prop} {time : J → ℕ}
    {T a : ℕ} {A : Boundary J} (hA : A.At time T a) (ha : 1 ≤ a ∧ a ≤ T) :
    A.desc r = DescAt r time a := by
  cases A with
  | left => simp only [Boundary.At] at hA; omega
  | right => simp only [Boundary.At] at hA; omega
  | actual Z => exact Boundary.actual_desc_eq hA

theorem sameUpdate_past {r : J → J → Prop} {p : Layout J} {rank : J → ℕ}
    {a b v ap B t : ℕ} {A Z A' : Boundary J} {W : Set J} {E : Finset J}
    {K : GlobalList J}
    (hp : p.Full r) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : A.At p.time (Fintype.card J / 3) a)
    (hA' : A'.At p.time (Fintype.card J / 3) ap)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hE : ∀ x, x ∈ E ↔ a < p.time x ∧ p.time x < v)
    (hv : v < b) (ha : a ≤ Fintype.card J / 3) (hap : ap < v)
    (hB : 0 < B) (hrank : ∀ x, rank x < B)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hK : K.Upsets r)
    (hhigh : ∀ x ∈ W, x ∈ K.Qual → x ∈ Z.pred r)
    (hlow : ∀ x ∈ W, x ∉ K.Qual → x ∈ A.desc r)
    (hpast : PastInvariant r p.time K A a)
    (hswap : SwapInvariant r p W K rank A a)
    (ht : t ≤ (K.indices.sup id + 1) * B)
    (hnorm : LocalObstruction E r p.time (K.samePriority rank B (Z.pred r)))
    (hsep : A'.Separates r p.time E
      (PriorityCut (K.samePriority rank B (Z.pred r)) (B+t)) ap)
    (hwalk : CutoffWalk E r p.time (K.samePriority rank B (Z.pred r))
      (PriorityCut (K.samePriority rank B (Z.pred r)) (B+t)) a ap) :
    PastInvariant r p.time (K.sameUpdate rank B t (A.desc r) (Z.pred r)) A' ap := by
  let H := (K.carry rank (t/B) (t%B)).Qual
  have hEW : (E : Set J) ⊆ W := by
    intro x hx
    have hxE := (hE x).mp hx
    exact (hW x).mpr ⟨hxE.1, hxE.2.trans hv⟩
  have hcover : ∀ x ∈ W, x ∈ A.desc r ∨ x ∈ Z.pred r := by
    intro x hx
    by_cases hq : x ∈ K.Qual
    · exact Or.inr (hhigh x hx hq)
    · exact Or.inl (hlow x hx hq)
  have hagree := GlobalList.sameUpdate_agreement hB hrank hhigh hcover ht
  have hHhigh : ∀ x ∈ E, x ∈ H → x ∉ PriorityCut
      (K.samePriority rank B (Z.pred r)) (B+t) := by
    intro x hx hH hS
    have := (GlobalList.samePriority_cut hB hrank hhigh ht x (hEW hx)).mp hS
    exact this.2 hH
  apply past_update hp htrans hA hA' ha hap hE hpast
    (GlobalList.qual_upset (GlobalList.carry_upsets hK hstrict))
    (GlobalList.carry_qual_subset K rank (t/B) (t%B))
  · intro x hx hxa
    rw [GlobalList.sameUpdate, GlobalList.append_qual] at hx
    rcases hx with hx | hx
    · exact hx
    · have := Boundary.desc_time hp.2 (p.time_bounds hp.1) hA hx.1
      omega
  · intro x hx hq
    exact (hagree x (hEW hx)).mp hq
  · exact hHhigh
  · exact hsep
  · exact hnorm
  · intro U hUideal _hUpre hUsub x hx
    apply first_boundary_force htrans hp.2 hE hUideal hx
    intro y hy hya
    have habound : 1 ≤ a ∧ a ≤ Fintype.card J / 3 := hya ▸ p.time_bounds hp.1 y
    have hxD : x ∉ A.desc r := by
      rw [Boundary.desc_eq_of_interior hA habound]
      exact hx.not_desc
    have hxW : x ∈ W := hEW hx.mem
    have hxK : x ∈ K.Qual := by by_contra hn; exact hxD (hlow x hxW hn)
    have hyK : y ∈ K.Qual := GlobalList.carry_qual_subset K rank _ _ hy
    have hxS := hUsub x hx.mem hx.low
    have hyval : t ≤ K.keyValue rank B y :=
      ((GlobalList.carryNumeric_selection hB hrank y).mp hy).2
    have hpriority : K.samePriority rank B (Z.pred r) x <
        K.samePriority rank B (Z.pred r) y := by
      change K.samePriority rank B (Z.pred r) x < B+t at hxS
      have hypri : K.samePriority rank B (Z.pred r) y = B + K.keyValue rank B y := by
        simp only [GlobalList.samePriority, ite_eq_left hyK]
      rw [hypri]
      omega
    exact hswap p (Layout.FixedOutside.refl p W) hp.2 x hxW hxD y hya hyK
      ((GlobalList.samePriority_key hrank hxK hyK).mp hpriority)
  · exact hwalk

theorem sameUpdate_swap_inherited {r : J → J → Prop} {p : Layout J}
    {rank : J → ℕ} {K : GlobalList J} {W W' : Set J}
    {A Z : Boundary J} {a b B t : ℕ}
    (hp : p.Full r) (hA : A.At p.time (Fintype.card J / 3) a)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b) (hsub : W' ⊆ W)
    (hparent : SwapInvariant r p W K rank A a)
    (hqual : ∀ x ∈ W', x ∉ A.desc r →
      x ∈ (K.sameUpdate rank B t (A.desc r) (Z.pred r)).Qual) :
    SwapInvariant r p W' (K.sameUpdate rank B t (A.desc r) (Z.pred r)) rank A a := by
  intro q hfix hq x hx hnx y hy hyq hkey
  have hAq := (hfix.mono hsub).boundary hW (Or.inl le_rfl) hA
  have hyD : y ∉ A.desc r := by
    intro hD
    have := Boundary.desc_time hq (q.time_bounds hp.1) hAq hD
    omega
  have hxI : x ∉ A.desc r \ Z.pred r := fun h => hnx h.1
  have hyI : y ∉ A.desc r \ Z.pred r := fun h => hyD h.1
  have hxC : x ∈ (K.carry rank (t/B) (t%B)).Qual := by
    have h := hqual x hx hnx
    rw [GlobalList.sameUpdate, GlobalList.append_qual] at h
    exact h.resolve_right hxI
  have hyC : y ∈ (K.carry rank (t/B) (t%B)).Qual := by
    rw [GlobalList.sameUpdate, GlobalList.append_qual] at hyq
    exact hyq.resolve_right hyI
  have hkeyOld : K.KeyLT rank x y := by
    change ((K.carry rank (t/B) (t%B)).append (A.desc r \ Z.pred r)).KeyLT rank x y at hkey
    exact (GlobalList.carry_key hxC hyC).mp
      ((GlobalList.append_key_of_not_mem hxI hyI).mp hkey)
  exact hparent q (hfix.mono hsub) hq x (hsub hx) hnx y hy
    (GlobalList.carry_qual_subset K rank _ _ hyC) hkeyOld

end SameBoundaryUpdate
end ThreeMachine.Structure

end

end OAI
