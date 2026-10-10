import OAI.Computability.Scheduling.GlobalBoundaries

namespace OAI

section

namespace ThreeMachine.Structure
namespace GlobalList
variable {J : Type}

noncomputable def append (K : GlobalList J) (A : Set J) : GlobalList J := by
  classical
  exact ⟨insert (max 1 (K.indices.sup id) + 1) K.indices,
    fun i => if i = max 1 (K.indices.sup id) + 1 then A else K.entry i⟩

def nextIndex (K : GlobalList J) : ℕ := max 1 (K.indices.sup id) + 1

theorem lt_nextIndex {K : GlobalList J} {i : ℕ} (hi : i ∈ K.indices) :
    i < K.nextIndex := by
  have h := Finset.le_sup (f := id) hi
  change i ≤ K.indices.sup id at h
  dsimp [nextIndex]
  omega

theorem nextIndex_not_mem (K : GlobalList J) : K.nextIndex ∉ K.indices := by
  intro hi
  exact (lt_irrefl _ (lt_nextIndex hi)).elim

theorem append_membership (K : GlobalList J) (A : Set J) (i : ℕ) (x : J) :
    i ∈ (K.append A).memberships x ↔
      (i = K.nextIndex ∧ x ∈ A) ∨ (i ∈ K.indices ∧ x ∈ K.entry i) := by
  classical
  rw [mem_memberships]
  change (i ∈ insert K.nextIndex K.indices ∧
    x ∈ (if i = K.nextIndex then A else K.entry i)) ↔ _
  by_cases hi : i = K.nextIndex
  · subst i
    simp [nextIndex_not_mem]
  · simp [hi]

theorem append_qual (K : GlobalList J) (A : Set J) :
    (K.append A).Qual = K.Qual ∪ A := by
  ext x
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases (append_membership K A i x).mp ((mem_memberships _ _ _).mpr ⟨hi, hx⟩)
      with ⟨_, hx⟩ | ⟨hi, hx⟩
    · exact Or.inr hx
    · exact Or.inl ⟨i, hi, hx⟩
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, (mem_memberships _ _ _).mp
        ((append_membership K A i x).mpr (Or.inr ⟨hi, hx⟩))⟩
    · exact ⟨K.nextIndex, (mem_memberships _ _ _).mp
        ((append_membership K A _ x).mpr (Or.inl ⟨rfl, hx⟩))⟩

theorem append_upsets {K : GlobalList J} {A : Set J} {r : J → J → Prop}
    (hK : K.Upsets r) (hA : GlobalUpset r A) : (K.append A).Upsets r := by
  classical
  intro i hi
  change i ∈ insert K.nextIndex K.indices at hi
  rcases Finset.mem_insert.mp hi with hi | hi
  · subst i
    simpa [append, nextIndex] using hA
  · have hn : i ≠ K.nextIndex := (lt_nextIndex hi).ne
    change GlobalUpset r (if i = K.nextIndex then A else K.entry i)
    simpa [hn] using hK i hi

theorem append_lastIndex_of_mem {K : GlobalList J} {A : Set J} {x : J}
    (hx : x ∈ A) : (K.append A).lastIndex x = K.nextIndex := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    rcases (append_membership K A i x).mp hi with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hi.le
    · exact (lt_nextIndex hi).le
  · apply Finset.le_sup (f := id) (b := K.nextIndex)
    exact (append_membership K A _ x).mpr (Or.inl ⟨rfl, hx⟩)

theorem append_lastIndex_of_not_mem {K : GlobalList J} {A : Set J} {x : J}
    (hx : x ∉ A) : (K.append A).lastIndex x = K.lastIndex x := by
  apply congrArg (fun s : Finset ℕ => s.sup id)
  ext i
  rw [append_membership, mem_memberships]
  simp [hx]

theorem append_key_of_not_mem {K : GlobalList J} {A : Set J} {rank : J → ℕ}
    {x y : J} (hx : x ∉ A) (hy : y ∉ A) :
    (K.append A).KeyLT rank x y ↔ K.KeyLT rank x y := by
  simp only [KeyLT, append_lastIndex_of_not_mem hx, append_lastIndex_of_not_mem hy]

theorem append_old_before_new {K : GlobalList J} {A : Set J} {rank : J → ℕ}
    {x y : J} (hx : x ∈ K.Qual) (hxA : x ∉ A) (hy : y ∈ A) :
    (K.append A).KeyLT rank x y := by
  apply Or.inl
  rw [append_lastIndex_of_not_mem hxA, append_lastIndex_of_mem hy]
  exact lt_nextIndex (lastIndex_mem hx).1

theorem injection_card_bound {K : GlobalList J} {r : J → J → Prop}
    {W W' : Set J} {B : Finset J} {I : Finset ℕ}
    (hI : I ⊆ K.indices) (hK : K.Upsets r)
    (hB : (B : Set J) ⊆ W)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∀ x ∈ W, x ∈ K.entry i → x ∉ K.entry j)
    (hmeet : ∀ i ∈ I, (K.entry i ∩ W').Nonempty)
    (hpred : ∀ x ∈ W', x ∈ K.Qual → ∃ z ∈ B, r x z) : I.card ≤ B.card := by
  classical
  have hex : ∀ i ∈ I, ∃ z ∈ B, z ∈ K.entry i := by
    intro i hi
    obtain ⟨x, hxi, hxW⟩ := hmeet i hi
    obtain ⟨z, hz, hxz⟩ := hpred x hxW ⟨i, hI hi, hxi⟩
    exact ⟨z, hz, hK i (hI hi) hxz hxi⟩
  let f : ↥I → ↥B := fun i =>
    ⟨Classical.choose (hex i.val i.property), (Classical.choose_spec (hex i.val i.property)).1⟩
  have hf : ∀ i : ↥I, (f i).val ∈ K.entry i.val := fun i =>
    (Classical.choose_spec (hex i.val i.property)).2
  have hinj : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hne
    have e : (f i).val = (f j).val := congrArg Subtype.val he
    exact hdisj i.val i.property j.val j.property hne (f i).val
      (hB (f i).property) (hf i) (e ▸ hf j)
  simpa using Fintype.card_le_of_injective f hinj

end GlobalList
end ThreeMachine.Structure

namespace ThreeMachine.Structure
variable {J : Type}

def Window (time : J → ℕ) (a b : ℕ) : Set J := {x | a < time x ∧ time x < b}

namespace Boundary

theorem pred_subset_weakPred (r : J → J → Prop) (B : Boundary J) :
    B.pred r ⊆ B.weakPred r := by
  cases B with
  | left => exact Set.Subset.rfl
  | right => exact Set.Subset.rfl
  | actual Z => exact Set.subset_union_left

theorem desc_subset_weakDesc (r : J → J → Prop) (B : Boundary J) :
    B.desc r ⊆ B.weakDesc r := by
  cases B with
  | left => exact Set.Subset.rfl
  | right => exact Set.Subset.rfl
  | actual Z => exact Set.subset_union_left

def Separates (B : Boundary J) (r : J → J → Prop) (time : J → ℕ)
    (W S : Set J) (s : ℕ) : Prop :=
  (∀ x ∈ W, time x < s → x ∉ S → x ∈ B.pred r) ∧
  (∀ x ∈ W, s < time x → x ∈ S → x ∈ B.desc r)

def before (B : Boundary J) (r : J → J → Prop) (H : Set J) : Set J :=
  B.pred r ∪ (H \ B.weakDesc r)

theorem separates_description {r : J → J → Prop} {time : J → ℕ} {T s : ℕ}
    {B : Boundary J} {W S H : Set J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    (hsep : B.Separates r time W S s) (hagree : ∀ x ∈ W, x ∈ H ↔ x ∈ S) :
    ∀ x ∈ W, x ∈ B.before r H ↔ time x < s := by
  intro x hx
  constructor
  · rintro (hP | ⟨hH, hnD⟩)
    · exact pred_time hrespect hbound hB hP
    · have hS := (hagree x hx).mp hH
      by_contra hn
      have hle : s ≤ time x := by omega
      rcases hle.eq_or_lt with he | hl
      · exact hnD (mem_weak_at_time hbound hB he.symm).2
      · exact hnD (desc_subset_weakDesc r B (hsep.2 x hx hl hS))
  · intro hlt
    by_cases hS : x ∈ S
    · refine Or.inr ⟨(hagree x hx).mpr hS, ?_⟩
      intro hD
      have := weakDesc_time hrespect hbound hB hD
      omega
    · exact Or.inl (hsep.1 x hx hlt hS)

theorem separates_congr {r : J → J → Prop} {time : J → ℕ}
    {B : Boundary J} {W S S' : Set J} {s : ℕ}
    (h : ∀ x ∈ W, x ∈ S ↔ x ∈ S') :
    B.Separates r time W S s ↔ B.Separates r time W S' s := by
  unfold Separates
  constructor <;> rintro ⟨hp, hd⟩
  · exact ⟨fun x hx ht hn => hp x hx ht (fun hs => hn ((h x hx).mp hs)),
      fun x hx ht hs => hd x hx ht ((h x hx).mpr hs)⟩
  · exact ⟨fun x hx ht hn => hp x hx ht (fun hs => hn ((h x hx).mpr hs)),
      fun x hx ht hs => hd x hx ht ((h x hx).mp hs)⟩

theorem left_separates {r : J → J → Prop} {time : J → ℕ} {W S : Set J} :
    (Boundary.left : Boundary J).Separates r time W S 0 := by
  exact ⟨fun _ _ h _ => (Nat.not_lt_zero _ h).elim, fun _ _ _ _ => trivial⟩

theorem right_separates {r : J → J → Prop} {time : J → ℕ} {T : ℕ}
    {W S : Set J} (hbound : ∀ x ∈ W, time x ≤ T) :
    (Boundary.right : Boundary J).Separates r time W S (T + 1) := by
  refine ⟨fun _ _ _ _ => trivial, ?_⟩
  intro x hx h _
  have := hbound x hx
  omega

theorem actual_separates {r : J → J → Prop} {time : J → ℕ} {T s : ℕ}
    {Z : Triple J} {W : Finset J} {S : Set J}
    (hZ : (Boundary.actual Z).At time T s) :
    (Boundary.actual Z).Separates r time W S s ↔ Separator W r time S s := by
  unfold Separates Separator EarlierHigh LaterLow
  rw [actual_pred_eq hZ, actual_desc_eq hZ]
  rfl

end Boundary

def PastInvariant (r : J → J → Prop) (time : J → ℕ)
    (K : GlobalList J) (A : Boundary J) (a : ℕ) : Prop :=
  ∀ x ∈ K.Qual, time x ≤ a → x ∈ A.weakPred r

theorem past_prune {r : J → J → Prop} {time : J → ℕ}
    {K : GlobalList J} {A : Boundary J} {a : ℕ} {W : Set J}
    (h : PastInvariant r time K A a) : PastInvariant r time (K.prune W) A a := by
  intro x hx ht
  exact h x (K.prune_qual_subset W hx) ht

theorem global_high_identity {r : J → J → Prop} {time : J → ℕ} {T a b : ℕ}
    {A B : Boundary J} {K : GlobalList J} {S : Set J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hA : A.At time T a) (hB : B.At time T b)
    (hlabels : ∀ x ∈ Window time a b, x ∈ K.Qual ↔ x ∉ S)
    (hhigh : ∀ x ∈ Window time a b, x ∉ S → x ∈ B.pred r)
    (hpast : PastInvariant r time K A a) :
    Window time a b \ S = K.Qual ∩ B.pred r ∩ (A.weakPred r)ᶜ := by
  ext x
  constructor
  · rintro ⟨hx, hS⟩
    refine ⟨⟨(hlabels x hx).mpr hS, hhigh x hx hS⟩, ?_⟩
    intro hbad
    have ht := A.weakPred_time hrespect hbound hA hbad
    exact (not_le_of_gt hx.1) ht
  · rintro ⟨⟨hq, hP⟩, hnP⟩
    have hxb := B.pred_time hrespect hbound hB hP
    have hax : a < time x := by
      by_contra h
      exact hnP (hpast x hq (by omega))
    exact ⟨⟨hax, hxb⟩, (hlabels x ⟨hax, hxb⟩).mp hq⟩

theorem global_low_identity {r : J → J → Prop} {time : J → ℕ}
    {T a b ap bp v : ℕ} {A' B B' V : Boundary J} {S Sstar H : Set J}
    (hrespect : ∀ u z, r u z → time u < time z)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hA' : A'.At time T ap) (hB : B.At time T b)
    (hB' : B'.At time T bp) (hV : V.At time T v)
    (ha : a ≤ ap) (_hap : ap < bp) (hbp : bp ≤ v) (hvb : v < b)
    (hagree : ∀ x ∈ Window time a b, x ∈ H ↔ x ∈ S)
    (hsub : ∀ x ∈ Window time a b, x ∈ S → x ∈ Sstar)
    (hcenter : V.Separates r time (Window time a b) Sstar v)
    (hend : B'.Separates r time (Window time a v) S bp)
    (hlow : ∀ x ∈ Window time ap bp, x ∈ S → x ∈ A'.desc r ∩ B.pred r) :
    Window time ap bp ∩ S =
      A'.desc r ∩ B.pred r ∩ (B'.weakDesc r)ᶜ ∩ (V.weakDesc r)ᶜ ∩ H := by
  ext x
  constructor
  · rintro ⟨hx, hS⟩
    have hxW : x ∈ Window time a b := ⟨by have := hx.1; omega, by have := hx.2; omega⟩
    refine ⟨⟨⟨hlow x hx hS, ?_⟩, ?_⟩, (hagree x hxW).mpr hS⟩
    · intro hbad
      have := B'.weakDesc_time hrespect hbound hB' hbad
      have := hx.2
      omega
    · intro hbad
      have := V.weakDesc_time hrespect hbound hV hbad
      have := hx.2
      omega
  · rintro ⟨⟨⟨⟨hD, hP⟩, hnB⟩, hnV⟩, hH⟩
    have hapx := A'.desc_time hrespect hbound hA' hD
    have hxb := B.pred_time hrespect hbound hB hP
    have hxW : x ∈ Window time a b := ⟨by omega, hxb⟩
    have hS := (hagree x hxW).mp hH
    have hxv : time x < v := by
      by_contra h
      have hle : v ≤ time x := by omega
      rcases hle.eq_or_lt with he | hl
      · exact hnV (Boundary.mem_weak_at_time hbound hV he.symm).2
      · exact hnV (V.desc_subset_weakDesc r (hcenter.2 x hxW hl (hsub x hxW hS)))
    have hxbp : time x < bp := by
      by_contra h
      have hle : bp ≤ time x := by omega
      rcases hle.eq_or_lt with he | hl
      · exact hnB (Boundary.mem_weak_at_time hbound hB' he.symm).2
      · have hxE : x ∈ Window time a v := ⟨by omega, hxv⟩
        exact hnB (B'.desc_subset_weakDesc r (hend.2 x hxE hl hS))
    exact ⟨⟨hapx, hxbp⟩, hS⟩

end ThreeMachine.Structure

namespace ThreeMachine.Structure
variable {J : Type}

def SwitchSet (r : J → J → Prop) (A₀ A V : Boundary J) (Hext : Set J) : Set J :=
  A₀.desc r ∩ (A.weakPred r)ᶜ ∩ (V.weakPred r)ᶜ ∩ Hext

theorem switchSet_upset {r : J → J → Prop}
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (A₀ A V : Boundary J) {Hext : Set J} (hH : GlobalUpset r Hext) :
    GlobalUpset r (SwitchSet r A₀ A V Hext) := by
  exact (((A₀.desc_upset htrans).inter (A.weakPred_downset htrans).compl).inter
    (V.weakPred_downset htrans).compl).inter hH

theorem switchSet_properties {r : J → J → Prop} {time : J → ℕ}
    {T a₀ b₀ v₀ a b : ℕ} {A₀ A V : Boundary J} {H Hstar Hext : Set J}
    (hrespect : ∀ x y, r x y → time x < time y)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hA₀ : A₀.At time T a₀) (hA : A.At time T a) (hV : V.At time T v₀)
    (ha₀v : a₀ < v₀) (hva : v₀ ≤ a) (hab : a < b) (hbb₀ : b ≤ b₀)
    (hagree : ∀ x ∈ Window time a₀ b₀, x ∈ Hext ↔ x ∈ H)
    (hsub : ∀ x ∈ Window time a₀ b₀, x ∈ H → x ∈ Hstar)
    (hdesc : ∀ x ∈ Window time a₀ b₀, x ∈ H → x ∈ A₀.desc r)
    (holdHigh : ∀ x ∈ Window time a b, x ∉ H → x ∈ A.desc r)
    (hcenter : V.Separates r time (Window time a₀ b₀) Hstarᶜ v₀)
    (hend : A.Separates r time (Window time v₀ b₀) Hᶜ a) :
    (Window time a b \ A.desc r ⊆ SwitchSet r A₀ A V Hext) ∧
    (∀ x ∈ SwitchSet r A₀ A V Hext, a < time x) := by
  constructor
  · rintro x ⟨hxW, hnD⟩
    have hxU : x ∈ Window time a₀ b₀ :=
      ⟨by have := hxW.1; omega, by have := hxW.2; omega⟩
    have hxH : x ∈ H := by
      by_contra hnH
      exact hnD (holdHigh x hxW hnH)
    refine ⟨⟨⟨hdesc x hxU hxH, ?_⟩, ?_⟩, (hagree x hxU).mpr hxH⟩
    · intro hP
      have := A.weakPred_time hrespect hbound hA hP
      have := hxW.1
      omega
    · intro hP
      have := V.weakPred_time hrespect hbound hV hP
      have := hxW.1
      omega
  · rintro x ⟨⟨⟨hD, hnA⟩, hnV⟩, hHext⟩
    by_contra h
    have hxa : time x ≤ a := by omega
    have ha₀x := A₀.desc_time hrespect hbound hA₀ hD
    have hxU : x ∈ Window time a₀ b₀ := ⟨ha₀x, by omega⟩
    have hxH := (hagree x hxU).mp hHext
    by_cases hxv : time x ≤ v₀
    · rcases hxv.eq_or_lt with he | hl
      · exact hnV (Boundary.mem_weak_at_time hbound hV he).1
      · have hnHS : x ∉ Hstarᶜ := fun hn => hn (hsub x hxU hxH)
        exact hnV (V.pred_subset_weakPred r (hcenter.1 x hxU hl hnHS))
    · have hvx : v₀ < time x := by omega
      rcases hxa.eq_or_lt with he | hl
      · exact hnA (Boundary.mem_weak_at_time hbound hA he).1
      · have hxSide : x ∈ Window time v₀ b₀ := ⟨hvx, hxU.2⟩
        exact hnA (A.pred_subset_weakPred r (hend.1 x hxSide hl (fun hn => hn hxH)))

theorem flatten_pair {Q₀ U D G B : Set J} {rank : J → ℕ} {k : ℕ}
    (hU : U ⊆ Q₀) (hG : Q₀ \ D ⊆ G)
    (hB : ∀ x ∈ U, x ∈ B ↔ x ∈ D) :
    ∀ x ∈ U, x ∈ (G ∩ {z | k ≤ rank z}) ∪ B ↔ x ∈ D ∪ {z | k ≤ rank z} := by
  intro x hxU
  constructor
  · rintro (⟨_, hk⟩ | hxB)
    · exact Or.inr hk
    · exact Or.inl ((hB x hxU).mp hxB)
  · rintro (hxD | hk)
    · exact Or.inr ((hB x hxU).mpr hxD)
    · by_cases hxD : x ∈ D
      · exact Or.inr ((hB x hxU).mpr hxD)
      · exact Or.inl ⟨hG ⟨hU hxU, hxD⟩, hk⟩

end ThreeMachine.Structure

end

end OAI
