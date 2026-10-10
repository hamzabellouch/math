import Mathlib

namespace OAI

/-! Cyclic subnormal series and their minimum lengths in finite p-groups. -/

namespace ChromaticCyclic

structure CyclicStep {G : Type*} [Group G] (H K : Subgroup G) : Prop where
  le : H ≤ K
  normal : (H.subgroupOf K).Normal
  cyclic : letI := normal; IsCyclic (K ⧸ H.subgroupOf K)

structure CyclicSeries {G : Type*} [Group G] (H K : Subgroup G) (n : ℕ) where
  group : ℕ → Subgroup G
  first : group 0 = H
  last : group n = K
  step : ∀ i < n, CyclicStep (group i) (group (i + 1))

noncomputable def cyclicLength {G : Type*} [Group G] (H : Subgroup G) : ℕ :=
  sInf {n | Nonempty (CyclicSeries H ⊤ n)}

abbrev CyclicPower (p r k : ℕ) := Fin k → Multiplicative (ZMod (p ^ r))

namespace CyclicStep
variable {G A : Type*} [Group G] [Group A] {H K : Subgroup G}

theorem normal_map (s : CyclicStep H K) (f : G →* A) :
    ((H.map f).subgroupOf (K.map f)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((Subgroup.map_mono
      ((Subgroup.normal_subgroupOf_iff_le_normalizer s.le).mp s.normal)).trans
      (H.le_normalizer_map f))

def factorMap (s : CyclicStep H K) (f : G →* A) :
    letI := s.normal
    letI := s.normal_map f
    K ⧸ H.subgroupOf K →* K.map f ⧸ (H.map f).subgroupOf (K.map f) := by
  letI := s.normal
  letI := s.normal_map f
  exact QuotientGroup.map _ _ (f.subgroupMap K) (by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem factorMap_surjective (s : CyclicStep H K) (f : G →* A) :
    letI := s.normal
    letI := s.normal_map f
    Function.Surjective (s.factorMap f) := by
  let := s.normal
  let := s.normal_map f
  exact QuotientGroup.map_surjective_of_surjective _ _ _
    (Quotient.mk''_surjective.comp (f.subgroupMap_surjective K)) _

protected theorem map (s : CyclicStep H K) (f : G →* A) :
    CyclicStep (H.map f) (K.map f) := by
  refine ⟨Subgroup.map_mono s.le, s.normal_map f, ?_⟩
  let := s.normal
  let := s.normal_map f
  let := s.cyclic
  exact isCyclic_of_surjective (s.factorMap f) (s.factorMap_surjective f)

theorem normal_comap (s : CyclicStep H K) (f : A →* G) :
    ((H.comap f).subgroupOf (K.comap f)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((Subgroup.comap_mono
      ((Subgroup.normal_subgroupOf_iff_le_normalizer s.le).mp s.normal)).trans
      (H.le_normalizer_comap f))

def factorComap (s : CyclicStep H K) (f : A →* G) :
    letI := s.normal
    letI := s.normal_comap f
    K.comap f ⧸ (H.comap f).subgroupOf (K.comap f) →* K ⧸ H.subgroupOf K := by
  letI := s.normal
  letI := s.normal_comap f
  let g : K.comap f →* K := (f.domRestrict (K.comap f)).codRestrict _ (fun x => x.property)
  exact QuotientGroup.map _ _ g (by intro x hx; exact hx)

theorem factorComap_injective (s : CyclicStep H K) (f : A →* G) :
    letI := s.normal
    letI := s.normal_comap f
    Function.Injective (s.factorComap f) := by
  let := s.normal
  let := s.normal_comap f
  apply (s.factorComap f).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change (↑(⟨f x.val, x.property⟩ : K) : K ⧸ H.subgroupOf K) = 1 at hx
  have hx' := (QuotientGroup.eq_one_iff (⟨f x.val, x.property⟩ : K)).mp hx
  change (↑x : K.comap f ⧸ (H.comap f).subgroupOf (K.comap f)) = 1
  exact (QuotientGroup.eq_one_iff _).mpr hx'

protected theorem comap (s : CyclicStep H K) (f : A →* G) :
    CyclicStep (H.comap f) (K.comap f) := by
  refine ⟨Subgroup.comap_mono s.le, s.normal_comap f, ?_⟩
  let := s.normal
  let := s.normal_comap f
  let := s.cyclic
  exact isCyclic_of_injective (s.factorComap f) (s.factorComap_injective f)

end CyclicStep

theorem cyclic_pGroup_disjoint {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G) {A B : Subgroup G}
    (hd : Disjoint A B) : A = ⊥ ∨ B = ⊥ := by
  let := IsCyclic.commGroup (α := G)
  let f : A × B →* G :=
    { toFun := fun x => x.1.val * x.2.val
      map_one' := mul_one 1
      map_mul' := by intro x y; simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]; ac_rfl }
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    change a.val * b.val = a'.val * b'.val at h
    have hab : a.val / a'.val = b'.val / b.val := (div_eq_div_iff_mul_eq_mul).mpr (by simpa [mul_comm] using h)
    have ha : a.val / a'.val = 1 := Subgroup.disjoint_def.mp hd
      (A.div_mem a.property a'.property) (hab ▸ B.div_mem b'.property b.property)
    have haa : a = a' := Subtype.ext (div_eq_one.mp ha)
    subst a'
    have hbb : b = b' := Subtype.ext (mul_left_cancel h)
    subst b'
    rfl
  have : IsCyclic (A × B) := isCyclic_of_injective f hf
  have hc := Group.isCyclic_prod_iff.mp (inferInstance : IsCyclic (A × B)) |>.2.2
  by_contra hn
  have hA : A ≠ ⊥ := fun h => hn (.inl h)
  have hB : B ≠ ⊥ := fun h => hn (.inr h)
  have : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hA
  have : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hB
  have ha : p ∣ Nat.card A := (hp.to_subgroup A).card_eq_or_dvd.resolve_left
    (by
      intro h
      obtain ⟨a, b, hab⟩ := exists_pair_ne A
      exact hab ((Nat.card_eq_one_iff_unique.mp h).1.elim a b))
  have hb : p ∣ Nat.card B := (hp.to_subgroup B).card_eq_or_dvd.resolve_left
    (by
      intro h
      obtain ⟨a, b, hab⟩ := exists_pair_ne B
      exact hab ((Nat.card_eq_one_iff_unique.mp h).1.elim a b))
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, Fact.out, ha, hb⟩) hc

namespace CyclicStep
variable {G A P : Type*} [Group G] [Group A] [Group P]
  {H K : Subgroup G}

theorem factorMap_injective_of_stable [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (s : CyclicStep H K) (f : G →* A) (i : P →* G)
    (hs : (H.map f).comap (f.comp i) = H.comap i)
    (hn : H.comap i ≠ K.comap i) :
    letI := s.normal
    letI := s.normal_map f
    Function.Injective (s.factorMap f) := by
  let := s.normal
  let := s.normal_map f
  let := s.cyclic
  let e : K.comap i →* K ⧸ H.subgroupOf K :=
    (QuotientGroup.mk' _).comp
      ((i.domRestrict (K.comap i)).codRestrict K (fun x => x.property))
  have he : e.range ≠ ⊥ := by
    intro he
    apply hn
    apply le_antisymm (Subgroup.comap_mono s.le)
    intro x hx
    have hx1 : e ⟨x, hx⟩ = 1 := by
      have : e ⟨x, hx⟩ ∈ e.range := ⟨⟨x, hx⟩, rfl⟩
      simpa only [he, Subgroup.mem_bot] using this
    exact (QuotientGroup.eq_one_iff (⟨i x, hx⟩ : K)).mp hx1
  have hd : Disjoint e.range (s.factorMap f).ker := by
    apply Subgroup.disjoint_def.mpr
    rintro z ⟨x, rfl⟩ hx
    change (↑(⟨f (i x.val), Subgroup.mem_map.mpr ⟨i x.val, x.property, rfl⟩⟩ : K.map f) :
      K.map f ⧸ (H.map f).subgroupOf (K.map f)) = 1 at hx
    have hx' := (QuotientGroup.eq_one_iff
      (⟨f (i x.val), Subgroup.mem_map.mpr ⟨i x.val, x.property, rfl⟩⟩ : K.map f)).mp hx
    have hh : i x.val ∈ H := by
      have : x.val ∈ (H.map f).comap (f.comp i) := hx'
      rwa [hs] at this
    change (↑(⟨i x.val, x.property⟩ : K) : K ⧸ H.subgroupOf K) = 1
    exact (QuotientGroup.eq_one_iff _).mpr hh
  have hker := (cyclic_pGroup_disjoint ((hp.to_subgroup K).to_quotient _) hd).resolve_left he
  exact (s.factorMap f).ker_eq_bot_iff.mp hker

end CyclicStep

namespace CyclicStep
variable {G : Type*} [Group G]

protected theorem refl (H : Subgroup G) : CyclicStep H H := by
  refine ⟨le_rfl, ?_, ?_⟩
  · rw [Subgroup.subgroupOf_self]; infer_instance
  · have : Subsingleton (H ⧸ H.subgroupOf H) := by
      simpa only [Subgroup.subgroupOf_self] using
        (QuotientGroup.subsingleton_quotient_top : Subsingleton (H ⧸ (⊤ : Subgroup H)))
    infer_instance

protected theorem bot (K : Subgroup G) [IsCyclic K] : CyclicStep ⊥ K := by
  refine ⟨bot_le, Subgroup.normal_subgroupOf, ?_⟩
  exact isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

end CyclicStep

namespace CyclicSeries
variable {G A : Type*} [Group G] [Group A] {H K L : Subgroup G} {n : ℕ}

def refl (H : Subgroup G) : CyclicSeries H H 0 where
  group := fun _ => H
  first := rfl
  last := rfl
  step := by omega

def cons (s : CyclicStep H K) (c : CyclicSeries K L n) : CyclicSeries H L (n + 1) where
  group := fun | 0 => H | i + 1 => c.group i
  first := rfl
  last := c.last
  step := by
    rintro (_ | i) hi
    · simpa [c.first] using s
    · exact c.step i (by omega)

def map (c : CyclicSeries H K n) (f : G →* A) :
    CyclicSeries (H.map f) (K.map f) n where
  group := fun i => (c.group i).map f
  first := congrArg (Subgroup.map f) c.first
  last := congrArg (Subgroup.map f) c.last
  step := fun i hi => (c.step i hi).map f

def comap (c : CyclicSeries H K n) (f : A →* G) :
    CyclicSeries (H.comap f) (K.comap f) n where
  group := fun i => (c.group i).comap f
  first := congrArg (Subgroup.comap f) c.first
  last := congrArg (Subgroup.comap f) c.last
  step := fun i hi => (c.step i hi).comap f

def tail (c : CyclicSeries H K (n + 1)) : CyclicSeries (c.group 1) K n where
  group := fun i => c.group (i + 1)
  first := rfl
  last := c.last
  step := fun i hi => c.step (i + 1) (by omega)

theorem le (c : CyclicSeries H K n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    c.group i ≤ c.group j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (c.step j (by omega)).le

end CyclicSeries

namespace CyclicStep
variable {G : Type*} [Group G]

theorem exists_larger (hnc : NormalizerCondition G) (H : Subgroup G) (hH : H < ⊤) :
    ∃ K, H < K ∧ CyclicStep H K := by
  let N := Subgroup.normalizer (H : Set G)
  have hHN : H < N := hnc H hH
  obtain ⟨x, hxN, hxH⟩ := SetLike.exists_of_lt hHN
  let q := QuotientGroup.mk' (H.subgroupOf N)
  let Z := Subgroup.zpowers (q ⟨x, hxN⟩)
  let K := (Z.comap q).map N.subtype
  have hb : ((⊥ : Subgroup (N ⧸ H.subgroupOf N)).comap q).map N.subtype = H := by
    change (QuotientGroup.mk' (H.subgroupOf N)).ker.map N.subtype = H
    rw [QuotientGroup.ker_mk', Subgroup.map_subgroupOf_eq_of_le hHN.le]
  have hs : CyclicStep H K := by
    rw [← hb]
    exact ((CyclicStep.bot Z).comap q).map N.subtype
  have hxK : x ∈ K := by
    exact Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, Subgroup.mem_zpowers _, rfl⟩
  refine ⟨K, lt_of_le_of_ne hs.le ?_, hs⟩
  intro he
  exact hxH (he.symm ▸ hxK)

end CyclicStep

namespace CyclicSeries
variable {G : Type*} [Group G] {H K : Subgroup G} {n m : ℕ}

theorem pad (c : CyclicSeries H K n) (h : n ≤ m) : Nonempty (CyclicSeries H K m) := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨c⟩
  | succ m h ih =>
    obtain ⟨c'⟩ := ih
    exact ⟨cons (CyclicStep.refl H) c'⟩

noncomputable def changes (c : CyclicSeries H K n) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range n, if c.group i = c.group (i + 1) then 0 else 1

noncomputable def repetitions (c : CyclicSeries H K n) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range n, if c.group i = c.group (i + 1) then 1 else 0

theorem changes_add_repetitions (c : CyclicSeries H K n) : c.changes + c.repetitions = n := by
  classical
  rw [changes, repetitions, ← Finset.sum_add_distrib]
  simp only [ite_add_ite, zero_add, add_zero, ite_self, Finset.sum_const,
    Finset.card_range, smul_eq_mul, mul_one]

theorem compressed (c : CyclicSeries H K n) : Nonempty (CyclicSeries H K c.changes) := by
  classical
  induction n generalizing H with
  | zero =>
    have hHK : H = K := c.first.symm.trans c.last
    subst K
    simpa [changes] using (show Nonempty (CyclicSeries H H 0) from ⟨refl H⟩)
  | succ n ih =>
    obtain ⟨ct⟩ := ih c.tail
    have he : c.changes = c.tail.changes + if H = c.group 1 then 0 else 1 := by
      simp only [changes, Finset.sum_range_succ', tail, c.first, Nat.zero_add]
      rfl
    have hs : CyclicStep H (c.group 1) := by simpa [c.first] using c.step 0 (by omega)
    by_cases h : H = c.group 1
    · rw [he, ite_eq_left h, add_zero]
      simpa only [h] using (show Nonempty (CyclicSeries (c.group 1) K c.tail.changes) from ⟨ct⟩)
    · rw [he, ite_eq_right h]
      exact ⟨cons hs ct⟩

theorem exists_of_normalizerCondition [Finite G] (hnc : NormalizerCondition G)
    (H : Subgroup G) : ∃ n, Nonempty (CyclicSeries H ⊤ n) := by
  induction H using (wellFounded_gt : WellFounded ((· > ·) : Subgroup G → Subgroup G → Prop)).induction with
  | h H ih =>
    by_cases hh : H = ⊤
    · subst H
      exact ⟨0, ⟨refl ⊤⟩⟩
    · obtain ⟨K, hHK, hs⟩ := CyclicStep.exists_larger hnc H (lt_top_iff_ne_top.mpr hh)
      obtain ⟨n, ⟨c⟩⟩ := ih K hHK
      exact ⟨n + 1, ⟨cons hs c⟩⟩

theorem exists_of_pGroup [Finite G] {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G)
    (H : Subgroup G) : ∃ n, Nonempty (CyclicSeries H ⊤ n) := by
  have := hp.isNilpotent
  exact exists_of_normalizerCondition Group.normalizerCondition_of_isNilpotent H

end CyclicSeries

theorem cyclicLength_le {G : Type*} [Group G] {H : Subgroup G} {n : ℕ}
    (c : CyclicSeries H ⊤ n) : cyclicLength H ≤ n := Nat.sInf_le ⟨c⟩

theorem cyclicLength_le_changes {G : Type*} [Group G] {H : Subgroup G} {n : ℕ}
    (c : CyclicSeries H ⊤ n) : cyclicLength H ≤ c.changes := by
  obtain ⟨d⟩ := c.compressed
  exact cyclicLength_le d

theorem cyclicLength_le_iff {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (H : Subgroup G) (n : ℕ) :
    cyclicLength H ≤ n ↔ Nonempty (CyclicSeries H ⊤ n) := by
  constructor
  · intro h
    obtain ⟨c⟩ := Nat.sInf_mem (CyclicSeries.exists_of_pGroup hp H)
    exact c.pad h
  · rintro ⟨c⟩
    exact cyclicLength_le c

namespace CyclicStep
variable {G A P : Type*} [Group G] [Group A] [Group P]
    {H K : Subgroup G}

theorem relIndex_dvd_of_pow (s : CyclicStep H K) {N : ℕ} (he : ∀ x : G, x ^ N = 1) :
    H.relIndex K ∣ N := by
  let := s.normal
  let := s.cyclic
  change Nat.card (K ⧸ H.subgroupOf K) ∣ N
  rw [← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [← map_pow]
  have hx : x ^ N = 1 := Subtype.ext (he x.val)
  rw [hx, map_one]

theorem relIndex_eq_of_stable [Finite G] {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G)
    (s : CyclicStep H K) (f : G →* A) (i : P →* G)
    (hstable : (H.map f).comap (f.comp i) = H.comap i)
    (hne : H.comap i ≠ K.comap i) :
    H.relIndex K = (H.map f).relIndex (K.map f) := by
  let := s.normal
  let := s.normal_map f
  exact Nat.card_congr (Equiv.ofBijective (s.factorMap f)
    ⟨s.factorMap_injective_of_stable hp f i hstable hne, s.factorMap_surjective f⟩)

end CyclicStep

namespace CyclicSeries
variable {G A P : Type*} [Group G] [Group A] [Group P]
    {H K : Subgroup G} {n : ℕ}

theorem prod_relIndex (c : CyclicSeries H K n) :
    (∏ i ∈ Finset.range n, (c.group i).relIndex (c.group (i + 1))) = H.relIndex K := by
  classical
  induction n generalizing H with
  | zero =>
    have hHK : H = K := c.first.symm.trans c.last
    simp [hHK]
  | succ n ih =>
    rw [Finset.prod_range_succ']
    have ht := ih c.tail
    change (∏ i ∈ Finset.range n, (c.group (i + 1)).relIndex (c.group (i + 1 + 1))) =
      (c.group 1).relIndex K at ht
    rw [ht, c.first, Nat.zero_add, mul_comm]
    exact Subgroup.relIndex_mul_relIndex H (c.group 1) K
      (by simpa only [c.first, Nat.zero_add] using (c.step 0 (by omega)).le)
      (by simpa only [c.last] using c.le (by omega : 1 ≤ n + 1) (le_refl _))

theorem prod_relIndex_bot_top (c : CyclicSeries (⊥ : Subgroup G) ⊤ n) :
    (∏ i ∈ Finset.range n, (c.group i).relIndex (c.group (i + 1))) = Nat.card G := by
  rw [c.prod_relIndex]
  simp [Subgroup.relIndex]

theorem card_growth [Finite G] [Finite A] {p N : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (he : ∀ x : G, x ^ N = 1) (hN : 0 < N)
    (c : CyclicSeries (⊥ : Subgroup G) ⊤ n) (f : G →* A) (hf : Function.Surjective f)
    (i : P →* G)
    (hstable : ∀ j ≤ n, ((c.group j).map f).comap (f.comp i) = (c.group j).comap i) :
    Nat.card G ≤ Nat.card A * N ^ (c.comap i).repetitions := by
  classical
  have hstep (j : ℕ) (hj : j < n) :
      (c.group j).relIndex (c.group (j + 1)) ≤
        ((c.group j).map f).relIndex ((c.group (j + 1)).map f) *
          N ^ (if (c.group j).comap i = (c.group (j + 1)).comap i then 1 else 0) := by
    by_cases h : (c.group j).comap i = (c.group (j + 1)).comap i
    · rw [ite_eq_left h, pow_one]
      have hle := Nat.le_of_dvd hN ((c.step j hj).relIndex_dvd_of_pow he)
      have hpos : 0 < ((c.group j).map f).relIndex ((c.group (j + 1)).map f) := Nat.card_pos
      exact hle.trans (by nlinarith)
    · rw [ite_eq_right h, pow_zero, mul_one]
      exact le_of_eq ((c.step j hj).relIndex_eq_of_stable hp f i (hstable j (by omega)) h)
  have hprod := Finset.prod_le_prod (fun j hj => hstep j (Finset.mem_range.mp hj))
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at hprod
  have hmapprod : (∏ j ∈ Finset.range n,
      ((c.group j).map f).relIndex ((c.group (j + 1)).map f)) = Nat.card A := by
    have ht := (c.map f).prod_relIndex
    simpa only [map, Subgroup.map_bot, Subgroup.map_top_of_surjective f hf,
      Subgroup.relIndex_top_right, Subgroup.index_bot] using ht
  rw [c.prod_relIndex_bot_top, hmapprod] at hprod
  exact hprod

end CyclicSeries

namespace CyclicPower

instance finite (p r k : ℕ) [Fact p.Prime] : Finite (CyclicPower p r k) := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero r (Fact.out : p.Prime).ne_zero⟩
  infer_instance

theorem card (p r k : ℕ) [Fact p.Prime] : Nat.card (CyclicPower p r k) = p ^ (r * k) := by
  rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin, pow_mul]

theorem pow_power (p r k : ℕ) (x : CyclicPower p r k) : x ^ (p ^ r) = 1 := by
  funext j
  change (x j) ^ (p ^ r) = 1
  apply Multiplicative.toAdd.injective
  change (p ^ r) • (x j).toAdd = 0
  simp [nsmul_eq_mul]

def reduction (p k : ℕ) {s t : ℕ} (hst : s ≤ t) :
    CyclicPower p t k →* CyclicPower p s k :=
  MonoidHom.pi fun j =>
    (AddMonoidHom.toMultiplicative (ZMod.castHom (Nat.pow_dvd_pow p hst) (ZMod (p ^ s))).toAddMonoidHom).comp
      (Pi.evalMonoidHom _ j)

theorem reduction_surjective (p k : ℕ) {s t : ℕ} (hst : s ≤ t) :
    Function.Surjective (reduction p k hst) := by
  intro x
  choose y hy using fun j => ZMod.castHom_surjective (Nat.pow_dvd_pow p hst) (x j).toAdd
  refine ⟨fun j => Multiplicative.ofAdd (y j), ?_⟩
  funext j
  exact hy j

theorem reduction_comp (p k : ℕ) {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    (reduction p k hrs).comp (reduction p k hst) = reduction p k (hrs.trans hst) := by
  apply MonoidHom.ext
  intro x
  funext j
  exact DFunLike.congr_fun (ZMod.castHom_comp (Nat.pow_dvd_pow p hrs) (Nat.pow_dvd_pow p hst)) (x j).toAdd

end CyclicPower

namespace ProductTower
variable (P : Type*) [Group P]

def reduction (p k : ℕ) {s t : ℕ} (hst : s ≤ t) :
    P × CyclicPower p t k →* P × CyclicPower p s k :=
  (MonoidHom.id P).prodMap (CyclicPower.reduction p k hst)

theorem reduction_surjective (p k : ℕ) {s t : ℕ} (hst : s ≤ t) :
    Function.Surjective (reduction P p k hst) := by
  rintro ⟨x, y⟩
  obtain ⟨z, hz⟩ := CyclicPower.reduction_surjective p k hst y
  exact ⟨(x, z), Prod.ext rfl hz⟩

theorem reduction_comp (p k : ℕ) {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    (reduction P p k hrs).comp (reduction P p k hst) = reduction P p k (hrs.trans hst) := by
  ext x : 1
  refine Prod.ext rfl ?_
  exact DFunLike.congr_fun (CyclicPower.reduction_comp p k hrs hst) x.2

theorem reduction_inl (p k : ℕ) {s t : ℕ} (hst : s ≤ t) :
    (reduction P p k hst).comp (MonoidHom.inl P (CyclicPower p t k)) =
      MonoidHom.inl P (CyclicPower p s k) := by
  ext x : 1
  change (x, CyclicPower.reduction p k hst 1) = (x, 1)
  rw [map_one]

theorem pow_power [Finite P] (p k : ℕ) {m r : ℕ} (hc : Nat.card P = p ^ m) (hmr : m ≤ r)
    (x : P × CyclicPower p r k) : x ^ (p ^ r) = 1 := by
  apply Prod.ext
  · change x.1 ^ (p ^ r) = 1
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact (orderOf_dvd_natCard x.1).trans (hc ▸ Nat.pow_dvd_pow p hmr)
  · exact CyclicPower.pow_power p r k x.2

theorem isPGroup [Finite P] (p : ℕ) [Fact p.Prime] (hP : IsPGroup p P) (r k : ℕ) :
    IsPGroup p (P × CyclicPower p r k) := by
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  apply IsPGroup.of_card (n := m + r * k)
  rw [Nat.card_prod, hm, CyclicPower.card, pow_add]

end ProductTower

namespace CyclicSeries
variable {G A : Type*} [Group G] [Group A] {n : ℕ}

def mapSurjective (c : CyclicSeries (⊥ : Subgroup G) ⊤ n) (f : G →* A)
    (hf : Function.Surjective f) : CyclicSeries (⊥ : Subgroup A) ⊤ n where
  group := fun j => (c.group j).map f
  first := by rw [c.first, Subgroup.map_bot]
  last := by rw [c.last, Subgroup.map_top_of_surjective f hf]
  step := fun j hj => (c.step j hj).map f

def comapInjective (c : CyclicSeries (⊥ : Subgroup G) ⊤ n) (i : A →* G)
    (hi : Function.Injective i) : CyclicSeries (⊥ : Subgroup A) ⊤ n where
  group := fun j => (c.group j).comap i
  first := by
    rw [c.first]
    exact i.ker_eq_bot_iff.mpr hi
  last := by rw [c.last, Subgroup.comap_top]
  step := fun j hj => (c.step j hj).comap i

end CyclicSeries

theorem product_series (p : ℕ) [Fact p.Prime] (P : Type*) [Group P] [Finite P]
    (hP : IsPGroup p P) (k l : ℕ)
    (h : ∀ r : ℕ, 0 < r →
      cyclicLength (⊥ : Subgroup (P × CyclicPower p r k)) ≤ l) :
    k + cyclicLength (⊥ : Subgroup P) ≤ l := by
  classical
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  let D := Fin (l + 1) → Subgroup P
  let : Fintype D := Fintype.ofFinite D
  let T := Fintype.card D
  let r : ℕ → ℕ := fun j => (m + 1) * (k + 2) ^ j
  have hrpos (j : ℕ) : 0 < r j := Nat.mul_pos (by omega) (pow_pos (by omega) j)
  have hrmono : Monotone r := fun a b hab =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hab)
  have hmle (j : ℕ) : m ≤ r j := by
    have h0 := hrmono (Nat.zero_le j)
    simp only [r, pow_zero, mul_one] at h0
    change m ≤ (m + 1) * (k + 2) ^ j
    omega
  have hrgrow {a b : ℕ} (hab : a < b) : k * r a < r b := by
    calc
      k * r a < (k + 2) * r a := Nat.mul_lt_mul_of_pos_right (by omega) (hrpos a)
      _ = r (a + 1) := by dsimp [r]; rw [pow_succ]; ring
      _ ≤ r b := hrmono (by omega)
  have hrbound (j : Fin (T + 1)) : r j ≤ r T := hrmono (by omega)
  obtain ⟨c⟩ := (cyclicLength_le_iff (ProductTower.isPGroup P p hP (r T) k) ⊥ l).mp
    (h (r T) (hrpos T))
  let F : Fin (T + 1) → D := fun j q =>
    ((c.group q).map (ProductTower.reduction P p k (hrbound j))).comap
      (MonoidHom.inl P (CyclicPower p (r j) k))
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt F (by
    simp only [Fintype.card_fin]; exact Nat.lt_succ_self T)
  have hex : ∃ a b : Fin (T + 1), a < b ∧ F a = F b := by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨a, b, hlt, heq⟩
    · exact ⟨b, a, hgt, heq.symm⟩
  obtain ⟨a, b, hab, heq⟩ := hex
  let s := r a
  let t := r b
  have hst : s ≤ t := hrmono (le_of_lt hab)
  let c' := c.mapSurjective (ProductTower.reduction P p k (hrbound b))
    (ProductTower.reduction_surjective P p k (hrbound b))
  let f := ProductTower.reduction P p k hst
  let i := MonoidHom.inl P (CyclicPower p t k)
  have hi : Function.Injective i := fun x y hxy => congrArg Prod.fst hxy
  have hstable (q : ℕ) (hq : q ≤ l) :
      ((c'.group q).map f).comap (f.comp i) = (c'.group q).comap i := by
    have hqeq := congrFun heq ⟨q, by omega⟩
    dsimp [c', f, i, CyclicSeries.mapSurjective]
    rw [ProductTower.reduction_inl, Subgroup.map_map, ProductTower.reduction_comp]
    exact hqeq
  have hg := c'.card_growth (ProductTower.isPGroup P p hP t k)
    (ProductTower.pow_power P p k hm (hmle b))
    (pow_pos (Fact.out : p.Prime).pos t) f (ProductTower.reduction_surjective P p k hst) i hstable
  let z := (c'.comap i).repetitions
  change Nat.card (P × CyclicPower p t k) ≤ Nat.card (P × CyclicPower p s k) * (p ^ t) ^ z at hg
  rw [Nat.card_prod, Nat.card_prod, CyclicPower.card, CyclicPower.card] at hg
  have hge : Nat.card P * p ^ (t * k) ≤ Nat.card P * p ^ (s * k + t * z) := by
    calc
      Nat.card P * p ^ (t * k) ≤ (Nat.card P * p ^ (s * k)) * (p ^ t) ^ z := hg
      _ = Nat.card P * p ^ (s * k + t * z) := by
        rw [pow_add, pow_mul p t z]
        exact Nat.mul_assoc _ _ _
  have hg' : t * k ≤ s * k + t * z :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
      (Nat.le_of_mul_le_mul_left hge Nat.card_pos)
  have hz : k ≤ z := by
    by_contra hn
    have hzk : z + 1 ≤ k := by omega
    have hmul := Nat.mul_le_mul_left t hzk
    have hgt : k * s < t := hrgrow hab
    nlinarith
  let cp := c'.comapInjective i hi
  have hc := cyclicLength_le_changes cp
  have hsum : cp.changes + z = l := (c'.comap i).changes_add_repetitions
  omega



namespace CyclicSeries
variable {G : Type*} [Group G] {H K L : Subgroup G} {n m : ℕ}

def append (c : CyclicSeries H K n) (d : CyclicSeries K L m) :
    CyclicSeries H L (n + m) := by
  induction n generalizing H with
  | zero =>
    have h : H = K := c.first.symm.trans c.last
    subst H
    simpa using d
  | succ n ih =>
    have s : CyclicStep H (c.group 1) := by
      simpa only [c.first] using c.step 0 (Nat.succ_pos n)
    simpa only [Nat.succ_add, Nat.add_succ] using cons s (ih c.tail)

theorem nonempty_zero_iff : Nonempty (CyclicSeries H K 0) ↔ H = K := by
  constructor
  · rintro ⟨c⟩
    exact c.first.symm.trans c.last
  · rintro rfl
    exact ⟨refl H⟩

end CyclicSeries

variable {G A : Type*} [Group G] [Group A]

theorem cyclicLength_spec [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (H : Subgroup G) :
    Nonempty (CyclicSeries H ⊤ (cyclicLength H)) :=
  (cyclicLength_le_iff hp H _).mp le_rfl

@[simp] theorem cyclicLength_top : cyclicLength (⊤ : Subgroup G) = 0 :=
  Nat.eq_zero_of_le_zero (cyclicLength_le (CyclicSeries.refl ⊤))

@[simp] theorem cyclicLength_eq_zero_iff [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (H : Subgroup G) :
    cyclicLength H = 0 ↔ H = ⊤ := by
  constructor
  · intro h
    apply CyclicSeries.nonempty_zero_iff.mp
    simpa only [h] using cyclicLength_spec hp H
  · rintro rfl
    exact cyclicLength_top

theorem cyclicLength_pos_iff [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (H : Subgroup G) :
    0 < cyclicLength H ↔ H < ⊤ := by
  rw [Nat.pos_iff_ne_zero, ne_eq, cyclicLength_eq_zero_iff hp, lt_top_iff_ne_top]

theorem cyclicLength_map_le [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (H : Subgroup G) (f : G →* A)
    (hf : Function.Surjective f) :
    cyclicLength (H.map f) ≤ cyclicLength H := by
  obtain ⟨c⟩ := cyclicLength_spec hp H
  have c' := c.map f
  rw [Subgroup.map_top_of_surjective f hf] at c'
  exact cyclicLength_le c'

theorem cyclicLength_comap_le [Finite A] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p A) (K : Subgroup A) (f : G →* A) :
    cyclicLength (K.comap f) ≤ cyclicLength K := by
  obtain ⟨c⟩ := cyclicLength_spec hp K
  have c' := c.comap f
  rw [Subgroup.comap_top] at c'
  exact cyclicLength_le c'

theorem cyclicLength_comap_surjective [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (f : G →* A) (hf : Function.Surjective f)
    (K : Subgroup A) :
    cyclicLength (K.comap f) = cyclicLength K := by
  have : Finite A := Finite.of_surjective f hf
  apply le_antisymm (cyclicLength_comap_le (hp.of_surjective f hf) K f)
  have h := cyclicLength_map_le hp (K.comap f) f hf
  rwa [Subgroup.map_comap_eq_self_of_surjective hf] at h

theorem cyclicLength_normal_quotient [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (H : Subgroup G) [H.Normal] :
    cyclicLength H = cyclicLength (⊥ : Subgroup (G ⧸ H)) := by
  have h := cyclicLength_comap_surjective hp (QuotientGroup.mk' H)
    (QuotientGroup.mk'_surjective H) ⊥
  simpa only [MonoidHom.comap_bot, QuotientGroup.ker_mk'] using h

theorem cyclicLength_map_equiv [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (e : G ≃* A) (H : Subgroup G) :
    cyclicLength (H.map e.toMonoidHom) = cyclicLength H := by
  have h := cyclicLength_comap_surjective hp e.toMonoidHom e.surjective
    (H.map e.toMonoidHom)
  rw [Subgroup.comap_map_eq_self_of_injective e.injective] at h
  exact h.symm

theorem cyclicLength_conj [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (g : G) (H : Subgroup G) :
    cyclicLength (H.map (MulAut.conj g).toMonoidHom) = cyclicLength H :=
  cyclicLength_map_equiv hp (MulAut.conj g) H

theorem cyclicLength_triangle [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) {H K : Subgroup G} (hHK : H ≤ K) :
    cyclicLength H ≤ cyclicLength (H.subgroupOf K) + cyclicLength K := by
  obtain ⟨c⟩ := cyclicLength_spec (hp.to_subgroup K) (H.subgroupOf K)
  obtain ⟨d⟩ := cyclicLength_spec hp K
  have c' := c.map K.subtype
  rw [Subgroup.map_subgroupOf_eq_of_le hHK, ← MonoidHom.range_eq_map, K.range_subtype] at c'
  exact cyclicLength_le (c'.append d)

end ChromaticCyclic

end OAI
