import OAI.Combinatorics.TreeEdit.CycleCharging

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace Words

variable {β : Type*} {n : ℕ}

def get (x : Word β n) (i : Fin n) : β := x.val.get (Fin.cast x.property.symm i)

def ofFn (x : Fin n → β) : Word β n := ⟨List.ofFn x, List.length_ofFn⟩

@[simp] lemma at_ofFn (x : Fin n → β) (i : Fin n) : get (ofFn x) i = x i := by
  simp [get, ofFn, List.get_eq_getElem, Fin.cast]

def map {γ : Type*} (f : β → γ) (x : Word β n) : Word γ n :=
  ⟨x.val.map f, by simp [x.property]⟩

@[simp] lemma at_map {γ : Type*} (f : β → γ) (x : Word β n) (i : Fin n) :
    get (map f x) i = f (get x i) := by simp [get, map, List.get_eq_getElem, Fin.cast]

lemma ext {x y : Word β n} (h : ∀ i, get x i = get y i) : x = y := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact x.property.trans y.property.symm
  · intro i hi hj
    simpa [get, List.get_eq_getElem] using h ⟨i, by rwa [x.property] at hi⟩

def cycles {m T B : ℕ} {β : Fin m → Type*}
    (blocks : Fin T → ∀ i, Word (β i) B) : Word (Sigma β) (T * (m * B)) :=
  ofFn fun r => ⟨r.modNat.divNat, get (blocks r.divNat r.modNat.divNat) r.modNat.modNat⟩

@[simp] lemma at_cycles {m T B : ℕ} {β : Fin m → Type*}
    (blocks : Fin T → ∀ i, Word (β i) B) (r : Fin (T * (m * B))) :
    get (cycles blocks) r =
      ⟨r.modNat.divNat, get (blocks r.divNat r.modNat.divNat) r.modNat.modNat⟩ := by
  simp [cycles]

lemma cycle_coordinates {m T B : ℕ} (r : Fin (T * (m * B))) :
    r.val = r.divNat.val * (m * B) + r.modNat.divNat.val * B +
      r.modNat.modNat.val := by
  dsimp [Fin.divNat, Fin.modNat]
  have h1 := Nat.mod_add_div r.val (m * B)
  have h2 := Nat.mod_add_div (r.val % (m * B)) B
  nlinarith

lemma cycle_offset_strict {m T B : ℕ} {r s : Fin (T * (m * B))}
    (ha : r.divNat = s.divNat) (hi : r.modNat.divNat = s.modNat.divNat)
    (hrs : r < s) : r.modNat.modNat < s.modNat.modNat := by
  have hr := cycle_coordinates r
  have hs := cycle_coordinates s
  rw [ha, hi] at hr
  change r.modNat.modNat.val < s.modNat.modNat.val
  change r.val < s.val at hrs
  omega

lemma cycle_block_alignment {m T B N : ℕ} {β : Fin m → Type*}
    (x y : Fin T → ∀ i, Word (β i) B)
    (f g : Fin N ↪o Fin (T * (m * B)))
    (hfg : ∀ j, get (cycles x) (f j) = get (cycles y) (g j))
    (s : Finset (Fin N)) (a b : Fin T) (i : Fin m)
    (hf : ∀ j ∈ s, (f j).divNat = a ∧ (f j).modNat.divNat = i)
    (hg : ∀ j ∈ s, (g j).divNat = b ∧ (g j).modNat.divNat = i) :
    s.card ≤ lcs (x a i).val (y b i).val := by
  let e := s.orderEmbOfFin rfl
  have hf' (j : Fin s.card) := hf (e j) (s.orderEmbOfFin_mem rfl j)
  have hg' (j : Fin s.card) := hg (e j) (s.orderEmbOfFin_mem rfl j)
  let fl : Fin s.card → Fin B := fun j => (f (e j)).modNat.modNat
  let gr : Fin s.card → Fin B := fun j => (g (e j)).modNat.modNat
  have hfl : StrictMono fl := by
    intro j k hjk
    exact cycle_offset_strict ((hf' j).1.trans (hf' k).1.symm)
      ((hf' j).2.trans (hf' k).2.symm) (f.strictMono (e.strictMono hjk))
  have hgr : StrictMono gr := by
    intro j k hjk
    exact cycle_offset_strict ((hg' j).1.trans (hg' k).1.symm)
      ((hg' j).2.trans (hg' k).2.symm) (g.strictMono (e.strictMono hjk))
  apply Alignment.le_lcs ⟨(OrderEmbedding.ofStrictMono fl hfl).comp
      (Fin.castOrderIso (x a i).property.symm).toOrderEmbedding,
    (OrderEmbedding.ofStrictMono gr hgr).comp
      (Fin.castOrderIso (y b i).property.symm).toOrderEmbedding, ?_⟩
  intro j
  have hh := hfg (e j)
  simp only [at_cycles] at hh
  have h1 := hf' j
  have h2 := hg' j
  rcases h1 with ⟨h1a, h1i⟩
  rcases h2 with ⟨h2a, h2i⟩
  rw [h1a, h1i, h2a, h2i] at hh
  exact eq_of_heq (Sigma.mk.inj hh).2

lemma cycle_fiber_bound {m T B N : ℕ} {β : Fin m → Type*}
    (x y : Fin T → ∀ i, Word (β i) B)
    (f g : Fin N ↪o Fin (T * (m * B)))
    (hfg : ∀ j, get (cycles x) (f j) = get (cycles y) (g j))
    (s : Finset (Fin N)) (a b : Fin T)
    (hf : ∀ j ∈ s, (f j).divNat = a)
    (hg : ∀ j ∈ s, (g j).divNat = b) :
    s.card ≤ ∑ i : Fin m, lcs (x a i).val (y b i).val := by
  classical
  have he : s.card = ∑ i : Fin m, (s.filter (fun j => (f j).modNat.divNat = i)).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := s) (t := Finset.univ) (f := fun j => (f j).modNat.divNat) (by simp)
  rw [he]
  apply Finset.sum_le_sum
  intro i _
  apply cycle_block_alignment x y f g hfg _ a b i
  · intro j hj
    exact ⟨hf j (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
  · intro j hj
    have heq := congrArg Sigma.fst (hfg j)
    simp only [at_cycles] at heq
    exact ⟨hg j (Finset.mem_filter.mp hj).1, heq.symm.trans (Finset.mem_filter.mp hj).2⟩

lemma cycles_deficit {m T B : ℕ} {β : Fin m → Type*} (hm : 2 ≤ m) (hB : 0 < B)
    (x y : Fin T → ∀ i, Word (β i) B) (δ : ℝ)
    (hδ : δ ≤ ((m - 2) * B : ℕ))
    (hblocks : ∀ a b, δ ≤ ∑ i : Fin m, (deficit (x a i).val (y b i).val : ℝ)) :
    (T : ℝ) * δ ≤ 2 * (deficit (cycles x).val (cycles y).val : ℝ) := by
  classical
  obtain ⟨al⟩ := exists_lcs_alignment (cycles x).val (cycles y).val
  let f := al.left.comp (Fin.castOrderIso (cycles x).property).toOrderEmbedding
  let g := al.right.comp (Fin.castOrderIso (cycles y).property).toOrderEmbedding
  have hfg (j) : get (cycles x) (f j) = get (cycles y) (g j) := al.agree j
  have hC : 0 < m * B := by positivity
  have hc (j) : (f j).val / B % m = (g j).val / B % m := by
    have he := congrArg Sigma.fst (hfg j)
    have hv := congrArg Fin.val he
    simp only [at_cycles, Fin.divNat, Fin.modNat] at hv
    simpa only [Nat.mul_comm m, Nat.mod_mul_right_div_self] using hv
  have hh := cycle_charging hm hB f g hc δ hδ (by
    intro a b hb
    let s := Finset.univ.filter (fun j => blockIndex hC (f j) = a)
    have hf' (j) (hj : j ∈ s) : (f j).divNat = a := (Finset.mem_filter.mp hj).2
    have hg' (j) (hj : j ∈ s) : (g j).divNat = b := hb j hj
    have hn := cycle_fiber_bound x y f g hfg s a b hf' hg'
    have hle (i : Fin m) : lcs (x a i).val (y b i).val ≤ B := by
      simpa [(x a i).property] using lcs_le_length_left (x a i).val (y b i).val
    have hs : (∑ i : Fin m, deficit (x a i).val (y b i).val) =
        m * B - ∑ i : Fin m, lcs (x a i).val (y b i).val := by
      simp only [deficit, (x a _).property]
      rw [Finset.sum_tsub_distrib _ (fun i _ => hle i)]
      simp
    have hsum : (∑ i : Fin m, (deficit (x a i).val (y b i).val : ℝ)) =
        ((m * B - ∑ i : Fin m, lcs (x a i).val (y b i).val : ℕ) : ℝ) := by
      exact_mod_cast hs
    have hb' := hblocks a b
    rw [hsum] at hb'
    exact hb'.trans (by exact_mod_cast Nat.sub_le_sub_left hn (m * B)))
  simpa only [deficit, (cycles x).property] using hh

end Words

lemma lcs_map_of_injective {β γ : Type*} (f : β → γ) (hf : Function.Injective f)
    (x y : List β) : lcs (x.map f) (y.map f) = lcs x y := by
  apply Nat.le_antisymm
  · obtain ⟨z, hz1, hz2, hz⟩ := exists_lcs (x.map f) (y.map f)
    obtain ⟨z1, hz1, he1⟩ := List.sublist_map_iff.mp hz1
    obtain ⟨z2, hz2, he2⟩ := List.sublist_map_iff.mp hz2
    have he : z1 = z2 := hf.list_map (he1.symm.trans he2)
    subst z2
    have hh := length_le_lcs hz1 hz2
    rw [← hz, he1, List.length_map]
    exact hh
  · obtain ⟨z, hz1, hz2, hz⟩ := exists_lcs x y
    have hh := length_le_lcs (hz1.map f) (hz2.map f)
    simpa [hz] using hh

lemma deficit_singleton {β : Type*} {x y : β} (hxy : x ≠ y) : deficit [x] [y] = 1 := by
  obtain ⟨z, hz1, hz2, hz⟩ := exists_lcs [x] [y]
  have he : z = [] := by
    rcases List.sublist_singleton.mp hz1 with he | he
    · exact he
    · subst z
      simp [List.sublist_singleton, hxy] at hz2
  have hl : lcs [x] [y] = 0 := by simpa [he] using hz.symm
  simp [deficit, hl]

lemma translation_cycle {A : Type*} [AddCommGroup A] (x v : A) (a b R : ℕ) (t : ℤ) :
    x + t • (R • v) + b • v =
    (x + a • v) + ((b : ℤ) - a + t * R) • v := by
  simp only [add_zsmul, sub_zsmul, mul_smul, Nat.cast_smul_eq_nsmul ℤ]
  abel

end TreeEdit

end OAI
