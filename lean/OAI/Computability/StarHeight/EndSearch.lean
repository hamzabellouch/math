import OAI.Computability.StarHeight.MarkerSearch

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uι uι2 uι3 uι4 uQ uP uP2 uQ2
universe uJ uKind uP3 uP4 uP5

namespace EndSearch

open scoped Classical

def width (B S a x : ℤ) : ℤ := a + x % B * S

def Eligible (markers : Set ℤ) (B S a z m : ℤ) : Prop :=
  m ∈ markers ∧ |m - z| ≤ width B S a (m - z)

lemma width_bounds {B S a x : ℤ} (hB : 0 < B) (hS : 0 ≤ S) :
    a ≤ width B S a x ∧ width B S a x ≤ a + (B - 1) * S := by
  have hlo := Int.emod_nonneg x (ne_of_gt hB)
  have hhi := Int.emod_lt_of_pos x hB
  dsimp [width]
  constructor
  · nlinarith
  · nlinarith

noncomputable def eligibleSet (markers : Set ℤ) (B S a z : ℤ) : Finset ℤ :=
  (Finset.Icc (z - (a + (B - 1) * S)) (z + (a + (B - 1) * S))).filter
    (Eligible markers B S a z)

lemma mem_eligibleSet {markers : Set ℤ} {B S a z m : ℤ}
    (hB : 0 < B) (hS : 0 ≤ S) :
    m ∈ eligibleSet markers B S a z ↔ Eligible markers B S a z m := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hm
    have hb := abs_le.mp (hm.2.trans (width_bounds hB hS).2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hm⟩

noncomputable def search (markers : Set ℤ) (B S a z : ℤ) : Option ℤ :=
  let F := eligibleSet markers B S a z
  if h : F.Nonempty then some (F.min' h) else none

lemma search_none {markers : Set ℤ} {B S a z : ℤ} (hB : 0 < B) (hS : 0 ≤ S) :
    search markers B S a z = none ↔ ∀ m, ¬Eligible markers B S a z m := by
  dsimp only [search]
  split_ifs with h
  · simp only [false_iff]
    obtain ⟨m, hm⟩ := h
    exact fun hn => hn m ((mem_eligibleSet hB hS).mp hm)
  · simp only [true_iff]
    exact fun m hm => h ⟨m, (mem_eligibleSet hB hS).mpr hm⟩

lemma search_some {markers : Set ℤ} {B S a z m : ℤ} (hB : 0 < B) (hS : 0 ≤ S) :
    search markers B S a z = some m ↔ Eligible markers B S a z m ∧
      ∀ m', Eligible markers B S a z m' → m ≤ m' := by
  dsimp only [search]
  split_ifs with h
  · constructor
    · intro he
      obtain rfl := Option.some.inj he
      exact ⟨(mem_eligibleSet hB hS).mp (Finset.min'_mem _ h),
        fun m' hm' => Finset.min'_le _ _ ((mem_eligibleSet hB hS).mpr hm')⟩
    · rintro ⟨hm, hmin⟩
      congr 1
      exact le_antisymm (Finset.min'_le _ _ ((mem_eligibleSet hB hS).mpr hm))
        (hmin _ ((mem_eligibleSet hB hS).mp (Finset.min'_mem _ h)))
  · constructor
    · intro he
      cases he
    · rintro ⟨hm, _⟩
      exact False.elim (h ⟨m, (mem_eligibleSet hB hS).mpr hm⟩)

lemma width_shift {B S a x v : ℤ} (hv : B ∣ v) :
    width B S a (x - v) = width B S a x := by
  dsimp [width]
  rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hv, sub_zero, Int.emod_emod]

lemma changed_eligibility {markers : Set ℤ} {B S a z v : ℤ}
    (hB : 0 < B) (hS : 0 ≤ S)
    (hne : search markers B S a z ≠ search markers B S a (z + v)) :
    ∃ m, ¬(Eligible markers B S a z m ↔ Eligible markers B S a (z + v) m) := by
  by_contra! hn
  apply hne
  have he : eligibleSet markers B S a z = eligibleSet markers B S a (z + v) := by
    ext m
    exact (mem_eligibleSet hB hS).trans ((hn m).trans (mem_eligibleSet hB hS).symm)
  simp only [search, he]

lemma crossing {x D v w : ℤ} (hv : |v| ≤ w)
    (hne : ¬(|x| ≤ D ↔ |x - v| ≤ D)) :
    |x - D| ≤ w ∨ |x + D| ≤ w := by
  have hv' := abs_le.mp hv
  by_cases hx : |x| ≤ D
  · have hx' := abs_le.mp hx
    have hn : ¬ |x - v| ≤ D := fun h => hne ⟨fun _ => h, fun _ => hx⟩
    have hn' : ¬(-D ≤ x - v ∧ x - v ≤ D) := by simpa only [abs_le] using hn
    rw [abs_le, abs_le]
    omega
  · have hx' : |x - v| ≤ D := by
      by_contra hh
      exact hne ⟨fun h => False.elim (hx h), fun h => False.elim (hh h)⟩
    have hx'' := abs_le.mp hx'
    have hn' : ¬(-D ≤ x ∧ x ≤ D) := by simpa only [abs_le] using hx
    rw [abs_le, abs_le]
    omega

lemma instability_charge {markers : Set ℤ} {B S a z v w : ℤ}
    (hB : 0 < B) (hS : 0 ≤ S) (hvB : B ∣ v) (hv : |v| ≤ w)
    (hne : search markers B S a z ≠ search markers B S a (z + v)) :
    ∃ m ∈ markers,
      |m - (z + width B S a (m - z))| ≤ w ∨
      |m - (z - width B S a (m - z))| ≤ w := by
  obtain ⟨m, hm⟩ := changed_eligibility hB hS hne
  have hmS : m ∈ markers := by
    by_contra hn
    exact hm (by simp [Eligible, hn])
  have he : width B S a (m - (z + v)) = width B S a (m - z) := by
    rw [show m - (z + v) = (m - z) - v by ring]
    exact width_shift hvB
  have hc : ¬(|m - z| ≤ width B S a (m - z) ↔
      |(m - z) - v| ≤ width B S a (m - z)) := by
    simp only [Eligible, hmS, true_and] at hm
    rw [he] at hm
    simpa only [show m - (z + v) = (m - z) - v by ring] using hm
  refine ⟨m, hmS, ?_⟩
  rw [show m - (z + width B S a (m - z)) = (m - z) - width B S a (m - z) by ring,
    show m - (z - width B S a (m - z)) = (m - z) + width B S a (m - z) by ring]
  exact crossing hv hc

end EndSearch

namespace EndSearch

open scoped Classical

def Boundary (B S a z m : ℤ) (positive : Bool) : ℤ :=
  if positive then z + width B S a (m - z) else z - width B S a (m - z)

lemma boundary_charge_card {ι : Type uι} (s : Finset ι) {markers : Set ℤ}
    {B S a z h w d : ℤ} (δ : ι → ℤ) (positive : Bool)
    (hB : 0 < B) (hS : 2 * h + 2 * w < S) (hSn : 0 ≤ S)
    (hmarkers : MarkerSearch.Separated markers d)
    (hlen : 2 * h + (B - 1) * S + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hmod : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i % B ≠ δ j % B) :
    (s.filter fun i => ∃ m ∈ markers, |m - Boundary B S a (z + δ i) m positive| ≤ w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, m, hm, hc⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, m', hm', hc'⟩ := Finset.mem_filter.mp hj
  have hiδ := abs_le.mp (hδ i hi)
  have hjδ := abs_le.mp (hδ j hj)
  have hmi := width_bounds (x := m - (z + δ i)) (a := a) hB hSn
  have hmj := width_bounds (x := m' - (z + δ j)) (a := a) hB hSn
  have hcb := abs_le.mp hc
  have hcb' := abs_le.mp hc'
  have he : m = m' := by
    cases positive
    · dsimp [Boundary] at hcb hcb'
      exact MarkerSearch.separated_interval_unique hmarkers (by omega) hm hm'
        (show z - a - h - (B - 1) * S - w ≤ m by omega)
        (show m ≤ z - a + h + w by omega) (by omega) (by omega)
    · dsimp [Boundary] at hcb hcb'
      exact MarkerSearch.separated_interval_unique hmarkers (by omega) hm hm'
        (show z + a - h - w ≤ m by omega)
        (show m ≤ z + a + h + (B - 1) * S + w by omega) (by omega) (by omega)
  subst m'
  by_contra hij
  have hidx : (m - (z + δ i)) % B ≠ (m - (z + δ j)) % B := by
    intro he
    have hh := (show Int.ModEq B (m - (z + δ i)) (m - (z + δ j)) from he).sub_left (m - z)
    apply hmod i hi j hj hij
    change Int.ModEq B (δ i) (δ j)
    convert hh using 1 <;> ring
  have hidx' := lt_or_gt_of_ne hidx
  cases positive <;> dsimp [Boundary, width] at hcb hcb'
  all_goals rcases hidx' with hlt | hlt <;> nlinarith

 def Unstable (markers : Set ℤ) (B S a z w : ℤ) : Prop :=
  ∃ v, B ∣ v ∧ |v| ≤ w ∧ search markers B S a z ≠ search markers B S a (z + v)

lemma unstable_card {ι : Type uι2} (s : Finset ι) {markers : Set ℤ}
    {B S a z h w d : ℤ} (δ : ι → ℤ)
    (hB : 0 < B) (hS : 2 * h + 2 * w < S) (hSn : 0 ≤ S)
    (hmarkers : MarkerSearch.Separated markers d)
    (hlen : 2 * h + (B - 1) * S + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hmod : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i % B ≠ δ j % B) :
    (s.filter fun i => Unstable markers B S a (z + δ i) w).card ≤ 2 := by
  let F := fun b => s.filter fun i =>
    ∃ m ∈ markers, |m - Boundary B S a (z + δ i) m b| ≤ w
  have hsub : (s.filter fun i => Unstable markers B S a (z + δ i) w) ⊆
      F true ∪ F false := by
    intro i hi
    obtain ⟨hi, v, hvB, hv, hn⟩ := Finset.mem_filter.mp hi
    obtain ⟨m, hm, hc | hc⟩ := instability_charge hB hSn hvB hv hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, m, hm, hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, m, hm, hc⟩)
  have ht : (F true).card ≤ 1 := boundary_charge_card s δ true hB hS hSn hmarkers hlen hδ hmod
  have hf : (F false).card ≤ 1 := boundary_charge_card s δ false hB hS hSn hmarkers hlen hδ hmod
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

lemma two_searches_card {ι : Type uι3} (s : Finset ι) {markers : Set ℤ}
    {B S a₀ a₁ z h w d : ℤ} (δ : ι → ℤ)
    (hB : 0 < B) (hS : 2 * h + 2 * w < S) (hSn : 0 ≤ S)
    (hmarkers : MarkerSearch.Separated markers d)
    (hlen : 2 * h + (B - 1) * S + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hmod : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i % B ≠ δ j % B) :
    (s.filter fun i => Unstable markers B S a₀ (z + δ i) w ∨
      Unstable markers B S a₁ (z + δ i) w).card ≤ 4 := by
  rw [Finset.filter_or]
  have h₀ := unstable_card (a := a₀) (z := z) s δ hB hS hSn hmarkers hlen hδ hmod
  have h₁ := unstable_card (a := a₁) (z := z) s δ hB hS hSn hmarkers hlen hδ hmod
  exact (Finset.card_union_le _ _).trans (by omega)

end EndSearch

namespace MarkerSearch

lemma interval_card {S : Set ℤ} {d l r : ℤ} (F : Finset ℤ) (N : ℕ)
    (hS : Separated S d) (hd : 0 < d) (hlen : r - l < N * d)
    (hF : ∀ m ∈ F, m ∈ S ∧ l ≤ m ∧ m ≤ r) : F.card ≤ N := by
  classical
  have hb : ∀ m : {m // m ∈ F}, 0 ≤ (m.val - l) / d ∧ (m.val - l) / d < N := by
    intro m
    obtain ⟨_, hl, hr⟩ := hF m.val m.2
    exact ⟨Int.ediv_nonneg (by omega) (le_of_lt hd),
      (Int.ediv_lt_iff_lt_mul hd).mpr (by omega)⟩
  let f : {m // m ∈ F} → Fin N := fun m =>
    ⟨((m.val - l) / d).toNat, (Int.toNat_lt (hb m).1).mpr (hb m).2⟩
  have hinj : Function.Injective f := by
    intro m m' he
    have hh := congrArg Fin.val he
    have hq : (m.val - l) / d = (m'.val - l) / d := by
      dsimp [f] at hh
      have h₀ := Int.toNat_of_nonneg (hb m).1
      have h₁ := Int.toNat_of_nonneg (hb m').1
      omega
    apply Subtype.ext
    by_contra hn
    have hsep := hS m.val (hF m.val m.2).1 m'.val (hF m'.val m'.2).1 hn
    have hmod₀ := Int.emod_nonneg (m.val - l) (ne_of_gt hd)
    have hmod₁ := Int.emod_nonneg (m'.val - l) (ne_of_gt hd)
    have hlt₀ := Int.emod_lt_of_pos (m.val - l) hd
    have hlt₁ := Int.emod_lt_of_pos (m'.val - l) hd
    have he₀ := Int.mul_ediv_add_emod (m.val - l) d
    have he₁ := Int.mul_ediv_add_emod (m'.val - l) d
    rw [hq] at he₀
    have habs : |m.val - m'.val| < d := abs_lt.mpr ⟨by omega, by omega⟩
    omega
  simpa using Fintype.card_le_of_injective f hinj

end MarkerSearch

namespace EndSearch

open scoped Classical

lemma nested {markers : Set ℤ} {B S a₀ a₁ z z' H : ℤ}
    (hB : 0 < B) (hS : 0 ≤ S) (hwidth : a₀ + (B - 1) * S + H ≤ a₁)
    (hzz : |z - z'| ≤ H) (hne : search markers B S a₀ z' ≠ none) :
    search markers B S a₁ z ≠ none := by
  intro hn
  cases he : search markers B S a₀ z' with
  | none => exact hne he
  | some m =>
    have hm := (search_some hB hS).mp he
    apply (search_none hB hS).mp hn m
    refine ⟨hm.1.1, ?_⟩
    have hdist : |m - z| ≤ |m - z'| + |z - z'| := by
      simpa only [abs_sub_comm z' z] using abs_sub_le m z' z
    exact (hdist.trans (add_le_add (hm.1.2.trans (width_bounds hB hS).2) hzz)).trans
      (hwidth.trans (width_bounds hB hS).1)

lemma anchor_card {ι : Type uι4} (s : Finset ι) {markers : Set ℤ}
    {B S d z h q₀ : ℤ} (δ : ι → ℤ)
    (hB : 0 < B) (hS : 0 ≤ S) (hd : 0 < d)
    (hmarkers : MarkerSearch.Separated markers d)
    (hlen : 2 * h + 2 * (B - 1) * S < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h) :
    (s.image fun i => (search markers B S (3 * d) (z + δ i)).getD q₀).card ≤ 8 := by
  classical
  let l := z - h - (3 * d + (B - 1) * S)
  let r := z + h + (3 * d + (B - 1) * S)
  let F := (Finset.Icc l r).filter (· ∈ markers)
  have hFc : F.card ≤ 7 := MarkerSearch.interval_card (l := l) (r := r) F 7 hmarkers hd (by dsimp [l, r]; nlinarith [hlen])
    (fun m hm => by
      obtain ⟨hb, hm⟩ := Finset.mem_filter.mp hm
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hb
      exact ⟨hm, hl, hr⟩)
  have hsub : (s.image fun i => (search markers B S (3 * d) (z + δ i)).getD q₀) ⊆
      insert q₀ F := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    cases he : search markers B S (3 * d) (z + δ i) with
    | none => simp
    | some m =>
      simp only [Option.getD_some, Finset.mem_insert]
      right
      have hm := (search_some hB hS).mp he
      have hb := abs_le.mp (hm.1.2.trans (width_bounds hB hS).2)
      have hiδ := abs_le.mp (hδ i hi)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp [l]; omega,
        by dsimp [r]; omega⟩, hm.1.1⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))

end EndSearch

namespace StencilSparsity

open scoped Classical

lemma biUnion_card_real {Q : Type uQ} {P : Type uP} (s : Finset Q) (F : Q → Finset P)
    (c : ℝ) (h : ∀ q ∈ s, ((F q).card : ℝ) ≤ c) :
    ((s.biUnion F).card : ℝ) ≤ s.card * c := by
  classical
  calc
    ((s.biUnion F).card : ℝ) ≤ ((∑ q ∈ s, (F q).card : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := s) (t := F))
    _ = ∑ q ∈ s, ((F q).card : ℝ) := by simp
    _ ≤ ∑ _q ∈ s, c := Finset.sum_le_sum h
    _ = s.card * c := by simp

lemma whole_stencil {P : Type uP2} {Q : Type uQ2} {J : Type uJ} (bad instability : Finset P)
    (anchors : Finset Q) (labels : Finset J) (clock : Q → Finset P)
    (inner : Q → J → Finset P) (c : ℝ) (μ : ℕ)
    (hc : 0 ≤ c) (hanchor : anchors.card ≤ 20)
    (hunstable : instability.card ≤ 4)
    (hclock : ∀ q ∈ anchors, ((clock q).card : ℝ) ≤ c)
    (hinner : ∀ q ∈ anchors, ∀ j ∈ labels, (inner q j).card ≤ 3)
    (hcover : bad ⊆ instability ∪ anchors.biUnion
      (fun q => clock q ∪ labels.biUnion (inner q)))
    (hμ : 20 * (c + 4 * labels.card) + 10 < μ) : bad.card < μ := by
  classical
  have hrow : ∀ q ∈ anchors,
      (((clock q ∪ labels.biUnion (inner q)).card : ℕ) : ℝ) ≤ c + 3 * labels.card := by
    intro q hq
    have ht := Finset.card_union_le (clock q) (labels.biUnion (inner q))
    have ht' : (((clock q ∪ labels.biUnion (inner q)).card : ℕ) : ℝ) ≤
        (clock q).card + (labels.biUnion (inner q)).card := by exact_mod_cast ht
    have hi := biUnion_card_real labels (inner q) 3 (fun j hj => by
      exact_mod_cast hinner q hq j hj)
    nlinarith [hclock q hq]
  have hall := biUnion_card_real anchors
    (fun q => clock q ∪ labels.biUnion (inner q)) (c + 3 * labels.card) hrow
  have hu := Finset.card_union_le instability
    (anchors.biUnion (fun q => clock q ∪ labels.biUnion (inner q)))
  have hb := (Finset.card_le_card hcover).trans hu
  have hb' : (bad.card : ℝ) ≤ instability.card +
      (anchors.biUnion (fun q => clock q ∪ labels.biUnion (inner q))).card := by
    exact_mod_cast hb
  have ha : (anchors.card : ℝ) ≤ 20 := by exact_mod_cast hanchor
  have hz : (instability.card : ℝ) ≤ 4 := by exact_mod_cast hunstable
  have hm : (bad.card : ℝ) < μ := by
    have hnon : 0 ≤ (labels.card : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right ha (show 0 ≤ c + 3 * labels.card by positivity)]
  exact_mod_cast hm

lemma good_copy {Kind : Type uKind} [Fintype Kind] (μ : ℕ)
    (bad : Finset ((Kind × Fin μ) × (Kind × Fin μ))) (hbad : bad.card < μ) :
    ∀ kind : Kind, ∃ copy : Fin μ, ∀ q, ((kind, copy), q) ∉ bad := by
  classical
  intro kind
  by_contra! hn
  choose q hq using hn
  let f : Fin μ → {p // p ∈ bad} := fun copy => ⟨((kind, copy), q copy), hq copy⟩
  have hf : Function.Injective f := by
    intro i j he
    exact congrArg (fun p : {p // p ∈ bad} => p.val.1.2) he
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  omega

noncomputable def decode {P : Type uP3} (witness : P → Prop) : Option P :=
  if h : ∃! p, witness p then some h.choose else none

lemma decode_eq_some {P : Type uP4} {witness : P → Prop} {p : P} :
    decode witness = some p ↔ witness p ∧ ∀ q, witness q → q = p := by
  classical
  dsimp only [decode]
  split_ifs with h
  · constructor
    · intro he
      have hp := Option.some.inj he
      exact hp ▸ h.choose_spec
    · rintro ⟨hp, huniq⟩
      exact congrArg some (huniq _ h.choose_spec.1)
  · constructor
    · intro he
      cases he
    · rintro ⟨hp, huniq⟩
      exact False.elim (h ⟨p, hp, huniq⟩)

lemma decode_sound {P : Type uP5} {witness : P → Prop} {actual decoded : P}
    (hactual : witness actual) (hdecode : decode witness = some decoded) : decoded = actual := by
  exact ((decode_eq_some.mp hdecode).2 actual hactual).symm

end StencilSparsity

end GeneralizedStarHeight

end OAI
