import OAI.Computability.WitnessedChoice.TermGraphs

namespace OAI

section

namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

@[simp] theorem stateCode_inj {x y : Finset A} : stateCode x = stateCode y ↔ x = y := by
  unfold stateCode
  rw [ofFinset_inj]
  exact Finset.image_inj atom_injective

@[simp] theorem smul_stateCode (g : Equiv.Perm A) (x : Finset A) :
    g • stateCode x = stateCode (x.image g) := by
  simp only [stateCode, smul_ofFinset, Finset.image_image]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_image, Function.comp_apply, smul_atom]
  rfl

@[simp] theorem smul_choiceCode (g : Equiv.Perm A) (c : Option A) :
    g • choiceCode c = choiceCode (c.map g) := by
  cases c <;> simp [choiceCode, ordinal, smul_ofFinset]

theorem stateCode_fixed_of_pointwise {g : Equiv.Perm A} {x : Finset A}
    (h : ∀ a ∈ x, g a = a) : g • stateCode x = stateCode x := by
  rw [smul_stateCode, stateCode_inj]
  calc
    x.image g = x.image id := Finset.image_congr h
    _ = x := Finset.image_id

namespace Selection

variable {P : Selection A}

theorem choices_nonempty (x : Finset A) : (P.choices x).Nonempty := by
  unfold choices
  split_ifs with h
  · exact h.1.image _
  · exact Finset.singleton_nonempty _

@[simp] theorem some_mem_choices {x : Finset A} {a : A} :
    some a ∈ P.choices x ↔ a ∈ P.candidates x ∧ P.TransitiveAt x := by
  unfold choices
  split_ifs with h
  · simp [h.2]
  · simp only [Finset.mem_singleton, reduceCtorEq, false_iff, not_and]
    intro ha ht
    exact h ⟨⟨a, ha⟩, ht⟩

@[simp] theorem none_mem_choices {x : Finset A} :
    none ∈ P.choices x ↔ ¬ ((P.candidates x).Nonempty ∧ P.TransitiveAt x) := by
  unfold choices
  split_ifs <;> simp_all

theorem advance_mono (x : Finset A) (c : Option A) : x ⊆ advance x c := by
  cases c
  · exact Finset.Subset.refl _
  · exact Finset.subset_insert _ _

theorem advance_card {x : Finset A} {c : Option A} (h : x ≠ advance x c) :
    (advance x c).card = x.card + 1 := by
  cases c with
  | none => exact (h rfl).elim
  | some a =>
    change (insert a x).card = _
    apply Finset.card_insert_of_notMem
    intro ha
    exact h (Finset.insert_eq_of_mem ha).symm

theorem Prefix.restrict {b c k l} (h : P.Prefix b c k) (hle : l ≤ k) :
    P.Prefix b c l :=
  ⟨h.1, fun i hi => h.2 i (Nat.lt_of_lt_of_le hi hle)⟩

theorem Prefix.monotone {b c k} (h : P.Prefix b c k) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k) : b i ⊆ b j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j hij ih =>
    have hjk : j < k := by omega
    have hs := h.2 j hjk
    rw [hs.2]
    exact (ih (by omega)).trans (advance_mono _ _)

theorem Prefix.card_eq {b c k} (h : P.Prefix b c k)
    (hstrict : ∀ i < k, b i ≠ b (i+1)) : ∀ i ≤ k, (b i).card = i := by
  intro i hi
  induction i with
  | zero => simp [h.1]
  | succ i ih =>
    have hic : i < k := by omega
    have hs := h.2 i hic
    rw [hs.2, advance_card (by simpa [hs.2] using hstrict i hic), ih (by omega)]

theorem FirstStabilization.length_le [Fintype A] {b c t} (h : P.FirstStabilization b c t) :
    t ≤ Fintype.card A := by
  have hc := (h.1.restrict (Nat.le_succ t)).card_eq h.2.1 t le_rfl
  rw [← hc]
  exact Finset.card_le_univ _

theorem exists_first_stabilization [Fintype A] {b c}
    (h : ∀ k, P.Prefix b c k) : ∃ t ≤ Fintype.card A, P.FirstStabilization b c t := by
  have hex : ∃ t, b t = b (t+1) := by
    by_contra hn
    push Not at hn
    have hc := (h (Fintype.card A + 1)).card_eq (fun i _ => hn i) (Fintype.card A + 1) le_rfl
    have hb := Finset.card_le_univ (b (Fintype.card A + 1))
    omega
  refine ⟨Nat.find hex, ?_, h _, ?_, Nat.find_spec hex⟩
  · have hh : P.FirstStabilization b c (Nat.find hex) :=
      ⟨h _, fun i hi => Nat.find_min hex hi, Nat.find_spec hex⟩
    exact hh.length_le
  · exact fun i hi => Nat.find_min hex hi

theorem Filtered.history {S : Input A} {α : HF A} (hf : P.Filtered S α)
    {b c k} (hp : P.Prefix b c k) {i : ℕ} (hi : i ≤ k)
    {g : Equiv.Perm A} (hg : g ∈ P.witnesses (b i)) : HistoryAut S α b i g := by
  refine ⟨hf.2.1 _ _ hg, ?_⟩
  intro j hji
  apply stateCode_fixed_of_pointwise
  intro a ha
  exact hf.2.2 _ _ hg _ (hp.monotone hji hi ha)

theorem Filtered.witnessed {S : Input A} {α : HF A} (hf : P.Filtered S α)
    {b c k} (hp : P.Prefix b c k) {i : ℕ} (hi : i ≤ k) (terminal : Finset A) :
    P.WitnessedAt S α b terminal i := by
  refine ⟨choices_nonempty _, fun g hg => hf.history hp hi hg, ?_⟩
  intro u hu v hv
  by_cases ht : (P.candidates (b i)).Nonempty ∧ P.TransitiveAt (b i)
  · simp only [choices, ite_eq_left ht, Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨a', ha', rfl⟩ := hv
    obtain ⟨g, hg, hga⟩ := ht.2 a ha a' ha'
    refine ⟨g, hg, ?_⟩
    simpa [choiceCode] using congrArg atom hga
  · have hu' : u = none := by simpa [choices, ht] using hu
    have hv' : v = none := by simpa [choices, ht] using hv
    subst u; subst v
    exact ⟨1, hf.1 _, one_smul _ _⟩

theorem Filtered.all_paths_witnessed {S : Input A} {α : HF A} (hf : P.Filtered S α)
    {b c t} (h : P.FirstStabilization b c t) :
    ∀ i ≤ t, P.WitnessedAt S α b (b t) i := by
  intro i hi
  exact hf.witnessed h.1 (by omega) _

end Selection

end

end WitnessedChoice

end

section

namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

@[simp] theorem choiceCode_inj {c d : Option A} : choiceCode c = choiceCode d ↔ c = d := by
  cases c with
  | none =>
    cases d with
    | none => simp
    | some a =>
      constructor
      · intro h
        have he := congrArg isSet h
        simp [choiceCode, ordinal] at he
      · simp
  | some a =>
    cases d with
    | none =>
      constructor
      · intro h
        have he := congrArg isSet h
        simp [choiceCode, ordinal] at he
      · simp
    | some b =>
      simp only [choiceCode, Option.some.injEq]
      exact atom_injective.eq_iff

theorem image_mul (g h : Equiv.Perm A) (x : Finset A) :
    x.image (g*h) = (x.image h).image g := by
  rw [Finset.image_image]
  rfl

@[simp] theorem image_inv_image (g : Equiv.Perm A) (x : Finset A) :
    (x.image g).image (g⁻¹ : Equiv.Perm A) = x := by
  simp [Finset.image_image, Function.comp_def]

namespace Selection

variable [Fintype A]

variable {P : Selection A} {S : Input A} {α : HF A}

theorem Equivariant.transitiveAt (he : P.Equivariant S α) {g : Equiv.Perm A}
    (hg : g ∈ paramAut S α) {x : Finset A} (ht : P.TransitiveAt x) :
    P.TransitiveAt (x.image g) := by
  intro a ha b hb
  rw [(he g hg x).1] at ha hb
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨h, hh, hab⟩ := ht a₀ ha₀ b₀ hb₀
  refine ⟨g*h*g⁻¹, ?_, ?_⟩
  · rw [(he g hg x).2]
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  · simpa [Equiv.Perm.mul_apply] using congrArg g hab

theorem Equivariant.transitiveAt_iff (he : P.Equivariant S α) {g : Equiv.Perm A}
    (hg : g ∈ paramAut S α) (x : Finset A) :
    P.TransitiveAt (x.image g) ↔ P.TransitiveAt x := by
  constructor
  · intro h
    have hh := he.transitiveAt ((paramAut S α).inv_mem hg) h
    rw [image_inv_image] at hh
    exact hh
  · exact he.transitiveAt hg

theorem Equivariant.choices_image (he : P.Equivariant S α) {g : Equiv.Perm A}
    (hg : g ∈ paramAut S α) (x : Finset A) :
    P.choices (x.image g) = (P.choices x).image (Option.map g) := by
  have hc : (P.candidates (x.image g)).Nonempty ↔ (P.candidates x).Nonempty := by
    rw [(he g hg x).1, Finset.image_nonempty]
  simp only [choices, hc, he.transitiveAt_iff hg]
  split_ifs with h
  · rw [(he g hg x).1]
    simp [Finset.image_image, Function.comp_def]
  · simp

omit [Fintype A] in
@[simp] theorem advance_image (g : Equiv.Perm A) (x : Finset A) (c : Option A) :
    (advance x c).image g = advance (x.image g) (c.map g) := by
  cases c <;> simp [advance]

theorem match_prefixes (hf : P.Filtered S α) (he : P.Equivariant S α)
    {b b' : ℕ → Finset A} {c c' : ℕ → Option A} {k : ℕ}
    (hp : P.Prefix b c k) (hp' : P.Prefix b' c' k) :
    ∃ g ∈ paramAut S α, ∀ i ≤ k, (b i).image g = b' i := by
  induction k with
  | zero =>
    refine ⟨1, (paramAut S α).one_mem, ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp [hp.1, hp'.1]
  | succ k ih =>
    obtain ⟨g, hg, hm⟩ := ih (hp.restrict (Nat.le_succ _))
      (hp'.restrict (Nat.le_succ _))
    have hkc := (hp.2 k (Nat.lt_succ_self _)).1
    have hkc' := (hp'.2 k (Nat.lt_succ_self _)).1
    have htc : (c k).map g ∈ P.choices (b' k) := by
      rw [← hm k le_rfl, he.choices_image hg]
      exact Finset.mem_image.mpr ⟨c k, hkc, rfl⟩
    have hw := hf.witnessed hp' (Nat.le_succ k) (b' (k+1))
    obtain ⟨h, hh, hch⟩ := hw.2.2 _ htc _ hkc'
    have hhistory := hw.2.1 h hh
    have hmap : ((c k).map g).map h = c' k := by
      exact choiceCode_inj.mp (by simpa only [smul_choiceCode] using hch)
    have hfixed : ∀ i ≤ k, (b' i).image h = b' i := by
      intro i hi
      exact stateCode_inj.mp (by simpa only [smul_stateCode] using hhistory.2 i hi)
    refine ⟨h*g, (paramAut S α).mul_mem hhistory.1 hg, ?_⟩
    intro i hi
    by_cases hik : i ≤ k
    · rw [image_mul, hm i hik, hfixed i hik]
    · have hik1 : i = k+1 := by omega
      subst i
      rw [(hp.2 k (Nat.lt_succ_self _)).2, image_mul, advance_image,
        hm k le_rfl, advance_image, hfixed k le_rfl, hmap,
        ← (hp'.2 k (Nat.lt_succ_self _)).2]

theorem first_stabilization_unique_length (hf : P.Filtered S α)
    (he : P.Equivariant S α) {b b' : ℕ → Finset A} {c c' : ℕ → Option A} {t u : ℕ}
    (ht : P.FirstStabilization b c t) (hu : P.FirstStabilization b' c' u) : t = u := by
  have not_lt {b b' : ℕ → Finset A} {c c' : ℕ → Option A} {t u : ℕ}
      (ht : P.FirstStabilization b c t) (hu : P.FirstStabilization b' c' u)
      (hlt : t < u) : False := by
    obtain ⟨g, _, hm⟩ := match_prefixes hf he ht.1 (hu.1.restrict (by omega))
    apply hu.2.1 t hlt
    rw [← hm t (by omega), ← hm (t+1) le_rfl, ht.2.2]
  apply Nat.le_antisymm
  · by_contra h
    exact not_lt hu ht (by omega)
  · by_contra h
    exact not_lt ht hu (by omega)

theorem terminal_orbit (hf : P.Filtered S α) (he : P.Equivariant S α)
    {b b' : ℕ → Finset A} {c c' : ℕ → Option A} {t u : ℕ}
    (ht : P.FirstStabilization b c t) (hu : P.FirstStabilization b' c' u) :
    ∃ g ∈ paramAut S α, (b t).image g = b' u := by
  have htu := first_stabilization_unique_length hf he ht hu
  subst u
  obtain ⟨g, hg, hm⟩ := match_prefixes hf he ht.1 hu.1
  exact ⟨g, hg, hm t (Nat.le_succ t)⟩

def selected (x : Finset A) : Option A := (choices_nonempty (P := P) x).choose

omit [Fintype A] in
theorem selected_mem (x : Finset A) : P.selected x ∈ P.choices x :=
  (choices_nonempty (P := P) x).choose_spec

def run (P : Selection A) : ℕ → Finset A
  | 0 => ∅
  | k+1 => advance (run P k) (P.selected (run P k))

omit [Fintype A] in
theorem run_prefix (k : ℕ) : P.Prefix P.run (fun i => P.selected (P.run i)) k := by
  exact ⟨rfl, fun i _ => ⟨selected_mem _, rfl⟩⟩

theorem exists_path : ∃ b c t, P.FirstStabilization b c t := by
  obtain ⟨t, _, ht⟩ := exists_first_stabilization (P := P) P.run_prefix
  exact ⟨P.run, (fun i => P.selected (P.run i)), t, ht⟩

end Selection

end

end WitnessedChoice

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type} [Fintype A]

def decodeState (x : HF A) : Finset A := Finset.univ.filter (fun a => atom a ∈ elements x)

def decodeChoice (x : HF A) : Option A :=
  if h : ∃ a, x = atom a then some h.choose else none

@[simp] theorem decodeState_code (x : Finset A) : decodeState (stateCode x) = x := by
  ext a
  simp [decodeState, stateCode, atom_injective.eq_iff]

@[simp] theorem decodeChoice_code (c : Option A) : decodeChoice (choiceCode c) = c := by
  cases c with
  | none =>
    have h : ¬ ∃ a : A, (ordinal (A := A) 0) = atom a := by
      rintro ⟨a, ha⟩
      have hi := congrArg isSet ha
      simp at hi
    simp [choiceCode, decodeChoice, h]
  | some a =>
    change (if h : ∃ b : A, atom a = atom b then some h.choose else none) = some a
    split
    next h => exact congrArg some (atom_injective h.choose_spec.symm)
    next h => exact (h ⟨a, rfl⟩).elim

omit [Fintype A] in
@[simp] theorem TC_stateCode (x : Finset A) : TC (stateCode x) = x.image atom := by
  have hc (a : A) : closure (atom a) = {atom a} := by
    rw [WitnessedSeparation.Hereditary.closure]
    rw [WitnessedSeparation.Hereditary.elements_atom]
    simp
  ext z
  simp [TC, stateCode, hc, eq_comm]

structure Realizes (P : Selection A)
    (step : HF A → HF A → Result (HF A))
    (choice : HF A → Result (HF A))
    (witness : HF A → HF A → Result (HF A)) : Prop where
  choice_eq : ∀ x, choice (stateCode x) =
    some (ofFinset ((P.choices x).image choiceCode))
  step_eq : ∀ x c, c ∈ P.choices x → step (stateCode x) (choiceCode c) =
    some (stateCode (Selection.advance x c))
  witness_eq : ∀ z x, witness (stateCode z) (stateCode x) =
    some (ofFinset ((P.witnesses x).image permutationGraph))

namespace Realizes

variable {P : Selection A} {step : HF A → HF A → Result (HF A)}
  {choice : HF A → Result (HF A)} {witness : HF A → HF A → Result (HF A)}
  (hr : Realizes P step choice witness)

include hr

theorem prefix_decode {b c : ℕ → HF A} {k : ℕ} (hp : ChoicePrefix step choice b c k) :
    P.Prefix (decodeState ∘ b) (decodeChoice ∘ c) k ∧
    (∀ i ≤ k, b i = stateCode (decodeState (b i))) ∧
    (∀ i < k, c i = choiceCode (decodeChoice (c i))) := by
  have h0 : decodeState (b 0) = ∅ := by simp [hp.1, emptyHF, decodeState]
  have hstates : ∀ i ≤ k, b i = stateCode (decodeState (b i)) := by
    intro i hi
    induction i with
    | zero => simp [hp.1, emptyHF, stateCode, decodeState]
    | succ i ih =>
      have hik : i < k := by omega
      obtain ⟨⟨D, hD, hc⟩, hs⟩ := hp.2 i hik
      have hb := ih (by omega)
      rw [hb, hr.choice_eq] at hD
      cases hD
      simp only [elements_ofFinset] at hc
      obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hc
      have he := hr.step_eq (decodeState (b i)) a ha
      rw [← hb, hac] at he
      rw [he] at hs
      have hs' := Option.some.inj hs
      rw [← hs', decodeState_code]
  have hchoices : ∀ i < k, ∃ a ∈ P.choices (decodeState (b i)), choiceCode a = c i := by
    intro i hi
    obtain ⟨⟨D, hD, hc⟩, _⟩ := hp.2 i hi
    rw [hstates i (by omega), hr.choice_eq] at hD
    cases hD
    simp only [elements_ofFinset] at hc
    exact Finset.mem_image.mp hc
  refine ⟨⟨h0, ?_⟩, hstates, ?_⟩
  · intro i hi
    obtain ⟨a, ha, hac⟩ := hchoices i hi
    have hd : decodeChoice (c i) = a := by rw [← hac, decodeChoice_code]
    refine ⟨by simpa only [Function.comp_apply, hd] using ha, ?_⟩
    obtain ⟨_, hs⟩ := hp.2 i hi
    rw [hstates i (by omega), ← hac, hr.step_eq _ _ ha] at hs
    have he := Option.some.inj hs
    simp only [Function.comp_apply, hd]
    rw [← he, decodeState_code]
  · intro i hi
    obtain ⟨a, _, hac⟩ := hchoices i hi
    rw [← hac, decodeChoice_code]

theorem first_decode {b c : ℕ → HF A} {t : ℕ} (hp : FirstPath step choice b c t) :
    P.FirstStabilization (decodeState ∘ b) (decodeChoice ∘ c) t := by
  obtain ⟨hpre, hb, _⟩ := hr.prefix_decode hp.1
  refine ⟨hpre, ?_, congrArg decodeState hp.2.2⟩
  intro i hi he
  apply hp.2.1 i hi
  rw [hb i (by omega), hb (i+1) (by omega)]
  exact congrArg stateCode he

theorem good {S : Input A} {α : HF A} (hf : P.Filtered S α)
    (p : ℕ) (hp : Fintype.card A + 2 ≤ p) (free : Finset (Fin 1))
    (output : HF A → Result Bool) (hout : ∀ x : Finset A, (output (stateCode x)).isSome) :
    GoodWSC S p free (Fin.cons α Fin.elim0) step choice witness output := by
  constructor
  · intro b c k hk hstrict
    obtain ⟨hpre, hb, hc⟩ := hr.prefix_decode hk
    have hs : ∀ i < k, (decodeState ∘ b) i ≠ (decodeState ∘ b) (i+1) := by
      intro i hi he
      apply hstrict i hi
      rw [hb i (by omega), hb (i+1) (by omega)]
      exact congrArg stateCode he
    have hn : k ≤ Fintype.card A := by
      rw [← hpre.card_eq hs k le_rfl]
      exact Finset.card_le_univ _
    refine ⟨by omega, ?_, ofFinset ((P.choices (decodeState (b k))).image choiceCode), ?_, ?_, ?_⟩
    · rw [hb k le_rfl, TC_stateCode, Finset.card_image_of_injective _ atom_injective]
      exact (Finset.card_le_univ _).trans (by omega)
    · rw [hb k le_rfl, hr.choice_eq, decodeState_code]
    · simpa only [elements_ofFinset, Finset.image_nonempty] using P.choices_nonempty (decodeState (b k))
    · intro u hu
      simp only [elements_ofFinset] at hu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      rw [hb k le_rfl, hr.step_eq _ _ ha]
      simp
  · intro b c t ht
    obtain ⟨hpre, hb, hc⟩ := hr.prefix_decode ht.1
    have hfirst := hr.first_decode ht
    have hn := hfirst.length_le
    refine ⟨by omega, ?_, ?_⟩
    · intro i hi
      let x := decodeState (b i)
      let z := decodeState (b t)
      refine ⟨ofFinset ((P.choices x).image choiceCode),
        ofFinset ((P.witnesses x).image permutationGraph), ?_, ?_, ?_⟩
      · rw [hb i (by omega), hr.choice_eq]
      · rw [hb t (by omega), hb i (by omega), hr.witness_eq]
      · obtain ⟨_, hwnd, htrans⟩ := hf.witnessed hpre (by omega : i ≤ t+1) z
        refine ⟨by simp, ?_, ?_⟩
        · intro w hw
          simp only [elements_ofFinset] at hw
          obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨hpar, hhist⟩ := hwnd g hg
          refine ⟨g, rfl, hpar.1, ?_, ?_⟩
          · intro j hj
            have hj0 : j = 0 := Fin.eq_zero j
            subst j
            exact hpar.2
          · intro j hj
            rw [hb j (by omega)]
            exact hhist j hj
        · intro u hu v hv
          simp only [elements_ofFinset] at hu
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
          simp only [elements_ofFinset] at hv
          obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hv
          obtain ⟨g, hg, he⟩ := htrans a ha a' ha'
          refine ⟨g, ?_, he⟩
          simp only [elements_ofFinset]
          apply Finset.mem_image.mpr
          exact ⟨g, hg, rfl⟩
    · rw [hb t (by omega)]
      exact hout _

theorem boolean {S : Input A} {α : HF A} (hf : P.Filtered S α)
    (p : ℕ) (hp : Fintype.card A + 2 ≤ p) (free : Finset (Fin 1))
    (output : HF A → Result Bool) (hout : ∀ x : Finset A, (output (stateCode x)).isSome) :
    ∃ b, witnessedIteration S p free (Fin.cons α Fin.elim0) step choice witness output = some b := by
  unfold witnessedIteration
  rw [ite_eq_left (hr.good hf p hp free output hout)]
  exact ⟨_, rfl⟩

end Realizes

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

def liftRen {n m : ℕ} (f : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (Fin.succ ∘ f)

@[simp] lemma liftRen_zero {n m : ℕ} (f : Fin n → Fin m) : liftRen f 0 = 0 := rfl

@[simp] lemma liftRen_succ {n m : ℕ} (f : Fin n → Fin m) (i : Fin n) :
    liftRen f i.succ = (f i).succ := rfl

lemma cons_comp_liftRen {X : Type} {n m : ℕ} (f : Fin n → Fin m) (env : Fin m → X) (x : X) :
    Fin.cons x env ∘ liftRen f = Fin.cons x (env ∘ f) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

mutual
  def Term.rename {n m : ℕ} (f : Fin n → Fin m) : Term n → Term m
    | .var i => .var (f i)
    | .empty => .empty
    | .atoms => .atoms
    | .pair a b => .pair (a.rename f) (b.rename f)
    | .union a => .union (a.rename f)
    | .unique a => .unique (a.rename f)
    | .card a => .card (a.rename f)
    | .comprehend body range guard => .comprehend (body.rename (liftRen f))
        (range.rename f) (guard.rename (liftRen f))
    | .iterate step => .iterate (step.rename (liftRen f))
  def Formula.rename {n m : ℕ} (f : Fin n → Fin m) : Formula n → Formula m
    | .equal a b => .equal (a.rename f) (b.rename f)
    | .input r a b => .input r (a.rename f) (b.rename f)
    | .neg a => .neg (a.rename f)
    | .and a b => .and (a.rename f) (b.rename f)
    | .or a b => .or (a.rename f) (b.rename f)
    | .wsc step choice witness output => .wsc (step.rename (liftRen (liftRen f)))
        (choice.rename (liftRen f)) (witness.rename (liftRen (liftRen f)))
        (output.rename (liftRen f))
end

mutual
  @[simp] theorem Term.rename_count {n m : ℕ} (t : Term n) (f : Fin n → Fin m) :
      (t.rename f).wscCount = t.wscCount := by
    cases t with
    | var i => rfl
    | empty => rfl
    | atoms => rfl
    | pair a b => simp only [Term.rename,Term.wscCount,a.rename_count,b.rename_count]
    | union a => exact a.rename_count f
    | unique a => exact a.rename_count f
    | card a => exact a.rename_count f
    | comprehend b r g => simp only [Term.rename,Term.wscCount,b.rename_count,r.rename_count,g.rename_count]
    | iterate s => exact s.rename_count (liftRen f)
  @[simp] theorem Formula.rename_count {n m : ℕ} (a : Formula n) (f : Fin n → Fin m) :
      (a.rename f).wscCount = a.wscCount := by
    cases a with
    | equal a b => simp only [Formula.rename,Formula.wscCount,a.rename_count,b.rename_count]
    | input r a b => simp only [Formula.rename,Formula.wscCount,a.rename_count,b.rename_count]
    | neg a => exact a.rename_count f
    | and a b => simp only [Formula.rename,Formula.wscCount,a.rename_count,b.rename_count]
    | or a b => simp only [Formula.rename,Formula.wscCount,a.rename_count,b.rename_count]
    | wsc s c w o => simp only [Formula.rename,Formula.wscCount,s.rename_count,c.rename_count,w.rename_count,o.rename_count]
end

variable {A : Type} [Fintype A]

mutual
  theorem Term.eval_rename (S : Input A) (p : Polynomial ℝ) {n m : ℕ}
      (t : Term n) (ht : t.wscCount = 0) (f : Fin n → Fin m) (env : Fin m → HF A) :
      (t.rename f).eval S p env = t.eval S p (env ∘ f) := by
    cases t with
    | var i => rfl
    | empty => rfl
    | atoms => rfl
    | pair a b =>
      simp only [Term.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Term.rename,Term.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | union a => simp only [Term.rename,Term.eval,a.eval_rename S p ht]
    | unique a => simp only [Term.rename,Term.eval,a.eval_rename S p ht]
    | card a => simp only [Term.rename,Term.eval,a.eval_rename S p ht]
    | comprehend b r g =>
      simp only [Term.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Term.rename,Term.eval,r.eval_rename S p ht.1.2]
      congr 1
      funext x
      have hb : (fun x => (b.rename (liftRen f)).eval S p (Fin.cons x env)) =
          fun x => b.eval S p (Fin.cons x (env ∘ f)) := by
        funext x
        rw [b.eval_rename S p ht.1.1,cons_comp_liftRen]
      have hg : (fun x => (g.rename (liftRen f)).eval S p (Fin.cons x env)) =
          fun x => g.eval S p (Fin.cons x (env ∘ f)) := by
        funext x
        rw [g.eval_rename S p ht.2,cons_comp_liftRen]
      rw [hb,hg]
    | iterate s =>
      simp only [Term.rename,Term.eval]
      congr 1
      funext x
      rw [s.eval_rename S p ht,cons_comp_liftRen]
  theorem Formula.eval_rename (S : Input A) (p : Polynomial ℝ) {n m : ℕ}
      (a : Formula n) (ht : a.wscCount = 0) (f : Fin n → Fin m) (env : Fin m → HF A) :
      (a.rename f).eval S p env = a.eval S p (env ∘ f) := by
    cases a with
    | equal a b =>
      simp only [Formula.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Formula.rename,Formula.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | input r a b =>
      simp only [Formula.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Formula.rename,Formula.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | neg a => simp only [Formula.rename,Formula.eval,a.eval_rename S p ht]
    | and a b =>
      simp only [Formula.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Formula.rename,Formula.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | or a b =>
      simp only [Formula.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Formula.rename,Formula.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | wsc s c w o => simp only [Formula.wscCount] at ht; omega
end

def Term.up {n : ℕ} (t : Term n) : Term (n+1) := t.rename Fin.succ

def Formula.up {n : ℕ} (a : Formula n) : Formula (n+1) := a.rename Fin.succ

def Formula.truth {n : ℕ} : Formula n := .equal .empty .empty

def Formula.falsity {n : ℕ} : Formula n := .neg .truth

def Term.singleton {n : ℕ} (a : Term n) : Term n := .pair a a

def Term.cup {n : ℕ} (a b : Term n) : Term n := .union (.pair a b)

def Term.orderedPair {n : ℕ} (a b : Term n) : Term n := .pair a.singleton (.pair a b)

def Formula.existsIn {n : ℕ} (r : Term n) (a : Formula (n+1)) : Formula n :=
  .neg (.equal (.comprehend .empty r a) .empty)

def Formula.allIn {n : ℕ} (r : Term n) (a : Formula (n+1)) : Formula n :=
  .neg (.existsIn r (.neg a))

def Formula.mem {n : ℕ} (a b : Term n) : Formula n :=
  .existsIn b (.equal (.var 0) a.up)

def Formula.imp {n : ℕ} (a b : Formula n) : Formula n := .or (.neg a) b

def Formula.iff {n : ℕ} (a b : Formula n) : Formula n := .and (a.imp b) (b.imp a)

def Term.inter {n : ℕ} (a b : Term n) : Term n :=
  .comprehend (.var 0) a (.mem (.var 0) b.up)

def Term.diff {n : ℕ} (a b : Term n) : Term n :=
  .comprehend (.var 0) a (.neg (.mem (.var 0) b.up))

def Term.when {n : ℕ} (a : Term n) (g : Formula n) : Term n :=
  .comprehend a.up (.singleton .empty) g.up

def Term.cond {n : ℕ} (g : Formula n) (a b : Term n) : Term n :=
  .unique ((a.when g).cup (b.when (.neg g)))

def Term.product {n : ℕ} (a b : Term n) : Term n := .union
  (.comprehend (.comprehend (.orderedPair (.var 1) (.var 0)) b.up .truth) a .truth)

@[simp] theorem Term.up_count {n : ℕ} (t : Term n) : t.up.wscCount = t.wscCount :=
  t.rename_count _

@[simp] theorem Formula.up_count {n : ℕ} (f : Formula n) : f.up.wscCount = f.wscCount :=
  f.rename_count _

@[simp] theorem Term.eval_up (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (t : Term n) (h : t.wscCount = 0) (env : Fin n → HF A) (x : HF A) :
    t.up.eval S p (Fin.cons x env) = t.eval S p env :=
  t.eval_rename S p h _ _

@[simp] theorem Formula.eval_up (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (f : Formula n) (h : f.wscCount = 0) (env : Fin n → HF A) (x : HF A) :
    f.up.eval S p (Fin.cons x env) = f.eval S p env :=
  f.eval_rename S p h _ _

omit [Fintype A] in
lemma collect_pure (r : HF A) (g : HF A → Bool) (b : HF A → HF A) :
    collect r (fun x => some (g x)) (fun x => some (b x)) =
      some (ofFinset (((elements r).filter (fun x => g x = true)).image b)) := by
  simp [collect]

omit [Fintype A] in
@[simp] lemma elements_emptyHF : elements (emptyHF : HF A) = ∅ := elements_ofFinset _

omit [Fintype A] in
@[simp] lemma uniqueHF_singleton (x : HF A) : uniqueHF (singleton x) = x := by
  unfold uniqueHF
  have h : ∃ y, elements (singleton x) = {y} := ⟨x,by simp [WitnessedSeparation.Hereditary.singleton]⟩
  rw [dite_eq_left h]
  exact Finset.singleton_injective (h.choose_spec.symm.trans (elements_ofFinset {x}))

omit [Fintype A] in
@[simp] lemma uniqueHF_empty : uniqueHF (emptyHF : HF A) = emptyHF := by
  unfold uniqueHF
  apply dite_eq_right
  simp

omit [Fintype A] in
@[simp] lemma unionHF_double (x y : HF A) :
    unionHF (double x y) = ofFinset (elements x ∪ elements y) := by
  simp [unionHF,double]

lemma Formula.eval_truth (S : Input A) (p : Polynomial ℝ) {n : ℕ} (env : Fin n → HF A) :
    (Formula.truth (n := n)).eval S p env = some true := by
  simp [truth,eval,Term.eval,lift₂]

lemma Formula.eval_existsIn (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (a : Formula (n+1)) (env : Fin n → HF A)
    {rv : HF A} {av : HF A → Bool} (hr : r.eval S p env = some rv)
    (ha : ∀ x, a.eval S p (Fin.cons x env) = some (av x)) :
    (Formula.existsIn r a).eval S p env =
      some (decide (∃ x ∈ elements rv, av x = true)) := by
  have hf : (fun x => a.eval S p (Fin.cons x env)) = fun x => some (av x) := funext ha
  simp only [existsIn,Formula.eval,Term.eval,hr,Option.bind_some,hf]
  rw [collect_pure]
  simp only [lift₂,Option.bind_some,Option.map_some,Option.some.injEq]
  have he : ofFinset (((elements rv).filter (fun x => av x = true)).image (fun _ => (emptyHF : HF A))) = emptyHF ↔
      ¬ ∃ x ∈ elements rv, av x = true := by
    rw [emptyHF,ofFinset_inj,Finset.image_eq_empty]
    simp
  simp only [he,decide_not,Bool.not_not]

lemma Formula.eval_allIn (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (a : Formula (n+1)) (env : Fin n → HF A)
    {rv : HF A} {av : HF A → Bool} (hr : r.eval S p env = some rv)
    (ha : ∀ x, a.eval S p (Fin.cons x env) = some (av x)) :
    (Formula.allIn r a).eval S p env =
      some (decide (∀ x ∈ elements rv, av x = true)) := by
  have hn (x : HF A) : (Formula.neg a).eval S p (Fin.cons x env) = some (!(av x)) := by
    simp [Formula.eval,ha]
  change ((Formula.existsIn r (.neg a)).eval S p env).map Bool.not = _
  rw [eval_existsIn S p r (.neg a) env hr hn]
  simp only [Option.map_some,Option.some.injEq]
  have he : (∃ x ∈ elements rv, av x = false) ↔ ¬ (∀ x ∈ elements rv, av x = true) := by
    simp only [not_forall, exists_prop, Bool.not_eq_true]
  simp only [Bool.not_eq_true_eq_eq_false, he, decide_not, Bool.not_not]

lemma Term.eval_singleton (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a : Term n) (env : Fin n → HF A) {x : HF A}
    (ha : a.eval S p env = some x) :
    a.singleton.eval S p env = some (Hereditary.singleton x) := by
  simp [Term.singleton,eval,ha,lift₂,Hereditary.singleton,double]

lemma Term.eval_cup (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a b : Term n) (env : Fin n → HF A) {x y : HF A}
    (ha : a.eval S p env = some x) (hb : b.eval S p env = some y) :
    (a.cup b).eval S p env = some (ofFinset (elements x ∪ elements y)) := by
  simp [Term.cup,eval,ha,hb,lift₂]

lemma Term.eval_orderedPair (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a b : Term n) (env : Fin n → HF A) {x y : HF A}
    (ha : a.eval S p env = some x) (hb : b.eval S p env = some y) :
    (a.orderedPair b).eval S p env = some (Hereditary.pair x y) := by
  simp [Term.orderedPair,Term.singleton,eval,ha,hb,lift₂,
    Hereditary.pair,Hereditary.singleton,double]

lemma Formula.eval_mem (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a b : Term n) (hz : a.wscCount = 0) (env : Fin n → HF A) {x y : HF A}
    (ha : a.eval S p env = some x) (hb : b.eval S p env = some y) :
    (Formula.mem a b).eval S p env = some (decide (x ∈ elements y)) := by
  have he : ∀ z, (Formula.equal (.var 0) a.up).eval S p (Fin.cons z env) =
      some (decide (z = x)) := by
    intro z
    simp [Formula.eval,Term.eval,Term.eval_up S p a hz env z,ha,lift₂]
  rw [Formula.mem,eval_existsIn S p b _ env hb he]
  congr 1
  simp

lemma Term.eval_when (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a : Term n) (g : Formula n) (hz : a.wscCount = 0) (hg : g.wscCount = 0)
    (env : Fin n → HF A) {x : HF A} {c : Bool}
    (ha : a.eval S p env = some x) (hc : g.eval S p env = some c) :
    (a.when g).eval S p env = some (if c then Hereditary.singleton x else emptyHF) := by
  simp only [Term.when,eval,Term.eval_singleton S p .empty env rfl,Option.bind_some]
  have hgu : (fun z => g.up.eval S p (Fin.cons z env)) = fun _ => some c := by
    funext z
    rw [Formula.eval_up S p g hg env z,hc]
  have hbo : (fun z => a.up.eval S p (Fin.cons z env)) = fun _ => some x := by
    funext z
    rw [Term.eval_up S p a hz env z,ha]
  rw [hgu,hbo,collect_pure]
  cases c <;> simp [Hereditary.singleton,emptyHF]

lemma Term.eval_cond (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (g : Formula n) (a b : Term n)
    (hg : g.wscCount = 0) (hz : a.wscCount = 0) (hw : b.wscCount = 0)
    (env : Fin n → HF A) {c : Bool} {x y : HF A}
    (hc : g.eval S p env = some c) (ha : a.eval S p env = some x)
    (hb : b.eval S p env = some y) :
    (Term.cond g a b).eval S p env = some (if c then x else y) := by
  have hn : (Formula.neg g).eval S p env = some (!c) := by simp [Formula.eval,hc]
  have hnz : (Formula.neg g).wscCount = 0 := hg
  have hw1 := Term.eval_when S p a g hz hg env ha hc
  have hw2 := Term.eval_when S p b (.neg g) hw hnz env hb hn
  simp only [Term.cond,Term.eval,Term.eval_cup S p _ _ env hw1 hw2,Option.map_some]
  cases c
  · simpa [emptyHF,Hereditary.singleton] using uniqueHF_singleton (A := A) y
  · simpa [emptyHF,Hereditary.singleton] using uniqueHF_singleton (A := A) x

def Term.letIn {n : ℕ} (v : Term n) (b : Term (n+1)) : Term n :=
  .unique (.comprehend b v.singleton .truth)

def Formula.letIn {n : ℕ} (v : Term n) (b : Formula (n+1)) : Formula n :=
  .existsIn v.singleton b

lemma Term.eval_letIn (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (v : Term n) (b : Term (n+1)) (env : Fin n → HF A) {x y : HF A}
    (hv : v.eval S p env = some x) (hb : b.eval S p (Fin.cons x env) = some y) :
    (v.letIn b).eval S p env = some y := by
  simp only [Term.letIn,eval,eval_singleton S p v env hv,Option.bind_some]
  have he : collect (Hereditary.singleton x) (fun z => Formula.truth.eval S p (Fin.cons z env))
      (fun z => b.eval S p (Fin.cons z env)) = some (Hereditary.singleton y) := by
    simp [collect,Formula.eval_truth,Hereditary.singleton,hb]
  rw [he,Option.map_some,uniqueHF_singleton]

lemma Formula.eval_letIn (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (v : Term n) (b : Formula (n+1)) (env : Fin n → HF A) {x : HF A} {c : Bool}
    (hv : v.eval S p env = some x) (hz : b.wscCount = 0)
    (hb : b.eval S p (Fin.cons x env) = some c) :
    (Formula.letIn v b).eval S p env = some c := by
  let f := fun z => (b.total S p hz (Fin.cons z env)).choose
  have hf (z) : b.eval S p (Fin.cons z env) = some (f z) :=
    (b.total S p hz (Fin.cons z env)).choose_spec
  have hx : f x = c := Option.some.inj ((hf x).symm.trans hb)
  rw [Formula.letIn,eval_existsIn S p _ _ env (Term.eval_singleton S p v env hv) hf]
  simp [Hereditary.singleton,hx]

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

@[simp] lemma cons_two {X : Type*} {n : ℕ} (a b c : X) (env : Fin n → X) :
    (Fin.cons a (Fin.cons b (Fin.cons c env)) : Fin (n+3) → X) 2 = c := by
  change (Fin.cons a (Fin.cons b (Fin.cons c env)) : Fin (n+3) → X) (1 : Fin (n+2)).succ = c
  rw [Fin.cons_succ,Fin.cons_one,Fin.cons_zero]

def Term.mapSet {n : ℕ} (r : Term n) (b : Term (n+1)) : Term n :=
  .comprehend b r .truth

def Term.bindSet {n : ℕ} (r : Term n) (b : Term (n+1)) : Term n :=
  .union (r.mapSet b)

def Term.addPairBody {n : ℕ} : Term (n+3) :=
  (Term.var 2).cup ((Term.orderedPair (.var 1) (.var 0)).singleton)

def Term.partialPool {n : ℕ} : ℕ → Term n
  | 0 => Term.empty.singleton
  | k+1 => (partialPool k).bindSet
      (Term.atoms.bindSet (Term.atoms.mapSet Term.addPairBody))

def Term.completeRelation {n : ℕ} : Term (n+1) :=
  (Term.var 0).cup (.comprehend (Term.orderedPair (.var 0) (.var 0)) .atoms
    (.neg (.existsIn .atoms (.mem (Term.orderedPair (.var 1) (.var 0)) (.var 2)))))

def Term.identityRelation {n : ℕ} : Term n :=
  .comprehend (Term.orderedPair (.var 0) (.var 0)) .atoms .truth

def Term.localPool {n : ℕ} (B : ℕ) : Term n :=
  Term.identityRelation.singleton.cup ((Term.partialPool B).mapSet Term.completeRelation)

@[simp] lemma Term.mapSet_count {n : ℕ} (r : Term n) (b : Term (n+1)) :
    (r.mapSet b).wscCount = b.wscCount + r.wscCount := by
  simp only [mapSet,Term.wscCount,Formula.truth,Formula.wscCount,Nat.add_zero]

@[simp] lemma Term.bindSet_count {n : ℕ} (r : Term n) (b : Term (n+1)) :
    (r.bindSet b).wscCount = b.wscCount + r.wscCount := r.mapSet_count b

@[simp] lemma Term.partialPool_count {n : ℕ} (B : ℕ) : (Term.partialPool (n := n) B).wscCount = 0 := by
  induction B with
  | zero => rfl
  | succ k ih =>
    simp only [partialPool,bindSet_count,mapSet_count,addPairBody,Term.cup,
      Term.singleton,Term.orderedPair,Term.wscCount,ih,Nat.add_zero]

@[simp] lemma Term.completeRelation_count {n : ℕ} : (Term.completeRelation (n := n)).wscCount = 0 := rfl

@[simp] lemma Term.identityRelation_count {n : ℕ} : (Term.identityRelation (n := n)).wscCount = 0 := rfl

@[simp] lemma Term.localPool_count {n : ℕ} (B : ℕ) : (Term.localPool (n := n) B).wscCount = 0 := by
  simp only [localPool,Term.cup,Term.singleton,Term.wscCount,mapSet_count,
    partialPool_count,completeRelation_count,identityRelation_count,Nat.add_zero]

variable {A : Type} [Fintype A]

lemma Term.eval_comprehend (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (b : Term (n+1)) (g : Formula (n+1)) (env : Fin n → HF A)
    {rv : HF A} {f : HF A → HF A} {c : HF A → Bool}
    (hr : r.eval S p env = some rv)
    (hb : ∀ x, b.eval S p (Fin.cons x env) = some (f x))
    (hg : ∀ x, g.eval S p (Fin.cons x env) = some (c x)) :
    (Term.comprehend b r g).eval S p env =
      some (ofFinset (((elements rv).filter (fun x => c x = true)).image f)) := by
  have hf := funext hb
  have hc := funext hg
  simp only [Term.eval,hr,Option.bind_some,hf,hc,collect_pure]

lemma Term.eval_mapSet (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (b : Term (n+1)) (env : Fin n → HF A)
    {rv : HF A} {f : HF A → HF A} (hr : r.eval S p env = some rv)
    (hb : ∀ x, b.eval S p (Fin.cons x env) = some (f x)) :
    (r.mapSet b).eval S p env = some (ofFinset ((elements rv).image f)) := by
  have hf : (fun x => b.eval S p (Fin.cons x env)) = fun x => some (f x) := funext hb
  simp only [mapSet,Term.eval,hr,Option.bind_some,hf,Formula.eval_truth]
  rw [collect_pure]
  simp

lemma Term.eval_bindSet (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (b : Term (n+1)) (env : Fin n → HF A)
    {rv : HF A} {f : HF A → HF A} (hr : r.eval S p env = some rv)
    (hb : ∀ x, b.eval S p (Fin.cons x env) = some (f x)) :
    (r.bindSet b).eval S p env =
      some (ofFinset ((elements rv).biUnion (fun x => elements (f x)))) := by
  simp only [bindSet,Term.eval,eval_mapSet S p r b env hr hb,Option.map_some,unionHF,
    elements_ofFinset]
  congr 2
  ext x
  simp

lemma Term.eval_addPairBody (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (env : Fin n → HF A) (r a b : HF A) :
    (Term.addPairBody (n := n)).eval S p (Fin.cons b (Fin.cons a (Fin.cons r env))) =
      some (ofFinset (insert (Hereditary.pair a b) (elements r))) := by
  have hp := Term.eval_orderedPair S p (Term.var (1 : Fin (n+3))) (Term.var 0)
    (Fin.cons b (Fin.cons a (Fin.cons r env))) rfl rfl
  have hs := Term.eval_singleton S p _ _ hp
  have hc := Term.eval_cup S p (Term.var (2 : Fin (n+3))) _ _ rfl hs
  simpa only [addPairBody,Hereditary.singleton,elements_ofFinset,Finset.union_singleton,Fin.cons_zero,Fin.cons_one,Fin.cons_succ,cons_two] using hc

end

end WitnessedChoice.BGS

end

end OAI
