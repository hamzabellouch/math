import OAI.Computability.Superstring.Windows

namespace OAI

namespace Superstring.Hierarchical

variable {α ι κ : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}

/-- The complete host construction for records normalized into one cyclic turn.
Different children share at most their Fine-Wilf overlap; any number of layers
of one child may request at its single record. Their distinct budgets are summed
with multiplicity. -/
theorem host_normalized (closed : SubstringClosed V) (D : Layer V A q)
    (hq : 0 < q) (per : Function.Periodic A (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (H : ι → HostedGroup D) (g : κ → ι) (R : ∀ i, (H (g i)).Request)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x + c))
    (I : Finset κ) (z : ι) (hz : ∃ i ∈ I, g i = z)
    (hmin : ∀ i ∈ I, (H z).period ≤ (H (g i)).period)
    (horder : ∀ i ∈ I,
      (H z).start ≤ (H (g i)).start ∧ (H (g i)).start ≤ (H z).start + q ∧
      (H z).stop ≤ (H (g i)).stop ∧ (H (g i)).stop ≤ (H z).stop + q) :
    ∃ Q : Path V [] [], Q.cost ≤ q + ∑ i ∈ I, (H (g i)).period ∧
      D.TouchedBy Q ∧ ∀ i ∈ I, (R i).layer.TouchedBy Q := by
  classical
  let initial := I.filter (fun i => g i = z)
  let later := I.filter (fun i => g i ≠ z)
  have hinit : initial.Nonempty := by
    obtain ⟨i, hi, he⟩ := hz
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩
  obtain ⟨i₀, hi₀, emin⟩ := initial.exists_min_image (fun i => (R i).stop) hinit
  have hi₀I : i₀ ∈ I := (Finset.mem_filter.mp hi₀).1
  have hi₀g : g i₀ = z := (Finset.mem_filter.mp hi₀).2
  let T := (H z).start + q
  let s := fun i => min ((H (g i)).start + (H (g i)).period) T
  let h := fun i => max (R i).stop (H z).stop
  have he₀ : (H z).start + (H z).period < (R i₀).stop := by
    simpa only [hi₀g] using (R i₀).long
  have he₀b : (R i₀).stop ≤ (H z).stop := by
    have hh := (R i₀).margin
    simp only [hi₀g] at hh
    omega
  have hbase : (H z).stop < T + (H z).period := by
    have hh := (H z).length_lt hq per
    dsimp only [T]
    omega
  have bounds (i : κ) (hi : i ∈ later) :
      (H (g i)).start ≤ s i ∧ s i ≤ (H (g i)).start + (H (g i)).period ∧
      s i ≤ h i ∧ h i ≤ (H (g i)).stop ∧ (R i).stop ≤ h i ∧
      h i ≤ (R i).stop + (H (g i)).period ∧
      (H z).start ≤ s i ∧ s i ≤ T ∧ (H z).stop ≤ h i ∧ h i < T + (H z).period := by
    obtain ⟨hiI, hig⟩ := Finset.mem_filter.mp hi
    have ho := horder i hiI
    have hd : (H z).text ≠ (H (g i)).text := by
      simpa only [add_zero] using different z (g i) (Ne.symm hig) 0
    have hl := (H z).overlap_lt (H (g i)) ho.1 ho.2.2.1 hd
    have hr := (H (g i)).next_overlap_lt (H z) per ho.2.1 ho.2.2.2
      (by simpa only [sub_eq_add_neg] using different (g i) z hig (-(q : ℤ)))
    exact host_target_bounds (H z).start (H z).stop (H (g i)).start (H (g i)).stop
      (R i).stop T (H z).period (H (g i)).period (hmin i hiI) ho.1 ho.2.1
      ho.2.2.1 (R i).long (R i).margin hl hr hbase
  have raw (i j : κ) (hij : g i ≠ g j)
      (ha : (H (g i)).start ≤ (H (g j)).start)
      (hb : (H (g i)).stop ≤ (H (g j)).stop) :
      (H (g i)).start + (H (g i)).period ≤ (H (g j)).start + (H (g j)).period ∧
      (R i).stop ≤ (R j).stop := by
    have hd : (H (g i)).text ≠ (H (g j)).text := by
      simpa only [add_zero] using different (g i) (g j) hij 0
    have hov := (H (g i)).overlap_lt (H (g j)) ha hb hd
    have hlong := (R i).long
    have hmargin := (R i).margin
    have hlong' := (R j).long
    constructor <;> omega
  have chain : ∀ i ∈ later, ∀ j ∈ later,
      (s i ≤ s j ∧ h i ≤ h j) ∨ (s j ≤ s i ∧ h j ≤ h i) := by
    intro i _ j _
    have hc :
        ((H (g i)).start + (H (g i)).period ≤ (H (g j)).start + (H (g j)).period ∧
          (R i).stop ≤ (R j).stop) ∨
        ((H (g j)).start + (H (g j)).period ≤ (H (g i)).start + (H (g i)).period ∧
          (R j).stop ≤ (R i).stop) := by
      by_cases he : g i = g j
      · rcases le_total (R i).stop (R j).stop with hr | hr
        · exact Or.inl ⟨by rw [he], hr⟩
        · exact Or.inr ⟨by rw [he], hr⟩
      · by_cases ha : (H (g i)).start < (H (g j)).start
        · exact Or.inl (raw i j he ha.le
            (D.window_order (H (g i)).le_last (H (g j)).first_le ha))
        · by_cases hb : (H (g j)).start < (H (g i)).start
          · exact Or.inr (raw j i (Ne.symm he) hb.le
              (D.window_order (H (g j)).le_last (H (g i)).first_le hb))
          · rcases le_total (H (g i)).stop (H (g j)).stop with hs | hs
            · exact Or.inl (raw i j he (by omega) hs)
            · exact Or.inr (raw j i (Ne.symm he) (by omega) hs)
    rcases hc with hc | hc
    · exact Or.inl ⟨min_le_min_right _ hc.1, max_le_max_right _ hc.2⟩
    · exact Or.inr ⟨min_le_min_right _ hc.1, max_le_max_right _ hc.2⟩
  have hQ (i : κ) (hi : i ∈ later) : textWord A (s i) (h i) ∈ V :=
    closed (H (g i)).host_mem (textWord_infix A (bounds i hi).1
      (bounds i hi).2.2.1 (bounds i hi).2.2.2.1)
  obtain ⟨P, hcP, hrP, hvP, htP, w, hwP, hwlen⟩ := host_excursion_finite closed A letters
    q (H z).period (H z).positive per (H z).start (H z).stop (R i₀).stop
    he₀ he₀b (H z).host_mem hbase later s h chain
    (fun i hi => ⟨(bounds i hi).2.2.2.2.2.2.1, (bounds i hi).2.2.2.2.2.2.2.1,
      (bounds i hi).2.2.1, (bounds i hi).2.2.2.2.2.2.2.2.1,
      (bounds i hi).2.2.2.2.2.2.2.2.2⟩) hQ
  let K := {i // i ∈ later}
  have attachments (i : K) : ∃ F : Loop V, F.base = textWord A (s i.val) (h i.val) ∧
      F.cost = (H (g i.val)).period ∧
      F.Visits (textWord (H (g i.val)).text (H (g i.val)).start (R i.val).stop) := by
    have hb := bounds i.val i.property
    have heq : textWord (H (g i.val)).text (s i.val) (h i.val) =
        textWord A (s i.val) (h i.val) := textWord_eq_of_agree (fun x hx hy =>
      (H (g i.val)).agree x (hb.1.trans hx) (hy.trans_le hb.2.2.2.1))
    obtain ⟨F, hcF, hvF⟩ := request_attachment closed (H (g i.val)).text
      (child_letters (g i.val)) (H (g i.val)).period (H (g i.val)).periodic
      (by have := (R i.val).long; omega) hb.2.2.1 hb.1 hb.2.1 hb.2.2.2.2.1
      hb.2.2.2.2.2.1 (R i.val).word_mem (heq.symm ▸ hQ i.val i.property)
    exact ⟨⟨_, F.copy heq heq⟩, rfl, by simpa only [Loop.cost, Path.cost_copy] using hcF,
      (Path.visits_copy ..).mpr hvF⟩
  choose F hbF hcF hvF using attachments
  let E : Loop V := ⟨_, P⟩
  obtain ⟨Q, hcQ, hvQ, haQ⟩ := Loop.root_attachments closed E F Finset.univ (H z).period
    (fun i _ => ⟨_, htP i.val i.property, by
      rw [← hbF i]; exact Path.visits_start (F i).path⟩) ⟨w, hwP, hwlen.le⟩
  have hsum : (∑ i : K, (F i).cost) = ∑ i ∈ later, (H (g i)).period := by
    simp_rw [hcF]
    exact Finset.sum_coe_sort later (fun i => (H (g i)).period)
  have hn₀ : i₀ ∉ later := by
    intro hh
    exact (Finset.mem_filter.mp hh).2 hi₀g
  have hs : (H z).period + ∑ i ∈ later, (H (g i)).period ≤ ∑ i ∈ I, (H (g i)).period := by
    have hsub : insert i₀ later ⊆ I := Finset.insert_subset hi₀I (Finset.filter_subset _ _)
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ =>
      Nat.zero_le ((H (g i)).period))
    simpa only [Finset.sum_insert hn₀, hi₀g] using hh
  refine ⟨Q, ?_, ⟨(H z).start, (H z).stop, (H z).first_le, (H z).le_last, hvQ _ hrP⟩, ?_⟩
  · change Q.cost ≤ P.cost + (∑ i : K, (F i).cost) + (H z).period at hcQ
    rw [hcP, hsum] at hcQ
    omega
  · intro i hi
    apply (R i).touched Q
    by_cases he : g i = z
    · have hlo := emin i (Finset.mem_filter.mpr ⟨hi, he⟩)
      have hmargin := (R i).margin
      have hlong := (R i).long
      have eqw : textWord (H (g i)).text (H (g i)).start (R i).stop =
          textWord A (H (g i)).start (R i).stop := textWord_eq_of_agree
        (fun x hx hy => (H (g i)).agree x hx (by omega))
      rw [eqw, show (H (g i)).start = (H z).start from congrArg (fun j => (H j).start) he]
      apply hvQ _ (hvP _ hlo _)
      simp only [he] at hmargin
      omega
    · exact haQ ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩ (Finset.mem_univ _) _
        (hvF ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩)

end Superstring.Hierarchical

namespace Superstring.Hierarchical
namespace Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- Simultaneous coordinate transport of a child text and its layer. -/
def translate (D : Layer V A p) (δ : ℤ) : Layer V (fun x => A (x - δ)) p where
  z x := D.z (x - δ) + δ
  mono := by
    intro x y h
    have hh := D.mono (sub_le_sub_right h δ)
    dsimp only
    omega
  lower x := by
    have hh := D.lower (x - δ)
    have he : x - 1 - δ = (x - δ) - 1 := by omega
    rw [he]
    omega
  shift x := by
    have he : x + p - δ = (x - δ) + p := by omega
    rw [he, D.shift]
    omega
  actual x e hfirst hlast := by
    have he : textWord (fun x => A (x - δ)) x e = textWord A (x - δ) (e - δ) := by
      simpa only [sub_eq_add_neg] using textWord_reindex A (-δ) x e
    rw [he]
    apply D.actual (x - δ) (e - δ)
    · have hx : x - δ - 1 = x - 1 - δ := by omega
      rw [hx]
      omega
    · omega

@[simp] theorem translate_first (D : Layer V A p) (δ x : ℤ) :
    (D.translate δ).first x = D.first (x - δ) + δ := by
  change D.z (x - 1 - δ) + δ = D.z (x - δ - 1) + δ
  congr 2
  omega

@[simp] theorem translate_last (D : Layer V A p) (δ x : ℤ) :
    (D.translate δ).last x = D.last (x - δ) + δ := rfl

theorem translate_touched (D : Layer V A p) (δ : ℤ) {s t : List α}
    (P : Path V s t) : (D.translate δ).TouchedBy P ↔ D.TouchedBy P := by
  constructor
  · rintro ⟨x, e, hf, hl, hv⟩
    rw [translate_first] at hf
    rw [translate_last] at hl
    refine ⟨x - δ, e - δ, by omega, by omega, ?_⟩
    have he : textWord (fun x => A (x - δ)) x e = textWord A (x - δ) (e - δ) := by
      simpa only [sub_eq_add_neg] using textWord_reindex A (-δ) x e
    rwa [he] at hv
  · rintro ⟨x, e, hf, hl, hv⟩
    refine ⟨x + δ, e + δ, ?_, ?_, ?_⟩
    · rw [translate_first, add_sub_cancel_right]
      omega
    · rw [translate_last, add_sub_cancel_right]
      omega
    · have he : textWord (fun x => A (x - δ)) (x + δ) (e + δ) = textWord A x e := by
        simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
          textWord_reindex A (-δ) (x + δ) (e + δ)
      rwa [he]

/-- A cyclic record can be placed between a fixed actual record and its next
copy in BOTH coordinates. Equal-start vertical runs are treated explicitly. -/
theorem normalize_window (D : Layer V A p) (hp : 0 < p)
    {a b a₀ b₀ : ℤ} (hf : D.first a ≤ b) (hl : b ≤ D.last a)
    (hf₀ : D.first a₀ ≤ b₀) (hl₀ : b₀ ≤ D.last a₀) :
    ∃ m : ℤ, a₀ ≤ a + m * p ∧ a + m * p ≤ a₀ + p ∧
      b₀ ≤ b + m * p ∧ b + m * p ≤ b₀ + p := by
  let m : ℤ := -((a - a₀) / p)
  let r : ℤ := a + m * p
  let e : ℤ := b + m * p
  have hr : r = a₀ + (a - a₀) % p := by
    have hh := Int.emod_add_ediv_mul (a - a₀) (p : ℤ)
    dsimp only [r, m]
    simp only [neg_mul]
    omega
  have hrlo : a₀ ≤ r := by
    have hh := Int.emod_nonneg (a - a₀) (show (p : ℤ) ≠ 0 by omega)
    omega
  have hrhi : r < a₀ + p := by
    have hh := Int.emod_lt_of_pos (a - a₀) (show (0 : ℤ) < p by omega)
    omega
  have hfe : D.first r ≤ e := by
    dsimp only [r, e]
    rw [D.first_shift_int]
    omega
  have hle : e ≤ D.last r := by
    dsimp only [r, e, last]
    rw [D.shift_int]
    change b ≤ D.z a at hl
    omega
  have hfnext : D.first (a₀ + p) ≤ b₀ + p := by
    rw [D.first_shift]
    omega
  have hehi : e ≤ b₀ + p := D.window_order hle hfnext hrhi
  by_cases helo : b₀ ≤ e
  · exact ⟨m, hrlo, hrhi.le, helo, hehi⟩
  · have hre : r = a₀ := by
      by_contra hn
      have hh := D.window_order hl₀ hfe (by omega : a₀ < r)
      omega
    have hfn : D.first (r + p) ≤ e + p := by
      rw [D.first_shift]
      omega
    have helon : b₀ ≤ e + p := D.window_order hl₀ hfn (by omega)
    refine ⟨m + 1, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [r, e] at * <;> nlinarith

end Layer
end Superstring.Hierarchical

namespace Superstring.Hierarchical
namespace HostedGroup

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ} {D : Layer V A q}

/-- Translate a hosted record by a whole number of host periods, transporting
its entire child text, not only its interval endpoints. -/
def translate (H : HostedGroup D) (per : Function.Periodic A (q : ℤ)) (m : ℤ) :
    HostedGroup D where
  text x := H.text (x - m * q)
  period := H.period
  positive := H.positive
  periodic x := by simpa only [add_sub_right_comm] using H.periodic (x - m * q)
  start := H.start + m * q
  stop := H.stop + m * q
  first_le := by
    rw [D.first_shift_int]
    have := H.first_le
    omega
  le_last := by
    change H.stop + m * q ≤ D.z (H.start + m * q)
    rw [D.shift_int]
    have := H.le_last
    change H.stop ≤ D.z H.start at this
    omega
  agree := by
    intro x hx hy
    have hp : A (x - m * q) = A x := by
      simpa using per.sub_int_mul_eq (x := x) m
    exact (H.agree (x - m * q) (by omega) (by omega)).trans hp
  foreign := by
    intro he
    apply H.foreign
    funext x
    have hh := congrFun he (x + m * q)
    change H.text (x + m * q - m * q) = A (x + m * q) at hh
    have hp : A (x + m * q) = A x := by simpa using (per.int_mul m) x
    simpa only [add_sub_cancel_right, hp] using hh

namespace Request

/-- All requester windows and layer coordinates travel with their one record. -/
def translate {H : HostedGroup D} (R : H.Request)
    (per : Function.Periodic A (q : ℤ)) (m : ℤ) : (H.translate per m).Request where
  layer := R.layer.translate (m * q)
  stop := R.stop + m * q
  first_le := by
    change (R.layer.translate (m * q)).first (H.start + m * q) ≤ R.stop + m * q
    rw [Layer.translate_first, add_sub_cancel_right]
    have := R.first_le
    omega
  le_last := by
    change R.stop + m * q ≤ (R.layer.translate (m * q)).last (H.start + m * q)
    rw [Layer.translate_last, add_sub_cancel_right]
    have := R.le_last
    omega
  long := by
    have := R.long
    change H.start + m * q + H.period < R.stop + m * q
    omega
  margin := by
    have := R.margin
    change R.stop + m * q ≤ H.stop + m * q - H.period
    omega

end Request
end HostedGroup


theorem host_requests {α ι κ : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}
    (closed : SubstringClosed V) (D : Layer V A q)
    (hq : 0 < q) (per : Function.Periodic A (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (H : ι → HostedGroup D) (g : κ → ι) (R : ∀ i, (H (g i)).Request)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x + c))
    (I : Finset κ) (hne : I.Nonempty) :
    ∃ Q : Path V [] [], Q.cost ≤ q + ∑ i ∈ I, (H (g i)).period ∧
      D.TouchedBy Q ∧ ∀ i ∈ I, (R i).layer.TouchedBy Q := by
  classical
  obtain ⟨i₀, hi₀, hmin⟩ := I.exists_min_image (fun i => (H (g i)).period) hne
  let z := g i₀
  have shifts : ∀ j, ∃ m : ℤ, (j = z → m = 0) ∧
      (H z).start ≤ (H j).start + m * q ∧ (H j).start + m * q ≤ (H z).start + q ∧
      (H z).stop ≤ (H j).stop + m * q ∧ (H j).stop + m * q ≤ (H z).stop + q := by
    intro j
    by_cases he : j = z
    · subst j
      exact ⟨0, fun _ => rfl, by omega, by omega, by omega, by omega⟩
    · obtain ⟨m, hm⟩ := D.normalize_window hq (H j).first_le (H j).le_last
        (H z).first_le (H z).le_last
      exact ⟨m, fun hj => (he hj).elim, hm⟩
  choose m hm hbound using shifts
  have hmz : m z = 0 := hm z rfl
  let H' := fun j => (H j).translate per (m j)
  let R' := fun i => (R i).translate per (m (g i))
  have hd : ∀ i j, i ≠ j → ∀ c, (H' i).text ≠ fun x => (H' j).text (x + c) := by
    intro i j hij c he
    apply different i j hij (m i * q + c - m j * q)
    funext x
    have hh := congrFun he (x + m i * q)
    change (H i).text (x + m i * q - m i * q) =
      (H j).text (x + m i * q + c - m j * q) at hh
    have hx : x + m i * q + c - m j * q = x + (m i * q + c - m j * q) := by omega
    simpa only [add_sub_cancel_right, hx] using hh
  have ho : ∀ i ∈ I,
      (H' z).start ≤ (H' (g i)).start ∧ (H' (g i)).start ≤ (H' z).start + q ∧
      (H' z).stop ≤ (H' (g i)).stop ∧ (H' (g i)).stop ≤ (H' z).stop + q := by
    intro i _
    simpa only [H', HostedGroup.translate, hmz, zero_mul, add_zero] using hbound (g i)
  obtain ⟨Q, hcQ, hvQ, hrQ⟩ := host_normalized closed D hq per letters H' g R'
    (fun j x => child_letters j (x - m j * q)) hd I z ⟨i₀, hi₀, rfl⟩ hmin ho
  refine ⟨Q, hcQ, hvQ, fun i hi => ?_⟩
  exact ((R i).layer.translate_touched (m (g i) * q) Q).mp (hrQ i hi)

end Superstring.Hierarchical

namespace Superstring.Hierarchical
namespace Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- The actual vertices of a fixed base layer, independent of its coordinate
presentation. This is not the larger set of all recorded prefixes. -/
def Content (L : Layer V A p) : Set (List α) :=
  {w | ∃ x e, L.first x ≤ e ∧ e ≤ L.last x ∧ w = textWord A x e}

theorem content_mem (L : Layer V A p) {w : List α} (hw : w ∈ L.Content) : w ∈ V := by
  obtain ⟨x, e, hf, hl, rfl⟩ := hw
  exact L.actual x e hf hl

theorem touched_iff (L : Layer V A p) {s t : List α} (P : Path V s t) :
    L.TouchedBy P ↔ ∃ w ∈ L.Content, P.Visits w := by
  constructor
  · rintro ⟨x, e, hf, hl, hv⟩
    exact ⟨_, ⟨x, e, hf, hl, rfl⟩, hv⟩
  · rintro ⟨_, ⟨x, e, hf, hl, rfl⟩, hv⟩
    exact ⟨x, e, hf, hl, hv⟩

theorem translate_content (L : Layer V A p) (δ : ℤ) :
    (L.translate δ).Content = L.Content := by
  ext w
  constructor
  · rintro ⟨x, e, hf, hl, rfl⟩
    refine ⟨x - δ, e - δ, ?_, ?_, ?_⟩
    · rw [translate_first] at hf
      omega
    · rw [translate_last] at hl
      omega
    · simpa only [sub_eq_add_neg] using textWord_reindex A (-δ) x e
  · rintro ⟨x, e, hf, hl, rfl⟩
    refine ⟨x + δ, e + δ, ?_, ?_, ?_⟩
    · rw [translate_first, add_sub_cancel_right]
      omega
    · rw [translate_last, add_sub_cancel_right]
      omega
    · symm
      simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
        textWord_reindex A (-δ) (x + δ) (e + δ)

/-- Every actual vertex is retained when one full base turn is materialized. -/
theorem content_loop (L : Layer V A p) (closed : SubstringClosed V)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) :
    ∃ P : Loop V, P.cost = p ∧ ∀ w ∈ L.Content, P.Visits w := by
  obtain ⟨P, hc, hv⟩ := L.full_turn closed hp per 0
  refine ⟨⟨_, P⟩, hc, ?_⟩
  rintro w ⟨x, e, hf, hl, rfl⟩
  exact hv x e hf hl


theorem below_baseline (L B : Layer V A p) (closed : SubstringClosed V)
    (letters : ∀ x, [A x] ∈ V) (per : Function.Periodic A (p : ℤ))
    (hbelow : ∀ x, L.z x ≤ B.z x) {a b : ℤ}
    (hbf : B.first a ≤ b) (hbl : b ≤ B.last a) (hlen : b - a < 2 * p) :
    (∃ Q : Path V [] [], Q.cost ≤ p ∧ L.TouchedBy Q) ∨
    (∃ Q : Path V (textWord A a b) (textWord A a b),
      Q.cost ≤ p ∧ L.TouchedBy Q) := by
  by_cases hs : L.HasShort p
  · obtain ⟨x, e, hf, hl, hshort⟩ := hs
    obtain ⟨Q, hc, hv⟩ := Path.root_loop closed _ (L.actual x e hf hl)
    exact Or.inl ⟨Q, hc.trans_le hshort, x, e, hf, hl, hv⟩
  · have hlf : L.first a ≤ b := (hbelow (a - 1)).trans hbf
    have hlong := L.first_long_of_not_short p hs a
    have hfl := L.first_le_last a
    obtain ⟨Q, hc, hv, _⟩ := individual_link closed A letters p p per L
      ((B.start_le_first a).trans hbf) (B.actual a b hbf hbl) hlf
      (by omega) (by omega)
    exact Or.inr ⟨Q, hc.le, hv⟩

end Layer


theorem fill_layers {α ι : Type} {V : Set (List α)}
    (closed : SubstringClosed V) {A : ι → ℤ → α} {p : ι → ℕ}
    (L : ∀ i, Layer V (A i) (p i)) (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (I : Finset ι) (P : Loop V) (htouch : ∀ i ∈ I, (L i).TouchedBy P.path) :
    ∃ Q : Loop V, Q.base = P.base ∧ Q.cost ≤ P.cost + ∑ i ∈ I, p i ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, Q.Visits w := by
  classical
  choose F hc hv using fun i => (L i).content_loop closed (hp i) (per i)
  have hmeet : ∀ i ∈ I, P.Meets (F i) := by
    intro i hi
    obtain ⟨w, hw, hP⟩ := ((L i).touched_iff P.path).mp (htouch i hi)
    exact ⟨w, hP, hv i w hw⟩
  obtain ⟨Q, hb, hcost, hP, hF⟩ := Loop.attach F I P hmeet
  refine ⟨Q, hb, ?_, hP, fun i hi w hw => hF i hi w (hv i w hw)⟩
  simpa only [hc] using hcost

/-- The easy round trip through the top first window visits every lower first
height on its up path. Its cost is the top window's length, not a sum of lengths. -/
theorem root_upper {α ι : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (closed : SubstringClosed V) (L : ι → Layer V A p) (top : ι)
    (hupper : ∀ i x, (L i).z x ≤ (L top).z x) (t : ℤ) :
    ∃ Q : Path V [] [], Q.cost = (textWord A t ((L top).first t)).length ∧
      ∀ i, (L i).TouchedBy Q := by
  let H := (L top).first t
  have htH : t ≤ H := (L top).start_le_first t
  have hs : textWord A t H ∈ V := (L top).first_actual t
  obtain ⟨U, hcU, hvU⟩ := window_append closed A (le_refl t) htH hs
  let W := textWord A t H
  let D := Path.deletePrefix closed W [] (by simpa using hs)
  let Q : Path V [] [] :=
    (U.copy (textWord_self A t) rfl).trans (D.copy (by simp [W]) rfl)
  refine ⟨Q, ?_, ?_⟩
  · simp only [Q, Path.cost_trans, Path.cost_copy, hcU, D, Path.cost_deletePrefix,
      Nat.add_zero, length_textWord]
    rfl
  · intro i
    refine ⟨t, (L i).first t, le_rfl, (L i).first_le_last t, ?_⟩
    exact Or.inl ((Path.visits_copy ..).mpr
      (hvU _ ((L i).start_le_first t) (hupper i (t - 1))))

end Superstring.Hierarchical

end OAI
