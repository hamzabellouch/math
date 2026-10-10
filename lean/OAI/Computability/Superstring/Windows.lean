import OAI.Computability.Superstring.Records

namespace OAI

namespace Superstring.Hierarchical

variable {α : Type}

/-- A finite chain of windows has a simultaneous greatest start and end.
The sum is used only to choose a point of the already totally ordered chain. -/
theorem greatest_window {ι : Type} (I : Finset ι) (s h : ι → ℤ)
    (hne : I.Nonempty)
    (hchain : ∀ i ∈ I, ∀ j ∈ I,
      (s i ≤ s j ∧ h i ≤ h j) ∨ (s j ≤ s i ∧ h j ≤ h i)) :
    ∃ j ∈ I, ∀ i ∈ I, s i ≤ s j ∧ h i ≤ h j := by
  obtain ⟨j, hj, hmax⟩ := I.exists_max_image (fun i => s i + h i) hne
  refine ⟨j, hj, fun i hi => ?_⟩
  rcases hchain i hi j hj with hh | hh
  · exact hh
  · have := hmax i hi
    constructor <;> omega

/-- Finite ordered-window routing. Repeated windows and distinct requesters
at the same coordinates are allowed; this is not a disjointness assumption. -/
theorem finite_ordered_windows {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    {ι : Type} (I : Finset ι) (s h : ι → ℤ)
    (hchain : ∀ i ∈ I, ∀ j ∈ I,
      (s i ≤ s j ∧ h i ≤ h j) ∨ (s j ≤ s i ∧ h j ≤ h i))
    (hvalid : ∀ i ∈ I, s i ≤ h i ∧ textWord A (s i) (h i) ∈ V)
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (hstart : textWord A a b ∈ V) (hend : textWord A c d ∈ V)
    (hbounds : ∀ i ∈ I, a ≤ s i ∧ s i ≤ c ∧ b ≤ h i ∧ h i ≤ d) :
    ∃ P : Path V (textWord A a b) (textWord A c d),
      P.cost = (d - b).toNat ∧ ∀ i ∈ I, P.Visits (textWord A (s i) (h i)) := by
  classical
  induction I using Finset.strongInductionOn generalizing a b c d with
  | _ I ih =>
    by_cases hn : I.Nonempty
    · obtain ⟨j, hj, hmax⟩ := greatest_window I s h hn hchain
      have hsub : I.erase j ⊂ I := Finset.erase_ssubset hj
      have hmem {i} (hi : i ∈ I.erase j) : i ∈ I := Finset.mem_of_mem_erase hi
      obtain ⟨P, hcP, hvP⟩ := ih _ hsub
        (fun i hi k hk => hchain i (hmem hi) k (hmem hk))
        (fun i hi => hvalid i (hmem hi)) a b (s j) (h j) hab (hvalid j hj).1
        (hbounds j hj).1 (hbounds j hj).2.2.1 hstart (hvalid j hj).2
        (fun i hi => ⟨(hbounds i (hmem hi)).1, (hmax i (hmem hi)).1,
          (hbounds i (hmem hi)).2.2.1, (hmax i (hmem hi)).2⟩)
      obtain ⟨Q, hcQ, _⟩ := ordered_windows closed A letters (hvalid j hj).1 hcd
        (hbounds j hj).2.1 (hbounds j hj).2.2.2 (hvalid j hj).2 hend
      refine ⟨P.trans Q, ?_, ?_⟩
      · simp only [Path.cost_trans, hcP, hcQ]
        have := (hbounds j hj).2.2.1
        have := (hbounds j hj).2.2.2
        omega
      · intro i hi
        by_cases he : i = j
        · subst i
          exact Or.inl (Path.visits_end P)
        · exact Or.inl (hvP i (Finset.mem_erase.mpr ⟨he, hi⟩))
    · obtain ⟨P, hcP, _⟩ := ordered_windows closed A letters hab hcd hac hbd hstart hend
      exact ⟨P, hcP, fun i hi => (hn ⟨i, hi⟩).elim⟩

/-- Host excursion for any finite chain of later targets, including the empty
case. No enumeration/sorting oracle is assumed by the conclusion. -/
theorem host_excursion_finite {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (q p₀ : ℕ)
    (hp₀ : 0 < p₀) (per : Function.Periodic A (q : ℤ))
    (a₀ b₀ e₀ : ℤ) (he₀ : a₀ + p₀ < e₀) (heb : e₀ ≤ b₀)
    (hR : textWord A a₀ b₀ ∈ V) (hshort : b₀ < a₀ + q + p₀)
    {ι : Type} (I : Finset ι) (s h : ι → ℤ)
    (hchain : ∀ i ∈ I, ∀ j ∈ I,
      (s i ≤ s j ∧ h i ≤ h j) ∨ (s j ≤ s i ∧ h j ≤ h i))
    (hbounds : ∀ i ∈ I, a₀ ≤ s i ∧ s i ≤ a₀ + q ∧ s i ≤ h i ∧
      b₀ ≤ h i ∧ h i < a₀ + q + p₀)
    (hQ : ∀ i ∈ I, textWord A (s i) (h i) ∈ V) :
    ∃ P : Path V (textWord A a₀ e₀) (textWord A a₀ e₀),
      P.cost = q ∧ P.Visits (textWord A a₀ b₀) ∧
      (∀ e, e₀ ≤ e → e ≤ b₀ → P.Visits (textWord A a₀ e)) ∧
      (∀ i ∈ I, P.Visits (textWord A (s i) (h i))) ∧
      ∃ w, P.Visits w ∧ w.length < p₀ := by
  by_cases hn : I.Nonempty
  · obtain ⟨j, hj, hmax⟩ := greatest_window I s h hn hchain
    have hae : a₀ ≤ e₀ := by omega
    have hab : a₀ ≤ b₀ := by omega
    have hE : textWord A a₀ e₀ ∈ V := closed hR (textWord_infix A le_rfl hae heb)
    obtain ⟨U, hcU, hvU⟩ := window_append closed A hae heb hR
    obtain ⟨P, hcP, hvP⟩ := finite_ordered_windows closed A letters I s h hchain
      (fun i hi => ⟨(hbounds i hi).2.2.1, hQ i hi⟩) a₀ b₀ (s j) (h j)
      hab (hbounds j hj).2.2.1 (hbounds j hj).1 (hbounds j hj).2.2.2.1 hR (hQ j hj)
      (fun i hi => ⟨(hbounds i hi).1, (hmax i hi).1,
        (hbounds i hi).2.2.2.1, (hmax i hi).2⟩)
    have heqE := textWord_translate A q per a₀ e₀
    obtain ⟨D, hcD, w, hvD, hw⟩ := ordered_windows closed A letters
      (hbounds j hj).2.2.1 (show a₀ + q ≤ e₀ + q by omega)
      (hbounds j hj).2.1 (show h j ≤ e₀ + q by
        have := (hbounds j hj).2.2.2.2; omega) (hQ j hj) (heqE.symm ▸ hE)
    refine ⟨((U.trans P).trans D).copy rfl heqE, ?_, ?_, ?_, ?_, w, ?_, ?_⟩
    · simp only [Path.cost_copy, Path.cost_trans, hcU, hcP, hcD]
      have := (hbounds j hj).2.2.2.1
      have := (hbounds j hj).2.2.2.2
      omega
    · exact (Path.visits_copy ..).mpr (Or.inl (Or.inl (Path.visits_end U)))
    · intro e he he'
      exact (Path.visits_copy ..).mpr (Or.inl (Or.inl (hvU e he he')))
    · intro i hi
      exact (Path.visits_copy ..).mpr (Or.inl (Or.inr (hvP i hi)))
    · exact (Path.visits_copy ..).mpr (Or.inr hvD)
    · have := (hbounds j hj).2.2.2.2
      omega
  · obtain ⟨P, hc, hr, hv, hs⟩ := host_excursion_single closed A letters q p₀ hp₀ per
      a₀ b₀ e₀ he₀ heb hshort hR
    exact ⟨P, hc, hr, hv, fun i hi => (hn ⟨i, hi⟩).elim, hs⟩

end Superstring.Hierarchical

namespace Superstring.Hierarchical

variable {α β ρ : Type}


structure BlockPlan (V : Set (List α)) (β ρ : Type) [LE ρ] where
  content : β → Set (List α)
  reserve : β → ℕ
  free : β → ℕ
  rank : β → ρ
  target : β → Option β
  record : β → List α
  target_mem : ∀ i j, target i = some j → record i ∈ content j
  link : ∀ i, ∃ P : Loop V, P.cost ≤ reserve i ∧
    (∀ w ∈ content i, P.Visits w) ∧ P.Visits (record i)
  internal : ∀ i, ∃ P : Loop V, P.cost + free i ≤ reserve i ∧
    ∀ w ∈ content i, P.Visits w
  short : ∀ i j, target i = some j → i ≠ j → rank j ≤ rank i →
    ∃ P : Loop V, P.cost ≤ reserve i ∧
      (∀ w ∈ content i, P.Visits w) ∧ P.Visits (record i) ∧
      ∃ w, P.Visits w ∧ w.length ≤ free j
  self_short : ∀ i, target i = some i → ∃ w ∈ content i, w.length ≤ free i

namespace BlockPlan

variable {V : Set (List α)} [LinearOrder ρ] (B : BlockPlan V β ρ)


theorem connect (closed : SubstringClosed V) (I : Finset β) (P : Path V [] [])
    (hready : ∀ i ∈ I, match B.target i with
      | none => P.Visits (B.record i)
      | some j => j ∈ I ∨ P.Visits (B.record i)) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + ∑ i ∈ I, B.reserve i ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ B.content i, Q.Visits w := by
  classical
  induction I using Finset.strongInductionOn generalizing P with
  | _ I ih =>
    have finish (J : Finset β) (hJI : J ⊆ I) (hJn : J.Nonempty)
        (Q : Path V [] []) (hQc : Q.cost ≤ P.cost + ∑ i ∈ J, B.reserve i)
        (hPQ : ∀ w, P.Visits w → Q.Visits w)
        (hQv : ∀ i ∈ J, ∀ w ∈ B.content i, Q.Visits w) :
        ∃ R : Path V [] [], R.cost ≤ P.cost + ∑ i ∈ I, B.reserve i ∧
          (∀ w, P.Visits w → R.Visits w) ∧
          ∀ i ∈ I, ∀ w ∈ B.content i, R.Visits w := by
      have hreadyQ : ∀ i ∈ I \ J, match B.target i with
          | none => Q.Visits (B.record i)
          | some j => j ∈ I \ J ∨ Q.Visits (B.record i) := by
        intro i hi
        have hr := hready i (Finset.mem_sdiff.mp hi).1
        cases ht : B.target i with
        | none => simpa only [ht] using hPQ _ (by simpa only [ht] using hr)
        | some j =>
          simp only [ht] at hr ⊢
          rcases hr with hj | hv
          · by_cases hjJ : j ∈ J
            · exact Or.inr (hQv j hjJ _ (B.target_mem i j ht))
            · exact Or.inl (Finset.mem_sdiff.mpr ⟨hj, hjJ⟩)
          · exact Or.inr (hPQ _ hv)
      obtain ⟨R, hRc, hQR, hRv⟩ := ih (I \ J) (Finset.sdiff_ssubset hJI hJn) Q hreadyQ
      refine ⟨R, ?_, fun w hw => hQR w (hPQ w hw), ?_⟩
      · have hs := Finset.sum_sdiff hJI (f := B.reserve)
        omega
      · intro i hi w hw
        by_cases hj : i ∈ J
        · exact hQR w (hQv i hj w hw)
        · exact hRv i (Finset.mem_sdiff.mpr ⟨hi, hj⟩) w hw
    by_cases hn : I.Nonempty
    · obtain ⟨i, hi, hmax⟩ := I.exists_max_image B.rank hn
      have ordinary (hv : P.Visits (B.record i)) :
          ∃ Q : Path V [] [], Q.cost ≤ P.cost + ∑ i ∈ I, B.reserve i ∧
            (∀ w, P.Visits w → Q.Visits w) ∧
            ∀ j ∈ I, ∀ w ∈ B.content j, Q.Visits w := by
        obtain ⟨L, hcL, hvL, hrL⟩ := B.link i
        obtain ⟨Q, hcQ, hvQ⟩ := P.splice L.path (B.record i) hv hrL
        apply finish {i} (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_nonempty i) Q
        · simp only [Finset.sum_singleton]
          change Q.cost = P.cost + L.cost at hcQ
          omega
        · intro w hw
          exact (hvQ w).mpr (Or.inl hw)
        · intro j hj w hw
          have : j = i := Finset.mem_singleton.mp hj
          subst j
          exact (hvQ w).mpr (Or.inr (hvL w hw))
      cases ht : B.target i with
      | none =>
        exact ordinary (by simpa only [ht] using hready i hi)
      | some j =>
        have hr : j ∈ I ∨ P.Visits (B.record i) := by simpa only [ht] using hready i hi
        rcases hr with hj | hv
        · by_cases he : i = j
          · subst j
            obtain ⟨L, hcL, hvL⟩ := B.internal i
            obtain ⟨w, hw, hlen⟩ := B.self_short i ht
            obtain ⟨R, hcR, hvR⟩ := L.root_at closed w (hvL w hw)
            apply finish {i} (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_nonempty i)
              (P.trans R)
            · simp only [Finset.sum_singleton, Path.cost_trans]
              omega
            · intro v hv
              exact Or.inl hv
            · intro k hk v hv
              have : k = i := Finset.mem_singleton.mp hk
              subst k
              exact Or.inr (hvR v (hvL v hv))
          · obtain ⟨L, hcL, hvL, hrL, w, hw, hlen⟩ := B.short i j ht he (hmax j hj)
            obtain ⟨D, hcD, hvD⟩ := B.internal j
            obtain ⟨A, hcA, hvA⟩ := L.path.splice D.path (B.record i) hrL
              (hvD _ (B.target_mem i j ht))
            let E : Loop V := ⟨L.base, A⟩
            have hew : E.Visits w := (hvA w).mpr (Or.inl hw)
            obtain ⟨R, hcR, hvR⟩ := E.root_at closed w hew
            have hcE : E.cost = L.cost + D.cost := hcA
            apply finish {i, j} (by simp only [Finset.insert_subset_iff,
              Finset.singleton_subset_iff]; exact ⟨hi, hj⟩) (Finset.insert_nonempty _ _)
              (P.trans R)
            · simp only [Finset.sum_pair he, Path.cost_trans]
              omega
            · intro v hv
              exact Or.inl hv
            · intro k hk v hv
              simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              rcases hk with rfl | rfl
              · exact Or.inr (hvR v ((hvA v).mpr (Or.inl (hvL v hv))))
              · exact Or.inr (hvR v ((hvA v).mpr (Or.inr (hvD v hv))))
        · exact ordinary hv
    · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst I
      exact ⟨P, by simp, fun _ h => h, by simp⟩

end BlockPlan
end Superstring.Hierarchical

namespace Superstring.Hierarchical

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}

namespace Layer

/-- Actual vertices on one monotone host path inherit the order of starts;
within a vertical run they are ordered by their ends. -/
theorem window_order (D : Layer V A q) {a b c d : ℤ}
    (hb : b ≤ D.last a) (hd : D.first c ≤ d) (hac : a < c) : b ≤ d := by
  exact hb.trans ((D.mono (by omega : a ≤ c - 1)).trans hd)

end Layer

/-- One child group's single recorded host window, in host coordinates.
This includes the actual recipient and full-window agreement, not just a common
substring or an assumed possibility of connecting it. -/
structure HostedGroup (D : Layer V A q) where
  text : ℤ → α
  period : ℕ
  positive : 0 < period
  periodic : Function.Periodic text (period : ℤ)
  start : ℤ
  stop : ℤ
  first_le : D.first start ≤ stop
  le_last : stop ≤ D.last start
  agree : AgreeOn text A start stop
  foreign : text ≠ A

namespace HostedGroup

variable {D : Layer V A q} (H : HostedGroup D)

theorem start_le_stop : H.start ≤ H.stop :=
  (D.start_le_first H.start).trans H.first_le

theorem host_mem : textWord A H.start H.stop ∈ V :=
  D.actual H.start H.stop H.first_le H.le_last

theorem child_mem : textWord H.text H.start H.stop ∈ V :=
  (textWord_eq_of_agree H.agree).symm ▸ H.host_mem

theorem length_lt (hq : 0 < q) (per : Function.Periodic A (q : ℤ)) :
    H.stop - H.start < H.period + q :=
  agreement_bound H.text A H.period q H.positive hq H.periodic per H.foreign
    H.start H.stop H.agree

/-- Cross-child overlaps cannot contain a full sum of their periods. -/
theorem overlap_lt (J : HostedGroup D)
    (hstart : H.start ≤ J.start) (hstop : H.stop ≤ J.stop)
    (hne : H.text ≠ J.text) : H.stop - J.start < H.period + J.period := by
  apply agreement_bound H.text J.text H.period J.period H.positive J.positive
    H.periodic J.periodic hne J.start H.stop
  intro x hx hy
  exact (H.agree x (hstart.trans hx) hy).trans (J.agree x hx (hy.trans_le hstop)).symm

/-- Overlap with the next q-translate of another record transports that
child's full text. -/
theorem next_overlap_lt (J : HostedGroup D) (per : Function.Periodic A (q : ℤ))
    (hstart : H.start ≤ J.start + q) (hstop : H.stop ≤ J.stop + q)
    (hne : H.text ≠ fun x => J.text (x - q)) :
    H.stop - (J.start + q) < H.period + J.period := by
  apply agreement_bound H.text (fun x => J.text (x - q)) H.period J.period
    H.positive J.positive H.periodic (fun x => by
      simpa only [add_sub_right_comm] using J.periodic (x - q)) hne
    (J.start + q) H.stop
  intro x hx hy
  have hp : A x = A (x - q) := by simpa only [sub_add_cancel] using per (x - q)
  exact (H.agree x (hstart.trans hx) hy).trans
    (hp.trans (J.agree (x - q) (by omega) (by omega)).symm)

/-- The primitive-layer requester uses an actual child vertex at this record. -/
structure Request (H : HostedGroup D) where
  layer : Layer V H.text H.period
  stop : ℤ
  first_le : layer.first H.start ≤ stop
  le_last : stop ≤ layer.last H.start
  long : H.start + H.period < stop
  margin : stop ≤ H.stop - H.period

namespace Request

variable {H : HostedGroup D} (R : H.Request)

theorem word_mem : textWord H.text H.start R.stop ∈ V :=
  R.layer.actual H.start R.stop R.first_le R.le_last

theorem touched {s t : List α} (P : Path V s t)
    (hv : P.Visits (textWord H.text H.start R.stop)) : R.layer.TouchedBy P :=
  ⟨H.start, R.stop, R.first_le, R.le_last, hv⟩

end Request
end HostedGroup
end Superstring.Hierarchical

end OAI
