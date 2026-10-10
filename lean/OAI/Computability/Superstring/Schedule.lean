import OAI.Computability.Superstring.Attachments

namespace OAI

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)

/-- A whole group is processed, reserving at most one outgoing request record.
Incoming reserves are spent once; every new block and request is included in
this exact numerical budget. -/
theorem process_group (closed : SubstringClosed V) (supply : C.RecordSupply)
    (g : G) (R : Finset C.Pending) (targets : ∀ r ∈ R, r.1.1 = g)
    (distinct : Set.InjOn Pending.source (R : Set C.Pending)) :
    ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (O : Finset C.Pending),
      Q.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ O, r.reserve) ≤
        2 * (C.size g * C.period g) + ∑ r ∈ R, r.reserve ∧
      (∀ i : Fin (C.size g), C.Covered Q B O ⟨g, i⟩) ∧
      (∀ r ∈ R, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w) ∧
      (∀ r ∈ O, r.source = g) ∧ O.card ≤ 1 := by
  classical
  obtain ⟨P, J, hcP, hjP, hrP, hshort, _⟩ := C.fulfill_all closed g R targets distinct
  have finish (cut : ℕ) (hcut : cut ≤ C.size g) (P' : Path V [] [])
      (hcP' : P'.cost ≤ 2 * (cut * C.period g) + ∑ r ∈ R, r.reserve)
      (hp : ∀ i : Fin (C.size g), i.val < cut → ∀ w ∈ (C.layer g i).Content, P'.Visits w)
      (hpres : ∀ w, P.Visits w → P'.Visits w) :
      ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (O : Finset C.Pending),
        Q.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ O, r.reserve) ≤
          2 * (C.size g * C.period g) + ∑ r ∈ R, r.reserve ∧
        (∀ i : Fin (C.size g), C.Covered Q B O ⟨g, i⟩) ∧
        (∀ r ∈ R, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w) ∧
        (∀ r ∈ O, r.source = g) ∧ O.card ≤ 1 := by
    obtain ⟨Q, B, O, hcQ, hvQ, hiQ, hsQ, hcardQ⟩ := C.complete_upper closed supply g cut hcut P' hp
    refine ⟨Q, B, O, ?_, ?_, ?_, hsQ, hcardQ⟩
    · have hmul := Nat.add_mul cut (C.size g - cut) (C.period g)
      rw [Nat.add_sub_of_le hcut] at hmul
      omega
    · intro i
      by_cases hi : i.val < cut
      · exact Or.inl (fun w hw => hvQ w (hp i hi w hw))
      · exact hiQ i ((C.mem_upper g cut i).mpr (by omega))
    · exact fun r hr i hi w hw => hvQ w (hpres w (hrP r hr i hi w hw))
  by_cases hJ : J.Nonempty
  · let base := J.max' hJ
    have hbJ : base ∈ J := Finset.max'_mem J hJ
    have hjbase : ∀ j ∈ J, j ≤ base := fun j hj => Finset.le_max' J j hj
    let I := Finset.Iic base \ J
    have hJsub : J ⊆ Finset.Iic base := fun j hj => Finset.mem_Iic.mpr (hjbase j hj)
    have hcard : I.card + J.card = base.val + 1 := by
      have hh := Finset.card_sdiff_add_card_eq_card hJsub
      rw [Fin.card_Iic] at hh
      exact hh
    obtain ⟨a, b, hf, hl, hlen⟩ := hshort base hbJ
    obtain ⟨Q, hcQ, hvQ, hiQ⟩ := C.root_below closed g base P (hjP base hbJ)
      a b hf hl hlen I (fun i hi => Finset.mem_Iic.mp (Finset.mem_sdiff.mp hi).1)
    apply finish (base.val + 1) (by omega) Q
    · have hmul := Nat.add_mul I.card J.card (C.period g)
      rw [hcard] at hmul
      omega
    · intro i hi w hw
      by_cases hj : i ∈ J
      · exact hvQ w (hjP i hj w hw)
      · exact hiQ i (Finset.mem_sdiff.mpr ⟨Finset.mem_Iic.mpr (by change i.val ≤ base.val; omega), hj⟩) w hw
    · exact hvQ
  · have heJ : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    apply finish 0 (Nat.zero_le _) P
    · simpa only [heJ, Finset.card_empty, Nat.zero_mul, Nat.mul_zero] using hcP
    · intro i hi
      omega
    · exact fun _ h => h

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)

namespace Covered
variable {C} {P Q : Path V [] []} {B D : Finset C.PlannedBlock} {R O : Finset C.Pending}

 theorem mono {i : C.Id} (h : C.Covered P B R i)
    (hp : ∀ w, P.Visits w → Q.Visits w) (hb : B ⊆ D) (hr : R ⊆ O) :
    C.Covered Q D O i := by
  rcases h with hv | ⟨b, hm, hi⟩ | ⟨r, hm, hi⟩
  · exact Or.inl (fun w hw => hp w (hv w hw))
  · exact Or.inr (Or.inl ⟨b, hb hm, hi⟩)
  · exact Or.inr (Or.inr ⟨r, hr hm, hi⟩)
end Covered

/-- Finite period-order scheduling, with all previously spent and reserved
budgets retained. Strict increase of outgoing requests is proved by their
actual record, and prevents both backward requests and duplicate sources. -/
theorem schedule (closed : SubstringClosed V) (supply : C.RecordSupply)
    (I : Finset G) (P : Path V [] []) (B : Finset C.PlannedBlock) (R : Finset C.Pending)
    (upward : ∀ g ∈ I, ∀ h, C.period g < C.period h → h ∈ I)
    (targets : ∀ r ∈ R, r.1.1 ∈ I) (sources : ∀ r ∈ R, r.source ∉ I)
    (distinct : Set.InjOn Pending.source (R : Set C.Pending))
    (ready : ∀ i : C.Id, i.1 ∈ I ∨ C.Covered P B R i) :
    ∃ Q : Path V [] [],
      Q.cost ≤ P.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ R, r.reserve) +
        ∑ g ∈ I, 2 * (C.size g * C.period g) ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i : C.Id, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  classical
  induction I using Finset.strongInductionOn generalizing P B R with
  | _ I ih =>
    by_cases hI : I.Nonempty
    · obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image I C.period hI
      let In := R.filter (fun r => r.1.1 = g)
      let Rest := R.filter (fun r => r.1.1 ≠ g)
      have hIn : ∀ r ∈ In, r.1.1 = g := fun _ h => (Finset.mem_filter.mp h).2
      have hdIn : Set.InjOn Pending.source (In : Set C.Pending) :=
        distinct.mono (by intro r hr; exact (Finset.mem_filter.mp hr).1)
      obtain ⟨F, D, O, hcF, hvF, hiF, hsO, hcardO⟩ := C.process_group closed supply g In hIn hdIn
      let P' := P.trans F
      let B' := B ∪ D
      let R' := Rest ∪ O
      have hup : ∀ a ∈ I.erase g, ∀ b, C.period a < C.period b → b ∈ I.erase g := by
        intro a ha b hb
        have haI := (Finset.mem_erase.mp ha).2
        apply Finset.mem_erase.mpr
        refine ⟨?_, upward a haI b hb⟩
        intro he
        subst b
        have := hmin a haI
        omega
      have htarget : ∀ r ∈ R', r.1.1 ∈ I.erase g := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hr).2,
            targets r (Finset.mem_filter.mp hr).1⟩
        · have hl := r.later
          rw [hsO r hr] at hl
          exact Finset.mem_erase.mpr ⟨by intro he; rw [he] at hl; omega,
            upward g hg _ hl⟩
      have hsource : ∀ r ∈ R', r.source ∉ I.erase g := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · exact fun hh => sources r (Finset.mem_filter.mp hr).1 (Finset.mem_of_mem_erase hh)
        · rw [hsO r hr]
          exact Finset.notMem_erase g I
      have hd : Set.InjOn Pending.source (R' : Set C.Pending) := by
        intro r hr s hs he
        rcases Finset.mem_union.mp hr with hr | hr <;>
          rcases Finset.mem_union.mp hs with hs | hs
        · exact distinct (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hs).1 he
        · have hh : r.source = g := he.trans (hsO s hs)
          exact False.elim (sources r (Finset.mem_filter.mp hr).1 (hh ▸ hg))
        · have hh : s.source = g := he.symm.trans (hsO r hr)
          exact False.elim (sources s (Finset.mem_filter.mp hs).1 (hh ▸ hg))
        · exact Finset.card_le_one.mp hcardO r hr s hs
      have hready : ∀ i : C.Id, i.1 ∈ I.erase g ∨ C.Covered P' B' R' i := by
        intro i
        by_cases hi : i.1 ∈ I.erase g
        · exact Or.inl hi
        apply Or.inr
        by_cases hig : i.1 = g
        · obtain ⟨a, j⟩ := i
          change a = g at hig
          subst a
          exact (hvF j).mono (fun _ h => Or.inr h)
            Finset.subset_union_right Finset.subset_union_right
        · have hnot : i.1 ∉ I := fun hm => hi (Finset.mem_erase.mpr ⟨hig, hm⟩)
          have hcov := (ready i).resolve_left hnot
          rcases hcov with hv | ⟨b, hb, hbi⟩ | ⟨r, hr, hri⟩
          · exact Or.inl (fun w hw => Or.inl (hv w hw))
          · exact Or.inr (Or.inl ⟨b, Finset.mem_union_left _ hb, hbi⟩)
          · by_cases hrg : r.1.1 = g
            · exact Or.inl (fun w hw => Or.inr (hiF r (Finset.mem_filter.mpr ⟨hr, hrg⟩) i hri w hw))
            · exact Or.inr (Or.inr ⟨r, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, hrg⟩), hri⟩)
      obtain ⟨Q, hcQ, hvQ, hlQ⟩ := ih (I.erase g) (Finset.erase_ssubset hg)
        P' B' R' hup htarget hsource hd hready
      refine ⟨Q, ?_, fun w hw => hvQ w (Or.inl hw), hlQ⟩
      have hBsum : (∑ b ∈ B', b.reserve) ≤ (∑ b ∈ B, b.reserve) + ∑ b ∈ D, b.reserve := by
        have hh := Finset.sum_union_inter (s₁ := B) (s₂ := D) (f := PlannedBlock.reserve)
        change _ ≤ _
        dsimp only [B']
        omega
      have hRsum : (∑ r ∈ R', r.reserve) ≤ (∑ r ∈ Rest, r.reserve) + ∑ r ∈ O, r.reserve := by
        have hh := Finset.sum_union_inter (s₁ := Rest) (s₂ := O) (f := Pending.reserve)
        dsimp only [R']
        omega
      have hpartition : (∑ r ∈ In, r.reserve) + (∑ r ∈ Rest, r.reserve) = ∑ r ∈ R, r.reserve :=
        Finset.sum_filter_add_sum_filter_not R (fun r => r.1.1 = g) Pending.reserve
      have hbudget := Finset.sum_erase_add I (fun g => 2 * (C.size g * C.period g)) hg
      have hPcost : P'.cost = P.cost + F.cost := Path.cost_trans _ _
      omega
    · have heI : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      have heR : R = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        have hh := targets r hr
        simp only [heI, Finset.notMem_empty] at hh
      obtain ⟨Q, hcQ, hvQ, hlQ⟩ := PlannedBlock.execute closed B P (by
        intro i
        have hh := ready i
        simp only [heI, Finset.notMem_empty, false_or] at hh
        rcases hh with hv | hb | ⟨r, hr, _⟩
        · exact Or.inl hv
        · exact Or.inr hb
        · simp only [heR, Finset.notMem_empty] at hr)
      exact ⟨Q, by simpa only [heI, heR, Finset.sum_empty, add_zero] using hcQ, hvQ, hlQ⟩

/-- The geometric main bound for any actual finite layer collection supplied
by the count rule. All local plans, requests, and functional cycles are paid. -/
theorem connect [Fintype G] (closed : SubstringClosed V) (he : [] ∈ V)
    (supply : C.RecordSupply) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * ∑ g, C.size g * C.period g ∧
      ∀ i : C.Id, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  classical
  obtain ⟨Q, hcQ, _, hvQ⟩ := C.schedule closed supply Finset.univ (.nil [] he) ∅ ∅
    (by simp) (by simp) (by simp) (by simp [Set.InjOn]) (by simp)
  refine ⟨Q, ?_, hvQ⟩
  simpa only [Path.cost, Finset.sum_empty, zero_add, Finset.mul_sum] using hcQ

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Counts.Data

variable {α : Type} [LinearOrder α] [DecidableEq α] [Inhabited α]

/-- Reading the fully connected actual layer graph gives a constructive
numerical bound, without treating recorded prefixes as vertices. -/
theorem superstring_of_counts (D : Data α) (hD : D.WellFormed)
    (required_valid : ∀ s ∈ D.required, s ∈ D.vertices ∧ s ≠ []) :
    ∃ T : List α, T.length ≤ 2 * D.weight ∧ ∀ s ∈ D.required, s <:+: T := by
  classical
  let C := (D.threading hD).collection hD.closed
  obtain ⟨Q, hcQ, hvQ⟩ := C.connect hD.closed hD.empty_mem (D.collection_records hD)
  have hbudget : (∑ g, C.size g * C.period g) = D.weight := by
    simpa only [C, Hierarchical.Threading.collection, Nat.mul_comm] using D.layer_budget hD
  refine ⟨Q.written, ?_, ?_⟩
  · rw [Hierarchical.Path.length_written]
    simpa only [hbudget] using hcQ
  · intro s hs
    obtain ⟨hsV, hsne⟩ := required_valid s hs
    have hn := D.required_le_count hsV hsne hs
    have hpos : 0 < Fintype.card ((D.threading hD).Recorded s) := by
      rw [D.recorded_count hD hsne]
      omega
    obtain ⟨o⟩ := Fintype.card_pos_iff.mp hpos
    let e := ((D.threading hD).occurrenceEquiv hD.closed s).symm o
    let L := C.layerAt e.1
    have hprefix : s <+: Hierarchical.textWord (C.text e.1.1) e.2.val.val (L.last e.2.val.val) :=
      (L.records_iff_prefix s e.2.val.val).mp e.2.property
    have hv := hvQ e.1 _ ⟨e.2.val.val, L.last e.2.val.val,
      L.first_le_last e.2.val.val, le_rfl, rfl⟩
    have hinfix := Q.visited_infix_written hv
    simpa only [List.nil_append] using hprefix.isInfix.trans hinfix

end Superstring.Counts.Data

namespace Superstring

/-- The approximation inequality, separated from computational implementation.
This lemma is NOT the main theorem: a polynomial bit implementation is required. -/
theorem exists_two_approximation (S : Instance) :
    ∃ T : Word, IsCommonSuperstring S T ∧ T.length ≤ 2 * opt S := by
  obtain ⟨T, hcT, hvT⟩ := (Input.data S).superstring_of_counts
    (Counts.Data.input_wellFormed S) (fun s hs =>
      ⟨Input.required_mem hs, (Input.mem_core.mp hs).2.1⟩)
  exact ⟨T, (Input.core_superstring_iff S T).mp hvT,
    hcT.trans (Nat.mul_le_mul_left 2 (weight_le_opt S))⟩

end Superstring

end OAI
