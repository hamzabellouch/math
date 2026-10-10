import OAI.Geometry.UnitDistances.Cutting

namespace OAI

namespace PlanarUnitDistances.Sweep
open Finset Classical
variable {α : Type*} [DecidableEq α]

def Lower (f : α → ℝ) (x : Option α) (y : ℝ) : Prop :=
  ∀ a, x=some a → f a<y

def GapBand (f : α → ℝ) (g : Option α × Option α) (y : ℝ) : Prop :=
  Lower f g.1 y ∧ ∀ a, g.2=some a → y<f a

lemma links_cover (f : α → ℝ) (x : Option α) (L : List α) (y : ℝ)
    (hx : Lower f x y) (hy : ∀ a ∈ L, y ≠ f a) :
    ∃ g ∈ links x L, GapBand f g y := by
  induction L generalizing x with
  | nil =>
    exact ⟨(x,none),by simp [links],hx,fun _ h => by cases h⟩
  | cons a L ih =>
    by_cases ha : y<f a
    · refine ⟨(x,some a),Finset.mem_insert_self _ _,hx,?_⟩
      intro b hb
      exact Option.some.inj hb ▸ ha
    · have hay : f a<y := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm (hy a List.mem_cons_self))
      obtain ⟨g,hg,hgy⟩ := ih (some a) (by
        intro b hb
        exact Option.some.inj hb ▸ hay) (fun b hb => hy b (List.mem_cons_of_mem a hb))
      exact ⟨g,Finset.mem_insert_of_mem hg,hgy⟩

lemma links_sound (f : α → ℝ) (x : Option α) (L : List α)
    (hL : L.Pairwise (fun a b => f a<f b))
    (hx : ∀ a, x=some a → ∀ b ∈ L, f a<f b)
    {g : Option α × Option α} (hg : g ∈ links x L) {y : ℝ}
    (hy : GapBand f g y) : Lower f x y ∧ ∀ a ∈ L, y≠f a := by
  induction L generalizing x with
  | nil =>
    have he := Finset.mem_singleton.mp hg
    subst g
    exact ⟨hy.1,by simp⟩
  | cons a L ih =>
    have hL' := List.pairwise_cons.mp hL
    rcases Finset.mem_insert.mp hg with he | hg
    · subst g
      refine ⟨hy.1,?_⟩
      intro b hb
      have hya := hy.2 a rfl
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hya.ne
      · exact (hya.trans (hL'.1 b hb)).ne
    · have hr := ih (some a) hL'.2 (by
        intro b hb c hc
        exact Option.some.inj hb ▸ hL'.1 c hc) hg
      have hay := hr.1 a rfl
      refine ⟨?_,?_⟩
      · intro b hb
        exact (hx b hb a List.mem_cons_self).trans hay
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hay.ne'
        · exact hr.2 b hb

lemma gaps_cover (f : α → ℝ) (L : List α) (y : ℝ) (hy : ∀ a ∈ L, y≠f a) :
    ∃ g ∈ gaps L, GapBand f g y :=
  links_cover f none L y (fun _ h => by cases h) hy

lemma gaps_avoid (f : α → ℝ) (L : List α)
    (hL : L.Pairwise (fun a b => f a<f b)) {g : Option α × Option α}
    (hg : g ∈ gaps L) {y : ℝ} (hy : GapBand f g y) : ∀ a ∈ L, y≠f a :=
  (links_sound f none L hL (fun _ h => by cases h) hg hy).2

lemma links_endpoints (x : Option α) (L : List α) {g : Option α × Option α}
    (hg : g ∈ links x L) {a : α} (ha : g.1=some a ∨ g.2=some a) :
    x=some a ∨ a ∈ L := by
  induction L generalizing x with
  | nil =>
    have he := Finset.mem_singleton.mp hg
    subst g
    rcases ha with h | h
    · exact Or.inl h
    · exact by cases h
  | cons b L ih =>
    rcases Finset.mem_insert.mp hg with he | hg
    · subst g
      rcases ha with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl (Option.some.inj h).symm))
    · rcases ih (some b) hg with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl (Option.some.inj h).symm))
      · exact Or.inr (List.mem_cons_of_mem b h)

lemma gaps_endpoints (L : List α) {g : Option α × Option α}
    (hg : g ∈ gaps L) {a : α} (ha : g.1=some a ∨ g.2=some a) : a ∈ L := by
  rcases links_endpoints none L hg ha with h | h
  · exact by cases h
  · exact h

end PlanarUnitDistances.Sweep

namespace PlanarUnitDistances.SweepRuns
open Finset Classical
variable {α : Type*}

def Reach (G : ℕ → Finset α) (bad : ℕ → α → Prop) (g : α) (lo hi : ℕ) : Prop :=
  lo ≤ hi ∧ (∀ k, lo ≤ k → k ≤ hi → g ∈ G k) ∧
    (∀ k, lo ≤ k → k < hi → ¬bad k g)

lemma reach_self {G : ℕ → Finset α} {bad : ℕ → α → Prop} {g : α} {k : ℕ}
    (h : g ∈ G k) : Reach G bad g k k :=
  ⟨le_rfl,fun _ h1 h2 => by simpa only [le_antisymm h2 h1] using h,
    fun _ h1 h2 => False.elim (not_lt_of_ge h1 h2)⟩

lemma reach_extend_left {G : ℕ → Finset α} {bad : ℕ → α → Prop} {g : α}
    {lo hi : ℕ} (hr : Reach G bad g (lo+1) hi) (hmem : g ∈ G lo)
    (hbad : ¬bad lo g) : Reach G bad g lo hi := by
  refine ⟨(Nat.le_succ lo).trans hr.1,?_,?_⟩
  · intro k hk hk'
    by_cases h : k=lo
    · simpa [h] using hmem
    · exact hr.2.1 k (by omega) hk'
  · intro k hk hk'
    by_cases h : k=lo
    · simpa [h] using hbad
    · exact hr.2.2 k (by omega) hk'

noncomputable def starts (G : ℕ → Finset α) (bad : ℕ → α → Prop) (k : ℕ) :=
  (G k).filter (fun g => k=0 ∨ g ∉ G (k-1) ∨ bad (k-1) g)

lemma mem_starts {G : ℕ → Finset α} {bad : ℕ → α → Prop} {g : α} {k : ℕ} :
    g ∈ starts G bad k ↔ g ∈ G k ∧ (k=0 ∨ g ∉ G (k-1) ∨ bad (k-1) g) :=
  Finset.mem_filter

lemma starts_zero (G : ℕ → Finset α) (bad : ℕ → α → Prop) : starts G bad 0=G 0 := by
  ext g
  simp only [mem_starts,true_or,and_true]

lemma starts_succ (G : ℕ → Finset α) (bad : ℕ → α → Prop) (k : ℕ) :
    starts G bad (k+1) = (G (k+1)).filter (fun g => g ∉ G k ∨ bad k g) := by
  ext g
  simp only [mem_starts,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,false_or,
    Nat.add_sub_cancel,Finset.mem_filter]

noncomputable def last (G : ℕ → Finset α) (bad : ℕ → α → Prop) (n : ℕ)
    (g : α) (lo : ℕ) := Nat.findGreatest (Reach G bad g lo) n

noncomputable def runs (G : ℕ → Finset α) (bad : ℕ → α → Prop) (n : ℕ) :
    Finset (α × ℕ × ℕ) :=
  (range (n+1)).biUnion fun lo => (starts G bad lo).image (fun g => (g,lo,last G bad n g lo))

lemma mem_runs {G : ℕ → Finset α} {bad : ℕ → α → Prop} {n : ℕ}
    {r : α × ℕ × ℕ} (h : r ∈ runs G bad n) :
    r.2.1 ≤ r.2.2 ∧ r.2.2 ≤ n ∧ Reach G bad r.1 r.2.1 r.2.2 := by
  obtain ⟨lo,hlo,hg⟩ := Finset.mem_biUnion.mp h
  obtain ⟨g,hstart,rfl⟩ := Finset.mem_image.mp hg
  have hn : lo ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hlo)
  have hr : Reach G bad g lo (last G bad n g lo) :=
    Nat.findGreatest_spec hn (reach_self (mem_starts.mp hstart).1)
  exact ⟨hr.1,Nat.findGreatest_le _,hr⟩

lemma runs_cover {G : ℕ → Finset α} {bad : ℕ → α → Prop} {n k : ℕ}
    {g : α} (hk : k ≤ n) (hg : g ∈ G k) :
    ∃ r ∈ runs G bad n, r.1=g ∧ r.2.1 ≤ k ∧ k ≤ r.2.2 := by
  let H : ∃ lo, Reach G bad g lo k := ⟨k,reach_self hg⟩
  let lo := Nat.find H
  have hlo : Reach G bad g lo k := Nat.find_spec H
  have hs : g ∈ starts G bad lo := by
    refine mem_starts.mpr ⟨hlo.2.1 lo le_rfl hlo.1,?_⟩
    by_cases hzero : lo=0
    · exact Or.inl hzero
    · right
      by_contra h
      push Not at h
      have he : lo-1+1=lo := by omega
      have hlo' : Reach G bad g (lo-1+1) k := by rw [he]; exact hlo
      have hr := reach_extend_left hlo' h.1 h.2
      exact Nat.find_min H (show lo-1 < lo by omega) hr
  refine ⟨(g,lo,last G bad n g lo),?_,rfl,hlo.1,?_⟩
  · exact Finset.mem_biUnion.mpr ⟨lo,Finset.mem_range.mpr (Nat.lt_succ_of_le (hlo.1.trans hk)),
      Finset.mem_image.mpr ⟨g,hs,rfl⟩⟩
  · exact Nat.le_findGreatest hk hlo

lemma runs_card (G : ℕ → Finset α) (bad : ℕ → α → Prop) (n : ℕ) :
    (runs G bad n).card ≤ (G 0).card +
      ∑ k ∈ range n, ((G (k+1)).filter (fun g => g ∉ G k ∨ bad k g)).card := by
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun lo _ => Finset.card_image_le)).trans
  rw [Finset.sum_range_succ']
  simp only [starts_zero,starts_succ,Nat.add_comm,le_refl]

end PlanarUnitDistances.SweepRuns

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

lemma continuous_graphPoint (c : Plane) (b : Bool) : Continuous (graphPoint c b) := by
  unfold graphPoint
  have := continuous_branch c b
  fun_prop

lemma unit_graph_closed {c p : Plane} (hp : dist p c=1) :
    ∃ b : Bool, p=graphPoint c b (p 0) := by
  have h := unit_projection_closed hp
  have hd := plane_dist_sq p c
  have hs := Real.sq_sqrt (closed_radicand h)
  rw [hp] at hd
  have he : (p 1-c 1)^2=(Real.sqrt (1-(p 0-c 0)^2))^2 := by nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · refine ⟨true,?_⟩
    ext i
    fin_cases i
    · rfl
    · change p 1=c 1+Real.sqrt (1-(p 0-c 0)^2)
      linarith
  · refine ⟨false,?_⟩
    ext i
    fin_cases i
    · rfl
    · change p 1=c 1+-Real.sqrt (1-(p 0-c 0)^2)
      linarith

lemma circle_open_avoids_abscissas {U : Set Plane} (hU : IsOpen U) {c p : Plane}
    (hp : p ∈ U) (hc : dist p c=1) (E : Finset ℝ) :
    ∃ q ∈ U, dist q c=1 ∧ q 0 ∉ E := by
  obtain ⟨b,hb⟩ := unit_graph_closed hc
  let V := graphPoint c b ⁻¹' U
  have hVo : IsOpen V := (continuous_graphPoint c b).isOpen_preimage U hU
  have hVp : p 0 ∈ V := by change graphPoint c b (p 0) ∈ U; rw [← hb]; exact hp
  have hmem : p 0 ∈ closure (Set.Ioo (c 0-1) (c 0+1)) := by
    rw [closure_Ioo (by linarith : c 0-1 ≠ c 0+1)]
    exact unit_projection_closed hc
  have hn : (V ∩ Set.Ioo (c 0-1) (c 0+1)).Nonempty :=
    mem_closure_iff.mp hmem V hVo hVp
  have ho : IsOpen (V ∩ Set.Ioo (c 0-1) (c 0+1)) := hVo.inter isOpen_Ioo
  obtain ⟨x,hx,hxE⟩ := ((E.finite_toSet.countable).dense_compl ℝ).inter_open_nonempty _ ho hn
  exact ⟨graphPoint c b x,hx.1,graphPoint_unit b ⟨hx.2.1.le,hx.2.2.le⟩,hxE⟩

abbrev Gap := Option Label × Option Label

noncomputable def region {n : ℕ} (a : Fin n → ℝ) (g : Gap) (lo hi : ℕ) : Set Plane :=
  {p | p 0 ∈ SweepIntervals.span a lo hi ∧ Sweep.GapBand (fun b => height b (p 0)) g (p 1)}

lemma region_open {n : ℕ} (a : Fin n → ℝ) (g : Gap) (lo hi : ℕ) :
    IsOpen (region a g lo hi) := by
  have h0 : Continuous (fun p : Plane => p 0) := by fun_prop
  have h1 : Continuous (fun p : Plane => p 1) := by fun_prop
  have hs := (SweepIntervals.span_open a lo hi).preimage h0
  have hb (b : Label) : Continuous (fun p : Plane => height b (p 0)) :=
    (continuous_branch _ _).comp h0
  rcases g with ⟨l,u⟩
  cases l with
  | none =>
    cases u with
    | none => convert hs using 1; ext p; simp [region,Sweep.GapBand,Sweep.Lower]
    | some u => convert hs.inter (isOpen_lt h1 (hb u)) using 1; ext p; simp [region,Sweep.GapBand,Sweep.Lower]
  | some l =>
    cases u with
    | none => convert hs.inter (isOpen_lt (hb l) h1) using 1; ext p; simp [region,Sweep.GapBand,Sweep.Lower]
    | some u =>
      convert hs.inter ((isOpen_lt (hb l) h1).inter (isOpen_lt h1 (hb u))) using 1
      ext p
      simp [region,Sweep.GapBand,Sweep.Lower]

lemma slab_list_transport {Q : Finset Plane} {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ z, z ∈ eventAbscissas Q ↔ ∃ i, a i=z) {k : ℕ}
    {x y : ℝ} (hx : x ∈ SweepIntervals.slab a k) (hy : y ∈ SweepIntervals.slab a k)
    {L : List Label} (hm : ∀ b, b ∈ L ↔ b ∈ activeLabels Q x)
    (ho : L.Pairwise (fun b d => height b x<height d x)) :
    (∀ b, b ∈ L ↔ b ∈ activeLabels Q y) ∧
      L.Pairwise (fun b d => height b y<height d y) := by
  have hE : ∀ z ∈ SweepIntervals.slab a k, z ∉ eventAbscissas Q := by
    intro z hz he
    obtain ⟨i,hi⟩ := (ha z).mp he
    exact SweepIntervals.slab_no_event hz i hi.symm
  have hS := SweepIntervals.span_ordConnected a k k
  have hm' : ∀ b, b ∈ L ↔ b ∈ activeLabels Q y := by
    intro b
    rw [hm,mem_activeLabels,mem_activeLabels]
    constructor
    · rintro ⟨hb,hbx⟩
      exact ⟨hb,(active_constant hS hE hb hx hy).mp hbx⟩
    · rintro ⟨hb,hby⟩
      exact ⟨hb,(active_constant hS hE hb hx hy).mpr hby⟩
  refine ⟨hm',ho.imp_of_mem ?_⟩
  intro b d hb hd hbd
  have hbx := mem_activeLabels.mp ((hm b).mp hb)
  have hdx := mem_activeLabels.mp ((hm d).mp hd)
  apply order_constant hS (continuous_branch _ _).continuousOn (continuous_branch _ _).continuousOn
    (fun z hz he => ?_) hx hy hbd
  exact hE z hz (branch_collision_event hbx.1 hdx.1
    ((active_constant hS hE hbx.1 hx hz).mp hbx.2)
    ((active_constant hS hE hdx.1 hx hz).mp hdx.2)
    (fun heq => by change b=d at heq; rw [heq] at hbd; exact lt_irrefl _ hbd) he)

lemma slab_gap_avoids {Q : Finset Plane} {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ z, z ∈ eventAbscissas Q ↔ ∃ i, a i=z) {k : ℕ} {p : Plane}
    (hp : p 0 ∈ SweepIntervals.slab a k) {L : List Label}
    (hm : ∀ b, b ∈ L ↔ b ∈ activeLabels Q (p 0))
    (ho : L.Pairwise (fun b d => height b (p 0)<height d (p 0)))
    {g : Gap} (hg : g ∈ Sweep.gaps L)
    (hpg : Sweep.GapBand (fun b => height b (p 0)) g (p 1)) :
    ∀ c ∈ Q, dist p c≠1 := by
  intro c hc hpc
  have hn : p 0 ∉ eventAbscissas Q := by
    intro he
    obtain ⟨i,hi⟩ := (ha _).mp he
    exact SweepIntervals.slab_no_event hp i hi.symm
  have hx := active_of_unit_nonextreme hpc
    (fun h => hn (h ▸ (extrema_mem_events hc).1))
    (fun h => hn (h ▸ (extrema_mem_events hc).2))
  obtain ⟨b,hb⟩ := (unit_iff_graph hx).mp hpc
  exact Sweep.gaps_avoid _ L ho hg hpg (c,b) ((hm _).mpr (mem_activeLabels.mpr ⟨hc,hx⟩)) hb

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

structure Arrangement (Q : Finset Plane) where
  n : ℕ
  a : Fin n → ℝ
  strict : StrictMono a
  events : ∀ z, z ∈ eventAbscissas Q ↔ ∃ i, a i=z
  L : ℕ → List Label
  nodup : ∀ k, (L k).Nodup
  mem : ∀ k x, x ∈ SweepIntervals.slab a k → ∀ b, b ∈ L k ↔ b ∈ activeLabels Q x
  order : ∀ k x, x ∈ SweepIntervals.slab a k → (L k).Pairwise (fun b d => height b x<height d x)

lemma arrangement_exists (Q : Finset Plane) : Nonempty (Arrangement Q) := by
  let E := eventAbscissas Q
  let a := E.orderEmbOfFin rfl
  have ha : StrictMono a := a.strictMono
  have he : ∀ z, z ∈ eventAbscissas Q ↔ ∃ i, a i=z := by
    intro z
    change z ∈ (E : Set ℝ) ↔ ∃ i, a i=z
    rw [← Finset.range_orderEmbOfFin E rfl]
    rfl
  have hL : ∀ k, ∃ L : List Label, L.Nodup ∧
      (∀ x ∈ SweepIntervals.slab a k, ∀ b, b ∈ L ↔ b ∈ activeLabels Q x) ∧
      (∀ x ∈ SweepIntervals.slab a k, L.Pairwise (fun b d => height b x<height d x)) := by
    intro k
    obtain ⟨x,hx⟩ := SweepIntervals.slab_nonempty ha k
    have hxE : x ∉ eventAbscissas Q := by
      intro hxE
      obtain ⟨i,hi⟩ := (he x).mp hxE
      exact SweepIntervals.slab_no_event hx i hi.symm
    obtain ⟨L,hLn,hLm,hLo⟩ := exists_ordered_branches hxE
    exact ⟨L,hLn,fun y hy => (slab_list_transport he hx hy hLm hLo).1,
      fun y hy => (slab_list_transport he hx hy hLm hLo).2⟩
  choose L hLn hLm hLo using hL
  exact ⟨⟨E.card,a,ha,he,L,hLn,hLm,hLo⟩⟩

namespace Arrangement
variable {Q : Finset Plane} (d : Arrangement Q)

noncomputable def criticalAt (k : ℕ) : Finset Label :=
  if h : k<d.n then critical Q (d.a ⟨k,h⟩) else ∅

noncomputable def G (k : ℕ) := Sweep.gaps (d.L k)

noncomputable def pieces := SweepRuns.runs d.G (fun k g => Sweep.touches (d.criticalAt k) g) d.n

lemma list_card_le (k : ℕ) : (d.L k).length ≤ 2*Q.card := by
  obtain ⟨x,hx⟩ := SweepIntervals.slab_nonempty d.strict k
  rw [← List.toFinset_card_of_nodup (d.nodup k)]
  have hsub : (d.L k).toFinset ⊆ labels Q := by
    intro b hb
    exact (Finset.mem_filter.mp ((d.mem k x hx b).mp (List.mem_toFinset.mp hb))).1
  exact (Finset.card_le_card hsub).trans_eq (by simp [labels,Finset.card_product,mul_comm])

lemma G_card_le (k : ℕ) : (d.G k).card ≤ 2*Q.card+1 :=
  (Sweep.links_card_le none (d.L k)).trans (Nat.add_le_add_right (d.list_card_le k) 1)

lemma skeleton (k : Fin d.n) :
    (d.L k.val).filter (· ∉ d.criticalAt k.val) =
      (d.L (k.val+1)).filter (· ∉ d.criticalAt k.val) := by
  unfold criticalAt
  rw [dite_eq_left k.is_lt]
  obtain ⟨x,hx⟩ := SweepIntervals.slab_nonempty d.strict k.val
  obtain ⟨y,hy⟩ := SweepIntervals.slab_nonempty d.strict (k.val+1)
  exact event_skeleton d.events k hx hy (d.nodup _) (d.nodup _)
    (d.mem _ x hx) (d.mem _ y hy) (d.order _ x hx) (d.order _ y hy)

lemma critical_sum : ∑ k ∈ range d.n, (d.criticalAt k).card ≤ 4*Q.card+4*Q.card^2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (d.criticalAt k).card)]
  simp only [criticalAt,dite_eq_left (Fin.is_lt _)]
  have he : ∑ k : Fin d.n, (critical Q (d.a k)).card =
      ∑ x ∈ eventAbscissas Q, (critical Q x).card := by
    apply Finset.sum_bij (fun k _ => d.a k)
    · intro k _
      exact (d.events _).mpr ⟨k,rfl⟩
    · intro k _ j _ h
      exact d.strict.injective h
    · intro x hx
      obtain ⟨k,hk⟩ := (d.events _).mp hx
      exact ⟨k,Finset.mem_univ _,hk⟩
    · intro _ _; rfl
  rw [he]
  exact critical_card_sum Q _

lemma pieces_card : d.pieces.card ≤ 43*(1+Q.card^2) := by
  have hs : ∑ k ∈ range d.n,
      ((d.G (k+1)).filter (fun g => g ∉ d.G k ∨ Sweep.touches (d.criticalAt k) g)).card ≤
      5 * ∑ k ∈ range d.n, (d.criticalAt k).card := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have h := Sweep.event_starts_card (d.criticalAt k) (d.L k) (d.L (k+1))
      (d.nodup k) (d.nodup (k+1)) (d.skeleton ⟨k,Finset.mem_range.mp hk⟩)
    convert h using 1
    apply congrArg Finset.card
    ext g
    simp only [G,Finset.mem_filter]
    exact Finset.mem_filter
  have hR := SweepRuns.runs_card d.G (fun k g => Sweep.touches (d.criticalAt k) g) d.n
  have h0 := d.G_card_le 0
  have hcrit := d.critical_sum
  have hq : Q.card ≤ Q.card^2 := by
    by_cases h : Q.card=0
    · simp [h]
    · have h1 : 1≤Q.card := Nat.one_le_iff_ne_zero.mpr h
      simpa [pow_two] using Nat.mul_le_mul_left Q.card h1
  change (d.pieces).card ≤ _ at hR
  nlinarith

lemma piece_avoids {r : Gap × ℕ × ℕ} (hr : r ∈ d.pieces) :
    ∀ p ∈ region d.a r.1 r.2.1 r.2.2, ∀ c ∈ Q, dist p c≠1 := by
  intro p hp c hc hpc
  obtain ⟨q,hq,hqc,hqE⟩ := circle_open_avoids_abscissas
    (region_open _ _ _ _) hp hpc (eventAbscissas Q)
  have hr' := SweepRuns.mem_runs hr
  have hq' : q 0 ∈ SweepIntervals.span d.a r.2.1 r.2.2 := hq.1
  rcases SweepIntervals.span_decomposition d.strict hr'.1 hr'.2.1 hq' with hj | hk
  · obtain ⟨j,_,_,hj⟩ := hj
    exact hqE ((d.events _).mpr ⟨j,hj.symm⟩)
  · obtain ⟨k,hk1,hk2,hqk⟩ := hk
    exact slab_gap_avoids d.events hqk (d.mem k (q 0) hqk) (d.order k (q 0) hqk)
      (hr'.2.2.2.1 k hk1 hk2) hq.2 c hc hqc

lemma pieces_cover {p : Plane} (hp : p 0 ∉ eventAbscissas Q)
    (hpc : ∀ c ∈ Q, dist p c≠1) :
    ∃ r ∈ d.pieces, p ∈ region d.a r.1 r.2.1 r.2.2 := by
  have hn : ∀ i, p 0 ≠ d.a i := by
    intro i hi
    exact hp ((d.events _).mpr ⟨i,hi.symm⟩)
  obtain ⟨k,hkn,hpk⟩ := SweepIntervals.cover_slabs d.strict hn
  have hh : ∀ b ∈ d.L k, p 1≠height b (p 0) := by
    intro b hb he
    have hb' := mem_activeLabels.mp ((d.mem k (p 0) hpk b).mp hb)
    have hdist := (unit_iff_graph hb'.2).mpr ⟨b.2,he⟩
    exact hpc b.1 hb'.1 hdist
  obtain ⟨g,hg,hpg⟩ := Sweep.gaps_cover (fun b => height b (p 0)) (d.L k) (p 1) hh
  obtain ⟨r,hr,hrg,hrk,hrk'⟩ := SweepRuns.runs_cover (G := d.G)
    (bad := fun k g => Sweep.touches (d.criticalAt k) g) hkn hg
  refine ⟨r,hr,SweepIntervals.slab_subset_span hrk hrk' hpk,?_⟩
  rw [hrg]
  exact hpg

end Arrangement
end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

lemma circleIntersections_mono {Q T : Finset Plane} (h : Q ⊆ T) :
    circleIntersections Q ⊆ circleIntersections T := by
  intro p hp
  obtain ⟨⟨c,d⟩,hcd,hp⟩ := Finset.mem_biUnion.mp hp
  have hc := Finset.mem_product.mp hcd
  split at hp
  · simp_all
  · simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] at hp
    exact mem_circleIntersections (h hc.1) (h hc.2) (by assumption) hp.1 hp.2

lemma eventAbscissas_mono {Q T : Finset Plane} (h : Q ⊆ T) :
    eventAbscissas Q ⊆ eventAbscissas T := by
  apply Finset.union_subset_union
  · intro x hx
    obtain ⟨c,hc,hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨c,h hc,hx⟩
  · exact Finset.image_subset_image (circleIntersections_mono h)

lemma eventAbscissas_card (Q : Finset Plane) :
    (eventAbscissas Q).card ≤ 2*Q.card+2*Q.card^2 := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add
  · apply Finset.card_biUnion_le.trans
    apply (Finset.sum_le_sum (fun c _ => Finset.card_le_two (a := c 0-1) (b := c 0+1))).trans
    simp [mul_comm]
  · exact Finset.card_image_le.trans (circleIntersections_card Q)

noncomputable def endpoints (Q : Finset Plane) : Finset (Option ℝ) :=
  insert none ((eventAbscissas Q).image some)

noncomputable def boundaries (Q : Finset Plane) : Finset (Option Label) :=
  insert none ((labels Q).image some)

abbrev RegionCode := (Option ℝ × Option ℝ) × Gap

noncomputable def codeRegion (r : RegionCode) : Set Plane :=
  {p | Sweep.GapBand id r.1 (p 0) ∧ Sweep.GapBand (fun b => height b (p 0)) r.2 (p 1)}

noncomputable def candidateCodes (Q : Finset Plane) : Finset RegionCode :=
  (endpoints Q ×ˢ endpoints Q) ×ˢ (boundaries Q ×ˢ boundaries Q)

lemma candidateCodes_card (Q : Finset Plane) :
    (candidateCodes Q).card ≤ 81*(1+Q.card)^6 := by
  have he : (endpoints Q).card ≤ 3*(1+Q.card)^2 := by
    have h := (Finset.card_insert_le none ((eventAbscissas Q).image some)).trans
      (Nat.add_le_add_right Finset.card_image_le 1)
    have hE := eventAbscissas_card Q
    change (endpoints Q).card ≤ _ at h
    nlinarith
  have hb : (boundaries Q).card ≤ 3*(1+Q.card) := by
    have h := (Finset.card_insert_le none ((labels Q).image some)).trans
      (Nat.add_le_add_right Finset.card_image_le 1)
    have hL : (labels Q).card=2*Q.card := by simp [labels,mul_comm]
    change (boundaries Q).card ≤ _ at h
    omega
  simp only [candidateCodes,Finset.card_product]
  calc
    _ ≤ (3*(1+Q.card)^2)*(3*(1+Q.card)^2)*((3*(1+Q.card))*(3*(1+Q.card))) :=
      Nat.mul_le_mul (Nat.mul_le_mul he he) (Nat.mul_le_mul hb hb)
    _ = _ := by ring

lemma span_description {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    {Q : Finset Plane} (he : ∀ i, a i ∈ eventAbscissas Q)
    {lo hi : ℕ} (hl : lo ≤ n) (hh : hi ≤ n) :
    ∃ e₁ ∈ endpoints Q, ∃ e₂ ∈ endpoints Q,
      SweepIntervals.span a lo hi = {x | Sweep.GapBand id (e₁,e₂) x} := by
  have hleft : ∃ e ∈ endpoints Q,
      ∀ x, (∀ i, i.val<lo → a i<x) ↔ Sweep.Lower id e x := by
    by_cases hz : lo=0
    · refine ⟨none,Finset.mem_insert_self _ _,?_⟩
      intro x
      simp [hz,Sweep.Lower]
    · let i : Fin n := ⟨lo-1,by omega⟩
      refine ⟨some (a i),Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a i,he i,rfl⟩),?_⟩
      intro x
      simp only [Sweep.Lower,Option.some.injEq,forall_eq',id_eq]
      constructor
      · exact fun h => h i (by dsimp [i]; omega)
      · intro h j hj
        apply (ha.monotone (show j ≤ i by change j.val ≤ lo-1; omega)).trans_lt h
  have hright : ∃ e ∈ endpoints Q,
      ∀ x, (∀ i, hi ≤ i.val → x<a i) ↔ (∀ z, e=some z → x<z) := by
    by_cases hh' : hi<n
    · let i : Fin n := ⟨hi,hh'⟩
      refine ⟨some (a i),Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a i,he i,rfl⟩),?_⟩
      intro x
      simp only [Option.some.injEq,forall_eq']
      constructor
      · exact fun h => h i le_rfl
      · intro h j hj
        exact h.trans_le (ha.monotone hj)
    · refine ⟨none,Finset.mem_insert_self _ _,?_⟩
      intro x
      constructor
      · intro _ z hz
        cases hz
      · intro _ i hi
        have hn := i.is_lt
        omega
  obtain ⟨e₁,he₁,h₁⟩ := hleft
  obtain ⟨e₂,he₂,h₂⟩ := hright
  refine ⟨e₁,he₁,e₂,he₂,?_⟩
  ext x
  exact and_congr (h₁ x) (h₂ x)

namespace Arrangement
variable {T Q : Finset Plane} (d : Arrangement T)

lemma piece_description (hT : T ⊆ Q) {r : Gap × ℕ × ℕ} (hr : r ∈ d.pieces) :
    ∃ c ∈ candidateCodes Q, region d.a r.1 r.2.1 r.2.2 = codeRegion c := by
  have hr' := SweepRuns.mem_runs hr
  obtain ⟨e₁,he₁,e₂,he₂,he⟩ := span_description d.strict
    (fun i => eventAbscissas_mono hT ((d.events _).mpr ⟨i,rfl⟩))
    (hr'.1.trans hr'.2.1) hr'.2.1
  have hb : ∀ b, b ∈ r.1.1 ∨ b ∈ r.1.2 → b ∈ labels Q := by
    intro b hb
    have hg := hr'.2.2.2.1 r.2.1 le_rfl hr'.1
    have hbL := Sweep.gaps_endpoints (d.L r.2.1) hg (hb.imp Option.mem_def.mp Option.mem_def.mp)
    obtain ⟨x,hx⟩ := SweepIntervals.slab_nonempty d.strict r.2.1
    exact mem_labels.mpr (hT (mem_activeLabels.mp ((d.mem _ x hx b).mp hbL)).1)
  have hb' (t : Option Label) (ht : t=r.1.1 ∨ t=r.1.2) : t ∈ boundaries Q := by
    cases t with
    | none => exact Finset.mem_insert_self _ _
    | some b =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨b,hb b ?_,rfl⟩
      rcases ht with ht | ht
      · exact Or.inl (ht.symm ▸ Option.mem_def.mpr rfl)
      · exact Or.inr (ht.symm ▸ Option.mem_def.mpr rfl)
  refine ⟨((e₁,e₂),r.1),Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨he₁,he₂⟩,
    Finset.mem_product.mpr ⟨hb' _ (Or.inl rfl),hb' _ (Or.inr rfl)⟩⟩,?_⟩
  ext p
  change (p 0 ∈ SweepIntervals.span d.a r.2.1 r.2.2 ∧ _) ↔ _
  rw [he]
  rfl

end Arrangement
end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

lemma rotate_surjective (e : Plane) (he : (e 0)^2+(e 1)^2=1) :
    Function.Surjective (rotate e) := by
  intro p
  refine ⟨WithLp.toLp 2 ![e 0*p 0-e 1*p 1,e 1*p 0+e 0*p 1],?_⟩
  ext i
  fin_cases i
  · change e 0*(e 0*p 0-e 1*p 1)+e 1*(e 1*p 0+e 0*p 1)=p 0
    nlinarith [congrArg (fun z : ℝ => z*p 0) he]
  · change -e 1*(e 0*p 0-e 1*p 1)+e 0*(e 1*p 0+e 0*p 1)=p 1
    nlinarith [congrArg (fun z : ℝ => z*p 1) he]

lemma mem_circleIntersections_iff {Q : Finset Plane} {p : Plane} :
    p ∈ circleIntersections Q ↔ ∃ c ∈ Q, ∃ d ∈ Q, c≠d ∧ dist p c=1 ∧ dist p d=1 := by
  constructor
  · intro hp
    obtain ⟨⟨c,d⟩,hcd,hp⟩ := Finset.mem_biUnion.mp hp
    have hc := Finset.mem_product.mp hcd
    split at hp
    · simp_all
    · simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] at hp
      exact ⟨c,hc.1,d,hc.2,by assumption,hp⟩
  · rintro ⟨c,hc,d,hd,hcd,hp,hp'⟩
    exact mem_circleIntersections hc hd hcd hp hp'

lemma good_rotated_position (P Q : Finset Plane) :
    ∃ e : Plane, (e 0)^2+(e 1)^2=1 ∧
      ∀ T ⊆ Q.image (rotate e), ∀ p ∈ P.image (rotate e),
        (∀ c ∈ T, dist p c≠1) → p 0 ∉ eventAbscissas T := by
  obtain ⟨e,he,hsep,hex⟩ := exists_good_direction (P ∪ circleIntersections Q) P Q
  refine ⟨e,he,?_⟩
  intro T hT p hp havoid hbad
  obtain ⟨p,hpP,rfl⟩ := Finset.mem_image.mp hp
  rcases Finset.mem_union.mp hbad with hextr | hint
  · obtain ⟨c,hc,hx⟩ := Finset.mem_biUnion.mp hextr
    obtain ⟨c,hcQ,rfl⟩ := Finset.mem_image.mp (hT hc)
    have hne := hex p hpP c hcQ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · apply hne.2
      change projection e p=projection e c-1 at hx
      unfold projection at *
      simp only [WithLp.ofLp_sub,Pi.sub_apply]
      linarith
    · apply hne.1
      change projection e p=projection e c+1 at hx
      unfold projection at *
      simp only [WithLp.ofLp_sub,Pi.sub_apply]
      linarith
  · obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hint
    obtain ⟨c,hc,d,hd,hcd,hyc,hyd⟩ := mem_circleIntersections_iff.mp hy
    obtain ⟨c,hcQ,rfl⟩ := Finset.mem_image.mp (hT hc)
    obtain ⟨d,hdQ,rfl⟩ := Finset.mem_image.mp (hT hd)
    obtain ⟨y,rfl⟩ := rotate_surjective e he y
    rw [rotate_dist e he] at hyc hyd
    have hyQ : y ∈ circleIntersections Q := mem_circleIntersections hcQ hdQ
      (fun h => hcd (congrArg (rotate e) h)) hyc hyd
    have hyp : y=p := by
      by_contra hne
      exact hsep y (Finset.mem_union_right _ hyQ) p (Finset.mem_union_left _ hpP) hne hyx
    subst y
    exact havoid (rotate e c) hc (by rw [rotate_dist e he]; exact hyc)

end PlanarUnitDistances.CircleCutting

end OAI
