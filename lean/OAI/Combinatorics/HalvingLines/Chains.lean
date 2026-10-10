import OAI.Combinatorics.HalvingLines.Batches

namespace OAI

open Filter Topology

namespace PlanarHalving.PlaneGraph

variable {V : Type*} [Fintype V] {P : V → Point}

def Drawing.NoMultiple (D : Drawing P) : Prop :=
  ∀ e ∈ D.edges, ∀ f ∈ D.edges, e ≠ f → ∀ g ∈ D.edges,
    g ≠ e → g ≠ f → ∀ z : Point,
    z ∈ openSegment ℝ (P e.1) (P e.2) →
    z ∈ openSegment ℝ (P f.1) (P f.2) →
    z ∉ segment ℝ (P g.1) (P g.2)

lemma Drawing.crossing_props (D : Drawing P) (w : ↥D.crossings) :
    w.val.1 ∈ D.edges ∧ w.val.2 ∈ D.edges ∧
    edgeIndex w.val.1 < edgeIndex w.val.2 ∧ Crosses P w.val.1 w.val.2 := by
  classical
  have h := Finset.mem_filter.mp w.property
  exact ⟨(Finset.mem_product.mp h.1).1, (Finset.mem_product.mp h.1).2, h.2⟩

noncomputable def Drawing.crossingPoint (D : Drawing P) (w : ↥D.crossings) : Point :=
  (Set.not_disjoint_iff.mp (D.crossing_props w).2.2.2).choose

lemma Drawing.crossingPoint_mem (D : Drawing P) (w : ↥D.crossings) :
    D.crossingPoint w ∈ openSegment ℝ (P w.val.1.1) (P w.val.1.2) ∧
    D.crossingPoint w ∈ openSegment ℝ (P w.val.2.1) (P w.val.2.2) :=
  (Set.not_disjoint_iff.mp (D.crossing_props w).2.2.2).choose_spec

lemma Drawing.crossingPoint_injective (D : Drawing P) (hD : D.NoMultiple) :
    Function.Injective D.crossingPoint := by
  intro w v hpoint
  have hw := D.crossing_props w
  have hv := D.crossing_props v
  have hwm := D.crossingPoint_mem w
  have hvm := D.crossingPoint_mem v
  have hne : w.val.1 ≠ w.val.2 := fun h => hw.2.2.1.ne (congrArg edgeIndex h)
  have he (g : V × V) (hg : g ∈ D.edges)
      (hgm : D.crossingPoint w ∈ segment ℝ (P g.1) (P g.2)) :
      g = w.val.1 ∨ g = w.val.2 := by
    by_contra hh
    push Not at hh
    exact hD _ hw.1 _ hw.2.1 hne _ hg hh.1 hh.2 _ hwm.1 hwm.2 hgm
  have h₁ := he v.val.1 hv.1 (by rw [hpoint]; exact openSegment_subset_segment ℝ _ _ hvm.1)
  have h₂ := he v.val.2 hv.2.1 (by rw [hpoint]; exact openSegment_subset_segment ℝ _ _ hvm.2)
  apply Subtype.ext
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · have := hv.2.2.1
    rw [h₁, h₂] at this
    exact False.elim (lt_irrefl _ this)
  · exact Prod.ext h₁.symm h₂.symm
  · have := hv.2.2.1
    rw [h₁, h₂] at this
    exact False.elim (lt_asymm hw.2.2.1 this)
  · have := hv.2.2.1
    rw [h₁, h₂] at this
    exact False.elim (lt_irrefl _ this)

lemma Drawing.crossing_slopes_ne (D : Drawing P) (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (w : ↥D.crossings) :
    slope (P w.val.1.1) (P w.val.1.2) ≠ slope (P w.val.2.1) (P w.val.2.2) := by
  have hw := D.crossing_props w
  have he := D.crossing_endpoints hP hx hw.1 hw.2.1
    (fun h => hw.2.2.1.ne (congrArg edgeIndex h)) hw.2.2.2
  have hm := D.crossingPoint_mem w
  have h₁ := (height_of_mem_openSegment (D.right _ hw.1).ne hm.1).2
  have h₂ := (height_of_mem_openSegment (D.right _ hw.2.1).ne hm.2).2
  intro hs
  have h₃ := height_right (P w.val.1.1) (P w.val.1.2) (D.right _ hw.1).ne
  apply hP.2 w.val.1.1 w.val.1.2 w.val.2.1 he.1 he.2.2.2.2.1 he.2.2.1
  unfold height at h₁ h₂ h₃
  rw [← hs] at h₂
  unfold orient
  have ha : (P w.val.1.2).2 - (P w.val.1.1).2 =
      ((P w.val.1.2).1 - (P w.val.1.1).1) * slope (P w.val.1.1) (P w.val.1.2) := by linarith only [h₃]
  have hb : (P w.val.2.1).2 - (P w.val.1.1).2 =
      ((P w.val.2.1).1 - (P w.val.1.1).1) * slope (P w.val.1.1) (P w.val.1.2) := by linarith only [h₁, h₂]
  rw [ha, hb]
  ring

structure ConvexCover (D : Drawing P) (I : Type*) where
  owner : V × V → I
  support : ∀ e ∈ D.edges, ∀ f ∈ D.edges, owner e = owner f →
    ∀ z ∈ segment ℝ (P f.1) (P f.2), height (P e.1) (P e.2) z.1 ≤ z.2

structure ConcaveCover (D : Drawing P) (I : Type*) where
  owner : V × V → I
  support : ∀ e ∈ D.edges, ∀ f ∈ D.edges, owner e = owner f →
    ∀ z ∈ segment ℝ (P f.1) (P f.2), z.2 ≤ height (P e.1) (P e.2) z.1

variable {I J : Type*} {D : Drawing P}

lemma height_difference (p q r s : Point) (x y : ℝ) :
    height p q x - height r s x = height p q y - height r s y +
      (x-y) * (slope p q - slope r s) := by unfold height; ring

lemma ConvexCover.crossing_support (C : ConvexCover D I) (A : ConcaveCover D J)
    (w v : ↥D.crossings) (hc : C.owner w.val.1 = C.owner v.val.1)
    (ha : A.owner w.val.2 = A.owner v.val.2) :
    ((D.crossingPoint v).1 - (D.crossingPoint w).1) *
      (slope (P w.val.1.1) (P w.val.1.2) - slope (P w.val.2.1) (P w.val.2.2)) ≤ 0 := by
  have hw := D.crossing_props w
  have hv := D.crossing_props v
  have hvm := D.crossingPoint_mem v
  have hwm := D.crossingPoint_mem w
  have h₀ := C.support _ hw.1 _ hv.1 hc _ (openSegment_subset_segment ℝ _ _ hvm.1)
  have h₁ := A.support _ hw.2.1 _ hv.2.1 ha _ (openSegment_subset_segment ℝ _ _ hvm.2)
  have h₂ := (height_of_mem_openSegment (D.right _ hw.1).ne hwm.1).2
  have h₃ := (height_of_mem_openSegment (D.right _ hw.2.1).ne hwm.2).2
  have h₄ := height_difference (P w.val.1.1) (P w.val.1.2) (P w.val.2.1) (P w.val.2.2)
    (D.crossingPoint v).1 (D.crossingPoint w).1
  linarith only [h₀, h₁, h₂, h₃, h₄]

lemma ConvexCover.crossing_eq_of_x (C : ConvexCover D I) (hD : D.NoMultiple)
    (w v : ↥D.crossings) (hc : C.owner w.val.1 = C.owner v.val.1)
    (h : (D.crossingPoint w).1 = (D.crossingPoint v).1) : w = v := by
  have hw := D.crossing_props w
  have hv := D.crossing_props v
  have hvm := D.crossingPoint_mem v
  have hwm := D.crossingPoint_mem w
  have h₀ := C.support _ hw.1 _ hv.1 hc _ (openSegment_subset_segment ℝ _ _ hvm.1)
  have h₁ := C.support _ hv.1 _ hw.1 hc.symm _ (openSegment_subset_segment ℝ _ _ hwm.1)
  have h₂ := (height_of_mem_openSegment (D.right _ hw.1).ne hwm.1).2
  have h₃ := (height_of_mem_openSegment (D.right _ hv.1).ne hvm.1).2
  apply D.crossingPoint_injective hD
  apply Prod.ext h
  rw [h] at h₁ h₂
  linarith only [h₀, h₁, h₂, h₃]

lemma ConvexCover.crossing_sign_injective (C : ConvexCover D I) (A : ConcaveCover D J)
    (hP : Position P) (hx : Function.Injective (fun v => (P v).1)) (hD : D.NoMultiple) :
    Function.Injective (fun w : ↥D.crossings =>
      (C.owner w.val.1, A.owner w.val.2,
        decide (slope (P w.val.1.1) (P w.val.1.2) < slope (P w.val.2.1) (P w.val.2.2)))) := by
  intro w v hh
  have hc := congrArg Prod.fst hh
  have ha := congrArg (fun p => p.2.1) hh
  have hs : (slope (P w.val.1.1) (P w.val.1.2) < slope (P w.val.2.1) (P w.val.2.2)) ↔
      (slope (P v.val.1.1) (P v.val.1.2) < slope (P v.val.2.1) (P v.val.2.2)) :=
    by simpa only [decide_eq_decide] using (congrArg (fun p => p.2.2) hh)
  have hw := C.crossing_support A w v hc ha
  have hv := C.crossing_support A v w hc.symm ha.symm
  apply C.crossing_eq_of_x hD w v hc
  have hnw := D.crossing_slopes_ne hP hx w
  have hnv := D.crossing_slopes_ne hP hx v
  by_cases h : slope (P w.val.1.1) (P w.val.1.2) < slope (P w.val.2.1) (P w.val.2.2)
  · have h' := hs.mp h
    have hxw : (D.crossingPoint w).1 ≤ (D.crossingPoint v).1 := by nlinarith only [hw, h]
    have hxv : (D.crossingPoint v).1 ≤ (D.crossingPoint w).1 := by nlinarith only [hv, h']
    exact le_antisymm hxw hxv
  · have h' := mt hs.mpr h
    have hnw' := lt_of_le_of_ne (le_of_not_gt h) hnw.symm
    have hnv' := lt_of_le_of_ne (le_of_not_gt h') hnv.symm
    have hxw : (D.crossingPoint w).1 ≤ (D.crossingPoint v).1 := by nlinarith only [hv, hnv']
    have hxv : (D.crossingPoint v).1 ≤ (D.crossingPoint w).1 := by nlinarith only [hw, hnw']
    exact le_antisymm hxw hxv

theorem ConvexCover.crossing_bound [Fintype I] [Fintype J]
    (C : ConvexCover D I) (A : ConcaveCover D J) (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (hD : D.NoMultiple) :
    D.crossings.card ≤ 2 * Fintype.card I * Fintype.card J := by
  classical
  have h := Fintype.card_le_of_injective _ (C.crossing_sign_injective A hP hx hD)
  simpa [Fintype.card_prod, Fintype.card_bool, mul_comm, mul_left_comm, mul_assoc] using h

end PlanarHalving.PlaneGraph

namespace PlanarHalving.Batches
open PlaneGraph

variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.edges (S : @System n R k a P) : Finset (Fin n × Fin n) :=
  Finset.univ.biUnion (fun b => S.loss b ×ˢ S.gain b)

lemma System.mem_edges (S : @System n R k a P) (e : Fin n × Fin n) :
    e ∈ S.edges ↔ ∃ b : Fin R, e.1 ∈ S.loss b ∧ e.2 ∈ S.gain b := by
  simp only [System.edges, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product]

lemma System.batch_unique (S : @System n R k a P) {e : Fin n × Fin n}
    {b c : Fin R} (hb : e.1 ∈ S.loss b ∧ e.2 ∈ S.gain b)
    (hc : e.1 ∈ S.loss c ∧ e.2 ∈ S.gain c) : b = c := by
  have h₁ := S.edge_slope b hb.1 hb.2
  have h₂ := S.edge_slope c hc.1 hc.2
  by_contra h
  rcases lt_or_gt_of_ne h with hbc | hcb
  · have ht : b.succ ≤ c.castSucc := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
      omega
    have := S.increasing.monotone ht
    linarith only [h₁.2, h₂.1, this]
  · have ht : c.succ ≤ b.castSucc := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
      omega
    have := S.increasing.monotone ht
    linarith only [h₂.2, h₁.1, this]

lemma System.card_edges (S : @System n R k a P) : S.edges.card = R * a ^ 2 := by
  classical
  rw [System.edges, Finset.card_biUnion]
  · simp [Finset.card_product, S.card_loss, S.card_gain, pow_two]
  · intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact hbc (S.batch_unique (Finset.mem_product.mp he) (Finset.mem_product.mp hf))

noncomputable def System.vertices (S : @System n R k a P) : Finset (Fin n) :=
  S.edges.image Prod.fst ∪ S.edges.image Prod.snd

lemma System.edge_ends (S : @System n R k a P) {e : Fin n × Fin n} (he : e ∈ S.edges) :
    e.1 ∈ S.vertices ∧ e.2 ∈ S.vertices := by
  exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,he,rfl⟩),
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)⟩

noncomputable def System.drawing (S : @System n R k a P) : Drawing P where
  vertices := S.vertices
  edges := S.edges
  right e he := by obtain ⟨b,hb,hc⟩ := (S.mem_edges e).mp he; exact S.edge_right b hb hc
  ends _ he := S.edge_ends he

structure System.EdgeTrace (S : @System n R k a P) [NeZero a] (e : Fin n × Fin n) where
  batch : Fin R
  number : Fin a
  token : ↥(S.marks 0)
  source : (S.tokenState number batch.castSucc token : Fin n) = e.1
  target : (S.tokenState number batch.succ token : Fin n) = e.2
  loss : e.1 ∈ S.loss batch
  gain : e.2 ∈ S.gain batch

lemma System.trace_exists (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) : Nonempty (S.EdgeTrace e) := by
  obtain ⟨b,hl,hg⟩ := (S.mem_edges e).mp he
  obtain ⟨j,hj,_⟩ := matching_unique (S.lossIndex b) (S.gainIndex b) ⟨e.1,hl⟩ ⟨e.2,hg⟩
  let u : ↥(S.marks b.castSucc) := ⟨e.1, (Finset.mem_sdiff.mp hl).1⟩
  let t := (S.tokenState j b.castSucc).symm u
  have hsrc : S.tokenState j b.castSucc t = u := Equiv.apply_symm_apply _ _
  refine ⟨⟨b,j,t,congrArg Subtype.val hsrc, ?_, hl,hg⟩⟩
  rw [S.tokenState_succ, hsrc]
  have hn : (u : Fin n) ∉ S.marks b.succ := (Finset.mem_sdiff.mp hl).2
  change (transport _ _ (S.match j b) u : Fin n) = e.2
  rw [transport_of_not_mem (S.match j b) _ hn]
  exact congrArg Subtype.val hj

noncomputable def System.trace (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) : S.EdgeTrace e :=
  Classical.choice (S.trace_exists he)

lemma System.token_fixed_of_outside (S : @System n R k a P) [NeZero a]
    (j : Fin a) (u : ↥(S.marks 0)) (hu : u.val ∉ S.vertices) (b : Fin (R + 1)) :
    (S.tokenState j b u : Fin n) = u.val := by
  induction b using Fin.induction with
  | zero => simp
  | succ b ih =>
    rcases S.token_step j u b with h | ⟨hl,hg⟩
    · exact h.symm.trans ih
    · have he : ((S.tokenState j b.castSucc u : Fin n), (S.tokenState j b.succ u : Fin n)) ∈ S.edges :=
        (S.mem_edges _).mpr ⟨b,hl,hg⟩
      have hv := (S.edge_ends he).1
      rw [ih] at hv
      exact False.elim (hu hv)

lemma System.trace_token_mem (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) : (S.trace he).token.val ∈ S.vertices := by
  by_contra hn
  have hh := S.token_fixed_of_outside (S.trace he).number (S.trace he).token hn (S.trace he).batch.castSucc
  rw [(S.trace he).source] at hh
  exact hn (hh ▸ (S.edge_ends he).1)

noncomputable def System.convexOwner (S : @System n R k a P) [NeZero n] [NeZero a]
    (e : Fin n × Fin n) : Fin a × Fin n :=
  if h : e ∈ S.edges then ((S.trace h).number, (S.trace h).token.val) else (0,0)

lemma System.convexOwner_eq (S : @System n R k a P) [NeZero n] [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) :
    S.convexOwner e = ((S.trace he).number, (S.trace he).token.val) := by
  simp only [System.convexOwner, dite_eq_left he]

lemma System.convexOwner_mem (S : @System n R k a P) [NeZero n] [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) :
    S.convexOwner e ∈ Finset.univ ×ˢ S.vertices := by
  rw [S.convexOwner_eq he]
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, S.trace_token_mem he⟩

noncomputable def System.convexCover (S : @System n R k a P) [NeZero n] [NeZero a] :
    ConvexCover S.drawing (Fin a × Fin n) where
  owner := S.convexOwner
  support e he f hf howner z hz := by
    have he' : e ∈ S.edges := he
    have hf' : f ∈ S.edges := hf
    rw [S.convexOwner_eq he', S.convexOwner_eq hf'] at howner
    have hj : (S.trace he').number = (S.trace hf').number := congrArg Prod.fst howner
    have hu : (S.trace he').token = (S.trace hf').token := Subtype.ext (congrArg Prod.snd howner)
    let C := S.tokenPath (S.trace he').number (S.trace he').token
    have h₀ : C.point (S.trace he').batch.castSucc = P e.1 := congrArg P (S.trace he').source
    have h₁ : C.point (S.trace he').batch.succ = P e.2 := congrArg P (S.trace he').target
    have h₂ : C.point (S.trace hf').batch.castSucc = P f.1 := by
      simp only [C, System.tokenPath, hj, hu, (S.trace hf').source]
    have h₃ : C.point (S.trace hf').batch.succ = P f.2 := by
      simp only [C, System.tokenPath, hj, hu, (S.trace hf').target]
    have hne : C.point (S.trace he').batch.castSucc ≠ C.point (S.trace he').batch.succ := by
      rw [h₀,h₁]
      exact fun h => (S.drawing.right _ he).ne (congrArg Prod.fst h)
    have hzs : z ∈ segment ℝ (C.point (S.trace hf').batch.castSucc) (C.point (S.trace hf').batch.succ) := by
      rwa [h₂,h₃]
    have h := C.support_segment (S.trace he').batch hne (S.trace hf').batch hzs
    rwa [h₀,h₁] at h

end PlanarHalving.Batches

namespace PlanarHalving.PlaneGraph
variable {V : Type*} [Fintype V] {P : V → Point} {I J : Type*} {D : Drawing P}

theorem ConvexCover.crossing_bound_finset [DecidableEq I] [DecidableEq J]
    (C : ConvexCover D I) (A : ConcaveCover D J) (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (hD : D.NoMultiple)
    (ci : Finset I) (cj : Finset J)
    (hci : ∀ e ∈ D.edges, C.owner e ∈ ci) (hcj : ∀ e ∈ D.edges, A.owner e ∈ cj) :
    D.crossings.card ≤ 2 * ci.card * cj.card := by
  classical
  let f := fun w : (V × V) × (V × V) =>
    (C.owner w.1, A.owner w.2,
      decide (slope (P w.1.1) (P w.1.2) < slope (P w.2.1) (P w.2.2)))
  have hm : Set.MapsTo f (D.crossings : Set _) (↑(ci ×ˢ (cj ×ˢ (Finset.univ : Finset Bool))) : Set _) := by
    intro w hw
    have hp := D.crossing_props ⟨w,hw⟩
    exact Finset.mem_product.mpr ⟨hci _ hp.1,
      Finset.mem_product.mpr ⟨hcj _ hp.2.1, Finset.mem_univ _⟩⟩
  have hi : (D.crossings : Set _).InjOn f := by
    intro w hw v hv hh
    exact congrArg Subtype.val (C.crossing_sign_injective A hP hx hD (a₁ := ⟨w,hw⟩) (a₂ := ⟨v,hv⟩) hh)
  have hc := Finset.card_le_card_of_injOn f hm hi
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_bool,
    mul_comm, mul_left_comm, mul_assoc] using hc

lemma slope_neg_reverse (p q : Point) : slope (-q) (-p) = slope p q := by
  simp only [slope, Prod.fst_neg, Prod.snd_neg]
  congr 1 <;> ring

lemma height_neg_reverse (p q : Point) (hx : p.1 ≠ q.1) (x : ℝ) :
    height (-q) (-p) (-x) = -height p q x := by
  have hy := height_right p q hx
  rw [height, slope_neg_reverse]
  simp only [Prod.fst_neg, Prod.snd_neg]
  unfold height at hy ⊢
  linarith only [hy]

end PlanarHalving.PlaneGraph

end OAI
