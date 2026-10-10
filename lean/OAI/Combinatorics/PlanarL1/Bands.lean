import OAI.Combinatorics.PlanarL1.SeedPacking

namespace OAI

section

namespace PlanarL1.Columns

lemma consecutive_rotate {n : ℕ} (i j : Fin (n+1)) :
    Consecutive (finRotate (n+1) i) (finRotate (n+1) j) ↔ Consecutive i j := by
  by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n
  · subst i; subst j
    simp [Consecutive, eq_comm]
  · subst i
    rw [finRotate_last]
    simp only [Consecutive, Fin.val_zero, Fin.val_last, coe_finRotate_of_ne_last hj]
    have := j.isLt
    have hjv : j.val ≠ n := fun h => hj (Fin.ext h)
    clear hj
    try simp only [true_and, and_true]
    omega
  · subst j
    rw [finRotate_last]
    simp only [Consecutive, Fin.val_zero, Fin.val_last, coe_finRotate_of_ne_last hi]
    have := i.isLt
    have hiv : i.val ≠ n := fun h => hi (Fin.ext h)
    clear hi
    try simp only [true_and, and_true]
    omega
  · simp only [Consecutive, coe_finRotate_of_ne_last hi, coe_finRotate_of_ne_last hj]
    have := i.isLt
    have := j.isLt
    have hiv : i.val ≠ n := fun h => hi (Fin.ext h)
    clear hi
    have hjv : j.val ≠ n := fun h => hj (Fin.ext h)
    clear hj
    try simp only [true_and, and_true]
    omega


lemma consecutive_iterate {n : ℕ} (k : ℕ) (i j : Fin (n+1)) :
    Consecutive ((finRotate (n+1))^[k] i) ((finRotate (n+1))^[k] j) ↔
      Consecutive i j := by
  induction k generalizing i j with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, consecutive_rotate]

lemma consecutive_cycle {n : ℕ} (a i j : Fin (n+1)) :
    Consecutive (finCycle a i) (finCycle a j) ↔ Consecutive i j := by
  rw [finCycle_eq_finRotate_iterate]
  exact consecutive_iterate a.val i j

namespace Model

/-- Relabelling columns does not change geometry. The two order conditions
are explicit, so the construction never assumes invariance under an arbitrary
permutation of the circular order. -/
def relabel {n : ℕ} (M : Model n) (e : Equiv.Perm (Fin n))
    (hnc : ColumnOrder.Noncrossing (M.link.comap e))
    (hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j) : Model n where
  link := M.link.comap e
  heights i j := M.heights (e i) (e j)
  symm i j := M.symm (e i) (e j)
  permitted i j H h := M.permitted (e i) (e j) H h
  compact i j := M.compact (e i) (e j)
  noncrossing := hnc
  terminal i j h hn := by
    obtain ⟨H,hH,ht⟩ := M.terminal (e i) (e j) h (fun hc => hn ((hcon i j).mp hc))
    exact ⟨H,hH,fun k T h => ht (e k) T h⟩

variable {n : ℕ} {M : Model n} {e : Equiv.Perm (Fin n)}
  {hnc : ColumnOrder.Noncrossing (M.link.comap e)}
  {hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j}
  {J : Set ℝ} {root i j : Fin n}

/-- Undo a column relabelling on actual finite switching paths. -/
def Path.unlabel : {i j : Fin n} → (M.relabel e hnc hcon).Path J i j →
    M.Path J (e i) (e j)
  | _, _, .nil _ => .nil _
  | _, _, .cons H hH hs p => .cons H hH hs p.unlabel

@[simp] lemma Path.length_unlabel (p : (M.relabel e hnc hcon).Path J i j) (s t : ℝ) :
    p.unlabel.length s t = p.length s t := by
  induction p generalizing s with
  | nil => rfl
  | cons H hH hs p ih => simp only [Path.unlabel, Path.length, ih]

def Path.label : {i j : Fin n} → M.Path J i j →
    (M.relabel e hnc hcon).Path J (e.symm i) (e.symm j)
  | _, _, .nil _ => .nil _
  | _, _, .cons H hH hs p => .cons H hH (by simpa only [relabel, e.apply_symm_apply] using hs)
      p.label

@[simp] lemma Path.length_label (p : M.Path J i j) (s t : ℝ) :
    (p.label (hnc := hnc) (hcon := hcon)).length s t = p.length s t := by
  induction p generalizing s with
  | nil => rfl
  | cons H hH hs p ih => simp only [Path.label, Path.length, ih]

/-- The point map keeps the height and moves only the column name. -/
def Point.unlabel (x : (M.relabel e hnc hcon).Point J root) : M.Point J (e root) where
  column := e x.column
  height := x.height
  inBand := x.inBand
  reachable := by
    obtain ⟨p⟩ := x.reachable
    obtain ⟨q,hq⟩ := Path.exists_word p
    exact ⟨q.unlabel.word⟩

def Path.cast {i j k l : Fin n} (p : M.Path J i j) (h : i = k) (g : j = l) :
    M.Path J k l := h ▸ g ▸ p

@[simp] lemma Path.length_cast {i j k l : Fin n} (p : M.Path J i j)
    (h : i = k) (g : j = l) (s t : ℝ) : (p.cast h g).length s t = p.length s t := by
  subst k; subst l; rfl

lemma Point.dist_unlabel (x y : (M.relabel e hnc hcon).Point J root) :
    dist x.unlabel y.unlabel = dist x y := by
  apply le_antisymm
  · change x.unlabel.distance y.unlabel ≤ _
    have := x.paths_nonempty y
    apply le_ciInf
    intro p
    exact (x.unlabel.distance_le y.unlabel p.unlabel).trans_eq (p.length_unlabel _ _)
  · change x.distance y ≤ x.unlabel.distance y.unlabel
    have := x.unlabel.paths_nonempty y.unlabel
    apply le_ciInf
    intro p
    let q := p.label (hnc := hnc) (hcon := hcon)
    have he₁ : e.symm x.unlabel.column = x.column := e.symm_apply_apply _
    have he₂ : e.symm y.unlabel.column = y.column := e.symm_apply_apply _
    have hd := x.distance_le y (q.cast he₁ he₂)
    exact hd.trans_eq ((Path.length_cast q he₁ he₂ x.height y.height).trans
      (Path.length_label p x.height y.height))

end Model
end PlanarL1.Columns

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- Inclusion of intrinsic components into a larger band. No equality of the
intrinsic metrics is asserted. -/
def Point.widen (x : M.Point J root) (hJI : J ⊆ I) : M.Point I root where
  column := x.column
  height := x.height
  inBand := hJI x.inBand
  reachable := by
    obtain ⟨p⟩ := x.reachable
    obtain ⟨q,_⟩ := Path.exists_word p
    exact ⟨(q.widen hJI).word⟩

lemma Point.dist_widen_le (x y : M.Point J root) (hJI : J ⊆ I) :
    dist (x.widen hJI) (y.widen hJI) ≤ dist x y := by
  change (x.widen hJI).distance (y.widen hJI) ≤ x.distance y
  have := x.paths_nonempty y
  apply le_ciInf
  intro p
  exact ((x.widen hJI).distance_le (y.widen hJI) (p.widen hJI)).trans_eq (p.length_widen _ _ _)

namespace Path

/-- The vertical connection to a tip uses only the thin band, not the much
wider old chart band where scalar distance fields are defined. -/
lemma tip_connection {i l b : Fin n} {s H a : ℝ}
    (hsJ : s ∈ J) (hHJ : H ∈ J) (hs : H ∈ M.heights l b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a) (hi : i = l ∨ i = b) :
    ∃ p : M.Path J i l, p.length s H ≤ a := by
  rcases hi with rfl | rfl
  · exact ⟨.nil _,hw s hsJ H hHJ⟩
  · refine ⟨.cons H hHJ (by rwa [M.symm]) (.nil _),?_⟩
    simpa only [length,sub_self,abs_zero,add_zero] using hw s hsJ H hHJ

end Path

namespace Field

/-- The source descent lives in the BROAD CURRENT band J, whereas the old
comparison field and witnesses live in the OLD chart I, possibly in different
J-components. The attaining condition refers to J, not to the larger band. -/
structure BandDescent (F : M.Field I 1) (J : Set ℝ) (x : M.Point I root) (ε : ℝ) where
  start_in : x.height ∈ J
  target : M.Point I root
  target_in : target.height ∈ J
  path : M.Path J x.column target.column
  shortest : ∀ p : M.Path J x.column target.column,
    path.length x.height target.height ≤ p.length x.height target.height
  lower : (1:ℝ)/100000 ≤ path.length x.height target.height
  upper : path.length x.height target.height ≤ (1:ℝ)/50
  drop : F.eval target ≤ F.eval x-path.length x.height target.height+ε

namespace BandDescent

variable {F : M.Field I 1} {x : M.Point I root} {ε : ℝ}

lemma column_prefix (D : F.BandDescent J x ε) (hJI : J ⊆ I)
    {v : Fin n} (hv : v ∈ D.path.word.support) :
    ∃ z : M.Point I root, z.column = v ∧ z.height ∈ J ∧
      ∃ q : M.Path J x.column z.column,
        q.length x.height z.height ≤ (1:ℝ)/50 ∧
        F.eval z ≤ F.eval x-q.length x.height z.height+ε := by
  obtain ⟨T,hT,q,r,hqr⟩ := D.path.split_at_column D.start_in D.target_in hv
  let z : M.Point I root := ⟨v,T,hJI hT,x.reachable.trans (q.widen hJI).word.reachable⟩
  have hf := F.path_bound (r.widen hJI) ⟨T,hJI hT⟩ ⟨D.target.height,D.target.inBand⟩
  rw [NNReal.coe_one,one_mul,Path.length_widen] at hf
  have hzval : F.eval z-F.eval D.target ≤ r.length T D.target.height :=
    (le_abs_self _).trans hf
  have hn := r.length_nonneg T D.target.height
  have hu := D.upper
  have hd := D.drop
  refine ⟨z,rfl,hT,q,?_,?_⟩
  all_goals dsimp only [z]; linarith

/-- Actual bounded-length path to a separating tip, even when the witness's
broad-band component was not known to be the seed's component beforehand. -/
lemma path_to_tip (D : F.BandDescent J x ε) (hJI : J ⊆ I)
    (e : M.Point I root) {b : Fin n} {a : ℝ}
    (heJ : e.height ∈ J) (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hx : e.column < x.column ∧ x.column < b)
    (hz : D.target.column < e.column ∨ b < D.target.column) :
    ∃ p : M.Path J x.column e.column, p.length x.height e.height ≤ (1:ℝ)/50+a := by
  have hadj : (M.activeGraph J).Adj e.column b := ⟨e.height,heJ,hs⟩
  have hv := ColumnOrder.chord_separation (M.active_noncrossing J) hadj D.path.word hx hz
  have hcase {v : Fin n} (hv : v ∈ D.path.word.support) (he : v = e.column ∨ v = b) :
      ∃ p : M.Path J x.column e.column, p.length x.height e.height ≤ (1:ℝ)/50+a := by
    obtain ⟨z,hz,hzJ,q,hq,_⟩ := D.column_prefix hJI hv
    obtain ⟨r,hr⟩ := Path.tip_connection hzJ heJ hs hw (hz ▸ he)
    exact ⟨q.append r,(q.length_append_le r x.height z.height e.height).trans (add_le_add hq hr)⟩
  exact hv.elim (fun h => hcase h (Or.inl rfl)) (fun h => hcase h (Or.inr rfl))

/-- The fine near-tip bound is witnessed by a path in the CURRENT broad band.
Only scalar evaluation, not path geometry, uses the old chart. -/
lemma short_path_to_tip (D : F.BandDescent J x ε) (hJI : J ⊆ I)
    (e : M.Point I root) {b : Fin n} {a j : ℝ}
    (heJ : e.height ∈ J) (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hx : e.column < x.column ∧ x.column < b)
    (hz : D.target.column < e.column ∨ b < D.target.column)
    (hlow : F.eval x-j ≤ F.eval e) :
    ∃ p : M.Path J x.column e.column, p.length x.height e.height ≤ j+ε+2*a := by
  have hadj : (M.activeGraph J).Adj e.column b := ⟨e.height,heJ,hs⟩
  have hv := ColumnOrder.chord_separation (M.active_noncrossing J) hadj D.path.word hx hz
  have hcase {v : Fin n} (hv : v ∈ D.path.word.support) (he : v = e.column ∨ v = b) :
      ∃ p : M.Path J x.column e.column, p.length x.height e.height ≤ j+ε+2*a := by
    obtain ⟨z,hz,hzJ,q,_,hdrop⟩ := D.column_prefix hJI hv
    obtain ⟨r,hr⟩ := Path.tip_connection hzJ heJ hs hw (hz ▸ he)
    have hf := F.path_bound (r.widen hJI) ⟨z.height,z.inBand⟩ ⟨e.height,e.inBand⟩
    rw [NNReal.coe_one,one_mul,Path.length_widen] at hf
    have hlo : F.eval e-F.eval z ≤ a := by
      have hn := (neg_le_abs (F.eval z-F.eval e)).trans (hf.trans hr)
      simpa only [neg_sub] using hn
    refine ⟨q.append r,?_⟩
    have hb := q.length_append_le r x.height z.height e.height
    linarith
  exact hv.elim (fun h => hcase h (Or.inl rfl)) (fun h => hcase h (Or.inr rfl))

end BandDescent
end Field
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Point

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- Actual distance field of an old chart. Outside its component we choose
zero only to make a whole-band scalar function; radial sublevels retain the
source's +infinity convention and never include those columns. -/
noncomputable def radialValue (o : M.Point I root) (i : Fin n) (H : I) : ℝ := by
  classical
  exact if hi : (M.activeGraph I).Reachable root i then
    dist o (⟨i,H.val,H.property,hi⟩ : M.Point I root) else 0

lemma radialValue_vertical (o : M.Point I root) (i : Fin n) :
    LipschitzWith 1 (o.radialValue i) := by
  by_cases hi : (M.activeGraph I).Reachable root i
  · apply LipschitzWith.of_dist_le_mul
    intro H T
    simp only [radialValue,dite_eq_left hi,NNReal.coe_one,one_mul]
    exact (dist_dist_dist_le_right o
      (⟨i,H.val,H.property,hi⟩ : M.Point I root)
      (⟨i,T.val,T.property,hi⟩ : M.Point I root)).trans_eq
      (Point.dist_same_column _ _ rfl)
  · apply LipschitzWith.of_dist_le_mul
    intro H T
    simp only [radialValue,dite_eq_right hi,dist_self,NNReal.coe_one,one_mul]
    exact dist_nonneg

lemma radialValue_switch (o : M.Point I root) (i j : Fin n) (H : I)
    (hs : H.val ∈ M.heights i j) : o.radialValue i H = o.radialValue j H := by
  have ha : (M.activeGraph I).Adj i j := ⟨H.val,H.property,hs⟩
  by_cases hi : (M.activeGraph I).Reachable root i
  · have hj := hi.trans ha.reachable
    simp only [radialValue,dite_eq_left hi,dite_eq_left hj]
    let x : M.Point I root := ⟨i,H.val,H.property,hi⟩
    let y : M.Point I root := ⟨j,H.val,H.property,hj⟩
    have hz : dist x y = 0 := by
      apply le_antisymm _ dist_nonneg
      simpa only [x,y,sub_self,abs_zero,add_zero] using x.dist_le_switch y H.property hs
    exact PseudoMetricSpace.dist_eq_of_dist_zero o hz
  · have hj : ¬(M.activeGraph I).Reachable root j := by
      intro hj
      exact hi (hj.trans ha.symm.reachable)
    simp only [radialValue,dite_eq_right hi,dite_eq_right hj]

noncomputable def radialField (o : M.Point I root) : M.Field I 1 where
  value := o.radialValue
  vertical := o.radialValue_vertical
  switch := o.radialValue_switch

@[simp] lemma radialField_eval (o x : M.Point I root) : o.radialField.eval x = dist o x := by
  simp only [Field.eval,radialField,radialValue,dite_eq_left x.reachable]

lemma sublevel_link_preconnected (hI : IsClosed I) (o : M.Point I root)
    (H : ℝ) (hH : H ∈ I) (t : ℝ) :
    (M.link.induce (o.sublevel H hH t)).Preconnected := by
  intro x y
  obtain ⟨p⟩ := o.sublevel_preconnected hI H hH t x y
  let f : (M.activeGraph I).induce (o.sublevel H hH t) →g
      M.link.induce (o.sublevel H hH t) :=
    { toFun := id, map_rel' := fun {_ _} h => M.active_subgraph I h }
  exact ⟨p.map f⟩

/-- The actual target of each almost-descending broad-band path is a member
of the old-distance low sublevel. Width is used only for the broad band J. -/
lemma descent_target_low (o w x : M.Point I root) (hJI : J ⊆ I)
    {ε a B δ : ℝ} (D : o.radialField.BandDescent J x ε) {H : ℝ} (hHJ : H ∈ J)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hclose : dist o x ≤ dist o w+B)
    (hsmall : B+ε+a < (1:ℝ)/100000-δ) :
    D.target.column ∈ o.sublevel H (hJI hHJ) (dist o w-δ) := by
  rw [o.mem_sublevel_iff D.target H (hJI hHJ)]
  have hd := D.drop
  rw [radialField_eval,radialField_eval] at hd
  have hv := D.target.dist_withHeight H (hJI hHJ)
  have hv' : dist D.target (D.target.withHeight H (hJI hHJ)) ≤ a := by
    rw [hv]
    exact hw _ D.target_in _ hHJ
  have ht := dist_triangle o D.target (D.target.withHeight H (hJI hHJ))
  have hl := D.lower
  linarith

/-- The same old-distance sublevel misses EVERY visited column of a short
center path. This establishes the manuscript's avoidance condition rather
than postulating it of a chosen set. -/
lemma short_path_avoids_low (o w c : M.Point I root) (hJI : J ⊆ I)
    {a A δ : ℝ} {H : ℝ} (hHJ : H ∈ J)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hcJ : c.height ∈ J) (hcw : dist c w ≤ A) (hsmall : 2*A+a < δ)
    {v : Fin n} (p : M.Path J c.column v) {T : ℝ}
    (hp : p.length c.height T ≤ A) :
    ∀ k ∈ p.word.support, k ∉ o.sublevel H (hJI hHJ) (dist o w-δ) := by
  intro k hk hlow
  obtain ⟨U,hU,hu⟩ := p.trace_on_column hcJ hk
  obtain ⟨z,hzk,hzU,hcz⟩ := c.point_on_trace hJI p hU hu
  have hl : dist o (z.withHeight H (hJI hHJ)) ≤ dist o w-δ := by
    exact (o.mem_sublevel_iff z H (hJI hHJ) _).mp (hzk.symm ▸ hlow)
  have hz : dist z (z.withHeight H (hJI hHJ)) ≤ a := by
    rw [z.dist_withHeight,hzU]
    exact hw _ hU _ hHJ
  have hzw : dist w z ≤ 2*A := by
    have ht := dist_triangle w c z
    rw [dist_comm w c] at ht
    linarith
  have ht₁ := dist_triangle o (z.withHeight H (hJI hHJ)) z
  have ht₂ := dist_triangle o z w
  rw [dist_comm (z.withHeight H (hJI hHJ)) z] at ht₁
  rw [dist_comm z w] at ht₂
  linarith

end PlanarL1.Columns.Model.Point

namespace PlanarL1.Columns.Model.Field

variable {n : ℕ} {M : Model n} {I J K : Set ℝ} {root : Fin n}

lemma BandDescent.partner_outside_tip {F : M.Field I 1} {ε a A : ℝ}
    (x y e : M.Point I root) (D : F.BandDescent K y ε) (hKI : K ⊆ I)
    {b : Fin n} (heK : e.height ∈ K) (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (hz : D.target.column < e.column ∨ b < D.target.column)
    (hxy : 1 ≤ dist x y) (hxe : dist x e ≤ A) (hsmall : (1:ℝ)/50+a+A < 1) :
    y.column < e.column ∨ b < y.column := by
  by_contra h
  have hle : e.column ≤ y.column ∧ y.column ≤ b := by push Not at h; exact h
  have hd : ∃ p : M.Path K y.column e.column,
      p.length y.height e.height ≤ (1:ℝ)/50+a := by
    by_cases hy : y.column = e.column
    · obtain ⟨p,hp⟩ := Path.tip_connection D.start_in heK hs hw (Or.inl hy)
      exact ⟨p,by linarith⟩
    by_cases hy' : y.column = b
    · obtain ⟨p,hp⟩ := Path.tip_connection D.start_in heK hs hw (Or.inr hy')
      exact ⟨p,by linarith⟩
    exact D.path_to_tip hKI e heK hs hw
      ⟨lt_of_le_of_ne hle.1 (Ne.symm hy),lt_of_le_of_ne hle.2 hy'⟩ hz
  obtain ⟨p,hp⟩ := hd
  have hd := y.distance_le e (p.widen hKI)
  rw [Path.length_widen] at hd
  change dist y e ≤ _ at hd
  have ht := dist_triangle x e y
  rw [dist_comm e y] at ht
  linarith

/-- The skipped-seed estimate keeps the old chart, broad current band and
narrow center-path band distinct. Its conclusion contains an ACTUAL broad-band
path to the trace, not just a distance in the larger old chart. -/
lemma skipped_seed_broad_path (F : M.Field I 1)
    {S : Set (Fin n)} (hS : (M.link.induce S).Preconnected)
    {cut : Fin n} (hcut : cut ∈ S) (hmin : ∀ v, cut ≤ v)
    (hJK : J ⊆ K) (hKI : K ⊆ I) {a A j ε : ℝ}
    (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (c x y : M.Point I root) (Dx : F.BandDescent K x ε) (Dy : F.BandDescent K y ε)
    (hxS : Dx.target.column ∈ S) (hyS : Dy.target.column ∈ S)
    (hxy : 1 ≤ dist x y) (hcx : dist c x ≤ A) (hA : 2*A ≤ 1)
    (hsmall : (1:ℝ)/50+a+2*A < 1) (hretain : F.NoLowTip x y J j)
    {v : Fin n} (p : M.Path J c.column v) {H : ℝ} (hp : p.length c.height H ≤ A)
    (havoid : ∀ k ∈ p.word.support, k ∉ S) (hskip : ColumnOrder.JumpsAcross x.column p.word) :
    ∃ e : M.Point I root, e.height ∈ J ∧ (e.column,e.height) ∈ p.trace c.height H ∧
      ∃ q : M.Path K x.column e.column, q.length x.height e.height ≤ j+ε+2*a := by
  obtain ⟨d,hd,hcross⟩ := hskip
  obtain ⟨T,hT,hs,ht₁,ht₂⟩ := p.dart_on_trace c.height H d hd
  have hcase {l r : Fin n} (hlr : l < x.column ∧ x.column < r)
      (hs : T ∈ M.heights l r) (htl : (l,T) ∈ p.trace c.height H)
      (htr : (r,T) ∈ p.trace c.height H) :
      ∃ e : M.Point I root, e.height ∈ J ∧ (e.column,e.height) ∈ p.trace c.height H ∧
        ∃ q : M.Path K x.column e.column, q.length x.height e.height ≤ j+ε+2*a := by
    have hl : l ∉ S := havoid l (p.trace_column htl)
    have hr : r ∉ S := havoid r (p.trace_column htr)
    have hcl : cut < l := lt_of_le_of_ne (hmin l) (fun h => hl (h ▸ hcut))
    have hgap := ColumnOrder.gap_of_chord M.noncrossing hS
      (M.permitted l r T hs) hl hr hcut (Or.inl hcl)
    obtain ⟨e,hecol,heheight,helen⟩ := c.point_on_trace (hJK.trans hKI) p hT htl
    have hetrace : (e.column,e.height) ∈ p.trace c.height H := by rwa [hecol,heheight]
    have hxe : dist x e ≤ 2*A := by
      have ht := dist_triangle x c e
      rw [dist_comm x c] at ht
      linarith
    have hes : e.height ∈ M.heights e.column r := by rwa [hecol,heheight]
    have heJ : e.height ∈ J := heheight ▸ hT
    have hyp : y.column < e.column ∨ r < y.column := Dy.partner_outside_tip x y e hKI
      (hJK heJ) hes hw (by simpa only [hecol] using hgap _ hyS) hxy hxe hsmall
    have hnc : ¬ Consecutive e.column r := by
      rw [hecol]
      exact not_consecutive_of_between hlr (Or.inl hcl)
    have hlow := (hretain e r heJ hes hnc
      (Or.inl ⟨by simpa only [hecol] using hlr.1,hlr.2,hyp⟩) (Or.inl (hxe.trans hA))).1
    refine ⟨e,heJ,hetrace,Dx.short_path_to_tip hKI e (hJK heJ) hes hw ?_ ?_ hlow⟩
    · simpa only [hecol] using hlr
    · simpa only [hecol] using hgap _ hxS
  rcases hcross with hc | hc
  · exact hcase hc hs ht₁ ht₂
  · exact hcase hc (by rwa [M.symm]) ht₂ ht₁

theorem restricted_broad_packing {W : Type*} [Fintype W]
    (F : M.Field I 1)
    {S : Set (Fin n)} (hS : (M.link.induce S).Preconnected)
    {cut : Fin n} (hcut : cut ∈ S) (hmin : ∀ v, cut ≤ v)
    (hJK : J ⊆ K) (hKI : K ⊆ I) {a A j ε b : ℝ} (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (hA₀ : 0 ≤ A) (hA : 2*A ≤ 1) (hsmall : (1:ℝ)/50+a+2*A < 1)
    (hb : 0 < b) (hpad : j+ε+2*a ≤ b/4) (hvisit : a ≤ j+ε+2*a)
    (c : M.Point K root) (hc : c.height ∈ J) (hcS : c.column ∉ S)
    (seed : W → M.Point K root) (partner : W → M.Point I root)
    (Dx : ∀ w, F.BandDescent K ((seed w).widen hKI) ε) (Dy : ∀ w, F.BandDescent K (partner w) ε)
    (hxS : ∀ w, (Dx w).target.column ∈ S) (hyS : ∀ w, (Dy w).target.column ∈ S)
    (hxy : ∀ w, 1 ≤ dist ((seed w).widen hKI) (partner w))
    (hretain : ∀ w, F.NoLowTip ((seed w).widen hKI) (partner w) J j)
    (cp : ∀ w, M.Path J c.column (seed w).column)
    (hp : ∀ w, (cp w).length c.height (seed w).height ≤ A)
    (havoid : ∀ w k, k ∈ (cp w).word.support → k ∉ S)
    (hsep : ∀ w v, w ≠ v → b ≤ dist (seed w) (seed v)) :
    (Fintype.card W : ℝ) ≤ 2+4*A/b := by
  classical
  let endpoint : Option W → M.Point K root := Option.elim' c seed
  let path : ∀ w : Option W, M.Path J c.column (endpoint w).column := fun w =>
    Option.rec (.nil c.column) cp w
  have hlen : ∀ w, (path w).length c.height (endpoint w).height ≤ A := by
    intro w
    cases w with
    | none => simpa only [path,endpoint,Option.elim',Path.length,sub_self,abs_zero] using hA₀
    | some w => exact hp w
  have hav : ∀ w k, k ∈ (path w).word.support → k ∉ S := by
    intro w k hk
    cases w with
    | none =>
      have he : k = c.column := by
        change k ∈ [c.column] at hk
        exact List.mem_singleton.mp hk
      exact he ▸ hcS
    | some w => exact havoid w k hk
  obtain ⟨l,_,hl⟩ := Finset.exists_min_image (Finset.univ : Finset (Option W))
    (fun w => (endpoint w).column) ⟨none,Finset.mem_univ _⟩
  obtain ⟨r,_,hr⟩ := Finset.exists_max_image (Finset.univ : Finset (Option W))
    (fun w => (endpoint w).column) ⟨none,Finset.mem_univ _⟩
  let select : Fin 2 → Option W := ![l,r]
  let paths (s : Fin 2) := path (select s)
  have hone (w : W) (v : Option W)
      (hv : (seed w).column ∈ (path v).word.support ∨
        ColumnOrder.JumpsAcross (seed w).column (path v).word) :
      ∃ e : M.Point K root, (e.column,e.height) ∈ (path v).trace c.height (endpoint v).height ∧
        dist (seed w) e ≤ j+ε+2*a := by
    rcases hv with hv | hv
    · obtain ⟨e,he,hnear⟩ := visited_seed_near_trace hJK hw c (seed w) hc (path v) hv
      exact ⟨e,he,hnear.trans hvisit⟩
    · have hcs : dist c (seed w) ≤ A := by
        have hd := c.distance_le (seed w) ((cp w).widen hJK)
        rw [Path.length_widen] at hd
        exact hd.trans (hp w)
      obtain ⟨e,heJ,he,q,hq⟩ := F.skipped_seed_broad_path hS hcut hmin hJK hKI hw
        (c.widen hKI) ((seed w).widen hKI) (partner w) (Dx w) (Dy w) (hxS w) (hyS w)
        (hxy w) ((c.dist_widen_le (seed w) hKI).trans hcs) hA hsmall (hretain w)
        (path v) (hlen v) (hav v) hv
      let eb : M.Point K root := ⟨e.column,e.height,hJK heJ,
        (seed w).reachable.trans q.word.reachable⟩
      exact ⟨eb,he,((seed w).distance_le eb q).trans hq⟩
  have hprox : ∀ w : W, ∃ (s : Fin 2) (e : M.Point K root),
      (e.column,e.height) ∈ (paths s).trace c.height (endpoint (select s)).height ∧
        dist (seed w) e ≤ j+ε+2*a := by
    intro w
    have h := ColumnOrder.extreme_words (path l).word (path r).word
      (hl (some w) (Finset.mem_univ _)) (hr (some w) (Finset.mem_univ _))
    rcases h with h | h
    · obtain ⟨e,he,hnear⟩ := hone w l h
      exact ⟨0,e,by simpa only [paths,select,Matrix.cons_val_zero] using he,hnear⟩
    · obtain ⟨e,he,hnear⟩ := hone w r h
      exact ⟨1,e,by simpa only [paths,select,Matrix.cons_val_one,Matrix.cons_val_zero] using he,hnear⟩
  choose side near htrace hnear using hprox
  exact near_two_traces_count hJK hb hA₀ hpad (fun _ => c.column)
    (fun s => (endpoint (select s)).column) paths (fun _ => c.height)
    (fun s => (endpoint (select s)).height) (fun s => hlen (select s))
    seed near side htrace hsep hnear


end PlanarL1.Columns.Model.Field


namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {e : Equiv.Perm (Fin n)}
  {hnc : ColumnOrder.Noncrossing (M.link.comap e)}
  {hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j}
  {J I : Set ℝ} {root : Fin n}

def Point.label (x : M.Point J (e root)) : (M.relabel e hnc hcon).Point J root where
  column := e.symm x.column
  height := x.height
  inBand := x.inBand
  reachable := by
    obtain ⟨p⟩ := x.reachable
    obtain ⟨q,_⟩ := Path.exists_word p
    simpa only [e.symm_apply_apply] using
      (q.label (hnc := hnc) (hcon := hcon)).word.reachable

@[simp] lemma Point.unlabel_label (x : M.Point J (e root)) :
    (x.label (hnc := hnc) (hcon := hcon)).unlabel = x := by
  cases x
  simp only [Point.label,Point.unlabel,e.apply_symm_apply]

@[simp] lemma Point.label_unlabel (x : (M.relabel e hnc hcon).Point J root) :
    x.unlabel.label = x := by
  cases x
  simp only [Point.label,Point.unlabel,e.symm_apply_apply]

lemma Point.dist_label (x y : M.Point J (e root)) :
    dist (x.label (hnc := hnc) (hcon := hcon)) y.label = dist x y := by
  rw [← Point.dist_unlabel,Point.unlabel_label,Point.unlabel_label]

noncomputable def Point.labelEquiv : M.Point J (e root) ≃ (M.relabel e hnc hcon).Point J root where
  toFun := Point.label
  invFun := Point.unlabel
  left_inv := Point.unlabel_label
  right_inv := Point.label_unlabel

def Field.label {L : NNReal} (F : M.Field I L) : (M.relabel e hnc hcon).Field I L where
  value := fun i => F.value (e i)
  vertical := fun i => F.vertical (e i)
  switch := fun i j H h => F.switch (e i) (e j) H h

@[simp] lemma Field.eval_label {L : NNReal} (F : M.Field I L) (x : M.Point I (e root)) :
    (F.label (hnc := hnc) (hcon := hcon)).eval x.label = F.eval x := by
  simp only [Field.eval,Field.label,Point.label,e.apply_symm_apply]

@[simp] lemma Field.eval_unlabel {L : NNReal} (F : M.Field I L)
    (x : (M.relabel e hnc hcon).Point I root) :
    (F.label (hnc := hnc) (hcon := hcon)).eval x = F.eval x.unlabel := rfl

noncomputable def Field.BandDescent.label {F : M.Field I 1} {x : M.Point I (e root)} {ε : ℝ}
    (D : F.BandDescent J x ε) :
    (F.label (hnc := hnc) (hcon := hcon)).BandDescent J x.label ε where
  start_in := D.start_in
  target := D.target.label
  target_in := D.target_in
  path := D.path.label
  shortest := by
    intro p
    let q := p.unlabel
    have he₁ : e (x.label (hnc := hnc) (hcon := hcon)).column = x.column := e.apply_symm_apply _
    have he₂ : e (D.target.label (hnc := hnc) (hcon := hcon)).column = D.target.column := e.apply_symm_apply _
    have hd := D.shortest (q.cast he₁ he₂)
    rw [Path.length_cast] at hd
    dsimp only [q] at hd
    rw [Path.length_unlabel] at hd
    simpa only [Path.length_label,Point.label] using hd
  lower := by simpa only [Path.length_label,Point.label] using D.lower
  upper := by simpa only [Path.length_label,Point.label] using D.upper
  drop := by
    simpa only [Path.length_label,Field.eval,Field.label,Point.label,e.apply_symm_apply] using D.drop

end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Field

/-- Strictly opposite sides of an unoriented circular chord. -/
def CircularTipSeparates {n : ℕ} (a b x y : Fin n) : Prop :=
  TipSeparates a b x y ∨ TipSeparates b a x y

lemma circularTip_rotate {n : ℕ} (a b x y : Fin (n+1)) :
    CircularTipSeparates (finRotate (n+1) a) (finRotate (n+1) b)
      (finRotate (n+1) x) (finRotate (n+1) y) ↔ CircularTipSeparates a b x y := by
  have hval (i : Fin (n+1)) : (finRotate (n+1) i).val =
      if i.val = n then 0 else i.val+1 := by
    split_ifs with hi
    · have he : i = Fin.last n := Fin.ext hi
      rw [he,finRotate_last]
      rfl
    · exact coe_finRotate_of_ne_last (fun h => hi (congrArg Fin.val h))
  unfold CircularTipSeparates TipSeparates
  simp only [Fin.lt_def,hval]
  split_ifs <;> omega

lemma circularTip_iterate {n : ℕ} (k : ℕ) (a b x y : Fin (n+1)) :
    CircularTipSeparates ((finRotate (n+1))^[k] a) ((finRotate (n+1))^[k] b)
      ((finRotate (n+1))^[k] x) ((finRotate (n+1))^[k] y) ↔ CircularTipSeparates a b x y := by
  induction k generalizing a b x y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply,
      Function.iterate_succ_apply,Function.iterate_succ_apply,ih,circularTip_rotate]

lemma circularTip_cycle {n : ℕ} (c a b x y : Fin (n+1)) :
    CircularTipSeparates (finCycle c a) (finCycle c b) (finCycle c x) (finCycle c y) ↔
      CircularTipSeparates a b x y := by
  rw [finCycle_eq_finRotate_iterate]
  exact circularTip_iterate c.val a b x y

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {e : Equiv.Perm (Fin n)}
  {hnc : ColumnOrder.Noncrossing (M.link.comap e)}
  {hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j}
  {J I : Set ℝ} {root : Fin n}

@[simp] lemma Point.widen_label (x : M.Point J (e root)) (hJI : J ⊆ I) :
    (x.label (hnc := hnc) (hcon := hcon)).widen hJI = (x.widen hJI).label := rfl

lemma Path.support_word_label {i j : Fin n} (p : M.Path J i j) :
    (p.label (hnc := hnc) (hcon := hcon)).word.support = p.word.support.map e.symm := by
  induction p with
  | nil => rfl
  | cons H hH hs p ih =>
    change _ :: p.label.word.support = _ :: p.word.support.map e.symm
    rw [ih]

namespace Field

/-- Absence of a low separating tip is intrinsically circular: reversing
the listed chord endpoints does not change the exclusion test. -/
def NoLowCircular (F : M.Field I 1) (x y : M.Point I root) (J : Set ℝ) (j : ℝ) : Prop :=
  ∀ (v : M.Point I root) (b : Fin n), v.height ∈ J →
    v.height ∈ M.heights v.column b → ¬ Consecutive v.column b →
    CircularTipSeparates v.column b x.column y.column →
    (dist x v ≤ 1 ∨ dist y v ≤ 1) →
    F.eval x-j ≤ F.eval v ∧ F.eval y-j ≤ F.eval v

lemma NoLowCircular.toNoLowTip {F : M.Field I 1} {x y : M.Point I root} {j : ℝ}
    (h : F.NoLowCircular x y J j) : F.NoLowTip x y J j := by
  intro v b hJ hs hc ht hd
  exact h v b hJ hs hc (Or.inl ht) hd

lemma NoLowCircular.label {F : M.Field I 1} {x y : M.Point I (e root)} {j : ℝ}
    (h : F.NoLowCircular x y J j)
    (hcirc : ∀ a b v w, CircularTipSeparates (e a) (e b) (e v) (e w) ↔
      CircularTipSeparates a b v w) :
    (F.label (hnc := hnc) (hcon := hcon)).NoLowCircular x.label y.label J j := by
  intro v b hvJ hvs hvc hvsep hvdist
  have h₁ : dist x v.unlabel = dist x.label v := by
    simpa only [Point.unlabel_label] using
      (Point.dist_unlabel (x.label (hnc := hnc) (hcon := hcon)) v)
  have h₂ : dist y v.unlabel = dist y.label v := by
    simpa only [Point.unlabel_label] using
      (Point.dist_unlabel (y.label (hnc := hnc) (hcon := hcon)) v)
  have hsep := (hcirc v.column b x.label.column y.label.column).mpr hvsep
  simp only [Point.label,e.apply_symm_apply] at hsep
  have hc : ¬Consecutive v.unlabel.column (e b) := fun hh => hvc ((hcon _ _).mp hh)
  have hh := h v.unlabel (e b) hvJ hvs hc hsep (by simpa only [h₁,h₂] using hvdist)
  simpa only [Field.eval_label,Field.eval_unlabel,Point.unlabel_label] using hh

end Field
end PlanarL1.Columns.Model

namespace PlanarL1.ColumnOrder

lemma preconnected_comap {n : ℕ} {G : SimpleGraph (Fin n)} {S : Set (Fin n)}
    (hS : (G.induce S).Preconnected) (e : Equiv.Perm (Fin n)) :
    ((G.comap e).induce (e ⁻¹' S)).Preconnected := by
  let f : G.induce S →g (G.comap e).induce (e ⁻¹' S) :=
    { toFun := fun v => ⟨e.symm v.val,by simpa only [Set.mem_preimage,e.apply_symm_apply] using v.property⟩
      map_rel' := fun {_ _} h => by
        change G.Adj _ _ at h
        change G.Adj (e (e.symm _)) (e (e.symm _))
        simpa only [e.apply_symm_apply, Function.Embedding.subtype_apply] using h }
  intro x y
  obtain ⟨p⟩ := hS ⟨e x.val,x.property⟩ ⟨e y.val,y.property⟩
  have hx : f ⟨e x.val,x.property⟩ = x := by
    apply Subtype.ext
    exact e.symm_apply_apply _
  have hy : f ⟨e y.val,y.property⟩ = y := by
    apply Subtype.ext
    exact e.symm_apply_apply _
  exact ⟨(p.map f).copy hx hy⟩

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model.Field

/-- Restricted geometric packing with NO privileged linear cut. The proof
rotates the actual model, fields, paths and all distance data at a low column.
The result measures separation in the BROAD current intrinsic component. -/
theorem circular_broad_packing {n : ℕ} {M : Model (n+1)} {I J K : Set ℝ} {root : Fin (n+1)}
    {W : Type*} [Fintype W] (F : M.Field I 1)
    {S : Set (Fin (n+1))} (hS : (M.link.induce S).Preconnected)
    {cut : Fin (n+1)} (hcut : cut ∈ S)
    (hJK : J ⊆ K) (hKI : K ⊆ I) {a A j ε b : ℝ}
    (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (hA₀ : 0 ≤ A) (hA : 2*A ≤ 1) (hsmall : (1:ℝ)/50+a+2*A < 1)
    (hb : 0 < b) (hpad : j+ε+2*a ≤ b/4) (hvisit : a ≤ j+ε+2*a)
    (c : M.Point K root) (hc : c.height ∈ J) (hcS : c.column ∉ S)
    (seed : W → M.Point K root) (partner : W → M.Point I root)
    (Dx : ∀ w, F.BandDescent K ((seed w).widen hKI) ε)
    (Dy : ∀ w, F.BandDescent K (partner w) ε)
    (hxS : ∀ w, (Dx w).target.column ∈ S) (hyS : ∀ w, (Dy w).target.column ∈ S)
    (hxy : ∀ w, 1 ≤ dist ((seed w).widen hKI) (partner w))
    (hretain : ∀ w, F.NoLowCircular ((seed w).widen hKI) (partner w) J j)
    (cp : ∀ w, M.Path J c.column (seed w).column)
    (hp : ∀ w, (cp w).length c.height (seed w).height ≤ A)
    (havoid : ∀ w k, k ∈ (cp w).word.support → k ∉ S)
    (hsep : ∀ w v, w ≠ v → b ≤ dist (seed w) (seed v)) :
    (Fintype.card W : ℝ) ≤ 2+4*A/b := by
  let e := finCycle cut
  obtain ⟨r,rfl⟩ := e.surjective root
  let hnc := ColumnOrder.noncrossing_comap_cycle M.noncrossing cut
  let hcon := consecutive_cycle cut
  let N := M.relabel e hnc hcon
  let F' : N.Field I 1 := F.label
  let c' : N.Point K r := c.label
  let seed' (w : W) : N.Point K r := (seed w).label
  let partner' (w : W) : N.Point I r := (partner w).label
  let dy' (w : W) : F'.BandDescent K (partner' w) ε := (Dy w).label
  -- Use the explicit transported data, so target membership is not lost
  -- behind a propositional existence witness.
  let dx' (w : W) : F'.BandDescent K ((seed' w).widen hKI) ε := (Dx w).label
  have hzero : e 0 = cut := by simp only [e,finCycle_apply,zero_add]
  refine F'.restricted_broad_packing (S := e ⁻¹' S)
    (ColumnOrder.preconnected_comap hS e) (cut := 0) (by simpa only [Set.mem_preimage,hzero] using hcut)
    (fun v => Fin.zero_le v) hJK hKI hw hA₀ hA hsmall hb hpad hvisit c' hc
    (by simpa only [c',Point.label,Set.mem_preimage,e.apply_symm_apply] using hcS)
    seed' partner' dx' dy' ?_ ?_ ?_ ?_ (fun w => (cp w).label) ?_ ?_ ?_
  · intro w
    simpa only [dx',Field.BandDescent.label,Point.label,Set.mem_preimage,e.apply_symm_apply] using hxS w
  · intro w
    simpa only [dy',Field.BandDescent.label,Point.label,Set.mem_preimage,e.apply_symm_apply] using hyS w
  · intro w
    exact (hxy w).trans_eq
      (Point.dist_label (hnc := hnc) (hcon := hcon) ((seed w).widen hKI) (partner w)).symm
  · intro w
    exact ((hretain w).label (hnc := hnc) (hcon := hcon) (circularTip_cycle cut)).toNoLowTip
  · intro w
    simpa only [c',seed',Point.label,Path.length_label] using hp w
  · intro w k hk
    change k ∈ ((cp w).label (hnc := hnc) (hcon := hcon)).word.support at hk
    rw [Path.support_word_label] at hk
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hk
    change e (e.symm v) ∉ S
    simpa only [e.apply_symm_apply] using havoid w v hv
  · intro w v hwv
    exact (hsep w v hwv).trans_eq
      (Point.dist_label (hnc := hnc) (hcon := hcon) (seed w) (seed v)).symm

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model.Field

/-- The low-set and circular-gap hypotheses of geometric packing are DERIVED
from the actual old chart distance and actual witness descents. This is the
band-faithful application of `pack:bound` to surviving seeds. -/
theorem radial_surviving_packing {n : ℕ} {M : Model (n+1)} {I J K : Set ℝ}
    {root : Fin (n+1)} {W : Type*} [Fintype W]
    (hI : IsClosed I) (hJK : J ⊆ K) (hKI : K ⊆ I)
    {a A E δ j ε b : ℝ} (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (hA₀ : 0 ≤ A) (hA : 2*A ≤ 1) (hE : 0 ≤ E)
    (hsmall : (1:ℝ)/50+a+2*A < 1)
    (hlow : 2*A+E+ε+a < (1:ℝ)/100000-δ) (hhigh : 2*A+a < δ)
    (hb : 0 < b) (hpad : j+ε+2*a ≤ b/4) (hvisit : a ≤ j+ε+2*a)
    (o : M.Point I root) (c : M.Point K root) (hc : c.height ∈ J)
    (seed : W → M.Point K root) (partner : W → M.Point I root)
    (hseed : ∀ w, (seed w).height ∈ J)
    (Dx : ∀ w, o.radialField.BandDescent K ((seed w).widen hKI) ε)
    (Dy : ∀ w, o.radialField.BandDescent K (partner w) ε)
    (hxy : ∀ w, 1 ≤ dist ((seed w).widen hKI) (partner w))
    (hfield : ∀ w, |dist o (partner w)-dist o ((seed w).widen hKI)| ≤ E)
    (hretain : ∀ w, o.radialField.NoLowCircular ((seed w).widen hKI) (partner w) J j)
    (cp : ∀ w, M.Path J c.column (seed w).column)
    (hp : ∀ w, (cp w).length c.height (seed w).height ≤ A)
    (hsep : ∀ w v, w ≠ v → b ≤ dist (seed w) (seed v)) :
    (Fintype.card W : ℝ) ≤ 2+4*A/b := by
  classical
  by_cases hn : Nonempty W
  · obtain ⟨w₀⟩ := hn
    let star := (seed w₀).widen hKI
    let H := (seed w₀).height
    have hHJ : H ∈ J := hseed w₀
    have hHI : H ∈ I := hKI (hJK hHJ)
    let S := o.sublevel H hHI (dist o star-δ)
    have hcs (w : W) : dist (c.widen hKI) ((seed w).widen hKI) ≤ A := by
      apply (c.dist_widen_le (seed w) hKI).trans
      exact (c.distance_le (seed w) ((cp w).widen hJK)).trans
        (by simpa only [Path.length_widen] using hp w)
    have hclose (w : W) : dist o ((seed w).widen hKI) ≤ dist o star+2*A+E := by
      have h₁ := dist_triangle o star (c.widen hKI)
      have h₂ := dist_triangle o (c.widen hKI) ((seed w).widen hKI)
      have hc₀ := hcs w₀
      change dist (c.widen hKI) star ≤ A at hc₀
      rw [dist_comm (c.widen hKI) star] at hc₀
      linarith [hcs w]
    have hclosePartner (w : W) : dist o (partner w) ≤ dist o star+(2*A+E) := by
      have h₁ := dist_triangle o star (c.widen hKI)
      have h₂ := dist_triangle o (c.widen hKI) ((seed w).widen hKI)
      have hc₀ := hcs w₀
      change dist (c.widen hKI) star ≤ A at hc₀
      rw [dist_comm (c.widen hKI) star] at hc₀
      have hf := (abs_le.mp (hfield w)).2
      linarith [hcs w]
    have hxS (w : W) : (Dx w).target.column ∈ S := by
      exact o.descent_target_low star ((seed w).widen hKI) hKI (Dx w) (hJK hHJ) hw
        (by linarith [hclose w]) hlow
    have hyS (w : W) : (Dy w).target.column ∈ S := by
      exact o.descent_target_low star (partner w) hKI (Dy w) (hJK hHJ) hw (hclosePartner w) hlow
    have hav (w : W) : ∀ k ∈ (cp w).word.support, k ∉ S := by
      exact o.short_path_avoids_low star (c.widen hKI) (hJK.trans hKI) hHJ
        (fun s hs t ht => hw s (hJK hs) t (hJK ht)) hc (hcs w₀) hhigh (cp w) (hp w)
    exact o.radialField.circular_broad_packing (o.sublevel_link_preconnected hI H hHI _)
      (hxS w₀) hJK hKI hw hA₀ hA hsmall hb hpad hvisit c hc
      (hav w₀ c.column (cp w₀).word.start_mem_support)
      seed partner Dx Dy hxS hyS hxy hretain cp hp hav hsep
  · have : IsEmpty W := not_nonempty_iff.mp hn
    simp only [Fintype.card_of_isEmpty,Nat.cast_zero]
    positivity

end PlanarL1.Columns.Model.Field



end

end OAI
