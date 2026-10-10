import OAI.Computability.Superstring.CollectionCode

namespace OAI

namespace Superstring.BitCode
variable {α : Type}
def keySort (xs : List (ℕ × α)) : List (ℕ × α) :=
  (List.range ((xs.map Prod.fst).foldl max 0+1)).flatMap fun k => xs.filter (fun x => equal x.1 k)

theorem initial_le_maxFold (xs : List ℕ) (a : ℕ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih _)

theorem le_maxFold {x : ℕ} (xs : List ℕ) (a : ℕ) (hx : x ∈ xs) : x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hh
    · exact (le_max_right a x).trans (initial_le_maxFold ys _)
    · exact ih _ hh

theorem mem_keySort (xs : List (ℕ × α)) (x : ℕ × α) : x ∈ keySort xs ↔ x ∈ xs := by
  constructor
  · intro h
    obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp h
    exact List.mem_of_mem_filter hk
  · intro h
    apply List.mem_flatMap.mpr
    refine ⟨x.1,List.mem_range.mpr ?_,List.mem_filter.mpr ⟨h,by simp [equal]⟩⟩
    have := le_maxFold (xs.map Prod.fst) 0 (List.mem_map.mpr ⟨x,h,rfl⟩)
    omega

theorem pairwise_keySort (xs : List (ℕ × α)) :
    (keySort xs).Pairwise (fun x y => x.1 ≤ y.1) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro k _
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj _
    have hx : (xs.filter (fun x => equal x.1 k))[i].1 = k :=
      of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hi)).2
    have hy : (xs.filter (fun x => equal x.1 k))[j].1 = k :=
      of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hj)).2
    omega
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij x hx y hy
    have hx := (List.mem_filter.mp hx).2
    have hy := (List.mem_filter.mp hy).2
    simp only [equal,decide_eq_true_eq,List.getElem_range] at hx hy
    omega

variable [Coded α]
@[fun_prop] theorem poly_keySort : Poly (keySort (α:=α)) := by
  unfold keySort
  change Poly (fun xs : List (ℕ × α) => ((List.range ((xs.map Prod.fst).foldl max 0+1)).map
    (fun k => xs.filter (fun x => equal x.1 k))).flatten)
  apply Poly.flatten.comp
  apply Poly.mapFn (f := fun q : List (ℕ × α) × ℕ => q.1.filter (fun x => equal x.1 q.2))
  · exact Poly.filterFn (p := fun q : (List (ℕ × α) × ℕ) × (ℕ × α) => equal q.2.1 q.1.2)
      (by fun_prop) (by fun_prop)
  · have hm : Poly (fun xs : List (ℕ × α) => (xs.map Prod.fst).foldl max 0) :=
      Poly.maxFold.comp (Poly.map Poly.fst)
    fun_prop
end Superstring.BitCode


namespace Superstring.WindowCode
open BitCode Hierarchical WalkCode

def mass (W : List Window) : ℕ := (W.map (fun v => v.1.natAbs+v.2.natAbs)).sum
def windowSort (W : List Window) : List Window :=
  (keySort (W.map (fun v => ((v.1+v.2+(mass W : ℤ)).toNat,v)))).map Prod.snd

theorem mass_bound {W : List Window} {v : Window} (hv : v ∈ W) :
    0 ≤ v.1+v.2+(mass W : ℤ) := by
  have h := List.le_sum_of_mem (List.mem_map.mpr ⟨v,hv,rfl⟩ :
    v.1.natAbs+v.2.natAbs ∈ W.map (fun v => v.1.natAbs+v.2.natAbs))
  change v.1.natAbs+v.2.natAbs ≤ mass W at h
  have h₁ := Int.le_natAbs (a := -v.1)
  have h₂ := Int.le_natAbs (a := -v.2)
  simp only [Int.natAbs_neg] at h₁ h₂
  omega

theorem mem_windowSort (W : List Window) (v : Window) : v ∈ windowSort W ↔ v ∈ W := by
  simp only [windowSort,List.mem_map,mem_keySort]
  constructor
  · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩; exact hy
  · intro hv; exact ⟨_,⟨v,hv,rfl⟩,rfl⟩

theorem ordered_windowSort (W : List Window)
    (hc : ∀ u ∈ W, ∀ v ∈ W, ordered u v ∨ ordered v u) :
    (windowSort W).Pairwise ordered := by
  apply List.pairwise_map.mpr
  apply (pairwise_keySort _).imp_of_mem
  intro x y hx hy hxy
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ((mem_keySort _ _).mp hx)
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ((mem_keySort _ _).mp hy)
  have hn₁ := mass_bound hu
  have hn₂ := mass_bound hv
  dsimp only at hxy ⊢
  rcases hc u hu v hv with hh | hh
  · exact hh
  · rcases hh with ⟨hs,he⟩
    constructor <;> omega

@[fun_prop] theorem poly_mass : Poly mass := by
  unfold mass
  exact Poly.sum.comp (BitCode.Poly.map (f := fun v : Window => v.1.natAbs+v.2.natAbs) (by fun_prop))
@[fun_prop] theorem poly_windowSort : Poly windowSort := by
  unfold windowSort
  apply (BitCode.Poly.map Poly.snd).comp
  apply poly_keySort.comp
  exact Poly.mapFn (f := fun q : List Window × Window =>
      ((q.2.1+q.2.2+(mass q.1 : ℤ)).toNat,q.2)) (by fun_prop) (by fun_prop)

variable {α : Type}
def through (A : ℤ → α) (a b c d : ℤ) (W : List Window) : Walk α :=
  routeList A (a,b) (windowSort W ++ [(c,d)])

theorem through_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (a b c d : ℤ) (W : List Window)
    (hc : ∀ u ∈ W, ∀ v ∈ W, ordered u v ∨ ordered v u)
    (hv : ∀ u ∈ W, u.1 ≤ u.2 ∧ textWord A u.1 u.2 ∈ V)
    (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (ha : textWord A a b ∈ V) (hb : textWord A c d ∈ V)
    (bounds : ∀ u ∈ W, a ≤ u.1 ∧ u.1 ≤ c ∧ b ≤ u.2 ∧ u.2 ≤ d) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A c d),
      Path.points P = through A a b c d W ∧ P.cost = (d-b).toNat ∧
      ∀ u ∈ W, P.Visits (textWord A u.1 u.2) := by
  have ho : ((a,b)::(windowSort W ++ [(c,d)])).Pairwise ordered := by
    apply List.pairwise_cons.mpr
    constructor
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · have hh := bounds u ((mem_windowSort W u).mp hu)
        exact ⟨hh.1,hh.2.2.1⟩
      · have he := List.mem_singleton.mp hu; subst u; exact ⟨hac,hbd⟩
    · apply List.pairwise_append.mpr
      refine ⟨ordered_windowSort W hc,by simp,?_⟩
      intro u hu v hv
      have he := List.mem_singleton.mp hv; subst v
      have hh := bounds u ((mem_windowSort W u).mp hu)
      exact ⟨hh.2.1,hh.2.2.2⟩
  have hvalid : ∀ u ∈ (a,b)::(windowSort W ++ [(c,d)]),
      u.1 ≤ u.2 ∧ textWord A u.1 u.2 ∈ V := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨hab,ha⟩
    · rcases List.mem_append.mp hu with hu | hu
      · exact hv u ((mem_windowSort W u).mp hu)
      · have he := List.mem_singleton.mp hu; subst u; exact ⟨hcd,hb⟩
  obtain ⟨P,hP,hcP,hvP⟩ := routeList_realizes closed A letters (a,b) _ ho hvalid
  refine ⟨P.copy rfl (by simp only [List.getLastD_concat]),?_,?_,?_⟩
  · simpa only [points_copy,through] using hP
  · simpa only [Hierarchical.Path.cost_copy,List.getLastD_concat] using hcP
  · intro u hu
    exact (Hierarchical.Path.visits_copy ..).mpr
      (hvP u (List.mem_cons_of_mem _ (List.mem_append_left _ ((mem_windowSort W u).mpr hu))))

variable [Inhabited α] [Coded α]
@[fun_prop] theorem poly_through : Poly (fun q : List α × ℤ × ℤ × ℤ × ℤ × List Window =>
    through (PeriodWord.text q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold through
  exact poly_routeList.comp (f := fun q : List α × ℤ × ℤ × ℤ × ℤ × List Window =>
    (q.1,(q.2.1,q.2.2.1),windowSort q.2.2.2.2.2 ++ [(q.2.2.2.1,q.2.2.2.2.1)])) (by fun_prop)
end Superstring.WindowCode


namespace Superstring.BitCode.Poly
variable {α : Type} [Coded α]
@[fun_prop] theorem getLastDWith : Poly (fun q : List α × α => q.1.getLastD q.2) := by
  have h : Poly (fun q : List α × α => q.1.reverse.headD q.2) := by fun_prop
  simpa only [List.headD_eq_head?_getD,List.head?_reverse,List.getLastD_eq_getLast?] using h
end Superstring.BitCode.Poly

namespace Superstring.WindowCode
open Hierarchical WalkCode BitCode
variable {α : Type}

theorem ordered_getLastD (W : List Window) (d : Window) (ho : W.Pairwise ordered) :
    ∀ v ∈ W, ordered v (W.getLastD d) := by
  induction W generalizing d with
  | nil => simp
  | cons w W ih =>
    rw [List.getLastD_cons]
    intro v hv
    obtain ⟨hw,hW⟩ := List.pairwise_cons.mp ho
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      rcases List.mem_cons.mp (List.getLastD_mem_cons (a:=w) (l:=W)) with he | he
      · rw [he]; exact ⟨le_rfl,le_rfl⟩
      · exact hw _ he
    · exact ih w hW v hv

def hostExcursion (A : ℤ → α) (q : ℕ) (a b e : ℤ) (W : List Window) : Walk α :=
  let last := (windowSort W).getLastD (a,b)
  join (join (up A a e b) (through A a b last.1 last.2 W))
    (route A last.1 last.2 (a+q) (e+q))

theorem hostExcursion_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (q p : ℕ)
    (hp : 0 < p) (per : Function.Periodic A (q : ℤ))
    (a b e : ℤ) (he : a+p < e) (heb : e ≤ b) (hR : textWord A a b ∈ V)
    (hshort : b < a+q+p) (W : List Window)
    (hc : ∀ u ∈ W, ∀ v ∈ W, ordered u v ∨ ordered v u)
    (hb : ∀ v ∈ W, a ≤ v.1 ∧ v.1 ≤ a+q ∧ v.1 ≤ v.2 ∧ b ≤ v.2 ∧ v.2 < a+q+p)
    (hv : ∀ v ∈ W, textWord A v.1 v.2 ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A a e) (textWord A a e),
      Path.points P = hostExcursion A q a b e W ∧ P.cost = q ∧
      P.Visits (textWord A a b) ∧ (∀ d, e ≤ d → d ≤ b → P.Visits (textWord A a d)) ∧
      (∀ v ∈ W, P.Visits (textWord A v.1 v.2)) ∧
      ∃ w, P.Visits w ∧ w.length < p := by
  let last := (windowSort W).getLastD (a,b)
  have hm : last = (a,b) ∨ last ∈ W := by
    rcases List.mem_cons.mp (List.getLastD_mem_cons (a:=(a,b)) (l:=windowSort W)) with hh | hh
    · exact Or.inl hh
    · exact Or.inr ((mem_windowSort W last).mp hh)
  have hlast : a ≤ last.1 ∧ last.1 ≤ a+q ∧ last.1 ≤ last.2 ∧ b ≤ last.2 ∧ last.2 < a+q+p := by
    rcases hm with hh | hh
    · rw [hh]; exact ⟨le_rfl,by omega,by omega,le_rfl,hshort⟩
    · exact hb _ hh
  have hLv : textWord A last.1 last.2 ∈ V := by
    rcases hm with hh | hh
    · rw [hh]; exact hR
    · exact hv _ hh
  have hmax : ∀ v ∈ W, ordered v last := by
    intro v hv
    exact ordered_getLastD _ _ (ordered_windowSort W hc) v ((mem_windowSort W v).mpr hv)
  have hae : a ≤ e := by omega
  have hE : textWord A a e ∈ V := closed hR (textWord_infix A le_rfl hae heb)
  obtain ⟨U,hU,hUc,hUv⟩ := up_realizes closed A hae heb hR
  obtain ⟨Q,hQ,hQc,hQv⟩ := through_realizes closed A letters a b last.1 last.2 W hc
    (fun v hv' => ⟨(hb v hv').2.2.1,hv v hv'⟩) (by omega) hlast.2.2.1
    hlast.1 hlast.2.2.2.1 hR hLv
    (fun v hv' => ⟨(hb v hv').1,(hmax v hv').1,(hb v hv').2.2.2.1,(hmax v hv').2⟩)
  have heq := textWord_translate A q per a e
  obtain ⟨D,hD,hDc,_,w,hw,hwlen⟩ := route_realizes closed A letters hlast.2.2.1
    (show a+(q:ℤ) ≤ e+q by omega) hlast.2.1 (show last.2 ≤ e+q by have := hlast.2.2.2.2; omega)
    hLv (heq.symm ▸ hE)
  refine ⟨((U.trans Q).trans D).copy rfl heq,?_,?_,?_,?_,?_,w,?_,?_⟩
  · simp only [points_copy,Path.points,hU,hQ,hD,hostExcursion,last]
  · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hUc,hQc,hDc]
    have := hlast.2.2.2.1
    have := hlast.2.2.2.2
    omega
  · exact (Hierarchical.Path.visits_copy ..).mpr (Or.inl (Or.inl (Hierarchical.Path.visits_end U)))
  · intro d hd hd'
    exact (Hierarchical.Path.visits_copy ..).mpr (Or.inl (Or.inl (hUv d hd hd')))
  · intro v hv
    exact (Hierarchical.Path.visits_copy ..).mpr (Or.inl (Or.inr (hQv v hv)))
  · exact (Hierarchical.Path.visits_copy ..).mpr (Or.inr hw)
  · have := hlast.2.2.2.2
    omega

variable [Inhabited α] [Coded α]
@[fun_prop] theorem poly_hostExcursion : Poly (fun t : List α × ℕ × ℤ × ℤ × ℤ × List Window =>
    hostExcursion (PeriodWord.text t.1) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2) := by
  unfold hostExcursion
  dsimp only
  have hlast : Poly (fun t : List α × ℕ × ℤ × ℤ × ℤ × List Window =>
      (windowSort t.2.2.2.2.2).getLastD (t.2.2.1,t.2.2.2.1)) :=
    Poly.getLastDWith.comp (f := fun t : List α × ℕ × ℤ × ℤ × ℤ × List Window =>
      (windowSort t.2.2.2.2.2,(t.2.2.1,t.2.2.2.1))) (by fun_prop)
  have hthrough := poly_through.comp
    (f := fun t : List α × ℕ × ℤ × ℤ × ℤ × List Window =>
      (t.1,t.2.2.1,t.2.2.2.1,((windowSort t.2.2.2.2.2).getLastD (t.2.2.1,t.2.2.2.1)).1,
        ((windowSort t.2.2.2.2.2).getLastD (t.2.2.1,t.2.2.2.1)).2,t.2.2.2.2.2)) (by fun_prop)
  fun_prop
end Superstring.WindowCode

end OAI
