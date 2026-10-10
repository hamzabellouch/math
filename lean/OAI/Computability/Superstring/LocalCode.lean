import OAI.Computability.Superstring.LayerBridge

namespace OAI

namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]

def exits (D : GroupData α) (j : ℕ) : List ℕ := D.2[j]?.getD []
def covered (D : GroupData α) (js : List ℕ) (P : Walk α) : Bool :=
  js.all (fun j => (content D.1 (exits D j)).all (fun w => member w P))
def collective (D : GroupData α) (js : List ℕ) (hi : ℕ) (a b : ℤ) : Walk α :=
  saturate D js (GeoCode.collective (PeriodWord.text D.1) (GeoCode.exit (exits D hi))
    D.1.length js.length a b)
def band (D : GroupData α) (js : List ℕ) (lo hi k : ℕ) (t : ℤ) : Walk α :=
  saturate D js (GeoCode.band (PeriodWord.text D.1) (GeoCode.exit (exits D lo))
    (GeoCode.exit (exits D hi)) D.1.length k t)
def shortSweep (D : GroupData α) (js : List ℕ) (hi : ℕ) (a b t : ℤ) : Walk α :=
  saturate D js (GeoCode.shortSweep (PeriodWord.text D.1) (GeoCode.exit (exits D hi))
    D.1.length js.length a b t)
def individual (D : GroupData α) (i : ℕ) (a b : ℤ) : Walk α :=
  saturate D [i] (GeoCode.individual (PeriodWord.text D.1) (GeoCode.exit (exits D i))
    D.1.length a b)

theorem covered_eq {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (P : Walk α) :
    covered D js P = true ↔ ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ P := by
  simp only [covered,List.all_eq_true,member,decide_eq_true_eq]
  constructor
  · intro hc j hj w hw
    exact hc j hj w ((mem_content (h j hj) hp per w).mpr hw)
  · intro hc j hj w hw
    exact hc j hj w ((mem_content (h j hj) hp per w).mp hw)

theorem filled_realized {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    {s : List α} {P : Hierarchical.Path V s s} {W : Walk α}
    (he : WalkCode.Path.points P = W) (ht : ∀ j ∈ js, (L j).TouchedBy P) :
    Runs V s s (saturate D js W) ∧
      cost (saturate D js W) = P.cost+js.length*p ∧
      (∀ w, P.Visits w → w ∈ saturate D js W) ∧
      ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ saturate D js W := by
  have hs := WalkCode.points_spec P
  obtain ⟨hr,hc,hv,hw⟩ := saturate_spec L h closed hp per
    (s:=s) (t:=s) (P:=W) (by rw [← he]; exact ⟨hs.1,hs.2.1,hs.2.2.1⟩)
    (by intro j hj; obtain ⟨x,e,hf,hl,hv⟩ := ht j hj
        exact ⟨_,⟨x,e,hf,hl,rfl⟩,he ▸ (hs.2.2.2.2 _).mpr hv⟩)
  refine ⟨hr,?_,fun w hw => hv w (he ▸ (hs.2.2.2.2 w).mpr hw),hw⟩
  rw [← he,hs.2.2.2.1] at hc
  simpa only [he] using hc

theorem collective_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {lo hi : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (hlo : lo ∈ js) (hhi : hi ∈ js)
    (lower : ∀ j ∈ js, ∀ x, (L lo).z x ≤ (L j).z x)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) {a b : ℤ} (hab : a ≤ b)
    (hR : textWord A a b ∈ V)
    (hH : (L hi).first a ≤ b + (js.length*p : ℕ))
    (hgap : (L hi).first a-(L lo).last a ≤ (js.length*p : ℕ))
    (hB : b ≤ (L lo).last a + (js.length*p : ℕ)) :
    Runs V (textWord A a b) (textWord A a b) (collective D js hi a b) ∧
      cost (collective D js hi a b) = 2*(js.length*p) ∧
      (∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ collective D js hi a b) ∧
      textWord A a b ∈ collective D js hi a b := by
  obtain ⟨P,he,hc,ht⟩ := GeoCode.collective_link_realizes closed A letters p js.length per
    (fun j : {j // j ∈ js} => L j.val) ⟨lo,hlo⟩ ⟨hi,hhi⟩
    (fun j => lower j.val j.property) (fun j => upper j.val j.property) hab hR hH hgap hB
  have he' : WalkCode.Path.points P = GeoCode.collective (PeriodWord.text D.1)
      (GeoCode.exit (exits D hi)) D.1.length js.length a b := by
    rw [(h hi hhi).text_eq,(h hi hhi).exit_eq,(h hi hhi).length_eq]; exact he
  obtain ⟨hr,hc',hv,hw⟩ := filled_realized L h closed hp per he' (fun j hj => ht ⟨j,hj⟩)
  refine ⟨hr,?_,hw,hv _ (Hierarchical.Path.visits_start P)⟩
  change cost (saturate D js _) = _
  rw [hc',hc,two_mul]

theorem band_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {lo hi k : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (hlo : lo ∈ js) (hhi : hi ∈ js)
    (lower : ∀ j ∈ js, ∀ x, (L lo).z x ≤ (L j).z x)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (t : ℤ)
    (hB : (L hi).first t-(L lo).last t ≤ (k*p : ℕ)) :
    Runs V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)) (band D js lo hi k t) ∧
      cost (band D js lo hi k t) ≤ (k+js.length)*p ∧
      ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ band D js lo hi k t := by
  obtain ⟨P,he,hc,ht⟩ := GeoCode.join_band_realizes closed A letters p k per
    (fun j : {j // j ∈ js} => L j.val) ⟨lo,hlo⟩ ⟨hi,hhi⟩
    (fun j => lower j.val j.property) (fun j => upper j.val j.property) t hB
  have he' : WalkCode.Path.points P = GeoCode.band (PeriodWord.text D.1)
      (GeoCode.exit (exits D lo)) (GeoCode.exit (exits D hi)) D.1.length k t := by
    rw [(h hi hhi).text_eq,(h hi hhi).exit_eq,(h lo hlo).exit_eq,(h hi hhi).length_eq]; exact he
  obtain ⟨hr,hc',_,hw⟩ := filled_realized L h closed hp per he' (fun j hj => ht ⟨j,hj⟩)
  refine ⟨hr,?_,hw⟩
  change cost (saturate D js _) ≤ _
  rw [hc',Nat.add_mul]
  omega

variable [Coded α]
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_exits : Poly (fun q : GroupData α × ℕ => exits q.1 q.2) := by
  unfold exits
  exact (BitCode.Poly.getD ([] : List ℕ)).comp (f := fun q : GroupData α × ℕ => (q.1.2,q.2)) (by fun_prop)
@[fun_prop] theorem poly_covered : Poly (fun q : GroupData α × List ℕ × Walk α => covered q.1 q.2.1 q.2.2) := by
  unfold covered
  apply BitCode.Poly.allFn (p := fun q : (GroupData α × List ℕ × Walk α) × ℕ =>
    (content q.1.1.1 (exits q.1.1 q.2)).all (fun w => member w q.1.2.2))
  · exact BitCode.Poly.allFn (p := fun q : ((GroupData α × List ℕ × Walk α) × ℕ) × List α =>
      member q.2 q.1.1.2.2) (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem saturate_fn {β : Type} [Coded β]
    {D : β → GroupData α} {js : β → List ℕ} {P : β → Walk α}
    (hD : Poly D) (hjs : Poly js) (hP : Poly P) :
    Poly (fun q => saturate (D q) (js q) (P q)) :=
  poly_saturate.comp (hD.pair (hjs.pair hP))
@[fun_prop] theorem poly_collective : Poly (fun q : GroupData α × List ℕ × ℕ × ℤ × ℤ =>
    collective q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold collective
  apply saturate_fn (by fun_prop) (by fun_prop)
  exact GeoCode.poly_collective.comp
    (f := fun q : GroupData α × List ℕ × ℕ × ℤ × ℤ =>
      (q.1.1,exits q.1 q.2.2.1,q.1.1.length,q.2.1.length,q.2.2.2.1,q.2.2.2.2)) (by fun_prop)
@[fun_prop] theorem poly_band : Poly (fun q : GroupData α × List ℕ × ℕ × ℕ × ℕ × ℤ =>
    band q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold band
  apply saturate_fn (by fun_prop) (by fun_prop)
  exact GeoCode.poly_band.comp
    (f := fun q : GroupData α × List ℕ × ℕ × ℕ × ℕ × ℤ =>
      (q.1.1,exits q.1 q.2.2.1,exits q.1 q.2.2.2.1,q.1.1.length,q.2.2.2.2.1,q.2.2.2.2.2)) (by fun_prop)
@[fun_prop] theorem poly_shortSweep : Poly (fun q : GroupData α × List ℕ × ℕ × ℤ × ℤ × ℤ =>
    shortSweep q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold shortSweep
  apply saturate_fn (by fun_prop) (by fun_prop)
  exact GeoCode.poly_shortSweep.comp
    (f := fun q : GroupData α × List ℕ × ℕ × ℤ × ℤ × ℤ =>
      (q.1.1,exits q.1 q.2.2.1,q.1.1.length,q.2.1.length,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) (by fun_prop)
@[fun_prop] theorem poly_individual : Poly (fun q : GroupData α × ℕ × ℤ × ℤ =>
    individual q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold individual
  apply saturate_fn (by fun_prop) (by fun_prop)
  exact GeoCode.poly_individual.comp
    (f := fun q : GroupData α × ℕ × ℤ × ℤ =>
      (q.1.1,exits q.1 q.2.1,q.1.1.length,q.2.2.1,q.2.2.2)) (by fun_prop)
end Superstring.LayerArray


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]

theorem individual_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {i : ℕ}
    (h : Represents D.1 (exits D i) (L i))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (q : ℕ) {a b : ℤ} (hab : a ≤ b)
    (hR : textWord A a b ∈ V) (hf : (L i).first a ≤ b) (hl : b ≤ (L i).last a+p)
    (hlen : b-a < p+q) :
    Runs V (textWord A a b) (textWord A a b) (individual D i a b) ∧
      cost (individual D i a b) = 2*p ∧
      (∀ w ∈ (L i).Content, w ∈ individual D i a b) ∧
      textWord A a b ∈ individual D i a b ∧
      ∃ w ∈ individual D i a b, w.length ≤ q := by
  obtain ⟨P,he,hc,ht,w,hw,hwlen⟩ := GeoCode.individual_link_realizes closed A letters p q per
    (L i) hab hR hf hl hlen
  have he' : WalkCode.Path.points P = GeoCode.individual (PeriodWord.text D.1)
      (GeoCode.exit (exits D i)) D.1.length a b := by
    rw [h.text_eq,h.exit_eq,h.length_eq]; exact he
  obtain ⟨hr,hc',hv,hcover⟩ := filled_realized L
    (D:=D) (js:=[i]) (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact h)
    closed hp per he' (by intro j hj; simpa only [List.mem_singleton.mp hj] using ht)
  refine ⟨hr,?_,hcover i (by simp),hv _ (Hierarchical.Path.visits_start P),w,hv w hw,hwlen⟩
  change cost (saturate D [i] _) = _
  rw [hc',hc]
  simp only [List.length_singleton,one_mul,two_mul]

theorem shortSweep_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {hi : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j)) (hhi : hi ∈ js)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (q : ℕ)
    (hlong : ∀ j ∈ js, ¬(L j).HasShort q) {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V) (hH : (L hi).first t ≤ b+(js.length*p : ℕ))
    (hlen : b-a < p+q) (hagr : b-t < q) :
    Runs V (textWord A a b) (textWord A a b) (shortSweep D js hi a b t) ∧
      cost (shortSweep D js hi a b t) = 2*(js.length*p) ∧
      (∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ shortSweep D js hi a b t) ∧
      textWord A a b ∈ shortSweep D js hi a b t ∧
      ∃ w ∈ shortSweep D js hi a b t, w.length ≤ q := by
  have hk : 1 ≤ js.length := by have := List.length_pos_of_mem hhi; omega
  obtain ⟨P,he,hc,ht,w,hw,hwlen⟩ := GeoCode.collective_short_sweep_realizes closed A letters p js.length q hk per
    (fun j : {j // j ∈ js} => L j.val) ⟨hi,hhi⟩
    (fun j => upper j.val j.property) (fun j => hlong j.val j.property) hat htb hR hH hlen hagr
  have he' : WalkCode.Path.points P = GeoCode.shortSweep (PeriodWord.text D.1)
      (GeoCode.exit (exits D hi)) D.1.length js.length a b t := by
    rw [(h hi hhi).text_eq,(h hi hhi).exit_eq,(h hi hhi).length_eq]; exact he
  obtain ⟨hr,hc',hv,hcover⟩ := filled_realized L h closed hp per he' (fun j hj => ht ⟨j,hj⟩)
  refine ⟨hr,?_,hcover,hv _ (Hierarchical.Path.visits_start P),w,hv w hw,hwlen⟩
  change cost (saturate D js _) = _
  rw [hc',hc,two_mul]

theorem collective_contact [LinearOrder α] {V : Set (List α)} {A B : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {lo hi : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j)) (hlo : lo ∈ js) (hhi : hi ∈ js)
    (lower : ∀ j ∈ js, ∀ x, (L lo).z x ≤ (L j).z x)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (q : ℕ) (hq : 0 < q) (perB : Function.Periodic B (q : ℤ))
    {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V) (hag : AgreeOn A B a b) (hne : A ≠ B)
    (hmax : ∀ x, forward A x ≤ forward A t) (hbelow : ∀ x, forward B x ≤ forward A t)
    (hH : (L hi).first t ≤ b+(js.length*p : ℕ))
    (hgap : (L hi).first a-(L lo).last a ≤ (js.length*p : ℕ))
    (hB : b ≤ (L lo).last a+(js.length*p : ℕ)) :
    ∃ P ∈ [collective D js hi a b,shortSweep D js hi a b t],
      Runs V (textWord A a b) (textWord A a b) P ∧ cost P = 2*(js.length*p) ∧
      (∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ P) ∧ textWord A a b ∈ P ∧
      ∃ w ∈ P, w.length ≤ q := by
  classical
  by_cases hs : ∃ j ∈ js, (L j).HasShort q
  · obtain ⟨hr,hc,hcover,hR'⟩ := collective_spec L h hlo hhi lower upper closed hp per letters
      (by omega) hR (le_trans ((L hi).first_mono hat) hH) hgap hB
    obtain ⟨j,hj,x,e,hf,hl,hshort⟩ := hs
    exact ⟨_,by simp,hr,hc,hcover,hR',_,hcover j hj _ ⟨x,e,hf,hl,rfl⟩,hshort⟩
  · have hlen := agreement_bound A B p q hp hq per perB hne a b hag
    have hagr : b-t < q := by
      obtain ⟨n,hn,hd⟩ := maximal_rotation A B p q hp hq per perB t hmax hbelow hne
      by_contra hh
      exact hd (hag (t+n) (by omega) (by omega))
    obtain ⟨hr,hc,hcover,hR',hw⟩ := shortSweep_spec L h hhi upper closed hp per letters q
      (by intro j hj hh; exact hs ⟨j,hj,hh⟩) hat htb hR hH hlen hagr
    exact ⟨_,by simp,hr,hc,hcover,hR',hw⟩
end Superstring.LayerArray


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}
theorem root_prefix {V : Set (List α)} (closed : SubstringClosed V) {w v : List α}
    (hw : w ∈ V) (hv : v <+: w) : v ∈ root w := by
  obtain ⟨u,rfl⟩ := hv
  have ha := append_spec closed [] (v++u) (by simpa using hw)
  have hd := delete_spec closed (v++u) [] (by simpa using hw)
  rw [root,mem_join ha.2.2.1 (by simpa only [List.nil_append,List.append_nil] using hd.2.1)]
  apply Or.inl
  simpa using mem_append ([] : List α) (v++u) v.length (by simp)
end Superstring.WalkCode

namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def rootContent (D : GroupData α) (js : List ℕ) (w : List α) : Walk α :=
  saturate D js (WalkCode.root w)
def shortPool (D : GroupData α) (i : ℕ) : List (Walk α) :=
  (content D.1 (exits D i)).map (rootContent D [i])
def rootUpper (D : GroupData α) (js : List ℕ) (hi : ℕ) (t : ℤ) : Walk α :=
  rootContent D js (PeriodWord.window D.1 t (GeoCode.first (exits D hi) t))

theorem rootContent_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {w : List α}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hw : w ∈ V) (htouch : ∀ j ∈ js, ∃ v ∈ (L j).Content, v <+: w) :
    Runs V [] [] (rootContent D js w) ∧ cost (rootContent D js w) = w.length+js.length*p ∧
      ∀ j ∈ js, ∀ v ∈ (L j).Content, v ∈ rootContent D js w := by
  have hr := WalkCode.root_spec closed hw
  obtain ⟨hR,hc,_,hv⟩ := saturate_spec L h closed hp per hr.1 (by
    intro j hj
    obtain ⟨v,hv,hpre⟩ := htouch j hj
    exact ⟨v,hv,WalkCode.root_prefix closed hw hpre⟩)
  exact ⟨hR,by simpa only [rootContent,hr.2.1] using hc,hv⟩

theorem shortPool_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {i : ℕ}
    (h : Represents D.1 (exits D i) (L i))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hs : (L i).HasShort p) :
    ∃ P ∈ shortPool D i, Runs V [] [] P ∧ cost P ≤ 2*p ∧
      ∀ w ∈ (L i).Content, w ∈ P := by
  obtain ⟨x,e,hf,hl,hlen⟩ := hs
  let w := textWord A x e
  have hw : w ∈ (L i).Content := ⟨x,e,hf,hl,rfl⟩
  refine ⟨rootContent D [i] w,List.mem_map.mpr ⟨w,(mem_content h hp per w).mpr hw,rfl⟩,?_⟩
  obtain ⟨hr,hc,hv⟩ := rootContent_spec L (D:=D) (js:=[i])
    (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact h)
    closed hp per ((L i).actual x e hf hl)
    (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact ⟨w,hw,List.prefix_refl _⟩)
  exact ⟨hr,by simp only [List.length_singleton,one_mul] at hc; dsimp only [w]; omega,hv i (by simp)⟩

theorem rootUpper_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {hi : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j)) (hh : Represents D.1 (exits D hi) (L hi))
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (t : ℤ)
    (hlen : (L hi).first t-t ≤ (js.length*p : ℕ)) :
    Runs V [] [] (rootUpper D js hi t) ∧ cost (rootUpper D js hi t) ≤ 2*(js.length*p) ∧
      ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ rootUpper D js hi t := by
  have he : PeriodWord.window D.1 t (GeoCode.first (exits D hi) t) =
      textWord A t ((L hi).first t) := by
    simp only [PeriodWord.window_eq,hh.text_eq,GeoCode.first,hh.exit_eq,Layer.first]
  unfold rootUpper
  rw [he]
  obtain ⟨hr,hc,hv⟩ := rootContent_spec L h closed hp per ((L hi).first_actual t) (by
    intro j hj
    refine ⟨textWord A t ((L j).first t),⟨t,_,le_rfl,(L j).first_le_last t,rfl⟩,?_⟩
    exact ⟨textWord A ((L j).first t) ((L hi).first t),
      textWord_append A ((L j).start_le_first t) (upper j hj (t-1))⟩)
  refine ⟨hr,?_,hv⟩
  rw [hc,length_textWord]
  have ht := (L hi).start_le_first t
  omega

variable [Coded α]
@[fun_prop] theorem poly_rootContent : Poly (fun q : GroupData α × List ℕ × List α =>
    rootContent q.1 q.2.1 q.2.2) := by unfold rootContent; fun_prop
@[fun_prop] theorem poly_shortPool : Poly (fun q : GroupData α × ℕ => shortPool q.1 q.2) := by
  unfold shortPool
  exact BitCode.Poly.mapFn
    (f := fun q : (GroupData α × ℕ) × List α => rootContent q.1.1 [q.1.2] q.2)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_rootUpper : Poly (fun q : GroupData α × List ℕ × ℕ × ℤ =>
    rootUpper q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold rootUpper
  exact poly_rootContent.comp
    (f := fun q : GroupData α × List ℕ × ℕ × ℤ =>
      (q.1,q.2.1,PeriodWord.window q.1.1 q.2.2.2 (GeoCode.first (exits q.1 q.2.2.1) q.2.2.2))) (by fun_prop)
end Superstring.LayerArray


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}
def rootShort (P : Walk α) (p : ℕ) : Walk α :=
  rootAt P (ThreadArray.first P.length (fun i => lessEq (P[i]?.getD []).length p))

theorem rootShort_spec {V : Set (List α)} (closed : SubstringClosed V) {P : Walk α} {s : List α}
    (hP : Runs V s s P) (p : ℕ) (hs : ∃ w ∈ P, w.length ≤ p) :
    Runs V [] [] (rootShort P p) ∧ cost (rootShort P p) ≤ cost P+p ∧
      ∀ w ∈ P, w ∈ rootShort P p := by
  obtain ⟨x,hx,hlen⟩ := hs
  obtain ⟨i,hi,hix⟩ := List.mem_iff_getElem.mp hx
  have he : lessEq (P[i]?.getD []).length p = true := by
    simpa only [List.getElem?_eq_getElem hi,Option.getD_some,hix,lessEq,decide_eq_true_eq] using hlen
  obtain ⟨hj,hp',_⟩ := ThreadArray.first_spec (P := fun i => lessEq (P[i]?.getD []).length p) ⟨i,hi,he⟩
  obtain ⟨hR,hc,hv⟩ := rootAt_spec closed hP hj
  have hl : P[ThreadArray.first P.length (fun i => lessEq (P[i]?.getD []).length p)].length ≤ p := by
    have hh := of_decide_eq_true hp'
    simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using hh
  exact ⟨hR,hc.trans_le (Nat.add_le_add_left hl _),hv⟩

variable [Coded α]
@[fun_prop] theorem poly_rootShort : Poly (fun q : Walk α × ℕ => rootShort q.1 q.2) := by
  unfold rootShort ThreadArray.first
  apply poly_rootAt.comp (f := fun q : Walk α × ℕ =>
    (q.1,((List.range q.1.length).filter (fun i => lessEq (q.1[i]?.getD []).length q.2)).headD 0))
  apply Poly.pair (by fun_prop)
  apply (Poly.headD 0).comp (f := fun q : Walk α × ℕ =>
     (List.range q.1.length).filter (fun i => lessEq (q.1[i]?.getD []).length q.2))
  apply Poly.filterFn (p := fun q : (Walk α × ℕ) × ℕ => lessEq (q.1.1[q.2]?.getD []).length q.1.2)
  · have h := (Poly.getD ([] : List α)).comp
      (f := fun q : (Walk α × ℕ) × ℕ => (q.1.1,q.2)) (by fun_prop)
    fun_prop
  · fun_prop
end Superstring.WalkCode

end OAI
