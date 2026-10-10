import OAI.GroupTheory.Kervaire.Capping

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

/-- A finite genus-zero relator ribbon with a marked outside vertex. Isolated
zero-sign darts are retained, so cap surgery never changes the finite universe. -/
structure OuterRibbon (ρ : Perm I) (a : I → A) (s : I → ℤ) (o : D) (l : List D) where
  σ : Perm D
  θ : Perm D
  involutive : ∀ d, θ (θ d) = d
  planar' : planar σ θ
  t : D → ℤ
  opposite : ∀ d, t (θ d) = - t d
  marker : θ o = o
  marker_sign : t o = 0
  circle : Circle σ o l
  nodup : (o::l).Nodup
  unit : ∀ d ∈ l, t d = 1 ∨ t d = -1
  atlas : DiskAtlas (V := V) ρ a s σ t
  disjoint : ∀ vi, atlas.disk vi ∉ o::l
  cover : ∀ d, (∃ vi, atlas.disk vi = d) ∨ d ∈ o::l ∨ (σ d = d ∧ θ d = d)
  u : D → A
  corners : ∀ v i, vertexCorner ρ a atlas.ε (v,i) = corner σ θ u (atlas.disk (v,i))

def OuterRibbon.value {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) : FreeProd A :=
  dartEval r.t (corner r.σ r.θ r.u) (o::l)

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] in
lemma dartEval_congr (t t' : D → ℤ) (c c' : D → A) (l : List D)
    (ht : ∀ d ∈ l, t d = t' d) (hc : ∀ d ∈ l, c d = c' d) :
    dartEval t c l = dartEval t' c' l := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro d hd
  simp only [dartLetter,ht d hd,hc d hd]

omit [Fintype V] [Fintype I] [Fintype D] in
lemma dartEval_cap (σ : Perm D) (t t' : D → ℤ) (c c' : D → A)
    (pre post : List D) (d x y : D) (hn : (pre++d::x::y::post).Nodup)
    (hd : σ d = x) (hc : c x = 1) (ht : t y = -t x)
    (ht' : ∀ z ∈ pre++d::post, t' z = t z)
    (hc' : ∀ z ∈ pre++d::post, c' z = if σ z = x then c z*c y else c z) :
    dartEval t' c' (pre++d::post) = dartEval t c (pre++d::x::y::post) := by
  have hdn : d ∉ pre ∧ d ∉ post := by
    have h := List.nodup_append.mp hn
    have hh := List.nodup_cons.mp h.2.1
    exact ⟨fun hm ↦ h.2.2 d hm d (by simp) rfl,fun hm ↦ hh.1 (by simp [hm])⟩
  have he (l : List D) (hl : ∀ z ∈ l, z ∈ pre++d::post) (hnd : d ∉ l) :
      dartEval t' c' l = dartEval t c l := by
    apply dartEval_congr _ _ _ _ _ (fun z hz ↦ ht' z (hl z hz))
    intro z hz
    rw [hc' z (hl z hz),ite_eq_right]
    exact fun h ↦ hnd ((σ.injective (hd.trans h.symm)) ▸ hz)
  rw [dartEval_append,dartEval_append,he pre (by intro z hz; simp [hz]) hdn.1,
    dartEval_cons,dartEval_cons,dartEval_cons,dartEval_cons,
    he post (by intro z hz; simp [hz]) hdn.2]
  simp only [dartLetter,ht' d (by simp),hc' d (by simp),hd,ite_true,hc,ht,map_one,mul_one,map_mul,
    ofAdd_neg,map_inv]
  group
end
section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma nodup_remove_pair (pre post : List D) (x y : D) (hn : (pre++x::y::post).Nodup) :
    x ≠ y ∧ (pre++post).Nodup ∧ ∀ z ∈ pre++post, z ≠ x ∧ z ≠ y := by
  obtain ⟨hp,hq,hdis⟩ := List.nodup_append.mp hn
  obtain ⟨hx,hy,hpost⟩ := by simpa only [List.nodup_cons] using hq
  have hxy : x ≠ y := fun h ↦ hx (by simp [h])
  refine ⟨hxy,List.nodup_append.mpr ⟨hp,hpost,fun a ha b hb ↦ hdis a ha b (by simp [hb])⟩,?_⟩
  intro z hz
  rcases List.mem_append.mp hz with hh | hh
  · exact ⟨hdis z hh x (by simp),hdis z hh y (by simp)⟩
  · exact ⟨fun h ↦ hx (by simp [← h,hh]),fun h ↦ hy (h ▸ hh)⟩

omit [Fintype V] [Fintype I] [Fintype D] [Group A] in
lemma circle_cap (σ : Perm D) (o : D) (pre post : List D) (x y : D)
    (hc : Circle σ o (pre++x::y::post)) (hn : (o::(pre++x::y::post)).Nodup) :
    Circle (erase (erase σ x) y) o (pre++post) := by
  let L := o::pre
  have hne : L ≠ [] := List.cons_ne_nil _ _
  let d := L.getLast hne
  let pr := L.dropLast
  have he : pr++[d] = o::pre := List.dropLast_concat_getLast hne
  have hcat (q : List D) : pr++d::q = o::(pre++q) := by
    calc
      _ = (pr++[d])++q := by simp only [List.append_assoc,List.cons_append,List.nil_append]
      _ = _ := by rw [he]; rfl
  have hchain : (pr++d::x::y::(post++[o])).IsChain (fun a b ↦ σ a = b) := by
    change (o::((pre++x::y::post)++[o])).IsChain _ at hc
    simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hc
  obtain ⟨hxy,_,hno⟩ := nodup_remove_pair (o::pre) post x y (by simpa using hn)
  have hh := chain_cap σ pr (post++[o]) hchain hxy (by
    intro z hz
    have hm : z ∈ o::(pre++post) := by
      have hh : z ∈ (pr++[d])++post++[o] := by simpa using hz
      rw [he] at hh
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh ⊢
      tauto
    exact hno z (by simpa using hm))
  change (o::((pre++post)++[o])).IsChain _
  simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hh

/-- Exact cap reduction, including preserved outside word and all relator
corners. The analytic rigidity theorem supplies the one necessary alignment. -/
theorem OuterRibbon.cap [Nonempty I]
    {ρ : Perm I} (hρ : ∀ i j, ρ.SameCycle i j) {a : I → A}
    {s : I → ℤ} (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    {o : D} (pre post : List D) (x y : D)
    (r : OuterRibbon (V := V) ρ a s o (pre++x::y::post))
    (hcx : corner r.σ r.θ r.u x = 1) (hpair : r.t y = -r.t x) :
    ∃ r' : OuterRibbon (V := V) ρ a s o (pre++post), r'.value = r.value := by
  obtain ⟨hxy,hn',hno⟩ := nodup_remove_pair (o::pre) post x y (by simpa using r.nodup)
  have hxmem : x ∈ o::(pre++x::y::post) := by simp
  have hymem : y ∈ o::(pre++x::y::post) := by simp
  have ho := hno o (by simp)
  have hsx : r.σ x = y := by
    have hc := r.circle
    change (o::((pre++x::y::post)++[o])).IsChain _ at hc
    simp only [List.append_assoc,List.cons_append] at hc
    change ((o::pre)++x::y::(post++[o])).IsChain _ at hc
    exact (List.isChain_append_cons_cons.mp hc).2.1
  have hsy : r.σ y ≠ x := by
    intro hh
    have hc := (circle_cycles r.σ o _ r.circle x).mpr hxmem
    rcases sameCycle_two r.σ hsx hh hc.symm with h | h
    · exact ho.1 h
    · exact ho.2 h
  have hx : r.θ x ≠ x := by
    intro hh
    have ht := r.opposite x
    rw [hh] at ht
    rcases r.unit x (by simp) with h | h <;> omega
  have hy : r.θ y ≠ y := by
    intro hh
    have ht := r.opposite y
    rw [hh] at ht
    rcases r.unit y (by simp) with h | h <;> omega
  have hdisj (vi) : ¬ r.σ.SameCycle (r.atlas.disk vi) x := by
    intro hh
    exact r.disjoint vi ((circle_cycles r.σ o _ r.circle _).mp
      (((circle_cycles r.σ o _ r.circle x).mpr hxmem).trans hh.symm))
  obtain ⟨v,hv,hvxy⟩ := cap_alignment ρ hρ a s hs hsum r.σ r.θ r.involutive r.t
    r.opposite r.planar' r.atlas r.u r.corners hxy hsx hsy hx hy hpair hcx hdisj (by
      intro d
      rcases r.cover d with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl (((circle_cycles r.σ o _ r.circle d).mpr hh).symm.trans
          ((circle_cycles r.σ o _ r.circle x).mpr hxmem)))
      · exact Or.inr (Or.inr hh))
  let σ' := erase (erase r.σ x) y
  let θ' := suppress r.θ x y
  let t' := capSign r.t x y
  have hne (vi) : r.atlas.disk vi ≠ x ∧ r.atlas.disk vi ≠ y :=
    ⟨fun h ↦ r.disjoint vi (by rw [h]; exact hxmem),fun h ↦ r.disjoint vi (by rw [h]; exact hymem)⟩
  have hnex (vi) : r.σ (r.atlas.disk vi) ≠ x := by
    intro hh
    apply hdisj vi
    have hc : r.σ.SameCycle (r.atlas.disk vi) (r.σ (r.atlas.disk vi)) := SameCycle.rfl.apply_right
    simpa only [hh] using hc
  have hnext (vi) : σ' (r.atlas.disk vi) = r.σ (r.atlas.disk vi) := by
    dsimp only [σ']; rw [cap_vertex_other r.σ hxy hsx (hne vi).1 (hne vi).2,ite_eq_right (hnex vi)]
  let b' : DiskAtlas (V := V) ρ a s σ' t' := {
    disk := r.atlas.disk, ε := r.atlas.ε, polarity := r.atlas.polarity
    next := fun v i ↦ (hnext (v,i)).trans (r.atlas.next v i)
    sign := fun v i ↦ (capSign_other r.t (hne _).1 (hne _).2).trans (r.atlas.sign v i) }
  have hcv : corner r.σ r.θ v x = 1 := by rw [hv,hcx]
  have hcorner (d) (hdx : d ≠ x) (hdy : d ≠ y) :
      corner σ' θ' v d = if r.σ d = x then corner r.σ r.θ r.u d * corner r.σ r.θ r.u y else corner r.σ r.θ r.u d := by
    simpa only [hv] using corner_cap r.σ r.θ r.involutive v hxy hsx hx hy hcv hvxy hdx hdy
  have hfix := suppress_fixed_all r.θ r.involutive hxy hx hy
  have hσx : σ' x = x := by dsimp only [σ']; rw [erase_apply _ _ _ hxy,erase_fixed,ite_eq_right hxy]
  have hσy : σ' y = y := erase_fixed _ _
  have hmark : θ' o = o := by
    dsimp only [θ']
    rw [suppress_other r.θ r.involutive ho.1 ho.2 (by
      intro h; have hh := congrArg r.θ h; rw [r.marker,r.involutive] at hh; exact ho.1 hh) (by
      intro h; have hh := congrArg r.θ h; rw [r.marker,r.involutive] at hh; exact ho.2 hh),r.marker]
  let r' : OuterRibbon (V := V) ρ a s o (pre++post) := {
    σ := σ', θ := θ', involutive := suppress_involutive_all r.θ r.involutive hxy hx hy
    planar' := planar_cap r.σ r.θ r.involutive hxy hsx hsy hx hy r.planar'
    t := t', opposite := suppress_sign r.θ r.involutive r.t r.opposite hxy hx hy hpair
    marker := hmark, marker_sign := (capSign_other r.t ho.1 ho.2).trans r.marker_sign
    circle := circle_cap r.σ o pre post x y r.circle r.nodup
    nodup := by simpa using hn'
    unit := by
      intro d hd
      have hnd := hno d (by simp [hd])
      change capSign r.t x y d = 1 ∨ capSign r.t x y d = -1
      rw [capSign_other r.t hnd.1 hnd.2]
      exact r.unit d (by rcases List.mem_append.mp hd with h | h <;> simp [h])
    atlas := b'
    disjoint := by
      intro vi hh
      change r.atlas.disk vi ∈ o::(pre++post) at hh
      apply r.disjoint vi
      rcases List.mem_cons.mp hh with hh | hh
      · exact List.mem_cons.mpr (Or.inl hh)
      · rcases List.mem_append.mp hh with hh | hh <;> simp [hh]
    cover := by
      intro d
      by_cases hdx : d = x
      · exact Or.inr (Or.inr (hdx ▸ ⟨hσx,hfix.1⟩))
      by_cases hdy : d = y
      · exact Or.inr (Or.inr (hdy ▸ ⟨hσy,hfix.2⟩))
      rcases r.cover d with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl (by simpa only [List.mem_cons,List.mem_append,hdx,hdy,false_or] using hh))
      · refine Or.inr (Or.inr ⟨?_,?_⟩)
        · dsimp only [σ']; rw [cap_vertex_other r.σ hxy hsx hdx hdy,hh.1,ite_eq_right hdx]
        · dsimp only [θ']; rw [suppress_other r.θ r.involutive hdx hdy (by
            intro h; have hj := congrArg r.θ h; rw [hh.2,r.involutive] at hj; exact hdx hj) (by
            intro h; have hj := congrArg r.θ h; rw [hh.2,r.involutive] at hj; exact hdy hj),hh.2]
    u := v
    corners := by
      intro v i
      change vertexCorner ρ a r.atlas.ε (v,i) = _
      rw [r.corners,hcorner _ (hne _).1 (hne _).2,ite_eq_right (hnex _)] }
  refine ⟨r',?_⟩
  let L := o::pre
  have hL : L ≠ [] := List.cons_ne_nil _ _
  let d := L.getLast hL
  let pr := L.dropLast
  have he : pr++[d] = o::pre := List.dropLast_concat_getLast hL
  have hcat (q : List D) : pr++d::q = o::(pre++q) := by
    calc
      _ = (pr++[d])++q := by simp only [List.append_assoc,List.cons_append,List.nil_append]
      _ = _ := by rw [he]; rfl
  have hchain : (pr++d::x::y::(post++[o])).IsChain (fun a b ↦ r.σ a = b) := by
    have hh := r.circle
    change (o::((pre++x::y::post)++[o])).IsChain _ at hh
    simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hh
  have hd : r.σ d = x := (List.isChain_append_cons_cons.mp hchain).2.1
  have hh := dartEval_cap r.σ r.t t' (corner r.σ r.θ r.u) (corner σ' θ' v) pr post d x y
    (by simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using r.nodup) hd hcx hpair
    (by intro z hz; have hnz := hno z (by simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hz)
        exact capSign_other r.t hnz.1 hnz.2)
    (by intro z hz; have hnz := hno z (by simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hz)
        exact hcorner z hnz.1 hnz.2)
  change dartEval t' (corner σ' θ' v) (o::(pre++post)) = dartEval r.t (corner r.σ r.θ r.u) (o::(pre++x::y::post))
  simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hh
end
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

/-- The outside word of a planar relator ribbon can be a coefficient only
when that coefficient is trivial. This is the complete inside-out cap induction. -/
theorem OuterRibbon.coefficient_eq_one [Nonempty I]
    {ρ : Perm I} (hρ : ∀ i j, ρ.SameCycle i j) {a : I → A}
    {s : I → ℤ} (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    {o : D} {l : List D} (r : OuterRibbon (V := V) ρ a s o l) (g : A)
    (he : r.value = Coprod.inl g) : g = 1 := by
  suffices ∀ n (l : List D), l.length = n → ∀ r : OuterRibbon (V := V) ρ a s o l,
      r.value = Coprod.inl g → g=1 by exact this l.length l rfl r he
  intro n
  induction n using Nat.strong_induction_on with | h n ih =>
    intro l hn r he
    by_cases hl : l = []
    · subst l
      have ho : r.σ o = o := by simpa only [Circle,List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true] using r.circle
      have hv : r.value = 1 := by
        simp only [OuterRibbon.value,dartEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
          dartLetter,corner,r.marker,r.marker_sign,ho,mul_inv_cancel,ofAdd_zero,map_one,mul_one]
      apply (Coprod.inl_injective (N := Multiplicative ℤ))
      simpa only [map_one] using he.symm.trans hv
    · have hd : dartEval r.t (corner r.σ r.θ r.u) l = Coprod.inl ((corner r.σ r.θ r.u o)⁻¹*g) := by
        have hh : Coprod.inl (corner r.σ r.θ r.u o) * dartEval r.t (corner r.σ r.θ r.u) l = Coprod.inl g := by
          simpa only [OuterRibbon.value,dartEval_cons,dartLetter,r.marker_sign,ofAdd_zero,map_one,one_mul] using he
        rw [map_mul,map_inv]
        exact (eq_inv_mul_iff_mul_eq).mpr hh
      obtain ⟨pre,post,x,y,hl',hcx,hpair⟩ := dart_pinch r.t (corner r.σ r.θ r.u) l hl r.unit
        ((corner r.σ r.θ r.u o)⁻¹*g) hd
      subst l
      obtain ⟨r',hr'⟩ := r.cap hρ hs hsum pre post x y hcx hpair
      apply ih (pre++post).length (by simp only [List.length_append,List.length_cons] at hn ⊢; omega)
        (pre++post) rfl r'
      exact hr'.trans he
end KervaireRibbon

end

end OAI
