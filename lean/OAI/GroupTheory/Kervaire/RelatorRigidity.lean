import OAI.GroupTheory.Kervaire.RibbonRigidity

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

/-- The coefficient on the corner immediately following a dart. -/
def corner (σ θ : Perm D) (u : D → A) (d : D) : A := u (θ d) * (u (σ d))⁻¹

omit [Fintype D] [DecidableEq D] in
lemma corner_gauge (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u c : D → A) (hc : ∀ d, c ((σ*θ) d) = c d) :
    corner σ θ (fun d ↦ u d*c d) = corner σ θ u := by
  funext d
  have h := hc (θ d)
  simp only [mul_apply,hθ] at h
  simp only [corner,h,mul_inv_rev]
  group

/-- Independent face gauges can align two vertices precisely when the two
 relevant faces are distinct. -/
lemma align_distinct_faces (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → A) {p q : D} (hpq : ¬ (σ*θ).SameCycle p q) :
    ∃ v : D → A, corner σ θ v = corner σ θ u ∧ v q = v p := by
  let φ := σ*θ
  let c : D → A := fun d ↦ if φ.SameCycle d q then (u q)⁻¹*u p else 1
  have hc (d : D) : c (φ d) = c d := by simp only [c,sameCycle_apply_left]
  refine ⟨fun d ↦ u d*c d,corner_gauge σ θ hθ u c hc,?_⟩
  simp only [c,φ,SameCycle.rfl,ite_true,ite_eq_right hpq,mul_one]
  group

omit [DecidableEq D] in
lemma planar_symm (σ θ : Perm D) : planar σ θ ↔ planar θ σ := by
  have hn : numCycles (σ*θ) = numCycles (θ*σ) := by
    have hh := numCycles_conj (σ*θ) σ⁻¹
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left] using hh.symm
  have hc : components σ θ = components θ σ := sup_comm _ _
  unfold planar
  rw [hn,hc]
  omega

omit [Fintype D] in
lemma cap_vertex (σ : Perm D) {x y : D} (hxy : x ≠ y) (hs : σ x = y) (hz : σ y ≠ x) :
    erase (erase σ x) y = swap x y * (swap x (σ y) * σ) := by
  have hzy : σ y ≠ y := fun h ↦ hxy (σ.injective (hs.trans h.symm))
  unfold erase
  rw [hs]
  change swap y (swap x y (σ y)) * (swap x y * σ) = _
  rw [swap_apply_of_ne_of_ne hz hzy]
  have hg : swap y (σ y) * swap x y = swap x y * swap x (σ y) := by
    ext d
    by_cases hd : d = x
    · subst d
      simp only [mul_apply,swap_apply_left,swap_apply_of_ne_of_ne hz hzy]
    by_cases hd' : d = y
    · subst d
      simp only [mul_apply,swap_apply_right,swap_apply_of_ne_of_ne hxy hz.symm,
        swap_apply_of_ne_of_ne hxy.symm hzy.symm]
    by_cases hd'' : d = σ y
    · subst d
      simp only [mul_apply,swap_apply_of_ne_of_ne hz hzy,swap_apply_right,swap_apply_left]
    · simp only [mul_apply,swap_apply_of_ne_of_ne hd hd',swap_apply_of_ne_of_ne hd' hd'',
        swap_apply_of_ne_of_ne hd hd'']
  rw [← mul_assoc,hg,mul_assoc]

omit [Fintype D] in
lemma cap_vertex_other (σ : Perm D) {x y d : D} (hxy : x ≠ y) (hs : σ x = y)
    (hdx : d ≠ x) (hdy : d ≠ y) :
    erase (erase σ x) y d = if σ d = x then σ y else σ d := by
  have hsy : σ d ≠ y := fun h ↦ hdx (σ.injective (h.trans hs.symm))
  rw [erase_apply _ _ _ hdy,erase_apply _ _ _ hdx]
  by_cases hdx' : σ d = x
  · rw [ite_eq_left hdx',hs,ite_eq_left rfl,erase_apply _ _ _ hxy.symm]
    by_cases hyx : σ y = x
    · rw [ite_eq_left hyx,hs,hyx]
      exact (hdy (σ.injective (hdx'.trans hyx.symm))).elim
    · rw [ite_eq_right hyx,ite_eq_left hdx']
  · rw [ite_eq_right hdx',ite_eq_right hsy,ite_eq_right hdx']

lemma planar_cap (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hs : σ x = y) (hz : σ y ≠ x)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hp : planar σ θ) :
    planar (erase (erase σ x) y) (suppress θ x y) := by
  let τ := swap x (σ y) * σ
  have hzy : σ y ≠ y := fun h ↦ hxy (σ.injective (hs.trans h.symm))
  have hτx : τ x = y := by simp only [τ,mul_apply,hs,swap_apply_of_ne_of_ne hxy.symm hzy.symm]
  have hτy : τ y = x := by simp [τ]
  have hcy : σ.SameCycle x (σ y) := (hs ▸ SameCycle.rfl.apply_right).apply_right
  have hτp := planar_vertex_split σ θ hz.symm hcy hp
  rw [cap_vertex σ hxy hs hz]
  by_cases ht : θ x = y
  · have ht' : suppress θ x y = swap x y * θ := by
      simp only [suppress,ht,swap_self]
      change swap x y * (1 * θ * 1) = _
      simp only [one_mul,mul_one]
    rw [ht']
    have htp := planar_vertex_split θ τ hxy (ht ▸ SameCycle.rfl.apply_right)
      ((planar_symm _ _).mp hτp)
    exact planar_vertex_split τ (swap x y*θ) hxy (hτx ▸ SameCycle.rfl.apply_right)
      ((planar_symm _ _).mp htp)
  · exact planar_suppress τ θ hθ hxy hτx hτy hx ht hy hτp

omit [Fintype D] [Group A] in
lemma suppress_u (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → A) {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y)
    (hup : u (θ x) = u y) (huq : u (θ y) = u x) {d : D} (hdx : d ≠ x) (hdy : d ≠ y) :
    u (suppress θ x y d) = u (θ d) := by
  by_cases ht : θ x = y
  · have hyx : θ y = x := by simpa only [hθ] using congrArg θ ht |>.symm
    have he : suppress θ x y = swap x y * θ := by
      simp only [suppress,ht,swap_self]
      change swap x y * (1 * θ * 1) = _
      simp only [one_mul,mul_one]
    rw [he,mul_apply,swap_apply_of_ne_of_ne]
    · exact fun h ↦ hdy (by simpa only [hθ,ht] using congrArg θ h)
    · exact fun h ↦ hdx (by simpa only [hθ,hyx] using congrArg θ h)
  · have hh := suppress_apply θ hθ hxy hx ht hy
    by_cases hd : d = θ x
    · subst d; rw [hh.2.2.1,hθ,huq]
    by_cases hd' : d = θ y
    · subst d; rw [hh.2.2.2,hθ,hup]
    rw [suppress_other θ hθ hdx hdy hd hd']

omit [Fintype D] in
lemma corner_cap (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → A) {x y : D} (hxy : x ≠ y) (hs : σ x = y)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hc : corner σ θ u x = 1) (huq : u (θ y) = u x)
    {d : D} (hdx : d ≠ x) (hdy : d ≠ y) :
    corner (erase (erase σ x) y) (suppress θ x y) u d =
      if σ d = x then corner σ θ u d * corner σ θ u y else corner σ θ u d := by
  have hup : u (θ x) = u y := by
    have hh : u (θ x) * (u y)⁻¹ = 1 := by simpa only [corner,hs] using hc
    exact mul_inv_eq_one.mp hh
  unfold corner
  rw [suppress_u θ hθ u hxy hx hy hup huq hdx hdy,cap_vertex_other σ hxy hs hdx hdy]
  split_ifs with hd
  · rw [hd,huq]
    group
  · rfl
end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
lemma components_map (e : D → B) (σ θ : Perm D) (σ' θ' : Perm B)
    (hs : ∀ d, e (σ d) = σ' (e d)) (ht : ∀ d, e (θ d) = θ' (e d))
    {x y : D} (h : components σ θ x y) : components σ' θ' (e x) (e y) := by
  have hl : components σ θ ≤ (components σ' θ').comap e := by
    apply sup_le
    · apply cycle_le_of_step
      intro d
      change components σ' θ' (e (σ d)) (e d)
      rw [hs]
      exact (le_sup_left : SameCycle.setoid σ' ≤ components σ' θ') SameCycle.rfl.apply_left
    · apply cycle_le_of_step
      intro d
      change components σ' θ' (e (θ d)) (e d)
      rw [ht]
      exact (le_sup_right : SameCycle.setoid θ' ≤ components σ' θ') SameCycle.rfl.apply_left
  exact hl h

lemma components_equiv (e : D ≃ B) (σ θ : Perm D) (x y : D) :
    components (e.permCongrHom σ) (e.permCongrHom θ) (e x) (e y) ↔ components σ θ x y := by
  constructor
  · intro h
    have hh := components_map e.symm _ _ σ θ (by intro d; simp [Equiv.permCongrHom])
      (by intro d; simp [Equiv.permCongrHom]) h
    simpa only [e.symm_apply_apply] using hh
  · exact components_map e σ θ _ _ (fun d ↦ by simp [Equiv.permCongrHom])
      (fun d ↦ by simp [Equiv.permCongrHom])

lemma classes_components_equiv (e : D ≃ B) (σ θ : Perm D) :
    classes (components (e.permCongrHom σ) (e.permCongrHom θ)) = classes (components σ θ) := by
  symm
  exact Fintype.card_congr (Quotient.congr e (fun x y ↦ (components_equiv e σ θ x y).symm))

lemma planar_equiv (e : D ≃ B) (σ θ : Perm D) :
    planar (e.permCongrHom σ) (e.permCongrHom θ) ↔ planar σ θ := by
  unfold planar
  rw [← map_mul]
  have hnum (τ : Perm D) : numCycles (e.permCongrHom τ) = numCycles τ := numCycles_equiv e τ
  rw [hnum σ,hnum θ,hnum (σ*θ),classes_components_equiv]
  rw [Fintype.card_congr e]

lemma connected_equiv (e : D ≃ B) (σ θ : Perm D) (hc : components σ θ = ⊤) :
    components (e.permCongrHom σ) (e.permCongrHom θ) = ⊤ := by
  apply top_unique
  intro x y _
  obtain ⟨x,rfl⟩ := e.surjective x
  obtain ⟨y,rfl⟩ := e.surjective y
  apply (components_equiv e σ θ x y).mpr
  rw [hc]
  trivial
end

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D : Type*} [Fintype V] [Fintype I] [Fintype D]

lemma sum_eq_zero_of_opposite (θ : Perm D) (t : D → ℤ) (ht : ∀ d, t (θ d) = -t d) : ∑ d, t d = 0 := by
  have hh := Equiv.sum_comp θ t
  rw [Finset.sum_congr rfl (fun d _ ↦ ht d),Finset.sum_neg_distrib] at hh
  omega

lemma vertex_balance (e : V × I ≃ D) (ε : V → ℤ) (s : I → ℤ)
    (hs : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1) (θ : Perm D) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (he : ∀ v i, t (e (v,i)) = ε v*s i) :
    ∑ v, ε v = 0 := by
  have hh := sum_eq_zero_of_opposite θ t ht
  rw [← e.sum_comp] at hh
  have hm : (∑ vi : V × I, t (e vi)) = (∑ v, ε v) * (∑ i, s i) := by
    simp only [Fintype.sum_prod_type,he,← Finset.mul_sum,← Finset.sum_mul]
  rw [hm] at hh
  rcases hs with hs | hs <;> rw [hs] at hh <;> simpa using hh

/-- Exact positive/negative disk coordinates, derived from the sign conservation
 of the bands rather than postulated as a balancing hypothesis. -/
lemma balanced_vertices (ε : V → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (hzero : (∑ v, ε v) = 0) :
    ∃ q : ({v // ε v = 1} ⊕ {v // ε v = 1}) ≃ V,
      (∀ k, ε (q (Sum.inl k)) = 1) ∧ (∀ k, ε (q (Sum.inr k)) = -1) := by
  let P := {v // ε v = 1}
  let N := {v // ¬ ε v = 1}
  let e : P ⊕ N ≃ V := Equiv.sumCompl (fun v ↦ ε v = 1)
  have hn (v : N) : ε v.val = -1 := (hε v.val).resolve_left v.property
  have hh := e.sum_comp ε
  rw [hzero] at hh
  simp only [Fintype.sum_sum_type] at hh
  have hP : ∑ p : P, ε (e (Sum.inl p)) = (Fintype.card P : ℤ) := by
    change (∑ p : P, ε p.val) = _
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using
      Finset.sum_congr rfl (fun (p : P) (_ : p ∈ Finset.univ) ↦ p.property)
  have hN : ∑ n : N, ε (e (Sum.inr n)) = -(Fintype.card N : ℤ) := by
    change (∑ n : N, ε n.val) = _
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_neg,one_mul,mul_one] using
      Finset.sum_congr rfl (fun (n : N) (_ : n ∈ Finset.univ) ↦ hn n)
  rw [hP,hN] at hh
  have hcard : Fintype.card P = Fintype.card N := by omega
  let f : P ≃ N := Fintype.equivOfCardEq hcard
  refine ⟨(Equiv.sumCongr (Equiv.refl P) f).trans e,?_,?_⟩
  · intro p
    exact p.property
  · intro p
    exact hn (f p)
end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

def vertexNext (ρ : Perm I) (ε : V → ℤ) (p : V × I) : V × I :=
  (p.1, if ε p.1 = 1 then ρ p.2 else ρ.symm p.2)
def vertexCorner (ρ : Perm I) (a : I → A) (ε : V → ℤ) (p : V × I) : A :=
  if ε p.1 = 1 then a p.2 else (a (ρ.symm p.2))⁻¹

theorem relator_corner_rigidity [Nonempty I]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (e : V × I ≃ D) (ε : V → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (σ θ : Perm D) (hσ : ∀ v i, σ (e (v,i)) = e (vertexNext ρ ε (v,i)))
    (hθ : ∀ d, θ (θ d) = d) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (he : ∀ v i, t (e (v,i)) = ε v*s i)
    (hconn : components σ θ = ⊤) (hp : planar σ θ)
    (u : D → A) (p : D)
    (hu : ∀ v i, e (v,i) ≠ p → vertexCorner ρ a ε (v,i) = corner σ θ u (e (v,i))) :
    vertexCorner ρ a ε (e.symm p) = corner σ θ u p := by
  have hz := vertex_balance e ε s hsum θ t ht he
  obtain ⟨q,hqP,hqN⟩ := balanced_vertices ε hε hz
  let K := {v // ε v = 1}
  have hK : Nonempty K := by
    have hV : Nonempty V := ⟨(e.symm p).1⟩
    let v := Classical.arbitrary V
    rcases q.symm v with k | k
    · exact ⟨k⟩
    · exact ⟨k⟩
  let E : KervaireMixing.Slot I K ≃ D := (Equiv.prodCongr q (Equiv.refl I)).trans e
  let S := KervaireMixing.successor (K := K) ρ
  let T := E.symm.permCongrHom θ
  have hES : ∀ d, σ (E d) = E (S d) := by
    rintro ⟨k|k,i⟩
    · change σ (e (q (Sum.inl k),i)) = e (q (Sum.inl k),ρ i)
      simpa only [vertexNext,hqP,ite_true] using hσ (q (Sum.inl k)) i
    · change σ (e (q (Sum.inr k),i)) = e (q (Sum.inr k),ρ.symm i)
      simpa only [vertexNext,hqN,show (-1:ℤ) ≠ 1 by omega,ite_false] using hσ (q (Sum.inr k)) i
  have hS : E.symm.permCongrHom σ = S := by
    apply Equiv.ext
    intro d
    change E.symm (σ (E d)) = _
    rw [hES,E.symm_apply_apply]
  have hT (d) : T (T d) = d := by
    change E.symm (θ (E (E.symm (θ (E d))))) = d
    rw [E.apply_symm_apply,hθ,E.symm_apply_apply]
  have htE (d) : t (E d) = KervaireBoundary.traversalSign s d := by
    rcases d with ⟨k|k,i⟩
    · change t (e (q (Sum.inl k),i)) = s i
      rw [he,hqP,one_mul]
    · change t (e (q (Sum.inr k),i)) = -s i
      rw [he,hqN,neg_one_mul]
  have hop (d) : KervaireBoundary.traversalSign s (T d) = - KervaireBoundary.traversalSign s d := by
    rw [← htE,← htE]
    change t (E (E.symm (θ (E d)))) = _
    rw [E.apply_symm_apply,ht]
  have hconn' : components S T = ⊤ := by
    rw [← hS]
    exact connected_equiv E.symm σ θ hconn
  have hp' : planar S T := by
    rw [← hS]
    exact (planar_equiv E.symm σ θ).mpr hp
  have hl (d) : (KervaireMixing.labels ρ a d)⁻¹ =
      vertexCorner ρ a ε (e.symm (E d)) := by
    rcases d with ⟨k|k,i⟩
    · change (a i)⁻¹⁻¹ = vertexCorner ρ a ε (e.symm (e (q (Sum.inl k),i)))
      simp only [e.symm_apply_apply,vertexCorner,hqP,ite_true,inv_inv]
    · change (a (ρ.symm i))⁻¹ = vertexCorner ρ a ε (e.symm (e (q (Sum.inr k),i)))
      simp only [e.symm_apply_apply,vertexCorner,hqN,show (-1:ℤ) ≠ 1 by omega,ite_false]
  have hc (d) : corner S T (u ∘ E) d = corner σ θ u (E d) := by
    simp only [corner,Function.comp_apply]
    change u (E (E.symm (θ (E d)))) * _ = _
    rw [E.apply_symm_apply,← hES]
  have hh := planar_corner_rigidity ρ hρ a s hs hsum T hT hop hconn' hp'
    (u ∘ E) (E.symm p) (by
      intro d hd
      rw [hl]
      change _ = corner S T (u ∘ E) d
      rw [hc]
      have hne : E d ≠ p := fun h ↦ hd (E.injective (h.trans (E.apply_symm_apply p).symm))
      simpa only [Prod.mk.eta,e.apply_symm_apply] using
        hu (e.symm (E d)).1 (e.symm (E d)).2 (by simpa only [Prod.mk.eta,e.apply_symm_apply] using hne))
  change _ = corner σ θ u p
  rw [hl] at hh
  change _ = corner S T (u ∘ E) (E.symm p) at hh
  rw [hc,E.apply_symm_apply] at hh
  exact hh

/-- Disjoint relator disks in a larger ribbon diagram. The other darts may
belong to an outside word or be isolated markers from previous cancellations. -/
structure DiskAtlas (ρ : Perm I) (a : I → A) (s : I → ℤ)
    (σ : Perm D) (t : D → ℤ) where
  disk : V × I ↪ D
  ε : V → ℤ
  polarity : ∀ v, ε v = 1 ∨ ε v = -1
  next : ∀ v i, σ (disk (v,i)) = disk (vertexNext ρ ε (v,i))
  sign : ∀ v i, t (disk (v,i)) = ε v*s i

omit [Fintype V] [Fintype D] [DecidableEq D] [Group A] in
/-- Every dart on a word disk lies in the same ribbon component as its
chosen representative. -/
lemma disk_sameCycle (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j)
    (a : I → A) (s : I → ℤ) (σ : Perm D) (t : D → ℤ)
    (b : DiskAtlas (V := V) ρ a s σ t) (v : V) (i j : I) :
    σ.SameCycle (b.disk (v,i)) (b.disk (v,j)) := by
  let f : I → D := fun i ↦ b.disk (v,i)
  by_cases hv : b.ε v = 1
  · have hf (i) : σ (f i) = f (ρ i) := by simpa only [f,vertexNext,hv,ite_true] using b.next v i
    obtain ⟨n,hn⟩ := (hρ i j).exists_nat_pow_eq
    have hp : ∀ n, (σ^n) (f i) = f ((ρ^n) i) := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ',mul_apply,ih,hf,pow_succ',mul_apply]
    have hh := (hp n).trans (congrArg f hn)
    change σ.SameCycle (f i) (f j)
    rw [← hh]
    exact SameCycle.rfl.pow_right
  · have hf (i) : σ (f i) = f (ρ.symm i) := by simpa only [f,vertexNext,hv,ite_false] using b.next v i
    obtain ⟨n,hn⟩ := (hρ i j).inv.exists_nat_pow_eq
    have hp : ∀ n, (σ^n) (f i) = f ((ρ.symm^n) i) := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ',mul_apply,ih,hf,pow_succ',mul_apply]
    have hh := (hp n).trans (congrArg f hn)
    change σ.SameCycle (f i) (f j)
    rw [← hh]
    exact SameCycle.rfl.pow_right

/-- Restricting whole relator disks to one component retains the literal word
coordinates, including the actual reversed corners of negative disks. -/
theorem atlas_component_rigidity [Nonempty I]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (hp : planar σ θ)
    (b : DiskAtlas (V := V) ρ a s σ t) (u : D → A) (p : D)
    (hcovered : ∀ d, components σ θ p d → ∃ vi, b.disk vi = d)
    (hu : ∀ v i, b.disk (v,i) ≠ p → vertexCorner ρ a b.ε (v,i) = corner σ θ u (b.disk (v,i))) :
    ∀ vi, b.disk vi = p → vertexCorner ρ a b.ε vi = corner σ θ u p := by
  let r := components σ θ
  let i₀ := Classical.arbitrary I
  let W := {v : V // r p (b.disk (v,i₀))}
  let c : Quotient r := Quotient.mk r p
  let F := Fiber r c
  let σ' := fiberPerm σ r le_sup_left c
  let θ' := fiberPerm θ r le_sup_right c
  have hvi (v : W) (i : I) : r p (b.disk (v.val,i)) :=
    r.trans' v.property ((le_sup_left : SameCycle.setoid σ ≤ r) (disk_sameCycle ρ hρ a s σ t b v.val i₀ i))
  let f : W × I → F := fun vi ↦ ⟨b.disk (vi.1.val,vi.2),Quotient.sound (r.symm' (hvi vi.1 vi.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v,i⟩ ⟨w,j⟩ hh
      have hcov := b.disk.injective (congrArg Subtype.val hh)
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hcov)
      · change i = j
        exact congrArg Prod.snd hcov
    · intro d
      have hd : r p d.val := r.symm' (Quotient.exact d.property)
      obtain ⟨⟨v,i⟩,hi⟩ := hcovered d.val hd
      have hv : r p (b.disk (v,i₀)) :=
        r.trans' (hi ▸ hd) ((le_sup_left : SameCycle.setoid σ ≤ r)
          (disk_sameCycle ρ hρ a s σ t b v i i₀))
      exact ⟨(⟨v,hv⟩,i),Subtype.ext hi⟩
  let e : W × I ≃ F := Equiv.ofBijective f hf
  let p' : F := ⟨p,rfl⟩
  have hh := relator_corner_rigidity ρ hρ a s hs hsum e (fun v : W ↦ b.ε v.val)
    (fun v ↦ b.polarity v.val) σ' θ'
    (by intro v i; apply Subtype.ext; exact b.next v.val i)
    (by intro d; apply Subtype.ext; exact hθ d.val)
    (fun d : F ↦ t d.val) (fun d ↦ ht d.val) (fun v i ↦ b.sign v.val i)
    (fiber_connected σ θ c) (planar_fiber σ θ hp c) (fun d : F ↦ u d.val) p'
    (by intro v i hne; exact hu v.val i (fun h ↦ hne (Subtype.ext h)))
  intro vi hvi'
  have hev : (e.symm p').1.val = vi.1 ∧ (e.symm p').2 = vi.2 := by
    have hh' := congrArg Subtype.val (e.apply_symm_apply p')
    change b.disk ((e.symm p').1.val,(e.symm p').2) = p at hh'
    exact Prod.mk.inj (b.disk.injective (hh'.trans hvi'.symm))
  change vertexCorner ρ a (fun v : W ↦ b.ε v.val) (e.symm p') = corner σ θ u p at hh
  simpa only [vertexCorner,hev] using hh
end KervaireRibbon

end

end OAI
