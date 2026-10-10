import OAI.Computability.Superstring.LayerCode

namespace OAI

namespace Superstring.PeriodWord
open BitCode Hierarchical
variable {α : Type} [Coded α] [Inhabited α]
@[fun_prop] theorem poly_down : Poly (fun q : List α × ℤ × ℤ × ℤ =>
    WindowCode.down (text q.1) q.2.1 q.2.2.1 q.2.2.2) := by
  unfold WindowCode.down
  exact WalkCode.poly_delete.comp
    ((poly_textWord.comp (f := fun q : List α × ℤ × ℤ × ℤ => (q.1,q.2.1,q.2.2.2)) (by fun_prop)).pair
    (poly_textWord.comp (f := fun q : List α × ℤ × ℤ × ℤ => (q.1,q.2.2.2,q.2.2.1)) (by fun_prop)))
@[fun_prop] theorem poly_up : Poly (fun q : List α × ℤ × ℤ × ℤ =>
    WindowCode.up (text q.1) q.2.1 q.2.2.1 q.2.2.2) := by
  unfold WindowCode.up
  exact WalkCode.poly_append.comp
    ((poly_textWord.comp (f := fun q : List α × ℤ × ℤ × ℤ => (q.1,q.2.1,q.2.2.1)) (by fun_prop)).pair
    (poly_textWord.comp (f := fun q : List α × ℤ × ℤ × ℤ => (q.1,q.2.2.1,q.2.2.2)) (by fun_prop)))
@[fun_prop] theorem down_fn {β : Type} [Coded β] {U : β → List α} {a b c : β → ℤ}
    (hU : Poly U) (ha : Poly a) (hb : Poly b) (hc : Poly c) :
    Poly (fun q => WindowCode.down (text (U q)) (a q) (b q) (c q)) :=
  poly_down.comp (hU.pair (ha.pair (hb.pair hc)))
@[fun_prop] theorem up_fn {β : Type} [Coded β] {U : β → List α} {a b c : β → ℤ}
    (hU : Poly U) (ha : Poly a) (hb : Poly b) (hc : Poly c) :
    Poly (fun q => WindowCode.up (text (U q)) (a q) (b q) (c q)) :=
  poly_up.comp (hU.pair (ha.pair (hb.pair hc)))
@[fun_prop] theorem textWord_fn {β : Type} [Coded β] {U : β → List α} {a b : β → ℤ}
    (hU : Poly U) (ha : Poly a) (hb : Poly b) :
    Poly (fun q => textWord (text (U q)) (a q) (b q)) :=
  poly_textWord.comp (hU.pair (ha.pair hb))
@[fun_prop] theorem poly_route : Poly (fun q : List α × ℤ × ℤ × ℤ × ℤ =>
    WindowCode.route (text q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have h : Poly (fun q : List α × ℤ × ℤ × ℤ × ℤ =>
      if decide (q.2.2.2.1 ≤ q.2.2.1) then
        WalkCode.join (WindowCode.down (text q.1) q.2.1 q.2.2.1 q.2.2.2.1)
          (WindowCode.up (text q.1) q.2.2.2.1 q.2.2.1 q.2.2.2.2)
      else WalkCode.join (WalkCode.join
        (WindowCode.down (text q.1) q.2.1 q.2.2.1 q.2.2.1)
        (WalkCode.gap (textWord (text q.1) q.2.2.1 q.2.2.2.1)))
        (WindowCode.up (text q.1) q.2.2.2.1 q.2.2.2.1 q.2.2.2.2)) := by
    apply BitCode.Poly.ite
    · exact BitCode.Poly.leInt.comp (f := fun q : List α × ℤ × ℤ × ℤ × ℤ => (q.2.2.2.1,q.2.2.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  simpa only [decide_eq_true_eq,WindowCode.route] using h
end Superstring.PeriodWord

namespace Superstring.GeoCode
open BitCode Hierarchical WalkCode
variable {α : Type}

def exit (Z : List ℕ) (x : ℤ) : ℤ :=
  x + ((Z[(x % (Z.length : ℤ)).toNat]?).getD 0 : ℕ)

def first (Z : List ℕ) (x : ℤ) : ℤ := exit Z (x-1)

@[fun_prop] theorem poly_exit : Poly (fun q : List ℕ × ℤ => exit q.1 q.2) := by
  unfold exit
  have h : Poly (fun q : List ℕ × ℤ => (q.1[(q.2 % (q.1.length : ℤ)).toNat]?).getD 0) :=
    (BitCode.Poly.getD 0).comp (BitCode.Poly.fst.pair (BitCode.Poly.modIntNat.comp
      (f := fun q : List ℕ × ℤ => (q.2,q.1.length)) (by fun_prop)))
  fun_prop
@[fun_prop] theorem poly_first : Poly (fun q : List ℕ × ℤ => first q.1 q.2) := by
  unfold first
  fun_prop

def passage (A : ℤ → α) (z : ℤ → ℤ) (x : ℤ) : Walk α :=
  join (WindowCode.up A x (z (x-1)) (z x)) (WindowCode.down A x (z x) (x+1))

def segment (A : ℤ → α) (z : ℤ → ℤ) (t : ℤ) (n : ℕ) : Walk α :=
  textWord A t (z (t-1)) ::
    (List.range n).flatMap (fun i : ℕ => (passage A z (t+(i : ℤ))).tail)

 theorem segment_zero (A : ℤ → α) (z : ℤ → ℤ) (t : ℤ) :
    segment A z t 0 = [textWord A t (z (t-1))] := rfl
 theorem segment_succ (A : ℤ → α) (z : ℤ → ℤ) (t : ℤ) (n : ℕ) :
    segment A z t (n+1) = join (segment A z t n) (passage A z (t+n)) := by
  simp only [segment,List.range_succ,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,join,List.cons_append]

 theorem passage_realizes {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : Layer V A p) (closed : SubstringClosed V) (x : ℤ) :
    ∃ P : Hierarchical.Path V (textWord A x (L.first x))
        (textWord A (x+1) (L.first (x+1))),
      Path.points P = passage A L.z x ∧
      P.cost = (L.first (x+1)-L.first x).toNat ∧
      ∀ e, L.first x ≤ e → e ≤ L.last x → P.Visits (textWord A x e) := by
  have heq : L.first (x+1) = L.last x := by simp [Layer.first,Layer.last]
  have hbound : x+1 ≤ L.last x := by simpa only [heq] using L.start_le_first (x+1)
  obtain ⟨U,hU,hUc,hUv⟩ := WindowCode.up_realizes closed A (L.start_le_first x)
    (L.first_le_last x) (L.last_actual x)
  obtain ⟨D,hD,hDc,_⟩ := WindowCode.down_realizes closed A (show x ≤ x+1 by omega)
    hbound (L.last_actual x)
  refine ⟨(U.trans D).copy rfl (by rw [heq]),?_,?_,?_⟩
  · rw [WalkCode.points_copy]
    change join (WalkCode.Path.points U) (WalkCode.Path.points D) = _
    rw [hU,hD]
    rfl
  · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hUc,hDc,Nat.add_zero,heq]
  · intro e hfe hel
    simpa only [Hierarchical.Path.visits_copy,Hierarchical.Path.Visits] using
      (Or.inl (hUv e hfe hel) : U.Visits (textWord A x e) ∨ D.Visits (textWord A x e))

 theorem segment_realizes {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : Layer V A p) (closed : SubstringClosed V) (t : ℤ) (n : ℕ) :
    ∃ P : Hierarchical.Path V (textWord A t (L.first t))
        (textWord A (t+n) (L.first (t+n))),
      Path.points P = segment A L.z t n ∧
      P.cost = (L.first (t+n)-L.first t).toNat ∧
      ∀ x e, t ≤ x → x < t+n → L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  induction n with
  | zero =>
    refine ⟨(Hierarchical.Path.nil _ (L.first_actual t)).copy rfl (by simp),?_,by simp [Hierarchical.Path.cost],?_⟩
    · rw [WalkCode.points_copy]
      rfl
    · intro x e htx hxt; omega
  | succ n ih =>
    obtain ⟨P,hP,hPc,hPv⟩ := ih
    obtain ⟨Q,hQ,hQc,hQv⟩ := passage_realizes L closed (t+n)
    have hend : t+(n : ℤ)+1 = t+(n+1 : ℕ) := by omega
    refine ⟨(P.trans Q).copy rfl (by rw [hend]),?_,?_,?_⟩
    · simp only [points_copy,Path.points,hP,hQ,segment_succ]
    · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hPc,hQc]
      have h₁ := L.first_mono (show t ≤ t+(n : ℤ) by omega)
      have h₂ := L.first_mono (show t+(n : ℤ) ≤ t+n+1 by omega)
      rw [hend] at *
      omega
    · intro x e htx hxt hfe hel
      simp only [Hierarchical.Path.visits_copy,Hierarchical.Path.Visits]
      by_cases h : x < t+n
      · exact Or.inl (hPv x e htx h hfe hel)
      · have hx : x = t+n := by omega
        subst x
        exact Or.inr (hQv e hfe hel)

variable [Coded α] [Inhabited α]
@[fun_prop] theorem poly_passage : Poly (fun q : List α × List ℕ × ℤ =>
    passage (PeriodWord.text q.1) (exit q.2.1) q.2.2) := by
  unfold passage
  fun_prop
@[fun_prop] theorem poly_segment : Poly (fun q : List α × List ℕ × ℤ × ℕ =>
    segment (PeriodWord.text q.1) (exit q.2.1) q.2.2.1 q.2.2.2) := by
  have h : Poly (fun q : List α × List ℕ × ℤ × ℕ =>
      (List.range q.2.2.2).flatMap (fun i : ℕ =>
        (passage (PeriodWord.text q.1) (exit q.2.1) (q.2.2.1+i)).tail)) := by
    exact BitCode.Poly.flatten.comp (BitCode.Poly.mapFn
      (f := fun q : (List α × List ℕ × ℤ × ℕ) × ℕ =>
        (passage (PeriodWord.text q.1.1) (exit q.1.2.1) (q.1.2.2.1+q.2)).tail)
      (BitCode.Poly.tail.comp (poly_passage.comp
        (f := fun q : (List α × List ℕ × ℤ × ℕ) × ℕ =>
          (q.1.1, q.1.2.1, q.1.2.2.1+(q.2 : ℤ))) (by fun_prop))) (by fun_prop))
  unfold segment
  fun_prop
end Superstring.GeoCode


namespace Superstring.GeoCode
open BitCode Hierarchical WalkCode
variable {α : Type}

def collective (A : ℤ → α) (hi : ℤ → ℤ) (p k : ℕ) (a b : ℤ) : Walk α :=
  let Y := max b (hi (a-1))
  join (WindowCode.up A a b Y) (WindowCode.route A a Y (a+(k*p : ℕ)) (b+(k*p : ℕ)))

def band (A : ℤ → α) (lo hi : ℤ → ℤ) (p k : ℕ) (t : ℤ) : Walk α :=
  let E := lo t
  let H := hi (t-1)
  if H ≤ E then [textWord A t E]
  else join (WindowCode.up A t E H) (WindowCode.route A t H (t+(k*p : ℕ)) (E+(k*p : ℕ)))

def shortSweep (A : ℤ → α) (hi : ℤ → ℤ) (p k : ℕ) (a b t : ℤ) : Walk α :=
  let K : ℕ := k*p
  let x := min t (a+K)
  let F := hi (x-1)
  join (join (WindowCode.down A a b x) (WindowCode.up A x b F))
    (WindowCode.route A x F (a+K) (b+K))

def individual (A : ℤ → α) (z : ℤ → ℤ) (p : ℕ) (a b : ℤ) : Walk α :=
  let e := max b (z (a+p-1))
  join (WindowCode.route A a b (a+p) e) (WindowCode.up A (a+p) e (b+p))
theorem collective_link_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    {a b : ℤ} (hab : a ≤ b) (hR : textWord A a b ∈ V)
    (h₁ : (L hi).first a ≤ b + (k * p : ℕ))
    (h₂ : (L hi).first a - (L lo).last a ≤ (k * p : ℕ))
    (h₃ : b ≤ (L lo).last a + (k * p : ℕ)) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A a b),
      WalkCode.Path.points P = collective A (L hi).z p k a b ∧
      P.cost = k * p ∧ ∀ i, (L i).TouchedBy P := by
  let K : ℕ := k * p
  let Y := max b ((L hi).first a)
  have hbY : b ≤ Y := le_max_left _ _
  have hHY : (L hi).first a ≤ Y := le_max_right _ _
  have hYK : Y ≤ b + K := by dsimp [Y, K]; omega
  have haY : a ≤ Y := le_trans hab hbY
  have hYV : textWord A a Y ∈ V := by
    by_cases h : b ≤ (L hi).first a
    · simpa only [Y, max_eq_right h] using (L hi).first_actual a
    · simpa only [Y, max_eq_left (le_of_not_ge h)] using hR
  have perK : ∀ x, A (x + K) = A x := periodic_mul A p per k
  have heqR := textWord_translate A (K : ℤ) perK a b
  have hRV : textWord A (a + K) (b + K) ∈ V := heqR.symm ▸ hR
  obtain ⟨U, hU, hUc, hUv⟩ := WindowCode.up_realizes closed A hab hbY hYV
  obtain ⟨Q, hQ, hQc, hQv, _⟩ := WindowCode.route_realizes closed A letters haY
    (show a + K ≤ b + K by omega) (show a ≤ a + K by omega) hYK hYV hRV
  refine ⟨(U.trans Q).copy rfl heqR, ?_, ?_, ?_⟩
  · rw [WalkCode.points_copy]
    change join (WalkCode.Path.points U) (WalkCode.Path.points Q) = _
    rw [hU,hQ]
    rfl
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hQc]
    dsimp [K] at *
    omega
  · intro i
    have hf : (L i).first a ≤ Y := le_trans (hhi i (a - 1)) hHY
    have hz : Y ≤ (L i).last (a + K) := by
      have heq := (L i).shift_mul k a
      have hlo' := hlo i a
      dsimp [Layer.last, K] at *
      rw [heq]
      dsimp [Y]
      omega
    obtain ⟨x, hax, hxK, hfx, hxl⟩ := (L i).meets_height a Y K hf hz
    refine ⟨x, Y, hfx, hxl, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inr (hQv x hax hxK (le_trans ((L i).start_le_first x) hfx))

theorem join_band_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (t : ℤ) (hband : (L hi).first t - (L lo).last t ≤ (k * p : ℕ)) :
    ∃ P : Hierarchical.Path V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)),
      WalkCode.Path.points P = band A (L lo).z (L hi).z p k t ∧
      P.cost ≤ k * p ∧ ∀ i, (L i).TouchedBy P := by
  let E := (L lo).last t
  let H := (L hi).first t
  let K := k * p
  have hE : textWord A t E ∈ V := (L lo).last_actual t
  have hH : textWord A t H ∈ V := (L hi).first_actual t
  have htE : t ≤ E := le_trans ((L lo).start_le_first t) ((L lo).first_le_last t)
  have htH : t ≤ H := (L hi).start_le_first t
  by_cases hHE : H ≤ E
  · refine ⟨Path.nil _ hE, ?_, Nat.zero_le _, ?_⟩
    · change (L hi).z (t-1) ≤ (L lo).z t at hHE
      simp only [WalkCode.Path.points,band,ite_eq_left hHE]
      rfl
    · intro i
      refine ⟨t, E, le_trans (hhi i (t - 1)) hHE, hlo i t, rfl⟩
  · have hEH : E ≤ H := by omega
    have hHK : H ≤ E + K := by dsimp [H, E, K]; omega
    have perK : ∀ x, A (x + K) = A x := periodic_mul A p per k
    have heqE := textWord_translate A (K : ℤ) perK t E
    obtain ⟨U, hU, hUc, hUv⟩ := WindowCode.up_realizes closed A htE hEH hH
    obtain ⟨Q, hQ, hQc, _, _⟩ := WindowCode.route_realizes closed A letters htH
      (show t + K ≤ E + K by omega) (show t ≤ t + K by omega) hHK hH
      (heqE.symm ▸ hE)
    refine ⟨(U.trans Q).copy rfl heqE, ?_, ?_, ?_⟩
    · rw [WalkCode.points_copy]
      change join (WalkCode.Path.points U) (WalkCode.Path.points Q) = _
      rw [hU,hQ]
      change ¬(L hi).z (t-1) ≤ (L lo).z t at hHE
      simp only [band,ite_eq_right hHE]
      rfl
    · simp only [Path.cost_copy, Path.cost_trans, hUc, hQc]
      dsimp [K] at *
      omega
    · intro i
      let e := max E ((L i).first t)
      have hfe : (L i).first t ≤ e := le_max_right _ _
      have heE : E ≤ e := le_max_left _ _
      have hel : e ≤ (L i).last t := max_le (hlo i t) ((L i).first_le_last t)
      have heH : e ≤ H := max_le hEH (hhi i (t - 1))
      refine ⟨t, e, hfe, hel, ?_⟩
      simp only [Path.visits_copy, Path.Visits]
      exact Or.inl (hUv e heE heH)

theorem collective_short_sweep_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k q : ℕ)
    (hk : 1 ≤ k) (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (hi : ι)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (hlong : ∀ i, ¬ (L i).HasShort q)
    {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V)
    (hH : (L hi).first t ≤ b + (k * p : ℕ))
    (hlen : b - a < p + q) (hagr : b - t < q) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A a b),
      WalkCode.Path.points P = shortSweep A (L hi).z p k a b t ∧
      P.cost = k * p ∧ (∀ i, (L i).TouchedBy P) ∧
      ∃ w, P.Visits w ∧ w.length ≤ q := by
  let K := k * p
  let x := min t (a + K)
  let F := (L hi).first x
  have hpK : (p : ℤ) ≤ K := by
    have := Nat.mul_le_mul_right p hk
    simp only [one_mul] at this
    exact_mod_cast this
  have hax : a ≤ x := le_min hat (by omega)
  have hxt : x ≤ t := min_le_left _ _
  have hxK : x ≤ a + K := min_le_right _ _
  have hxb : x ≤ b := by omega
  have hshort : b - x < q := by
    by_cases h : t ≤ a + K
    · dsimp [x]; rw [min_eq_left h]; exact hagr
    · have heq : x = a + K := min_eq_right (by omega)
      rw [heq]
      omega
  have hbfirst : ∀ i, b ≤ (L i).first x := by
    intro i
    have := (L i).first_long_of_not_short q (hlong i) x
    omega
  have hbF : b ≤ F := hbfirst hi
  have hFK : F ≤ b + K := le_trans ((L hi).first_mono hxt) hH
  have hFV : textWord A x F ∈ V := (L hi).first_actual x
  have heqR := textWord_translate A (K : ℤ) (periodic_mul A p per k) a b
  obtain ⟨D, hD, hDc, _⟩ := WindowCode.down_realizes closed A hax hxb hR
  obtain ⟨U, hU, hUc, hUv⟩ := WindowCode.up_realizes closed A hxb hbF hFV
  obtain ⟨Q, hQ, hQc, _, _⟩ := WindowCode.route_realizes closed A letters (le_trans hxb hbF)
    (show a + K ≤ b + K by omega) hxK hFK hFV (heqR.symm ▸ hR)
  refine ⟨((D.trans U).trans Q).copy rfl heqR, ?_, ?_, ?_, ?_⟩
  · rw [WalkCode.points_copy]
    change join (join (WalkCode.Path.points D) (WalkCode.Path.points U)) (WalkCode.Path.points Q) = _
    rw [hD,hU,hQ]
    rfl
  · simp only [Path.cost_copy, Path.cost_trans, hDc, hUc, hQc]
    dsimp [K] at *
    omega
  · intro i
    refine ⟨x, (L i).first x, le_rfl, (L i).first_le_last x, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inr (hUv _ (hbfirst i) (hhi i (x - 1))))
  · refine ⟨textWord A x b, ?_, ?_⟩
    · simp only [Path.visits_copy, Path.Visits]
      exact Or.inl (Or.inl (Path.visits_end D))
    · simp only [length_textWord]
      omega

theorem individual_link_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p q : ℕ)
    (per : ∀ x, A (x + p) = A x) (L : Layer V A p)
    {a b : ℤ} (hab : a ≤ b) (hR : textWord A a b ∈ V)
    (hfirst : L.first a ≤ b) (hlast : b ≤ L.last a + p)
    (hlen : b - a < p + q) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A a b),
      WalkCode.Path.points P = individual A L.z p a b ∧
      P.cost = p ∧ L.TouchedBy P ∧ ∃ w, P.Visits w ∧ w.length ≤ q := by
  let e := max b (L.first (a + p))
  have hbe : b ≤ e := le_max_left _ _
  have hfe : L.first (a + p) ≤ e := le_max_right _ _
  have heL : e ≤ L.last (a + p) := by
    apply max_le
    · simpa only [Layer.last_shift] using hlast
    · exact L.first_le_last _
  have hebp : e ≤ b + p := by
    apply max_le
    · omega
    · rw [Layer.first_shift]
      omega
  have hapse : a + p ≤ e := le_trans (L.start_le_first _) hfe
  have heV : textWord A (a + p) e ∈ V := L.actual _ _ hfe heL
  have heq := textWord_translate A p per a b
  obtain ⟨Q, hQ, hQc, _, w, hQw, hwlen⟩ := WindowCode.route_realizes closed A letters hab hapse
    (by omega) hbe hR heV
  obtain ⟨U, hU, hUc, _⟩ := WindowCode.up_realizes closed A hapse hebp (heq.symm ▸ hR)
  refine ⟨(Q.trans U).copy rfl heq, ?_, ?_, ?_, w, ?_, ?_⟩
  · rw [WalkCode.points_copy]
    change join (WalkCode.Path.points Q) (WalkCode.Path.points U) = _
    rw [hQ,hU]
    rfl
  · simp only [Path.cost_copy, Path.cost_trans, hQc, hUc]
    omega
  · refine ⟨a + p, e, hfe, heL, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Path.visits_end Q)
  · simpa only [Path.visits_copy, Path.Visits] using (Or.inl hQw : Q.Visits w ∨ U.Visits w)
  · omega

end Superstring.GeoCode


namespace Superstring.WalkCode
open BitCode
variable {α β : Type} [Coded α] [Coded β]
@[fun_prop] theorem join_fn {P Q : β → Walk α} (hP : Poly P) (hQ : Poly Q) :
    Poly (fun q => join (P q) (Q q)) := poly_join.comp (hP.pair hQ)
end Superstring.WalkCode
namespace Superstring.PeriodWord
open BitCode Hierarchical
variable {α β : Type} [Coded α] [Coded β] [Inhabited α]
@[fun_prop] theorem route_fn {U : β → List α} {a b c d : β → ℤ}
    (hU : Poly U) (ha : Poly a) (hb : Poly b) (hc : Poly c) (hd : Poly d) :
    Poly (fun q => WindowCode.route (text (U q)) (a q) (b q) (c q) (d q)) :=
  poly_route.comp (hU.pair (ha.pair (hb.pair (hc.pair hd))))
end Superstring.PeriodWord
namespace Superstring.BitCode.Poly
variable {β : Type} [Coded β]
@[fun_prop] theorem leInt_fn {a b : β → ℤ} (ha : Poly a) (hb : Poly b) :
    Poly (fun q => decide (a q ≤ b q)) := leInt.comp (ha.pair hb)
@[fun_prop] theorem maxInt_fn {a b : β → ℤ} (ha : Poly a) (hb : Poly b) :
    Poly (fun q => Max.max (a q) (b q)) := maxInt.comp (ha.pair hb)
@[fun_prop] theorem minInt_fn {a b : β → ℤ} (ha : Poly a) (hb : Poly b) :
    Poly (fun q => Min.min (a q) (b q)) := minInt.comp (ha.pair hb)
end Superstring.BitCode.Poly
namespace Superstring.GeoCode
open BitCode Hierarchical WalkCode
variable {α : Type} [Coded α] [Inhabited α]
@[fun_prop] theorem exit_fn {β : Type} [Coded β] {Z : β → List ℕ} {x : β → ℤ}
    (hZ : Poly Z) (hx : Poly x) : Poly (fun q => exit (Z q) (x q)) :=
  poly_exit.comp (hZ.pair hx)
@[fun_prop] theorem poly_collective : Poly (fun q : List α × List ℕ × ℕ × ℕ × ℤ × ℤ =>
    collective (PeriodWord.text q.1) (exit q.2.1) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold collective
  dsimp only
  fun_prop
@[fun_prop] theorem poly_band : Poly (fun q : List α × List ℕ × List ℕ × ℕ × ℕ × ℤ =>
    band (PeriodWord.text q.1) (exit q.2.1) (exit q.2.2.1) q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold band
  dsimp only
  have h : Poly (fun q : List α × List ℕ × List ℕ × ℕ × ℕ × ℤ =>
      if decide (exit q.2.2.1 (q.2.2.2.2.2-1) ≤ exit q.2.1 q.2.2.2.2.2) then
        [textWord (PeriodWord.text q.1) q.2.2.2.2.2 (exit q.2.1 q.2.2.2.2.2)] else
        join (WindowCode.up (PeriodWord.text q.1) q.2.2.2.2.2 (exit q.2.1 q.2.2.2.2.2)
          (exit q.2.2.1 (q.2.2.2.2.2-1)))
        (WindowCode.route (PeriodWord.text q.1) q.2.2.2.2.2 (exit q.2.2.1 (q.2.2.2.2.2-1))
          (q.2.2.2.2.2+(q.2.2.2.2.1*q.2.2.2.1 : ℕ))
          (exit q.2.1 q.2.2.2.2.2+(q.2.2.2.2.1*q.2.2.2.1 : ℕ)))) := by
    apply BitCode.Poly.ite
    · fun_prop
    · fun_prop
    · fun_prop
  simpa only [decide_eq_true_eq] using h
@[fun_prop] theorem poly_shortSweep : Poly (fun q : List α × List ℕ × ℕ × ℕ × ℤ × ℤ × ℤ =>
    shortSweep (PeriodWord.text q.1) (exit q.2.1) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2) := by
  unfold shortSweep
  dsimp only
  fun_prop
@[fun_prop] theorem poly_individual : Poly (fun q : List α × List ℕ × ℕ × ℤ × ℤ =>
    individual (PeriodWord.text q.1) (exit q.2.1) q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold individual
  dsimp only
  fun_prop
end Superstring.GeoCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

def root (w : List α) : Walk α := join (append [] w) (delete w [])
def rootAt (P : Walk α) (i : ℕ) : Walk α :=
  let w := P[i]?.getD []
  join (join (append [] w) (rotate P i)) (delete w [])

theorem root_spec {V : Set (List α)} (closed : SubstringClosed V) {w : List α} (hw : w ∈ V) :
    Runs V [] [] (root w) ∧ cost (root w) = w.length ∧ w ∈ root w := by
  have ha := append_spec closed [] w (by simpa using hw)
  have hd := delete_spec closed w [] (by simpa using hw)
  have hA : Runs V [] w (append [] w) := by simpa only [List.nil_append] using ⟨ha.1,ha.2.1,ha.2.2.1⟩
  have hD : Runs V w [] (delete w []) := by exact ⟨hd.1,by simpa only [List.append_nil] using hd.2.1,hd.2.2.1⟩
  refine ⟨runs_join hA hD,?_,?_⟩
  · rw [root,cost_join _ _ _ hA.2.2 hD.2.1,ha.2.2.2,hd.2.2.2,Nat.add_zero]
  · rw [root,mem_join hA.2.2 hD.2.1]
    exact Or.inr (List.mem_of_head? hD.2.1)

theorem rootAt_spec {V : Set (List α)} (closed : SubstringClosed V) {P : Walk α} {s : List α}
    (hP : Runs V s s P) {i : ℕ} (hi : i < P.length) :
    Runs V [] [] (rootAt P i) ∧ cost (rootAt P i) = cost P + P[i].length ∧
      ∀ w ∈ P, w ∈ rootAt P i := by
  have hw := hP.1.2.1 P[i] (List.getElem_mem hi)
  obtain ⟨hR,hcR,hvR⟩ := rotate_spec hP hi
  have ha := append_spec closed [] P[i] (by simpa using hw)
  have hd := delete_spec closed P[i] [] (by simpa using hw)
  have hA : Runs V [] P[i] (append [] P[i]) := by simpa only [List.nil_append] using ⟨ha.1,ha.2.1,ha.2.2.1⟩
  have hD : Runs V P[i] [] (delete P[i] []) := by exact ⟨hd.1,by simpa only [List.append_nil] using hd.2.1,hd.2.2.1⟩
  simp only [rootAt,List.getElem?_eq_getElem hi,Option.getD_some]
  have hAR := runs_join hA hR
  refine ⟨runs_join hAR hD,?_,?_⟩
  · rw [cost_join _ _ _ hAR.2.2 hD.2.1,cost_join _ _ _ hA.2.2 hR.2.1,ha.2.2.2,hd.2.2.2,hcR]
    omega
  · intro w hw
    rw [mem_join hAR.2.2 hD.2.1,mem_join hA.2.2 hR.2.1,hvR]
    exact Or.inl (Or.inr hw)

variable [Coded α]
@[fun_prop] theorem poly_root : Poly (root : List α → Walk α) := by unfold root; fun_prop
@[fun_prop] theorem poly_rootAt : Poly (fun q : Walk α × ℕ => rootAt q.1 q.2) := by
  have hw : Poly (fun q : Walk α × ℕ => q.1[q.2]?.getD []) := BitCode.Poly.getD []
  unfold rootAt
  dsimp only
  fun_prop
end Superstring.WalkCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type} [Inhabited α] [DecidableEq α]

def edgeCheck (s t : List α) : Bool :=
  equal t (s ++ [t[s.length]?.getD default]) || equal s ((s[0]?.getD default)::t)

theorem edgeCheck_eq (s t : List α) : edgeCheck s t = true ↔ Edge s t := by
  simp only [edgeCheck,Bool.or_eq_true,BitCode.equal,decide_eq_true_eq,Edge]
  constructor
  · rintro (h|h)
    · exact Or.inl ⟨_,h⟩
    · exact Or.inr ⟨_,h⟩
  · rintro (⟨a,rfl⟩|⟨a,rfl⟩)
    · left
      simp
    · right
      simp

def check (vs P : Walk α) : Bool :=
  !(equal P []) && equal (P.filter (fun w => member w vs)) P &&
    equal ((P.zip P.tail).filter (fun q => edgeCheck q.1 q.2)) (P.zip P.tail)

omit [Inhabited α] [DecidableEq α] in
theorem chain_zip (P : Walk α) : P.IsChain Edge ↔ ∀ q ∈ P.zip P.tail, Edge q.1 q.2 := by
  induction P with
  | nil => simp
  | cons s P ih =>
    cases P with
    | nil => simp
    | cons t P =>
      simp only [List.tail_cons,List.zip_cons_cons,List.isChain_cons_cons,List.mem_cons]
      constructor
      · rintro ⟨hs,hP⟩ q (rfl|hq)
        · exact hs
        · exact ih.mp hP q hq
      · intro h
        exact ⟨h (s,t) (Or.inl rfl),ih.mpr (fun q hq => h q (Or.inr hq))⟩

theorem check_eq (vs P : Walk α) : check vs P = true ↔ Valid {w | w ∈ vs} P := by
  simp only [check,Bool.and_eq_true,Bool.not_eq_true',BitCode.equal,decide_eq_false_iff_not,
    decide_eq_true_eq,List.filter_eq_self,member,Valid,Set.mem_ofPred_eq]
  rw [chain_zip]
  constructor
  · rintro ⟨⟨hne,hv⟩,hc⟩
    exact ⟨hne,fun w hw => hv w hw,fun q hq => (edgeCheck_eq ..).mp (hc q hq)⟩
  · rintro ⟨hne,hv,hc⟩
    exact ⟨⟨hne,fun w hw => hv w hw⟩,fun q hq => (edgeCheck_eq ..).mpr (hc q hq)⟩

variable [Coded α]
@[fun_prop] theorem poly_edgeCheck : Poly (fun q : List α × List α => edgeCheck q.1 q.2) := by
  have h₁ : Poly (fun q : List α × List α => q.2[q.1.length]?.getD default) :=
    (BitCode.Poly.getD default).comp (f := fun q : List α × List α => (q.2,q.1.length)) (by fun_prop)
  have h₂ : Poly (fun q : List α × List α => q.1[0]?.getD default) :=
    (BitCode.Poly.getD default).comp (f := fun q : List α × List α => (q.1,0)) (by fun_prop)
  unfold edgeCheck
  fun_prop
@[fun_prop] theorem poly_check : Poly (fun q : Walk α × Walk α => check q.1 q.2) := by
  unfold check
  have hv : Poly (fun q : Walk α × Walk α => q.2.filter (fun w => member w q.1)) :=
    BitCode.Poly.filterFn (p := fun q : (Walk α × Walk α) × List α => member q.2 q.1.1)
      (by fun_prop) (by fun_prop)
  have he : Poly (fun q : Walk α × Walk α => (q.2.zip q.2.tail).filter (fun x => edgeCheck x.1 x.2)) :=
    BitCode.Poly.filterFn (p := fun q : (Walk α × Walk α) × (List α × List α) => edgeCheck q.2.1 q.2.2)
      (by fun_prop) (by fun_prop)
  fun_prop
end Superstring.WalkCode


namespace Superstring.GeoCode
open BitCode Hierarchical WalkCode
variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}
theorem full_turn_realizes (L : Layer V A p) (closed : SubstringClosed V) (hp : 0 < p)
    (per : ∀ x, A (x + p) = A x) (t : ℤ) :
    ∃ P : Hierarchical.Path V (textWord A t (L.first t)) (textWord A t (L.first t)),
      WalkCode.Path.points P = segment A L.z t p ∧
      P.cost = p ∧ ∀ x e, L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  obtain ⟨Q, hQ, hcQ, hvQ⟩ := segment_realizes L closed t p
  have heq : textWord A (t + p) (L.first (t + p)) = textWord A t (L.first t) := by
    rw [L.first_shift]
    exact textWord_translate A p per t (L.first t)
  let P := Q.copy rfl heq
  have hP : WalkCode.Path.points P = segment A L.z t p := by
    rw [WalkCode.points_copy]
    exact hQ
  have hPc : P.cost = p := by
    simp only [P,Hierarchical.Path.cost_copy,hcQ,L.first_shift]
    omega
  have hPv : ∀ x e, t ≤ x → x < t+p → L.first x ≤ e → e ≤ L.last x →
      P.Visits (textWord A x e) := by
    intro x e htx hxp hfe hel
    exact (Hierarchical.Path.visits_copy ..).mpr (hvQ x e htx hxp hfe hel)
  refine ⟨P,hP, hPc, ?_⟩
  intro x e hfe hel
  let r := t + (x - t) % (p : ℤ)
  let m := (x - t) / (p : ℤ)
  have htr : t ≤ r := by
    have := Int.emod_nonneg (x - t) (show (p : ℤ) ≠ 0 by omega)
    dsimp [r]; omega
  have hrt : r < t + p := by
    have := Int.emod_lt_of_pos (x - t) (show (0 : ℤ) < p by omega)
    dsimp [r]; omega
  have hrx : r + m * p = x := by
    have := Int.emod_add_ediv_mul (x - t) (p : ℤ)
    dsimp [r, m]; omega
  have hf : L.first r ≤ e - m * p := by
    have hh := L.first_shift_int m r
    rw [hrx] at hh
    omega
  have hl : e - m * p ≤ L.last r := by
    have hh := L.shift_int m r
    rw [hrx] at hh
    change e ≤ L.z x at hel
    change e - m * p ≤ L.z r
    omega
  have hpA : Function.Periodic A (p : ℤ) := per
  have heq := textWord_translate A (m * p) (hpA.int_mul m) r (e - m * p)
  rw [hrx, sub_add_cancel] at heq
  rw [heq]
  exact hPv r (e - m * p) htr hrt hf hl


end Superstring.GeoCode

end OAI
