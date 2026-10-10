import OAI.NumberTheory.SingleFold.Power

namespace OAI

namespace SingleFold.Binary

def Bits (x y : ℕ) : Prop := ∀ i, x/2^i%2 ≤ y/2^i%2

lemma split (x y : ℕ) : Bits x y ↔ x%2 ≤ y%2 ∧ Bits (x/2) (y/2) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, ?_⟩
    intro i
    simpa [Nat.div_div_eq_div_mul, pow_succ', mul_comm] using h (i+1)
  · rintro ⟨h,h'⟩ (_|i)
    · simpa using h
    · simpa [Nat.div_div_eq_div_mul, pow_succ', mul_comm] using h' i

lemma zero_right (x : ℕ) : Bits x 0 ↔ x=0 := by
  constructor
  · induction x using Nat.strong_induction_on with
    | h x ih =>
      intro hx
      by_cases h : x=0
      · exact h
      have he := (split x 0).mp hx
      have hh := ih (x/2) (Nat.div_lt_self (by omega) (by omega)) (by simpa using he.2)
      simp only [Nat.zero_mod] at he
      omega
  · rintro rfl; intro i; simp

lemma choose_odd_iff (x y : ℕ) : y.choose x % 2=1 ↔ Bits x y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases hy : y=0
    · subst y
      rw [zero_right]
      cases x <;> simp
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n:=y) (k:=x) (p:=2)
    change y.choose x%2 = (y%2).choose (x%2)*(y/2).choose (x/2)%2 at hl
    rw [hl,Nat.mul_mod,split, ← ih (y/2) (Nat.div_lt_self (by omega) (by omega))]
    have hx := Nat.mod_lt x (by omega : 0<2)
    have hy' := Nat.mod_lt y (by omega : 0<2)
    have hz := Nat.mod_lt ((y/2).choose (x/2)) (by omega : 0<2)
    interval_cases hxm : x%2 <;> interval_cases hym : y%2 <;> simp_all

lemma le {x y : ℕ} (h : Bits x y) : x≤y := by
  have hh := (choose_odd_iff x y).mpr h
  by_contra hl
  rw [Nat.choose_eq_zero_of_lt (by omega)] at hh
  omega

lemma ofDigits_digit {B : ℕ} (hB : 0<B) (l : List ℕ) (hl : ∀ a∈l, a<B) (i : ℕ) :
    Nat.ofDigits B l/B^i%B=l[i]?.getD 0 := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i hB l hl]
  have hd : ∀ a∈l.drop i,a<B := fun a ha => hl a (List.mem_of_mem_drop ha)
  have he : l[i]?=(l.drop i)[0]? := by simp
  rw [he]
  generalize l.drop i = v at *
  cases v with
  | nil => simp
  | cons a v =>
    simp only [Nat.ofDigits_cons, Nat.add_mul_mod_self_left, List.getElem?_cons_zero, Option.getD_some]
    exact Nat.mod_eq_of_lt (hd a List.mem_cons_self)

lemma ofDigits_map_range (B n : ℕ) (f : ℕ → ℕ) :
    Nat.ofDigits B ((List.range n).map f) = ∑ i∈Finset.range n, f i*B^i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,Nat.ofDigits_append]
    simp [ih,Finset.sum_range_succ, mul_comm]

lemma choose_digit {x y B : ℕ} (hxy : x≤y) (hB : 2^y<B) :
    (B+1)^y/B^x%B=y.choose x := by
  have hpos : 0<B := lt_of_lt_of_le (by positivity : 0<2^y) (Nat.le_of_lt hB)
  have hl : ∀ a∈(List.range (y+1)).map (Nat.choose y),a<B := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact lt_of_le_of_lt (Nat.choose_le_two_pow y i) hB
  have he : (B+1)^y=Nat.ofDigits B ((List.range (y+1)).map (Nat.choose y)) := by
    rw [ofDigits_map_range,add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_comm]
  rw [he,ofDigits_digit hpos _ hl]
  simp [show x<y+1 by omega]

def System (x y : ℕ) (w : Fin 7 → ℕ) : Prop :=
  let B:=w 0; let H:=w 1; let N:=w 2; let s:=w 3; let d:=w 4; let r:=w 5; let t:=w 6
  x≤y ∧ B=2^(y+1) ∧ H=B^x ∧ N=(B+1)^y ∧
    N=s*B*H+d*H+r ∧ d<B ∧ r<H ∧ d=2*t+1

lemma extract_unique {B H N s d r : ℕ} (h : N=s*B*H+d*H+r) (hd : d<B) (hr : r<H) :
    r=N%H ∧ d=N/H%B ∧ s=N/H/B := by
  have hH : 0<H := by omega
  have hB : 0<B := by omega
  have he : N=(s*B+d)*H+r := by nlinarith only [h]
  have hq : N/H=s*B+d := by rw [he, Nat.add_comm, Nat.add_mul_div_right _ _ hH, Nat.div_eq_of_lt hr, zero_add]
  have hm : N%H=r := by rw [he,Nat.add_mod]; simp [Nat.mod_eq_of_lt hr]
  rw [hq]
  constructor
  · exact hm.symm
  constructor
  · simp [Nat.mod_eq_of_lt hd]
  · rw [Nat.add_comm,Nat.add_mul_div_right _ _ hB,Nat.div_eq_of_lt hd,zero_add]

lemma sound {x y : ℕ} {w : Fin 7 → ℕ} (hw : System x y w) : Bits x y := by
  rcases hw with ⟨hxy,hB,hH,hN,he,hd,hr,ht⟩
  have hh := (extract_unique he hd hr).2.1
  have hpow : 2^y<2^(y+1) := by simp [pow_succ]
  rw [hN,hH,hB,choose_digit hxy hpow] at hh
  apply (choose_odd_iff x y).mp
  rw [← hh,ht]
  omega

lemma unique {x y : ℕ} {w v : Fin 7 → ℕ} (hw : System x y w) (hv : System x y v) : w=v := by
  rcases hw with ⟨_,hB,hH,hN,he,hd,hr,ht⟩
  rcases hv with ⟨_,hB',hH',hN',he',hd',hr',ht'⟩
  have h0 : w 0=v 0 := hB.trans hB'.symm
  have h1 : w 1=v 1 := by rw [hH,hH',h0]
  have h2 : w 2=v 2 := by rw [hN,hN',h0]
  have hh := extract_unique he hd hr
  have hh' := extract_unique he' hd' hr'
  rw [h0,h1,h2] at hh
  have h3 := hh.2.2.trans hh'.2.2.symm
  have h4 := hh.2.1.trans hh'.2.1.symm
  have h5 := hh.1.trans hh'.1.symm
  have h6 : w 6=v 6 := by omega
  funext i; fin_cases i <;> assumption

lemma complete {x y : ℕ} (h : Bits x y) : ∃ w, System x y w := by
  let B:=2^(y+1)
  let H:=B^x
  let N:=(B+1)^y
  let d:=N/H%B
  have hB : 0<B := by positivity
  have hH : 0<H := by positivity
  have hpow : 2^y<B := by dsimp [B]; simp [pow_succ]
  have hd : d=y.choose x := choose_digit (le h) hpow
  have ho : d%2=1 := by rw [hd]; exact (choose_odd_iff x y).mpr h
  refine ⟨![B,H,N,N/H/B,d,N%H,d/2],le h,rfl,rfl,rfl,?_,Nat.mod_lt _ hB,Nat.mod_lt _ hH,?_⟩
  · change N=N/H/B*B*H+(N/H%B)*H+N%H
    have hq := Nat.mod_add_div (N/H) B
    have hn := Nat.mod_add_div N H
    nlinarith only [hq,hn]
  · change d=2*(d/2)+1
    omega
end SingleFold.Binary

namespace SingleFold.Compiler.MapSF
lemma vector {α ι : Type} [Finite ι] {f : ι → (α → ℕ) → ℕ}
    (h : ∀ i, ScalarSF (f i)) : MapSF (fun z i => f i z) := by
  exact ((MapSF.proj (fun i => (i,()))).comp (MapSF.all h)).congr (by intros; rfl)
end SingleFold.Compiler.MapSF

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g h : (α → ℕ) → ℕ}
lemma powerRel (hf : ScalarSF f) (hg : ScalarSF g) (hh : ScalarSF h) :
    SF (fun z => 2≤f z ∧ h z=f z^g z) := by
  have hv : MapSF (fun z => ![f z,g z,h z]) := MapSF.vector (by intro i; fin_cases i <;> assumption)
  exact hv.pullback PowerCompilation.power
end SingleFold.Compiler.ScalarSF

namespace SingleFold.Binary
open Compiler
lemma system_sf : SF (fun z : Fin 2⊕Fin 7 → ℕ => System (z (.inl 0)) (z (.inl 1)) (z ∘ Sum.inr)) := by
  let α:=Fin 2⊕Fin 7
  let a (i : α) : ScalarSF (fun z : α → ℕ => z i) := ScalarSF.proj i
  let x:=a (.inl 0); let y:=a (.inl 1)
  let B:=a (.inr 0); let H:=a (.inr 1); let N:=a (.inr 2)
  let s:=a (.inr 3); let d:=a (.inr 4); let r:=a (.inr 5); let t:=a (.inr 6)
  let k (j : ℕ) : ScalarSF (fun _ : α → ℕ => j) := ScalarSF.const j
  have h := (x.le y).and (((k 2).powerRel (y.add (k 1)) B).and
    ((B.powerRel x H).and (((B.add (k 1)).powerRel y N).and
      ((N.eq ((((s.mul B).mul H).add (d.mul H)).add r)).and
        ((d.lt B).and ((r.lt H).and (d.eq (((k 2).mul t).add (k 1)))))))))
  refine h.congr ?_
  intro z

  constructor
  · rintro ⟨hxy,⟨_,hB⟩,⟨_,hH⟩,⟨_,hN⟩,he⟩
    exact ⟨hxy,hB,hH,hN,he⟩
  · rintro ⟨hxy,hB,hH,hN,he⟩
    have hb : 2≤z (.inr 0) := by
      change 2≤(z ∘ Sum.inr) 0
      rw [hB,pow_succ]
      have := Nat.two_pow_pos (z (.inl 1))
      omega
    exact ⟨hxy,⟨by omega,hB⟩,⟨hb,hH⟩,⟨by omega,hN⟩,he⟩

theorem bits : SF (fun z : Fin 2 → ℕ => Bits (z 0) (z 1)) := by
  have h := system_sf.ex (by intro z w w' hw hw'; exact unique hw hw')
  refine h.congr ?_
  intro z
  exact ⟨fun ⟨w,hw⟩ => sound hw,complete⟩
end SingleFold.Binary

end OAI
