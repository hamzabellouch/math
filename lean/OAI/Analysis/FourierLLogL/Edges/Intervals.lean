import OAI.Analysis.FourierLLogL.Edges.Window

/-! # Charging marked intervals on the path -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Wire
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Pulse
open scoped Classical

variable {M J j : ℕ} {s : Scene M}

abbrev Policy (M : ℕ) := Scene M → ℕ

def tags (p : Policy M) (e : Pulse M) (l : List (Pulse M)) : ℕ :=
    if e.active = true ∧ startMark (p e.scene) (e::l) then 1 else 0
def labels (p : Policy M) : List (Pulse M) → ℕ
| [] => 0
| e::l => tags p e l + labels p l

/-- index budget K=0 requests the all-bit bound -/
def due (K : ℕ) (e : Pulse M) : ℝ :=
    if K=0 ∨ e.active=true then e.signal else 0

lemma due_nonneg (K : ℕ) (e : Pulse M) : 0 ≤ due K e := by
  unfold due; split_ifs; exact signal_nonneg _; exact le_rfl

def fading : List (Pulse M) → Bool → Prop
| [], _ => True
| e::l, a => (e.active=true → a=true) ∧ fading l e.active

lemma faded (l : List (Pulse M)) (h : fading l false) :
    ∀ e∈l, e.active=false := by
  induction l with
  | nil => simp
  | cons i l ih =>
    obtain ⟨h,hl⟩ := h
    have he : i.active=false := by cases H:i.active <;> simp_all
    rw [he] at hl
    intro j hj; rcases List.mem_cons.mp hj with H|H; exact H.symm ▸ he; exact ih hl j H

lemma fades (t : Wire M s) {a : Bool} (h : t.Valid a) (x : Grid M) :
    fading (t.read x) a := by
  induction t generalizing a with
  | term => trivial
  | stay s v t ih => exact ih h.2
  | spot s u k ih => exact ih _ (h.2.2.2 _)
  | link s v k ih => exact ⟨h.2.2.1, ih _ (h.2.2.2 _)⟩

private lemma mark_rent (l : List (Pulse M)) (i : ℕ) (ht : startMark i l) :
    (reach i:ℝ) ≤ 64 * (((l.take (reach i)).map Pulse.signal).sum) := by
  let n := reach i; let L := l.take n
  let f := fun e : Pulse M => max e.realized 0
  have hf (e) : f e^2 ≤ 4*e.signal := whistle_high _ _
  have hQ (l : List (Pulse M)) :
      ((l.map f).sum)^2 ≤ l.length*(4:ℝ)*((l.map Pulse.signal).sum) := by
    have HH (z : List (Pulse M)) :
        0 ≤ (z.map Pulse.signal).sum ∧
        ((z.map f).sum)^2 ≤ z.length*(4:ℝ)*((z.map Pulse.signal).sum) := by
      induction z with
      | nil => simp
      | cons i z ih =>
        obtain ⟨ha,hb⟩ := ih
        simp only [List.sum_cons,List.map_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        refine ⟨add_nonneg (signal_nonneg _) ha,?_⟩
        let m := (z.length:ℝ)
        let a := (z.map Pulse.signal).sum
        let b := (z.map f).sum
        change b^2 ≤ m*4*a at hb
        change (f i+b)^2 ≤ (m+1)*4*(i.signal+a)
        have hv : 0 ≤ m := by unfold m; positivity
        have HH : 2*f i*b ≤ 4*(a + m*i.signal) := by
          rcases eq_or_lt_of_le hv with hi|hi
          · have hx : b=0 := by nlinarith
            rw [← hi,hx]; linarith
          have he := hf i
          by_contra! h
          have hX := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ m^2)
          have hZ := mul_lt_mul_of_pos_left h hi
          nlinarith [sq_nonneg (m*f i-b)]
        nlinarith [hf i]
    exact (HH l).2
  have H (a : List (Pulse M)) : (a.map Pulse.realized).sum ≤ (a.map f).sum := by
    induction a with
    | nil => exact le_rfl
    | cons i a hi =>
      simp only [List.sum_cons,List.map_cons]
      exact add_le_add (le_max_left _ _) hi
  have hx := H L; have he := hQ L
  change ↑n*log 2/2 ≤ (L.map Pulse.realized).sum at ht
  have hn : (0:ℝ)< n := by unfold n; exact_mod_cast reach_pos i
  have hb : (0.5:ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  let a := (L.map Pulse.signal).sum
  have hh : (L.length:ℝ) ≤ n := by unfold L; simp
  have ha : 0 ≤ a := List.sum_nonneg (by intro i hi; rcases List.mem_map.mp hi with ⟨x,_,rfl⟩; exact signal_nonneg x)
  change (n:ℝ) ≤ 64*a
  change _ ≤ _*4*a at he
  have hE : (n:ℝ)/4 ≤ (L.map f).sum := by nlinarith
  have hY : ((n:ℝ)/4)^2 ≤ (n:ℝ)*4*a := (pow_le_pow_left₀ (by positivity) hE 2).trans (he.trans (by gcongr))
  nlinarith

private lemma fades_suffix (l l' : List (Pulse M)) {a : Bool} (h : fading (l++l') a) :
    (∃ b, fading l' b) ∧ ((∃ i∈l, i.active=false) → fading l' false) := by
  induction l generalizing a with
  | nil =>
    refine ⟨⟨a,h⟩,?_⟩; simp
  | cons i l ih =>
    change (_→_)∧fading (l++l') i.active at h
    obtain ⟨hh,hx⟩ := ih h.2
    refine ⟨hh,?_⟩
    rintro ⟨x,hx',hf⟩
    rcases List.mem_cons.mp hx' with H|H; subst x
    · have he (l l' : List (Pulse M)) : fading (l++l') false → fading l' false := by
        induction l with
        | nil => exact fun h => h
        | cons i l ih =>
          rintro ⟨h,h'⟩
          apply ih
          have hh : i.active=false := by cases H : i.active <;> simp_all
          exact hh ▸ h'
      exact he l l' (hf ▸ h.2)
    exact hx ⟨x,H,hf⟩

theorem mark_intervals (p : Policy M) (t : Wire M s) {a : Bool} (h : t.Valid a)
    (K : ℕ) (hk : ∀ x : Scene M, K=0 ∨ reach (p x) ≤ K) (x : Grid M) :
      (labels p (t.read x):ℝ) ≤ 64*(((t.read x).map (due K)).sum) + K := by
  have hv0 (z : List (Pulse M)) : 0 ≤ (z.map (due K)).sum :=
    List.sum_nonneg (by intro i hi; rcases List.mem_map.mp hi with ⟨x,_,rfl⟩; exact due_nonneg K x)
  have hc : ∀ k : ℕ, ∀ (l : List (Pulse M)), l.length=k → ∀ a, fading l a →
      (labels p l:ℝ) ≤ 64*((l.map (due K)).sum) + K := by
    intro k; induction k using Nat.strong_induction_on with
    | h k ih =>
    intro l hl a ha
    cases l with
    | nil => simp [labels]
    | cons e l =>
      let Z := e::l
      rcases ha with ⟨H,hh⟩
      by_cases ht : e.active=true ∧ startMark (p e.scene) (e::l)
      · let n := reach (p e.scene)
        let U := Z.take n; let V := Z.drop n
        have hE : U ++ V= Z := List.take_append_drop n Z
        have he : V.length < k := by
          have h1 : 0 < n := reach_pos _
          change (e::l).length=k at hl; unfold V Z; rw [List.length_drop]
          simp only [List.length_cons] at *; omega
        have hT : (labels p Z:ℝ) ≤ (U.length:ℝ)+labels p V := by
          have hh (l : List (Pulse M)) :
              labels p (l++V) ≤ l.length+labels p V := by
            induction l with
            | nil => simp
            | cons i l ih =>
              change tags p i (l++V) + labels p (l++V) ≤ _
              have ht : tags p i (l++V) ≤ 1 := by unfold tags; split_ifs <;> omega
              simp only [List.length_cons]
              omega
          have H := hh U; rw [hE] at H
          exact_mod_cast H
        have hx1 := mark_rent (e::l) _ ht.2
        have HX : fading Z a := ⟨H,hh⟩
        rw [← hE] at HX
        obtain ⟨⟨b,hx⟩,hx'⟩ := fades_suffix U V HX
        have hz : (Z.map (due K)).sum = (U.map (due K)).sum + (V.map (due K)).sum :=
          calc
            _ = ((U++V).map (due K)).sum := by rw [hE]
            _ = _ := by simp
        have hn : (U.length:ℝ) ≤ n := by simp [U]
        change (labels p Z:ℝ) ≤ 64* (Z.map (due K)).sum + K
        rw [hz]
        by_cases HH : ∀ y∈U, K=0 ∨ y.active=true
        · have hhi := ih _ he V rfl b hx
          change (n:ℝ) ≤ 64*(U.map Pulse.signal).sum at hx1
          have hQ : U.map (due K) = U.map Pulse.signal :=
            List.map_congr_left (fun i hi => ite_eq_left (HH i hi))
          rw [hQ]
          linarith
        push Not at HH
        obtain ⟨i,hi,hK,hi'⟩ := HH
        have hk : (n:ℝ) ≤ K := by
          exact_mod_cast ((hk _).resolve_left hK : n ≤ K)
        have hi'' : fading V false :=
          hx' ⟨i,hi,by cases H:i.active <;> simp_all⟩
        have hj (l : List (Pulse M)) (hh : ∀ i∈l,i.active=false) : labels p l=0 := by
          induction l with
          | nil => rfl
          | cons i l ih =>
            have he : i.active=false := hh i List.mem_cons_self
            have hV := ih fun i hi => hh i (List.mem_cons_of_mem _ hi)
            simp [labels, tags,hV, he]
        rw [hj _ (faded V hi''),Nat.cast_zero] at hT
        linarith [hv0 V,hv0 U]
      have HE : tags p e l=0 := ite_eq_right ht
      have h1 := ih _ (by rw [List.length_cons] at hl; omega : l.length < k) l rfl _ hh
      simp only [labels,HE,zero_add,List.map_cons,List.sum_cons]
      linarith [due_nonneg K e]
  exact hc _ (t.read x) rfl a (t.fades h x)

end FourierLLogL.Dyadic.Procedure.Wire

end OAI
