import OAI.MathematicalPhysics.Heisenberg.LatticePaths

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

def Ball {d : ℕ} (r : ℤ) (x : Site d) : Set (Site d) :=
  {z | ∀ j, |z j - x j| ≤ r}

lemma step_translate {d : ℕ} (u : Site d) {x y : Site d} (h : Step x y) :
    Step (u + x) (u + y) := by
  obtain ⟨j, hj, hk⟩ := h
  refine ⟨j, ?_, ?_⟩
  · simp only [Pi.add_apply]
    rcases hj with h | h
    · left; omega
    · right; omega
  · intro k hkj
    simp only [Pi.add_apply, hk k hkj]

lemma reach_translate {d : ℕ} (u : Site d) (U W : Set (Site d))
    (hUW : ∀ z ∈ U, u + z ∈ W) {x y : Site d} (h : Reach U x y) :
    Reach W (u + x) (u + y) := by
  induction h with
  | refl => exact reach_refl W (u + x)
  | @tail b c hbc hstep ih =>
    exact ih.tail ⟨step_translate u hstep.1, hUW b hstep.2.1, hUW c hstep.2.2⟩

lemma translate_mem_ball {d : ℕ} (u z : Site d) (r : ℤ) :
    u + z ∈ Ball r u ↔ z ∈ Box r := by
  simp [Ball, Box]

def ballFinset (d r : ℕ) (u : Site d) : Finset (Site d) :=
  (boxFinset d r).image (fun z => u + z)

@[simp] lemma mem_ballFinset (d r : ℕ) (u z : Site d) :
    z ∈ ballFinset d r u ↔ z ∈ Ball r u := by
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact (translate_mem_ball u a r).mpr ((mem_boxFinset ..).mp ha)
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨z - u, ?_, by abel⟩
    exact (mem_boxFinset ..).mpr hz

lemma ballFinset_card (d r : ℕ) (u : Site d) :
    (ballFinset d r u).card = (2 * r + 1) ^ d := by
  rw [ballFinset, Finset.card_image_of_injective _ (add_right_injective u), card_boxFinset]

theorem local_connectivity {d : ℕ} (hd : 2 ≤ d) (K : ℕ) (hK : 1 ≤ K)
    (u v : Site d) (F : Set (Site d)) (hvu : v ∈ Ball K u)
    (huF : u ∉ F) (hvF : v ∉ F)
    (hF : ((ballFinset d (K + 2 * d) u).filter (· ∈ F)).card < 2 * d) :
    ∃ p : (latticeGraph (Ball (K + 2 * d) u \ F)).Walk u v,
      p.IsPath ∧ p.length ≤ (2 * (K + 2 * d) + 1) ^ d := by
  let C := (ballFinset d (K + 2 * d) u).filter (· ∈ F)
  let G := C.image (fun z => z - u)
  have hG : G.card < 2 * d := (Finset.card_image_le).trans_lt hF
  have hzero : (0 : Site d) ∉ G := by
    intro hz
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
    have hae : a = u := sub_eq_zero.mp he
    exact huF (hae ▸ (Finset.mem_filter.mp ha).2)
  have hvG : v - u ∉ G := by
    intro hz
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
    have hae : a = v := sub_left_injective he
    exact hvF (hae ▸ (Finset.mem_filter.mp ha).2)
  have hzbox : (0 : Site d) ∈ Box K := by intro j; simp
  have hvbox : v - u ∈ Box K := hvu
  have hconn := finite_obstacle_connection hd K (by positivity) 0 (v - u)
    hzbox hvbox G hzero hvG hG
  have hball : Reach (Ball (K + 2 * d) u \ F) u v := by
    have h := reach_translate u (Box (K + 2 * d) \ (G : Set (Site d)))
      (Ball (K + 2 * d) u \ F) (fun z hz => ?_) hconn
    · have he : u + (v - u) = v := by abel
      simpa only [add_zero, he] using h
    · refine ⟨(translate_mem_ball ..).mpr hz.1, ?_⟩
      intro hzF
      apply hz.2
      apply Finset.mem_image.mpr
      refine ⟨u + z, Finset.mem_filter.mpr ⟨?_, hzF⟩, by abel⟩
      apply (mem_ballFinset ..).mpr
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (translate_mem_ball u z (K + 2 * d)).mpr hz.1
  obtain ⟨p, hp⟩ := reach_has_simple_path _ u v hball
  refine ⟨p, hp, ?_⟩
  have hsupport : p.support.toFinset ⊆ ballFinset d (K + 2 * d) u := by
    intro z hz
    apply (mem_ballFinset ..).mpr
    have hzU := path_support_mem (Ball (K + 2 * d) u \ F) u v
      ⟨by intro j; simp; positivity, huF⟩ p z (List.mem_toFinset.mp hz)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hzU.1
  have hc := Finset.card_le_card hsupport
  rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support,
    ballFinset_card] at hc
  omega

end Heisenberg.Geometry

namespace Heisenberg.LatticePotential
variable {A : Type*} [AddCommGroup A]

def integral (f : ℤ → A) : ℤ → A
  | .ofNat n => ∑ k ∈ Finset.range n, f k
  | .negSucc n => -(∑ k ∈ Finset.range (n+1), f (-(k:ℤ)-1))

@[simp] lemma integral_zero (f : ℤ → A) : integral f 0 = 0 := by simp [integral]

lemma integral_succ (f : ℤ → A) (z : ℤ) : integral f (z+1) = integral f z + f z := by
  cases z with
  | ofNat n =>
    change (∑ k ∈ Finset.range (n+1), f (k:ℤ)) = (∑ k ∈ Finset.range n, f (k:ℤ)) + f (n:ℤ)
    exact Finset.sum_range_succ (fun k => f (k:ℤ)) n
  | negSucc n =>
    cases n with
    | zero => simp [integral]
    | succ n =>
      change -(∑ k ∈ Finset.range (n+1), f (-(k:ℤ)-1)) =
        -(∑ k ∈ Finset.range (n+1+1), f (-(k:ℤ)-1)) + f (Int.negSucc (n+1))
      rw [Finset.sum_range_succ (fun k : ℕ => f (-(k:ℤ)-1)) (n+1)]
      have he : Int.negSucc (n+1) = -((n+1:ℕ):ℤ)-1 := by omega
      rw [he]
      abel

lemma integral_ext_zero (f g : ℤ → A) (h0 : f 0 = g 0)
    (h : ∀ z, f (z+1)-f z = g (z+1)-g z) : f = g := by
  funext z
  induction z using Int.induction_on with
  | zero => exact h0
  | succ z ih => have := h z; rw [ih] at this; simpa only [Nat.cast_add,Nat.cast_one] using sub_left_inj.mp this
  | pred z ih =>
    have he := h (-(z:ℤ)-1)
    simp only [sub_add_cancel] at he
    rw [ih] at he
    exact sub_right_inj.mp he

lemma integral_sub (f g : ℤ → A) (z : ℤ) :
    integral (fun k => f k-g k) z = integral f z-integral g z := by
  cases z <;> simp [integral,Finset.sum_sub_distrib]; abel

lemma integral_telescoping (f : ℤ → A) (z : ℤ) :
    integral (fun k => f (k+1)-f k) z = f z-f 0 := by
  have h := integral_ext_zero (integral (fun k => f (k+1)-f k)) (fun z => f z-f 0)
    (by simp) (fun k => by rw [integral_succ]; abel)
  exact congrFun h z

abbrev Site (d : ℕ) := Fin d → ℤ

def shift {d : ℕ} (x : Site d) (i : Fin d) : Site d := Function.update x i (x i+1)

lemma shift_cons_zero {d : ℕ} (a : ℤ) (x : Site d) :
    shift (Fin.cons a x) 0 = Fin.cons (a+1) x := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [shift]

lemma shift_cons_succ {d : ℕ} (a : ℤ) (x : Site d) (i : Fin d) :
    shift (Fin.cons a x) i.succ = Fin.cons a (shift x i) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [shift,Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · by_cases he : j = i
    · subst j; simp [shift]
    · simp [shift,he]

def Closed {d : ℕ} (F : Site d → Fin d → A) : Prop :=
  ∀ x i j, F x i+F (shift x i) j = F x j+F (shift x j) i

theorem exists_potential (d : ℕ) (F : Site d → Fin d → A) (hF : Closed F) :
    ∃ g : Site d → A, ∀ x i, g (shift x i)-g x = F x i := by
  induction d with
  | zero => exact ⟨fun _ => 0, fun _ i => Fin.elim0 i⟩
  | succ d ih =>
    let F₀ : Site d → Fin d → A := fun x i => F (Fin.cons 0 x) i.succ
    have h₀ : Closed F₀ := by
      intro x i j
      simpa only [F₀,shift_cons_succ] using hF (Fin.cons 0 x) i.succ j.succ
    obtain ⟨g₀,hg₀⟩ := ih F₀ h₀
    let g : Site (d+1) → A := fun x =>
      g₀ (Fin.tail x)+integral (fun k => F (Fin.cons k (Fin.tail x)) 0) (x 0)
    refine ⟨g,?_⟩
    intro x i
    have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    nth_rw 1 [hx]
    rw [hx]
    generalize x 0 = a
    generalize Fin.tail x = y
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [shift_cons_zero]
      simp only [g,Fin.tail_cons,Fin.cons_zero,integral_succ]
      abel
    · rw [shift_cons_succ]
      simp only [g,Fin.tail_cons,Fin.cons_zero]
      have hdiff : (fun k => F (Fin.cons k (shift y j)) 0-F (Fin.cons k y) 0) =
          (fun k => F (Fin.cons (k+1) y) j.succ-F (Fin.cons k y) j.succ) := by
        funext k
        have hc := hF (Fin.cons k y) 0 j.succ
        rw [shift_cons_zero,shift_cons_succ] at hc
        apply sub_eq_sub_iff_add_eq_add.mpr
        simpa only [add_comm] using hc.symm
      have hent := integral_telescoping (fun k => F (Fin.cons k y) j.succ) a
      rw [← hdiff,integral_sub] at hent
      have hbase := hg₀ y j
      dsimp only [F₀] at hbase
      calc
        _ = (g₀ (shift y j)-g₀ y) +
            (integral (fun k => F (Fin.cons k (shift y j)) 0) a -
              integral (fun k => F (Fin.cons k y) 0) a) := by abel
        _ = _ := by rw [hbase,hent]; abel

end Heisenberg.LatticePotential

namespace Heisenberg.LatticeCut
open Heisenberg.LatticePotential
abbrev Edge (d : ℕ) := Site d × Fin d

def color {d : ℕ} (H : Set (Site d)) (x : Site d) : ℤ := if x ∈ H then 1 else 0

def Cut {d : ℕ} (H : Set (Site d)) (e : Edge d) : Prop := color H e.1 ≠ color H (shift e.1 e.2)

def square {d : ℕ} (x : Site d) (i j : Fin d) : Finset (Edge d) :=
  {(x,i),(shift x i,j),(x,j),(shift x j,i)}

def Linked {d : ℕ} (H : Set (Site d)) (e f : Edge d) : Prop :=
  Cut H e ∧ Cut H f ∧ ∃ x i j, i ≠ j ∧ e ∈ square x i j ∧ f ∈ square x i j

def CutReach {d : ℕ} (H : Set (Site d)) (e f : Edge d) := Relation.ReflTransGen (Linked H) e f

lemma cutReach_cut {d : ℕ} {H : Set (Site d)} {e f : Edge d} (he : Cut H e) (h : CutReach H e f) : Cut H f := by
  induction h with
  | refl => exact he
  | tail _ h _ => exact h.2.1

lemma cutReach_square {d : ℕ} {H : Set (Site d)} {e f f' : Edge d} {x : Site d} {i j : Fin d}
    (he : Cut H e) (h : CutReach H e f) (hf : f ∈ square x i j) (hf' : f' ∈ square x i j)
    (hc : Cut H f') (hij : i ≠ j) : CutReach H e f' := by
  exact h.tail ⟨cutReach_cut he h,hc,⟨x,i,j,hij,hf,hf'⟩⟩

def gradient {d : ℕ} (H : Set (Site d)) (e : Edge d) (x : Site d) (i : Fin d) : ℤ :=
  if CutReach H e (x,i) then color H (shift x i)-color H x else 0

lemma shift_comm {d : ℕ} (x : Site d) (i j : Fin d) : shift (shift x i) j = shift (shift x j) i := by
  by_cases hij : i = j
  · subst j; rfl
  funext k
  by_cases hki : k = i
  · subst k; simp [shift,Function.update_of_ne hij,Function.update_of_ne (Ne.symm hij)]
  by_cases hkj : k = j
  · subst k; simp [shift,Function.update_of_ne hij,Function.update_of_ne (Ne.symm hij)]
  simp [shift,Function.update_of_ne hki,Function.update_of_ne hkj]

lemma gradient_closed {d : ℕ} (H : Set (Site d)) (e : Edge d) (he : Cut H e) : Closed (gradient H e) := by
  intro x i j
  by_cases hij : i = j
  · subst j; rfl
  by_cases h : ∃ f ∈ square x i j, CutReach H e f
  · obtain ⟨f,hf,hr⟩ := h
    have hg : ∀ f' ∈ square x i j,
        gradient H e f'.1 f'.2 = color H (shift f'.1 f'.2)-color H f'.1 := by
      intro f' hf'
      by_cases hc : Cut H f'
      · exact ite_eq_left (cutReach_square he hr hf hf' hc hij)
      · have hs : color H (shift f'.1 f'.2)-color H f'.1 = 0 := by
          exact sub_eq_zero.mpr (not_not.mp hc).symm
        simp [gradient,hs]
    have h1 := hg (x,i) (by simp [square])
    have h2 := hg (shift x i,j) (by simp [square])
    have h3 := hg (x,j) (by simp [square])
    have h4 := hg (shift x j,i) (by simp [square])
    rw [h1,h2,h3,h4]
    dsimp only
    rw [shift_comm x i j]
    omega
  · have hg : ∀ f ∈ square x i j, gradient H e f.1 f.2 = 0 := by
      intro f hf
      exact ite_eq_right (fun hr => h ⟨f,hf,hr⟩)
    rw [hg (x,i) (by simp [square]),hg (shift x i,j) (by simp [square]),
      hg (x,j) (by simp [square]),hg (shift x j,i) (by simp [square])]

def Connected {d : ℕ} (H : Set (Site d)) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, Heisenberg.Geometry.Reach H x y

lemma step_shift {d : ℕ} {x y : Site d} (h : Heisenberg.Geometry.Step x y) :
    (∃ i, y = shift x i) ∨ (∃ i, x = shift y i) := by
  obtain ⟨i,hi,hother⟩ := h
  rcases hi with hi | hi
  · left
    refine ⟨i,?_⟩
    funext j
    by_cases hji : j = i
    · subst j; simpa [shift] using hi
    · simpa [shift,Function.update_of_ne hji] using hother j hji
  · right
    refine ⟨i,?_⟩
    funext j
    by_cases hji : j = i
    · subst j; simpa [shift] using hi
    · simpa [shift,Function.update_of_ne hji] using (hother j hji).symm

lemma potential_constant {d : ℕ} (H : Set (Site d)) (e : Edge d) (g : Site d → ℤ)
    (hg : ∀ x i, g (shift x i)-g x = gradient H e x i) {U : Set (Site d)}
    (hU : ∀ x ∈ U, ∀ y ∈ U, color H x = color H y)
    {x y : Site d} (h : Heisenberg.Geometry.Reach U x y) : g x = g y := by
  induction h with
  | refl => rfl
  | @tail a b hab hstep ih =>
    have hcol := hU a hstep.2.1 b hstep.2.2
    have he : g a = g b := by
      rcases step_shift hstep.1 with ⟨j,rfl⟩ | ⟨j,rfl⟩
      · have hb := hg a j
        simp only [gradient,← hcol,sub_self,ite_self] at hb
        omega
      · have hb := hg b j
        simp only [gradient,hcol,sub_self,ite_self] at hb
        omega
    exact ih.trans he

theorem cut_connected {d : ℕ} (H : Set (Site d)) (hH : Connected H) (hU : Connected Hᶜ)
    (e f : Edge d) (he : Cut H e) (hf : Cut H f) : CutReach H e f := by
  obtain ⟨g,hg⟩ := exists_potential d (gradient H e) (gradient_closed H e he)
  have hconst : ∀ x y, (x ∈ H ↔ y ∈ H) → g x = g y := by
    intro x y hxy
    by_cases hx : x ∈ H
    · apply potential_constant H e g hg (U := H) (fun z hz w hw => by simp [color,hz,hw])
      exact hH x hx y (hxy.mp hx)
    · have hy : y ∈ Hᶜ := fun hy => hx (hxy.mpr hy)
      apply potential_constant H e g hg (U := Hᶜ) (fun z hz w hw => by simp [color, show z ∉ H from hz, show w ∉ H from hw])
      exact hU x hx y hy
  by_contra hn
  have hf0 := hg f.1 f.2
  simp only [gradient,ite_eq_right hn] at hf0
  have her : CutReach H e e := Relation.ReflTransGen.refl
  have he1 := hg e.1 e.2
  simp only [gradient,ite_eq_left her] at he1
  unfold Cut color at he hf
  by_cases heH : e.1 ∈ H <;> by_cases heH' : shift e.1 e.2 ∈ H <;>
    by_cases hfH : f.1 ∈ H <;> by_cases hfH' : shift f.1 f.2 ∈ H <;>
    simp only [heH,heH',hfH,hfH',↓reduceIte,ne_eq] at he hf
  all_goals try contradiction
  all_goals
    simp only [color,heH,heH',↓reduceIte] at he1
    have ha := hconst e.1 (if e.1 ∈ H ↔ f.1 ∈ H then f.1 else shift f.1 f.2)
      (by split_ifs <;> simp_all)
    have hb := hconst (shift e.1 e.2) (if shift e.1 e.2 ∈ H ↔ f.1 ∈ H then f.1 else shift f.1 f.2)
      (by split_ifs <;> simp_all)
    simp only [heH,heH',hfH,iff_self,true_iff,false_iff,not_true_eq_false,↓reduceIte] at ha hb
    omega

end Heisenberg.LatticeCut
end

end OAI
