import OAI.Analysis.FourierLLogL.Procedure.Road
import OAI.Analysis.FourierLLogL.Thermal.True

/-! # Observation records in the comparison proof -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal
variable {M J j : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

structure Memory (M : ℕ) where
  profile : Profile M
  current : Grid M

namespace Memory
def piece (A B : Form M) (w : Clutch j M) : Profile M :=
    (B,w.1) :: List.ofFn (fun i => (A,w.2 i))

def stash (m : Memory M) (A B : Form M) (w : Clutch j M) :
    Memory M := ⟨piece A B w ++ m.profile,w.1⟩

structure Ready (m : Memory M) (j : ℕ) (c : Fund M) : Prop where
  ordered : ∀ i ∈ m.profile, 0 ≤ i.1 ∧ i.1 ≤ c.mood
  has : (c.mood, m.current)∈m.profile
  num : m.profile.length = 1+c.uses*(1+clones j)


def temp (j : ℕ) := cushion j / (capA * H j)

def loadE (A B : Form M) (w : Clutch j M) (x : Grid M) :=
    form B (w.1-x) + ∑ i, form A (w.2 i-x)

lemma stash_ready (m : Memory M) {s : Scene M} (h : Ready m j s.fund)
    (u : Update j M s.here) (hD : 0 ≤ u.changeForm) (hA : 0 ≤ s.fund.mood) (w : Clutch j M) :
    Ready (m.stash s.fund.mood (u.next s.fund.mood) w) j (s.fund.advance s.here u) := by
  let B := u.next s.fund.mood
  have H : s.fund.mood ≤ B :=
    (le_add_of_nonneg_right (place_valid _ _)).trans (le_add_of_nonneg_right hD)
  constructor
  · intro t ht
    simp only [stash,piece,List.mem_append,List.mem_cons,List.mem_ofFn] at ht
    rcases ht with (he|he)|he
    · subst t; exact ⟨hA.trans H,le_rfl⟩
    · obtain ⟨i,rfl⟩ := he; exact ⟨hA,H⟩
    obtain ⟨hl,hr⟩ := h.ordered t he
    exact ⟨hl,hr.trans H⟩
  · simp [advance,stash,piece]
  · simp only [stash,List.length_append,piece,List.length_cons,List.length_ofFn,h.num,advance]
    ring

lemma stash_length_bound (m : Memory M) {s : Scene M} (h : Ready m j s.fund)
    (hg : Safe s j J f) :
    ↑(m.profile.length) ≤ observationBudget capA j := by
  rw [h.num,observationBudget]
  push_cast; gcongr
  exact hg.capital.under

lemma sumE_piece (A B : Form M) (w : Clutch j M) (x : Grid M) :
    sumE (piece A B w) x = loadE A B w x := by
  simp only [sumE,piece,List.map_cons,List.map_ofFn,Function.comp_def,
    List.sum_cons,List.sum_ofFn,loadE]

lemma sumE_stash (m : Memory M) (A B : Form M) (w : Clutch j M) (x : Grid M) :
    sumE (m.stash A B w).profile x = loadE A B w x + sumE m.profile x := by
  rw [←sumE_piece]
  simp only [stash,sumE,List.map_append,List.sum_append]

lemma form_in_past (m : Memory M) (p : Form M × Grid M)
    (h : ∀ i∈m.profile, 0 ≤ i.1) (hp : p ∈ m.profile) (x : Grid M) :
    form p.1 (p.2-x) ≤ sumE m.profile x := by
  suffices HH : ∀ l : Profile M, (∀ i∈l, 0 ≤ i.1) → p∈l →
      form p.1 (p.2-x) ≤ sumE l x from HH _ h hp
  intro l; induction l with
  | nil => simp
  | cons i l ih =>
    intro h h'
    have he : 0 ≤ i.1 := h i List.mem_cons_self
    have hh : ∀ i∈l, 0 ≤ i.1 := fun i hi => h i (List.mem_cons_of_mem _ hi)
    simp only [sumE,List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp h' with rfl|H
    · apply le_add_of_nonneg_right
      apply List.sum_nonneg
      intro i hi
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
      exact form_nonneg (hh _ hx) _
    exact (ih hh H).trans (le_add_of_nonneg_left (form_nonneg he _))

def stashRate (A B : Form M) (j : ℕ) :=
    (side M*exp (F B)) * (side M*exp (F A))^(clones j)

lemma multiply_stash (m : Memory M) (A B : Form M) (p : Node) (x : Grid M)
    (w : Clutch j M) :
    prefixE m.profile p x * fresh A B j x w =
      stashRate A B j * prefixE (m.stash A B w).profile p x := by
  have hi (A : Form M) (v) :
      channel A x v = (side M*exp (F A)) * exp (-form A (v-x)) := by
    rw [ch_K,K_eq,sub_eq_add_neg,exp_add,mul_assoc]
  have H (v : Fin (clones j) → Grid M) :
      ∏ i, channel A x (v i) = (side M*exp (F A))^(clones j) *
        exp (-(∑ i, form A (v i-x))) := by
    simp_rw [hi,Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_neg_distrib]
    simp [mul_pow,exp_nat_mul]
  unfold prefixE
  split_ifs with hh
  · obtain ⟨v,c⟩ := w
    rw [fresh,tensorP_apply,pack_apply,H,hi,stashRate]
    simp_rw [tune,sumE_stash,loadE,neg_add,Real.exp_add]
    ring
  · ring

lemma rate_positive (j : ℕ) (A B : Form M) : 0 ≤ stashRate A B j := by
  unfold stashRate; have := side_pos M; positivity

lemma batch_expected (A B : Form M) (x : Grid M) (j : ℕ) :
    (fresh A B j x).Ex (fun w => loadE A B w x) =
      (label B).Ex (form B) + clones j * (label A).Ex (form A) := by
  simp_rw [fresh,Ex_tensorP,loadE,Ex_add,Ex_const,Ex_finset_sum,
    Ex_pack_proj (fun _ => channel A x) _ (fun z => form A (z-x))]
  rw [ch_noise B (form B)]
  simp_rw [ch_noise A (form A)]
  simp

lemma batch_scale :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ, ∀ x : Grid M,
      ∀ u : Update j M s.here, s.Safe j J f → (s.win u).Safe j J f →
        let A := s.fund.mood
        let B := u.next A
        (fresh A B j x).prob (fun w => temp j < loadE A B w x) ≤ 1/4 := by
  filter_upwards [h_large (100000*capA^2),hpoly (100000*capA^2) 230] with j h1 h2 M J s f x u ha hb A B
  let T := fresh A B j x
  have hA : 0 ≤ A := ha.capital.effects.nonneg
  have hB : 0 ≤ B := hb.capital.effects.nonneg
  have hT (w : Clutch j M) : 0 ≤ loadE A B w x := add_nonneg (form_nonneg hB _)
      (Finset.sum_nonneg fun i _ => form_nonneg hA _)
  let p (w : Clutch j M) : Prop := temp j < loadE A B w x
  have he := upperTail T p (fun w => loadE A B w x) hT (temp j) fun _ hx => hx.le
  let h := H j
  have hh : 1 ≤ h := H_ge j
  have hc := cap_ok; have hp : 0 < h := H_pos j
  let d := height j; have hd : 0 < d := d_pos j
  have ht : 0 < temp j := by
    have he : 0 < capA := by linarith
    change 0 < d/h^100/(capA*h)
    positivity
  let L := 2*plateErr j +100
  have hL : 0 ≤ L := by
    change 0 ≤ 2*(d/h^400)+100; positivity
  have Hx (s : Scene M) (hS : s.Safe j J f) :
      (label s.fund.mood).Ex (form s.fund.mood) ≤ capA*h*L :=
    hS.capital.effects.energy.trans (mul_le_mul_of_nonneg_right hS.capital.under hL)
  have hw :
      temp j * T.prob p ≤ capA*h*L+h^120*(capA*h*L) := by
    apply he.trans
    unfold T; rw [batch_expected,clones_eq]
    exact add_le_add (Hx (s.win u) hb) (mul_le_mul_of_nonneg_left (Hx s ha) (by positivity))
  change _ ≤ (1/4:ℝ)
  refine le_of_mul_le_mul_left (hw.trans ?_) ht
  have hP : 1 ≤ h^120 := one_le_pow₀ hh
  have HC : 0 < capA := by linarith
  change capA*h*L+h^120*(capA*h*L) ≤ d/h^100/(capA*h)*(1/4)
  have h3 : 8*capA^2*h^222*L ≤ d := by
    unfold L
    change 8*capA^2*h^222*(2*(d/h^400)+100) ≤ d
    have Hz : 100000*capA^2 ≤ h^178 := by
      change 100000*capA^2 ≤ h at h1
      exact h1.trans (by simpa using pow_le_pow_right₀ hh (by omega : 1 ≤ 178))
    have Hi : 8*capA^2*h^222 * (2*(d/h^400)) ≤ d/2 := by
      rw [show h^400=h^222*h^178 by ring]
      field_simp
      nlinarith
    rw [mul_add]
    change 100000*capA^2*h^230 ≤ d at h2
    have Hx := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hh (show 222 ≤ 230 by omega))
      (show 0 ≤ 100000*capA^2 by positivity)
    nlinarith
  calc
    _ ≤ 2*(h^120*(capA*h*L)) := by
      have h1 : 0 ≤ capA*h*L := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hP h1]
    _ ≤ _ := by field_simp; nlinarith

end Memory
end FourierLLogL.Dyadic.Procedure

end OAI
