import OAI.Analysis.FourierLLogL.Capture.Flex
import OAI.Analysis.FourierLLogL.Dyadic.Span

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Capture
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread

variable {M : ℕ}
open scoped Classical

def atReach (d : Finset (Grid M)) (r : ℝ) (x : Grid M) :=
    ∃ i, enclosed d 1 i ∧ rad (x-i) ≤ r

def tinted (d : Finset (Grid M)) (r : ℝ) (f : Grid M → ℝ) :=
    ∀ i, ¬ atReach d r i → fc (fun x => (↑(f x):ℂ)) i = 0

lemma atReach_neg {d : Finset (Grid M)} {r : ℝ} {x : Grid M} (h : atReach d r x) :
    atReach d r (-x) := by
  obtain ⟨i,h1,h2⟩ := h
  exact ⟨-i,enclosed_neg h1,by rw [show -x- -i= -(x-i) by ring,rad_even]; exact h2⟩

lemma tinted_mul {d : Finset (Grid M)} {r s : ℝ} {f g : Grid M → ℝ} (hf : tinted d r f)
    (hg : limitR g s) : tinted d (r+s) (fun i => f i*g i) := by
  intro i hi
  simp only [Complex.ofReal_mul]
  rw [fc_prod]
  apply Finset.sum_eq_zero; intro j _
  by_cases h : atReach d r j
  · obtain ⟨v,hv,H⟩ := h
    have hX : s < rad (i-j) := by
      by_contra! he; apply hi; refine ⟨v,hv,?_⟩
      have hZ := rad_add (i-j) (j-v); rw [sub_add_sub_cancel] at hZ; linarith
    rw [hg _ hX,mul_zero]
  rw [hf j h,zero_mul]

lemma tinted_cancel {d : Finset (Grid M)} {r : ℝ} {f : Grid M → ℝ} (hf : tinted d r f)
    {i : Grid M} (hh : ¬ atReach d r i) (c : ℂ) :
    expU (fun x => f x*(c*chi i x).re)=0 := by
  have H : c* fc (fun x => (↑(f x):ℂ)) (-i) = 0 := by
    rw [hf (-i) (fun h => hh (by simpa using atReach_neg h)),mul_zero]
  unfold fc at H
  rw [expU_cx,← Cx_lmul] at H
  have HE := congrArg Complex.re H
  simp_rw [re_Cx,neg_neg,mul_left_comm c, Complex.re_ofReal_mul,← expU_ex,
    Complex.zero_re] at HE
  exact HE

lemma tinted_one (d : Finset (Grid M)) {r : ℝ} (h : 0 ≤ r) : tinted d r (fun _ => 1) := by
  intro i hi
  have hn : ¬ enclosed d 1 i := by
    intro H; apply hi; exact ⟨i,H,by simp [rad,h]⟩
  simp only [Complex.ofReal_one]; exact spanned_one _ _ hn

lemma tinted_extend (f g : Grid M → ℝ) (d : Finset (Grid M)) (r s : ℝ) (hf : tinted d r f)
    (hg : limitR g s) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (i : Grid M) (hi : ¬ atReach d (r+s) i) (c : ℂ) :
    i∉d ∧ tinted (insert i d) (r+s)
      (fun x => f x*(1+g x*(c*chi i x).re)) := by
  have hx : i∉d := fun H => hi ⟨i,enclosed_mem _ H,by simp [rad]; linarith⟩
  let F : Grid M → ℂ := fun x => (f x * g x:ℝ)
  have Hf : ∀ x, ¬ atReach d (r+s) x → fc F x=0 := tinted_mul hf hg
  refine ⟨hx,?_⟩
  intro x hh
  have H (p : Grid M) (h : ¬ atReach (insert i d) (r+s) x)
      (j : ℤ) (hj : |j| ≤ 1) (heq : x=p+j•i) :
      ¬ atReach d (r+s) p := by
    intro hL
    obtain ⟨u,hu,hb⟩ := hL
    apply h
    refine ⟨u+j•i,enclosed_insert hx hu j (by simpa using hj),?_⟩
    rw [heq]; simpa only [add_sub_add_right_eq_sub] using hb
  have hX : ¬ atReach d (r+s) x := H x hh 0 (by norm_num) (by simp)
  have hA : ¬ atReach d r x := by
    rintro ⟨p,hp,hb⟩
    exact hX ⟨p,hp,by linarith⟩
  have hB : ¬ atReach d (r+s) (x-i) := H _ hh 1 (by norm_num) (by simp)
  have hC : ¬ atReach d (r+s) (x+i) := H _ hh (-1) (by norm_num) (by simp)
  have he (x) :
    (↑(f x * (1 + g x *(c*chi i x).re)):ℂ) = (↑(f x):ℂ)+F x*((c*chi i x).re) := by
    unfold F; push_cast; ring
  simp_rw [he,fc_add,hf x hA]
  have ht := expand_one_step F c i x
  rw [Hf x hX,Hf (x-i) hB,Hf (x+i) hC] at ht
  have h₁ (x) : F x*(1+(↑((c*chi i x).re):ℂ))=F x+F x*((c*chi i x).re) := by ring
  simp_rw [h₁,fc_add,Hf x hX] at ht
  exact ht.trans (by ring)

structure Chart (M : ℕ) where
  refs : ProductRef M
  items : Finset (Grid M)
  wide : ℝ

namespace Chart
def classic (M : ℕ) : Chart M := ⟨fun _ _ => 1,∅,0⟩
def size (c : Chart M) := c.items.card
structure Sound (c : Chart M) : Prop where
  bound : 0 ≤ c.wide
  total z y : side c.size ≤ c.refs z y ∧ c.refs z y ≤ 2^c.size
  radius z : tinted c.items c.wide (c.refs z)

lemma classic_sound (M : ℕ) : (classic M).Sound :=
    ⟨le_rfl, by simp [classic,size,side], fun z => tinted_one _ le_rfl⟩
lemma Sound.pos (c : Chart M) (h : c.Sound) (z y) : 0 < c.refs z y :=
  lt_of_lt_of_le (side_pos _) (h.total z y).1

end Chart

end FourierLLogL.Dyadic.Procedure.Capture

end OAI
