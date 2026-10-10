import OAI.Analysis.FourierLLogL.Compress.Search
import OAI.Analysis.FourierLLogL.Compress.Fraction
/-! # Using the refinement search -/

open Function Filter Set
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real

private lemma any_above {f : ℕ → ℝ} {k : ℕ} (a : ℝ)
    (h : k*a < ∑ i ∈ Finset.range k, f i) :
    ∃ i < k, a < f i := by
  by_contra! hh
  have he : ∑ i ∈ Finset.range k, f i ≤ ∑ i ∈ Finset.range k, a :=
    Finset.sum_le_sum fun i hi => hh i (Finset.mem_range.mp hi)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at he
  linarith

private lemma exists_offer (k m : ℕ) (hkm : k ≤ m) (hmp : 0 < m)
    (d c : ℕ → ℝ) (τ p : ℝ) (hT : 0 < τ) (hp : 0 ≤ p)
    (h : τ < ∑ i ∈ Finset.range k, d i) (h1 : ∑ i ∈ Finset.range k, c i = τ*p)
    (hg : ∀ i, 0 ≤ c i) :
    ∃ i < k, τ/(2*m) ≤ d i ∧ c i ≤ 2*p*d i := by
  have hpos : (0:ℝ) < m := by exact_mod_cast hmp
  let v := τ/(2*m)
  have hv : 0 ≤ v := by unfold v; positivity
  have HH : k*v ≤ τ/2 := calc
    _ ≤ (m:ℝ)*v := by gcongr
    _ = τ/2 := by unfold v; field_simp
  obtain hs|hs := eq_or_lt_of_le hp
  · obtain ⟨i,hi,hb⟩ := any_above v (f:=d) (k:=k) (by linarith)
    refine ⟨i,hi,hb.le,?_⟩
    have he := Finset.single_le_sum (fun i (_ : i ∈ Finset.range k) => hg i)
      (Finset.mem_range.mpr hi)
    rw [← hs] at h1 ⊢
    linarith
  obtain ⟨i,hi,hb⟩ := any_above v (f:=fun i => d i - c i/(2*p)) (k:=k) (by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div,h1]
    rw [show τ*p/(2*p)=τ/2 by field_simp]
    linarith)
  have hn : 0 ≤ c i/(2*p) := by have := hg i; positivity
  refine ⟨i,hi,le_of_lt (by linarith),?_⟩
  have hI : c i/(2*p) ≤ d i := by linarith
  have he := (div_le_iff₀ (show 0 < 2*p by positivity)).mp hI
  linarith

/-- Parameters of the two-order search. -/
structure Schedule where
  N : ℕ
  q : ℕ
  n : ℕ
  N0 : 0 < N
  q0 : 0 < q
  n0 : 0 < n
  u : ℝ
  a : ℝ
  δ : ℝ
  η : ℝ
  α : ℝ
  ε : ℝ
  u0 : 0 < u
  a0 : 0 < a
  d0 : 0 < δ
  heta : δ*exp (2*u/a) ≤ η
  hn : 1 < (n:ℝ)*δ
  hα : 0 < α
  hε : 0 < ε
  hβ : 2*(a/α) ≤ 1
  hc : (ε+η)*exp (2*(a/α)*q) ≤ 1
  hq : 1 < (q:ℝ)*u
  ht : 1 < (N:ℝ)*ε

namespace Schedule
def size (w : Schedule) := w.N*(w.q*w.n)
def loss (w : Schedule) := 2*w.α+w.a*(1+w.η)
lemma loss_pos (w : Schedule) : 0 < w.loss := by
  have H := lt_of_lt_of_le (mul_pos w.d0 (exp_pos _)) w.heta
  unfold loss; nlinarith [w.hα,w.a0]
end Schedule

variable {A G : Type} [Fintype A] [Fintype G] [AddCommGroup G]

lemma offer_at (tag : A→G) (hi : Injective tag) (c : G→ℝ) (s : Labelled A)
    (D F : ℝ) (hd : 0 < D) (hf : 0 < F) (r l u M : ℕ) (hl : l ≤ u) (hu : u ≤ M)
    (hm : 0 < M) (hno : F+fundK tag c s l r < fundK tag c s u r)
    (x : ℝ) (hx : 0 < x) (hb : x ≤ F/D/(2*M)) :
    ∃ t, refines t s ∧
      x ≤ fundI tag s r / D - fundI tag t r / D ∧
      F/D * (fundG tag s 1 / D - fundG tag t 1 / D) ≤
        2*(fundG tag s u/D-fundG tag s l/D)*x := by
  let g n := fundG tag s n/D
  let a t := fundI tag t r/D
  let τ := F/D
  let T m := observe tag s (l+m)
  let k := u-l
  let f m := a s - a (T m)
  let b m := τ*(fundG tag s 1/D - fundG tag (T m) 1 / D)
  let K n := fundK tag c s n r
  have hg : Monotone g := fun i j hh => div_le_div_of_nonneg_right
    (fundG_mono tag s hh) hd.le
  have hτ : 0 < τ := div_pos hf hd
  have h1 : τ < ∑ i ∈ Finset.range k, f i := by
    have hc (i : ℕ) : K (l+(i+1))/D-K (l+i)/D ≤ f i := by
      have hh := observe_save tag c s (l+i) r
      unfold K f a T; rw [← sub_div, ← sub_div,← Nat.add_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hd.le
    refine lt_of_lt_of_le ?_ (Finset.sum_le_sum (fun i _ => hc i))
    rw [Finset.sum_range_sub (fun i => K (l+i)/D)]
    unfold k τ K
    rw [Nat.add_zero,Nat.add_sub_of_le hl, ← sub_div]
    gcongr; linarith
  have heq (i : ℕ) : b i = τ*(g (l+(i+1))-g (l+i)) := by
    unfold b g T
    rw [← sub_div,observe_cost tag hi s (l+i),← sub_div,Nat.add_assoc]
  have h2 : ∑ i ∈ Finset.range k, b i = τ*(g u-g l) := by
    simp_rw [heq,← Finset.mul_sum]
    rw [Finset.sum_range_sub (fun i => g (l+i))]
    simp only [k,Nat.add_sub_of_le hl,Nat.add_zero]
  obtain ⟨i,hh,hI,hJ⟩ := exists_offer k M (by omega) hm f b τ (g u-g l)
    hτ (sub_nonneg.mpr (hg hl)) h1 h2 (by
      intro i; rw [heq]; exact mul_nonneg hτ.le (sub_nonneg.mpr (hg (by omega))))
  have hX : x ≤ f i := le_trans hb hI
  have Hf : 0 < f i := lt_of_lt_of_le hx hX
  let y := x/f i
  have hy0 : 0 ≤ y := (div_pos hx Hf).le
  have hy1 : y ≤ 1 := (div_le_one Hf).mpr hX
  refine ⟨blend (T i) s y hy0 hy1,
    blend_refines _ _ _ (observe_refines _ _ _) (refines_refl s) _ _ _, ?_,?_⟩
  · have hh := blend_I tag (T i) s y hy0 hy1 r
    have hi := div_le_div_of_nonneg_right hh hd.le
    have He : y*f i=x := div_mul_cancel₀ _ Hf.ne'
    unfold f a at He; rw [add_div,mul_div_assoc,mul_div_assoc] at hi
    linarith
  · rw [blend_G1 tag hi _ _ _]
    change τ*_ ≤ 2*(g u-g l)*x
    calc
      _ = y*b i := by unfold b; ring
      _ ≤ y*(2*(g u-g l)*f i) := mul_le_mul_of_nonneg_left hJ hy0
      _ = _ := by rw [mul_left_comm,show y*f i=x from div_mul_cancel₀ _ Hf.ne']

/-- Reach a long, low-cost block length. -/
theorem reach (tag : A → G) (hi : Injective tag) (c : G → ℝ) (_hc0 : ∀ x, 0 ≤ c x)
    (S : Labelled A) (D F : ℝ) (hd : 0 < D) (hf : 0 < F) (B : Schedule)
    (m : ℕ) (l u r : ℕ → ℕ) (hm : 0 < m)
    (hl : ∀ i, i < B.size → l i ≤ u i ∧ u i ≤ m)
    (hp : ∀ i j, i < j → j < B.size → u j ≤ l i ∧ r i ≤ r j)
    (hG : ∀ i, i<B.size → fundG tag S (u i) ≤ D)
    (hI : ∀ i, i<B.size → fundI tag S (r i) ≤ D) :
    ∃ T, refines T S ∧ fundG tag S 1 - fundG tag T 1 ≤ B.loss*D*D/F ∧
      ∃ i, i < B.size ∧ fundK tag c T (u i) (r i) ≤ F+fundK tag c T (l i) (r i) := by
  let Ω := {p // refines p S}
  let τ := F/D
  have hτ : 0 < τ := div_pos hf hd
  let g (i : ℕ) (x : Ω) := fundG tag x.val i / D
  let a (i : ℕ) (x : Ω) := fundI tag x.val (r i) / D
  let v : Arena Ω :=
    { N := B.size
      mov := fun s t => refines t.val s.val
      refl := fun s => refines_refl _
      trans := fun h1 h2 => refines_trans h2 h1
      topc := fun x => τ*g 1 x
      pay := fun {x y} hh => mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (G_anti tag hh 1) hd.le) hτ.le
      A := a
      Alo := fun s i _ => div_nonneg (opt_nonneg _ s.val.law (tag ∘ Prod.fst) Prod.snd
        (fun _ : Unit => 0) (fun _ => 0) (fun _ => le_refl _)) hd.le
      Ahi := fun s i hi => (div_le_one hd).mpr ((I_anti tag s.property _).trans (hI i hi))
      Am := fun s {i j} hij hj => by
        obtain h|h := eq_or_lt_of_le hij
        · subst i; exact le_rfl
        · exact div_le_div_of_nonneg_right (fundI_mono tag _ (hp i j h hj).2) hd.le
      As := fun {x y} h _ _ => div_le_div_of_nonneg_right (I_anti _ h _) hd.le
      L := fun i => g (l i)
      H := fun i => g (u i)
      Llo := fun s i h => div_nonneg (show 0 ≤ fundG tag s.val (l i) from Hcond_nonneg _ _ _) hd.le
      Hhi := fun s i hi => (div_le_one hd).mpr ((G_anti tag s.property _).trans (hG i hi))
      LH := fun s i h => div_le_div_of_nonneg_right (fundG_mono _ _ (hl i h).1) hd.le
      BC := fun s {i j} h hb => div_le_div_of_nonneg_right (fundG_mono _ _ (hp i j h hb).1) hd.le
      Ls := fun {s t} h i _ => div_le_div_of_nonneg_right (G_anti _ h _) hd.le
      Hs := fun {s t} h i _ => div_le_div_of_nonneg_right (G_anti _ h _) hd.le
      found := fun s => ∃ i, i < B.size ∧ fundK tag c s.val (u i) (r i) ≤ F +
        fundK tag c s.val (l i) (r i)
      rate := τ/(2*m)
      r0 := by have : (0:ℝ) < m := by exact_mod_cast hm
               positivity
      offer := by
        intro s i hb h x hx hx'
        obtain ⟨Q,hQ,h1,h2⟩ := offer_at tag hi c s.val D F hd hf (r i) (l i) (u i)
          m (hl i hb).1 (hl i hb).2 hm (lt_of_not_ge (fun hh => h ⟨i,hb,hh⟩)) x hx hx'
        exact ⟨⟨Q,refines_trans hQ s.property⟩,hQ,h1,by rwa [← mul_sub]⟩ }
  obtain ⟨t,ht,hc,hP⟩ :=
    v.complete_search ⟨S,refines_refl S⟩ B.N B.q B.n B.n0 B.q0 B.N0 le_rfl
      B.u B.a B.δ B.η B.α B.ε B.u0 B.a0 B.d0 B.heta B.hn B.hα B.hε B.hβ B.hc B.hq B.ht
  refine ⟨t.val,t.property,?_,hc⟩
  change F/D * (fundG tag S 1 / D) - F/D*(fundG tag t.val 1 / D) ≤ B.loss at hP
  field_simp at *

  linarith

end FourierLLogL.Compress

end OAI
