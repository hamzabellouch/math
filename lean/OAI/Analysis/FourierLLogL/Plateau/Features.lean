import OAI.Analysis.FourierLLogL.Plateau.Output
import OAI.Analysis.FourierLLogL.Finite.Tail

/-! # Finite joint observation moments -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread
variable {M J j : ℕ} {s q : Scene M} {α β : Type} [Fintype α] [Fintype β]
open scoped Classical

def share (s : Scene M) := s.mass/s.norm
def ante (s : Scene M) (x : Grid M) := wt s.here s.wage s.norm x

lemma ante_nonneg (s : Scene M) (hs : 0 ≤ s.wage) (hp : 0 ≤ s.norm) (x : Grid M) : 0 ≤ ante s x :=
    wt_nonneg _ hs hp _
lemma ante_total (s : Scene M) (hp : s.here.ok M) : ∑ x, ante s x = share s := wt_total _ hp _ _

lemma ante_split (s : Scene M) (hp : s.here.valid) (hM : s.here.lev < M) (x : Grid M) :
    ante (s.smaller false) x + ante (s.smaller true) x=2*ante s x := by
  unfold ante
  simp only [smaller, wt_half hp hM]
  by_cases hh : x∈s.here.block M
  · have h₁ := Set.disjoint_left.mp (s.here.block_separate M)
    rw [block_union] at hh
    rcases hh with hh|hh
    · simp [child,hh,h₁ hh]
    · have h2 : x∉s.here.L.block M := fun he => h₁ he hh
      simp [child,hh,h2]
  · have h (b : Bool) : ¬ x∈(s.here.child b).block M := fun h => hh
      (block_of_below (child_below _ _) _ h)
    simp_rw [ite_eq_right (h _),wt,dice_apply ⟨hp,hM.le⟩,ite_eq_right hh,zero_mul,zero_div]
    ring

lemma share_split (s : Scene M) :
    share (s.smaller false)+share (s.smaller true)=2*share s := by
  unfold share mass; rw [show s.here.avg s.wage = _ from s.here.avg_split_real s.wage]
  dsimp only [smaller,child]; ring

def Packet (M : ℕ) (α : Type) := Grid M → α → ℝ

def addMass (s : Scene M) (k : Grid M → Law α) (x : Grid M) (i : α) :=
    ante s x*k x i

def rung (s : Scene M) (k : Grid M → Law α) (f : Grid M → α → ℝ) :=
    ∑ x, ∑ i, addMass s k x i * f x i

def rungC (s : Scene M) (k : Grid M → Law α) (f : Grid M → α → ℂ) :=
    ∑ x, ∑ i, (addMass s k x i:ℂ) * f x i

lemma nonnegative_hist (s : Scene M) (hs : 0 ≤ s.wage) (hp : 0 ≤ s.norm) (k : Grid M → Law α)
    (z : α) : 0 ≤ hist s k z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ante_nonneg s hs hp _) ((k i).nonneg _)

lemma total_hist (s : Scene M) (hp : s.here.ok M) (k : Grid M → Law α) :
    ∑ z, hist s k z=share s := by
  unfold hist
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, Law.total,mul_one]
  exact ante_total s hp

lemma rung_mono (s : Scene M) (hs : 0 ≤ s.wage) (hp : 0 ≤ s.norm) (k : Grid M → Law α)
    (f g : Grid M → α → ℝ) (h : ∀ i j, f i j ≤ g i j) :
    rung s k f ≤ rung s k g :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (h _ _)
    (mul_nonneg (ante_nonneg _ hs hp _) ((k _).nonneg _))

lemma rung_const (s : Scene M) (hp : s.here.ok M) (k : Grid M → Law α) (c : ℝ) :
    rung s k (fun _ _ => c) = share s*c := by
  unfold rung; rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [← total_hist s hp k]
  rfl

lemma rung_add (s : Scene M) (k : Grid M → Law α) (f g : Grid M → α → ℝ) :
    rung s k (fun i j => f i j + g i j)=rung s k f+rung s k g := by
  unfold rung; simp_rw [mul_add,Finset.sum_add_distrib]

lemma rung_lmul (s : Scene M) (k : Grid M → Law α) (f : Grid M → α → ℝ) (c : ℝ) :
    rung s k (fun i j => c*f i j)=c*rung s k f := by
  unfold rung
  simp_rw [Finset.mul_sum,mul_left_comm c]

lemma rung_error (s : Scene M) (hs : 0 ≤ s.wage) (hp : 0 ≤ s.norm) (hv : s.here.ok M)
    (k : Grid M → Law α) {f g : Grid M → α → ℝ} {r : ℝ}
    (hh : ∀ i j, |f i j-g i j| ≤ r) :
    |rung s k f-rung s k g| ≤ share s*r := by
  have he {f g : Grid M → α → ℝ} (h : ∀ i j, f i j ≤ r+g i j) :
      rung s k f ≤ share s*r+rung s k g := by
    apply le_trans (rung_mono s hs hp _ _ _ h)
    rw [rung_add (f:=fun _ _ => r),rung_const _ hv]
  have h1 := he (f:=f) (g:=g) fun i j => by linarith [(abs_le.mp (hh i j)).2]
  have h2 := he (f:=g) (g:=f) fun i j => by linarith [(abs_le.mp (hh i j)).1]
  rw [abs_le]; constructor <;> linarith

lemma rung_hist (s : Scene M) (k : Grid M → Law α) (f : α→ℝ) :
    ∑ i, hist s k i*f i = rung s k (fun _ i => f i) := by
  unfold rung; rw [Finset.sum_comm]; simp_rw [hist,Finset.sum_mul]
  rfl

lemma rung_split (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (k : Grid M → Law α) (f : Grid M → α → ℝ) :
    rung (s.smaller false) k f+rung (s.smaller true) k f= 2*rung s k f := by
  unfold rung
  rw [← Finset.sum_add_distrib]; simp_rw [← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_; refine Finset.sum_congr rfl fun j _ => ?_
  rw [addMass,addMass,← add_mul,← add_mul,ante_split s hp hh]
  unfold addMass; ring

lemma hist_split (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (k : Grid M → Law α) (z : α) :
    hist (s.smaller false) k z + hist (s.smaller true) k z = 2*hist s k z := by
  unfold hist; rw [← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have H := ante_split s hp hh i
  unfold ante at H
  rw [← add_mul,H,mul_assoc]

lemma hist_le {s q : Scene M} (h : Less s q) (hs : ReadyAt s) (hh : 0 ≤ s.norm)
    (k : Grid M → Law α) (z : α) :
    hist q k z ≤ hist s k z := by
  unfold hist wt; rw [h.here,h.flat]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ ((k _).nonneg _)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (h.antitone hs.2 i)
    ((s.here.dice M).nonneg i)) hh

lemma fisher_range (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (hs : 0 ≤ s.wage) (he : 0 ≤ s.norm) (k : Grid M → Law α) : 0 ≤ fisher s k ∧ fisher s k ≤ share s := by
  have hM := nonnegative_hist s hs he k
  constructor
  exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hM i)
  rw [← total_hist s ⟨hp,hh.le⟩ k]
  apply Finset.sum_le_sum; intro i _
  have h1 (b : Bool) := nonnegative_hist (s.smaller b) hs he k i
  have h2 := hist_split _ hp hh k i
  unfold diff
  rcases eq_or_lt_of_le (hM i) with hm|hm
  · rw [← hm,div_zero]
  apply (div_le_iff₀ hm).mpr
  nlinarith [h1 true,h1 false,mul_nonneg (h1 true) (h1 false)]

lemma fz_split (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (A : Form M) (i z : Grid M) :
    fz s.here.L s.wage s.norm A i z + fz s.here.R s.wage s.norm A i z =
      2*fz s.here s.wage s.norm A i z := by
  unfold fz omegaObs
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have H := ante_split s hp hh x
  simp_rw [ante,smaller,child] at H
  rw [← add_mul,← Complex.ofReal_add,← add_mul,H]
  push_cast; ring

end FourierLLogL.Dyadic.Procedure

end OAI
