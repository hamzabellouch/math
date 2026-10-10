import Mathlib
import OAI.Combinatorics.KMedian.Rounding.WeightedRounding

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

abbrev point (p : Vector ℚ n) (i : Fin n) : ℚ := p[i.val]
def realPoint (p : Vector ℚ n) (i : Fin n) : ℝ := (point p i:ℝ)
def fractional (p : Vector ℚ n) : Finset (Fin n) :=
  univ.filter (fun i => 0 < point p i ∧ point p i < 1)

def pair (p : Vector ℚ n) (h : 1 < (fractional p).card) :
    {a : Fin n × Fin n // a.1 ∈ fractional p ∧ a.2 ∈ fractional p ∧ a.1 ≠ a.2} :=
  let F := fractional p
  have hFc : 1 < F.card := h
  have hF : F.Nonempty := card_pos.mp (by omega)
  let i := F.min' hF
  have hi : i ∈ F := min'_mem _ _
  have hE : (F.erase i).Nonempty := by
    rw [← card_pos,card_erase_of_mem hi]
    omega
  let j := (F.erase i).min' hE
  have hj : j ∈ F.erase i := min'_mem _ _
  ⟨(i,j),hi,(mem_erase.mp hj).2,(mem_erase.mp hj).1.symm⟩

def move (p : Vector ℚ n) (i j : Fin n) (r t : ℚ) : Vector ℚ n :=
  Vector.ofFn (fun k => point p k+t*((if k=i then 1 else 0)-(if k=j then r else 0)))

def up (p : Vector ℚ n) (i j : Fin n) (r : ℚ) : ℚ := min (1-point p i) (point p j/r)
def down (p : Vector ℚ n) (i j : Fin n) (r : ℚ) : ℚ := min (point p i) ((1-point p j)/r)

@[simp] theorem real_move (p : Vector ℚ n) (i j : Fin n) (r t : ℚ) :
    realPoint (move p i j r t)=WeightedRounding.move (realPoint p) i j (r:ℝ) (t:ℝ) := by
  funext k
  simp only [realPoint,point,move,Vector.getElem_ofFn,Fin.eta,WeightedRounding.move,
    WeightedRounding.sign,Rat.cast_add,Rat.cast_mul,Rat.cast_sub]
  split_ifs <;> simp only [Rat.cast_one,Rat.cast_zero]

@[simp] theorem real_up (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    (up p i j r:ℝ)=WeightedRounding.up (realPoint p) i j (r:ℝ) := by
  simp only [up,WeightedRounding.up,realPoint,Rat.cast_min,Rat.cast_sub,Rat.cast_one,Rat.cast_div]

@[simp] theorem real_down (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    (down p i j r:ℝ)=WeightedRounding.down (realPoint p) i j (r:ℝ) := by
  simp only [down,WeightedRounding.down,realPoint,Rat.cast_min,Rat.cast_sub,Rat.cast_one,Rat.cast_div]

@[simp] theorem real_fractional (p : Vector ℚ n) :
    MarginalRounding.fractional (realPoint p)=fractional p := by
  ext i
  simp only [fractional,mem_filter,mem_univ,true_and,MarginalRounding.mem_fractional,
    realPoint]
  constructor <;> rintro ⟨h0,h1⟩ <;> exact ⟨by exact_mod_cast h0,by exact_mod_cast h1⟩

theorem up_pos (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < up p i j r := by
  exact lt_min (sub_pos.mpr (mem_filter.mp hi).2.2)
    (div_pos (mem_filter.mp hj).2.1 hr)

theorem down_pos (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < down p i j r := by
  exact lt_min (mem_filter.mp hi).2.1
    (div_pos (sub_pos.mpr (mem_filter.mp hj).2.2) hr)

def probability (β : Fin n → ℚ) (p : Vector ℚ n) : ℚ :=
  if h : 1 < (fractional p).card then
    let a := pair p h
    let r := β a.val.1/β a.val.2
    down p a.val.1 a.val.2 r/(up p a.val.1 a.val.2 r+down p a.val.1 a.val.2 r)
  else 0

def endpoint (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) : Vector ℚ n :=
  if h : 1 < (fractional p).card then
    let a := pair p h
    let r := β a.val.1/β a.val.2
    move p a.val.1 a.val.2 r (if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r)
  else p

theorem probability_unit (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) :
    0 ≤ probability β p ∧ probability β p ≤ 1 := by
  unfold probability
  split_ifs with h
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    exact ⟨(div_pos hd (add_pos hu hd)).le,(div_le_one (add_pos hu hd)).mpr (by linarith)⟩
  · exact ⟨le_rfl,by norm_num⟩

theorem endpoint_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) (k : Fin n) :
    probability β p*point (endpoint β p 0) k+
      (1-probability β p)*point (endpoint β p 1) k=point p k := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_mean (realPoint p) a.val.1 a.val.2 k (r:ℝ) hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add]

end MetricKMedian.RationalWeightedStep
end
end

end OAI
