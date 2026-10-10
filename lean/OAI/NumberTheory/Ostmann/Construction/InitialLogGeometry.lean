import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

structure InitialCoordinates (b s k : ℕ) where
  giant : Bool → ℝ
  bulk : Bool → Fin b → ℝ
  spectator : Bool → Fin s → ℝ
  top : Bool → Fin 3 → ℝ
  compensation : Bool → Fin k → Fin 2 → ℝ

namespace InitialCoordinates
variable {b s k : ℕ}

def logTotal (x : InitialCoordinates b s k) : ℝ :=
  (∑ h, Real.log (x.giant h)) + (∑ h, ∑ i, Real.log (x.bulk h i)) +
  (∑ h, ∑ i, Real.log (x.spectator h i)) + (∑ h, ∑ i, Real.log (x.top h i)) +
  (∑ h, ∑ j, ∑ i, Real.log (x.compensation h j i))

def product (x : InitialCoordinates b s k) : ℝ :=
  (∏ h, x.giant h) * (∏ h, ∏ i, x.bulk h i) *
  (∏ h, ∏ i, x.spectator h i) * (∏ h, ∏ i, x.top h i) *
  (∏ h, ∏ j, ∏ i, x.compensation h j i)

def Positive (x : InitialCoordinates b s k) : Prop :=
  (∀h,0<x.giant h) ∧ (∀h i,0<x.bulk h i) ∧
  (∀h i,0<x.spectator h i) ∧ (∀h i,0<x.top h i) ∧
  (∀h j i,0<x.compensation h j i)

theorem log_product (x : InitialCoordinates b s k) (hx : x.Positive) :
    Real.log x.product=x.logTotal := by
  obtain ⟨hg,hb,hs,ht,hc⟩ := hx
  have hgp : 0<∏ h,x.giant h := Finset.prod_pos (fun h _ => hg h)
  have hbp : 0<∏ h,∏ i,x.bulk h i := Finset.prod_pos (fun h _ =>
    Finset.prod_pos (fun i _ => hb h i))
  have hsp : 0<∏ h,∏ i,x.spectator h i := Finset.prod_pos (fun h _ =>
    Finset.prod_pos (fun i _ => hs h i))
  have htp : 0<∏ h,∏ i,x.top h i := Finset.prod_pos (fun h _ =>
    Finset.prod_pos (fun i _ => ht h i))
  have hcp : 0<∏ h,∏ j,∏ i,x.compensation h j i := Finset.prod_pos (fun h _ =>
    Finset.prod_pos (fun j _ => Finset.prod_pos (fun i _ => hc h j i)))
  unfold product logTotal
  rw [Real.log_mul (mul_pos (mul_pos (mul_pos hgp hbp) hsp) htp).ne' hcp.ne',
    Real.log_mul (mul_pos (mul_pos hgp hbp) hsp).ne' htp.ne',
    Real.log_mul (mul_pos hgp hbp).ne' hsp.ne', Real.log_mul hgp.ne' hbp.ne']
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · exact Real.log_prod (fun h _ => (hg h).ne')
        · rw [Real.log_prod (fun h _ => (Finset.prod_pos (fun i _ => hb h i)).ne')]
          exact Finset.sum_congr rfl (fun h _ => Real.log_prod (fun i _ => (hb h i).ne'))
      · rw [Real.log_prod (fun h _ => (Finset.prod_pos (fun i _ => hs h i)).ne')]
        exact Finset.sum_congr rfl (fun h _ => Real.log_prod (fun i _ => (hs h i).ne'))
    · rw [Real.log_prod (fun h _ => (Finset.prod_pos (fun i _ => ht h i)).ne')]
      exact Finset.sum_congr rfl (fun h _ => Real.log_prod (fun i _ => (ht h i).ne'))
  · rw [Real.log_prod (fun h _ => (Finset.prod_pos (fun j _ =>
      Finset.prod_pos (fun i _ => hc h j i))).ne')]
    apply Finset.sum_congr rfl
    intro h _
    rw [Real.log_prod (fun j _ => (Finset.prod_pos (fun i _ => hc h j i)).ne')]
    exact Finset.sum_congr rfl (fun j _ => Real.log_prod (fun i _ => (hc h j i).ne'))

end InitialCoordinates

lemma abs_fintype_sum_sub_le {ι : Type*} [Fintype ι] (f g e : ι → ℝ)
    (h : ∀i,|f i-g i|≤e i) : |(∑i,f i)-(∑i,g i)|≤∑i,e i := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => h i))

lemma abs_add_five_le (a b c d e : ℝ) :
    |a+b+c+d+e|≤|a|+|b|+|c|+|d|+|e| := by
  have h₁ := abs_add_le a b
  have h₂ := abs_add_le (a+b) c
  have h₃ := abs_add_le (a+b+c) d
  have h₄ := abs_add_le (a+b+c+d) e
  linarith

theorem initial_log_product_support {b s k : ℕ} (x : InitialCoordinates b s k)
    (hx : x.Positive) (G tb td : ℝ)
    (topCenter : Bool → Fin 3 → ℝ) (compCenter : Bool → Fin k → Fin 2 → ℝ)
    (hg : ∀h,|Real.log (x.giant h)-G|≤1)
    (hb : ∀h,|(∑i,Real.log (x.bulk h i))-tb|≤1)
    (hs : ∀h,|(∑i,Real.log (x.spectator h i))-td|≤1)
    (ht : ∀h i,|Real.log (x.top h i)-topCenter h i|≤1)
    (hc : ∀h j i,|Real.log (x.compensation h j i)-compCenter h j i|≤1) :
    |Real.log x.product-(2*G+2*tb+2*td+
      (∑h,∑i,topCenter h i)+(∑h,∑j,∑i,compCenter h j i))|≤12+4*(k:ℝ) := by
  have hgg := abs_fintype_sum_sub_le (fun h => Real.log (x.giant h)) (fun _ => G)
    (fun _ => 1) hg
  have hbb := abs_fintype_sum_sub_le (fun h => ∑i,Real.log (x.bulk h i)) (fun _ => tb)
    (fun _ => 1) hb
  have hss := abs_fintype_sum_sub_le (fun h => ∑i,Real.log (x.spectator h i)) (fun _ => td)
    (fun _ => 1) hs
  have htt := abs_fintype_sum_sub_le (fun h => ∑i,Real.log (x.top h i))
    (fun h => ∑i,topCenter h i) (fun _ => 3) (fun h => by
      simpa using abs_fintype_sum_sub_le (fun i => Real.log (x.top h i))
        (topCenter h) (fun _ => 1) (ht h))
  have hcc := abs_fintype_sum_sub_le (fun h => ∑j,∑i,Real.log (x.compensation h j i))
    (fun h => ∑j,∑i,compCenter h j i) (fun _ => 2*(k:ℝ)) (fun h => by
      have hj := abs_fintype_sum_sub_le (fun j => ∑i,Real.log (x.compensation h j i))
        (fun j => ∑i,compCenter h j i) (fun _ => 2) (fun j => by
          simpa using abs_fintype_sum_sub_le (fun i => Real.log (x.compensation h j i))
            (compCenter h j) (fun _ => 1) (hc h j))
      simpa [mul_comm] using hj)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul] at hgg hbb hss htt hcc
  rw [x.log_product hx]
  unfold InitialCoordinates.logTotal
  calc
    _ = |((∑h,Real.log (x.giant h))-2*G)+
      ((∑h,∑i,Real.log (x.bulk h i))-2*tb)+
      ((∑h,∑i,Real.log (x.spectator h i))-2*td)+
      ((∑h,∑i,Real.log (x.top h i))-(∑h,∑i,topCenter h i))+
      ((∑h,∑j,∑i,Real.log (x.compensation h j i))-(∑h,∑j,∑i,compCenter h j i))| := by
        congr 1; ring
    _ ≤ |(∑h,Real.log (x.giant h))-2*G|+
      |(∑h,∑i,Real.log (x.bulk h i))-2*tb|+
      |(∑h,∑i,Real.log (x.spectator h i))-2*td|+
      |(∑h,∑i,Real.log (x.top h i))-(∑h,∑i,topCenter h i)|+
      |(∑h,∑j,∑i,Real.log (x.compensation h j i))-(∑h,∑j,∑i,compCenter h j i)| := by
        exact abs_add_five_le _ _ _ _ _
    _ ≤ _ := by norm_num at hgg hbb hss htt hcc ⊢; linarith

end Ostmann.Construction

end

end OAI
