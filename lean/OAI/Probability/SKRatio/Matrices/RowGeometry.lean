import Mathlib
import OAI.Probability.SKRatio.Matrices.PlantedSquares

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open Set Real
namespace SKRatio.Planted
open MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def otherEnd (i : Fin n) (e : Edge n) : Fin n :=
  if e.1.1=i then e.1.2 else e.1.1

lemma mem_incident (i : Fin n) (e : Edge n) :
    e∈incidentEdges i ↔ e.1.1=i ∨ e.1.2=i := by simp [incidentEdges]

lemma otherEnd_ne {i : Fin n} {e : Edge n} (he : e∈incidentEdges i) :
    otherEnd i e ≠ i := by
  have h := (mem_incident i e).mp he
  unfold otherEnd
  split_ifs with h₁
  · have hlt := e.2
    rw [h₁] at hlt
    exact ne_of_gt hlt
  · exact h₁

lemma coupling_otherEnd {i : Fin n} {e : Edge n} (g : Disorder n)
    (he : e∈incidentEdges i) : coupling g i (otherEnd i e)=g e := by
  have h := (mem_incident i e).mp he
  rcases h with h | h
  · simp only [otherEnd,ite_eq_left h]
    subst i
    simp [coupling,e.2]
  · have h₁ : e.1.1 ≠ i := by rw [←h]; exact ne_of_lt e.2
    simp only [otherEnd,ite_eq_right h₁]
    subst i
    simp [coupling,not_lt_of_gt e.2,e.2]

lemma sum_coupling_weighted_row (g : Disorder n) (i : Fin n) (f : Fin n → ℝ) :
    ∑ j, coupling g i j*f j = ∑ e∈incidentEdges i, g e*f (otherEnd i e) := by
  have he := coupling_bilinear (fun j => if j=i then 1 else 0) f g
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
  rw [he,incidentEdges,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hne : e.1.1≠e.1.2 := ne_of_lt e.2
  by_cases h₁ : e.1.1=i <;> by_cases h₂ : e.1.2=i <;>
    simp_all [otherEnd,mul_comm]

def diagonalField (ζ : Fin n → ℝ) (g : Disorder n) (j : Fin n) : ℝ :=
  ζ j+∑ k, coupling g j k

def eraseRow (i : Fin n) (g : Disorder n) : Disorder n :=
  fun e => if e∈incidentEdges i then 0 else g e

lemma coupling_eraseRow (i : Fin n) (g : Disorder n) (j k : Fin n) :
    coupling (eraseRow i g) j k = if j=i ∨ k=i then 0 else coupling g j k := by
  unfold coupling eraseRow
  split_ifs <;> simp_all [mem_incident]

lemma diagonalField_eraseRow (ζ : Fin n → ℝ) (g : Disorder n) (i j : Fin n)
    (hji : j≠i) :
    diagonalField ζ g j-diagonalField ζ (eraseRow i g) j = coupling g i j := by
  have h (k : Fin n) : coupling g j k - coupling (eraseRow i g) j k =
      if k=i then coupling g j i else 0 := by
    rw [coupling_eraseRow]
    by_cases hk : k=i <;> simp [hji,hk]
  simp only [diagonalField,add_sub_add_left_eq_sub,←Finset.sum_sub_distrib,h,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,coupling_symm g j i]

def outsideDisorder (β : ℝ) (i : Fin n)
    (y : {e // e∉incidentEdges i} → ℝ) : Disorder n :=
  fun e => if he : e∈incidentEdges i then 0 else β/sqrt n*y ⟨e,he⟩+β^2/(n:ℝ)

lemma outsideDisorder_eq (β : ℝ) (i : Fin n) (z : Disorder n) :
    outsideDisorder β i (fun e => z e) = eraseRow i (affineDisorder β z) := by
  funext e
  simp only [outsideDisorder,eraseRow,affineDisorder]
  split_ifs <;> rfl

lemma outside_field_error (β : ℝ) (i : Fin n) (ζ : Fin n → ℝ) (z : Disorder n)
    (e : incidentEdges i) :
    diagonalField ζ (affineDisorder β z) (otherEnd i e) -
      diagonalField ζ (outsideDisorder β i (fun j => z j)) (otherEnd i e) =
        affineDisorder β z e := by
  rw [outsideDisorder_eq,diagonalField_eraseRow ζ _ i _ (otherEnd_ne e.2),coupling_otherEnd _ e.2]

lemma continuous_diagonalField (j : Fin n) :
    Continuous (fun p : (Fin n → ℝ) × Disorder n => diagonalField p.1 p.2 j) := by
  apply ((continuous_apply j).comp continuous_fst).add
  exact continuous_finsetSum _ (fun k _ => (continuous_coupling j k).comp continuous_snd)

lemma continuous_outsideDisorder (β : ℝ) (i : Fin n) :
    Continuous (outsideDisorder β i) := by
  apply continuous_pi
  intro e
  unfold outsideDisorder
  split_ifs <;> fun_prop

lemma continuous_outside_field (β : ℝ) (i j : Fin n) :
    Continuous (fun p : (Fin n → ℝ) × ({e // e∉incidentEdges i} → ℝ) =>
      diagonalField p.1 (outsideDisorder β i p.2) j) :=
  (continuous_diagonalField j).comp (continuous_fst.prodMk ((continuous_outsideDisorder β i).comp continuous_snd))

end SKRatio.Planted

end
end

end OAI
