import OAI.Analysis.AncientFlat.Kernel.SymbolCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V]
lemma decay_le_one (x : V) (n : ℕ) : (1+‖x‖)^(-(4:ℝ)-n)≤1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · linarith [norm_nonneg x]
  · have := Nat.cast_nonneg (α := ℝ) n
    linarith
lemma norm_mul_decay_le_one (x : V) : ‖x‖*(1+‖x‖)^(-(4:ℝ)-1)≤1 := by
  have hp : 0<1+‖x‖ := by positivity
  calc
    ‖x‖*(1+‖x‖)^(-(4:ℝ)-1)≤(1+‖x‖)*(1+‖x‖)^(-(4:ℝ)-1) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hp.le _)
    _=(1+‖x‖)^(-(4:ℝ)-(0:ℕ)) := by
      calc
        _=(1+‖x‖)^(1:ℝ)*(1+‖x‖)^(-(4:ℝ)-1) := by rw [Real.rpow_one]
        _=(1+‖x‖)^((1:ℝ)+(-4-1)) := (Real.rpow_add hp _ _).symm
        _=_ := by norm_num
    _≤1 := decay_le_one x 0
variable [InnerProductSpace ℝ V]
lemma SymbolBounds.deviation_jets {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ (∀ x, ‖iteratedFDeriv ℝ n (fun y => Af y-c^2) x‖≤C) ∧
      (∀ x, ‖iteratedFDeriv ℝ n Bf x‖≤C) := by
  obtain ⟨C,hC,hb⟩ := h.2.2.2.2 n
  refine ⟨C,hC,fun x => ?_,fun x => ?_⟩
  · calc
      _≤C*(1+‖x‖)^(-(4:ℝ)-n) := (le_add_of_nonneg_right (norm_nonneg _)).trans (hb x)
      _≤C := mul_le_of_le_one_right hC (decay_le_one x n)
  · calc
      _≤C*(1+‖x‖)^(-(4:ℝ)-n) := (le_add_of_nonneg_left (norm_nonneg _)).trans (hb x)
      _≤C := mul_le_of_le_one_right hC (decay_le_one x n)
lemma SymbolBounds.absolute_bound {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) :
    ∃ M : ℝ, 0≤M ∧ (∀ x, ‖Af x‖≤M) ∧ (∀ x, ‖Bf x‖≤M) := by
  obtain ⟨C,hC,hA,hB⟩ := h.deviation_jets 0
  simp only [norm_iteratedFDeriv_zero] at hA hB
  refine ⟨C+c^2,by positivity,fun x => ?_,fun x => (hB x).trans (by nlinarith [sq_nonneg c])⟩
  calc
    ‖Af x‖=‖(Af x-c^2)+c^2‖ := by congr 1; ring
    _≤‖Af x-c^2‖+‖c^2‖ := norm_add_le _ _
    _≤C+c^2 := by rw [Real.norm_of_nonneg (sq_nonneg c)]; exact add_le_add (hA x) le_rfl
lemma SymbolBounds.first_bounds {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) :
    ∃ C : ℝ, 0≤C ∧ ∀ x,
      ‖fderiv ℝ Af x‖≤C ∧ ‖fderiv ℝ Bf x‖≤C ∧
      ‖x‖*‖fderiv ℝ Af x‖≤C ∧ ‖x‖*‖fderiv ℝ Bf x‖≤C := by
  obtain ⟨C,hC,hb⟩ := h.2.2.2.2 1
  have hAA (x : V) : fderiv ℝ (fun y => Af y-c^2) x=fderiv ℝ Af x := fderiv_sub_const _
  simp only [norm_iteratedFDeriv_one,hAA,Nat.cast_one] at hb
  have hA (x : V) : ‖fderiv ℝ Af x‖≤C*(1+‖x‖)^(-(4:ℝ)-1) :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hb x)
  have hB (x : V) : ‖fderiv ℝ Bf x‖≤C*(1+‖x‖)^(-(4:ℝ)-1) :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hb x)
  refine ⟨C,hC,fun x => ⟨?_,?_,?_,?_⟩⟩
  · exact (hA x).trans (mul_le_of_le_one_right hC (by simpa using decay_le_one x 1))
  · exact (hB x).trans (mul_le_of_le_one_right hC (by simpa using decay_le_one x 1))
  · calc
      _≤‖x‖*(C*(1+‖x‖)^(-(4:ℝ)-1)) := mul_le_mul_of_nonneg_left (hA x) (norm_nonneg x)
      _=C*(‖x‖*(1+‖x‖)^(-(4:ℝ)-1)) := by ring
      _≤C := mul_le_of_le_one_right hC (norm_mul_decay_le_one x)
  · calc
      _≤‖x‖*(C*(1+‖x‖)^(-(4:ℝ)-1)) := mul_le_mul_of_nonneg_left (hB x) (norm_nonneg x)
      _=C*(‖x‖*(1+‖x‖)^(-(4:ℝ)-1)) := by ring
      _≤C := mul_le_of_le_one_right hC (norm_mul_decay_le_one x)
end FlatSimilarity

end

end OAI
