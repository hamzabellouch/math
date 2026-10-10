import OAI.MathematicalPhysics.Heisenberg.SpinMatrixConservation

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Selection
variable {I : Type*} [Fintype I]

def weightedTail (w : I → ℝ) (m : I → ℝ) (a : ℝ) : ℝ :=
  ∑ i,if a≤ m i then w i else 0

def tiltPartition (w m : I → ℝ) (b : ℝ) : ℝ := ∑ i,w i*Real.exp (b*m i)

def tiltLowerMass (w m : I → ℝ) (b a : ℝ) : ℝ :=
  (∑ i,if m i<a then w i*Real.exp (b*m i) else 0)/tiltPartition w m b

lemma tail_le_partition (w m : I → ℝ) (hw : ∀ i,0≤w i) (a : ℝ) :
    weightedTail w m a≤∑ i,w i := by
  unfold weightedTail
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp_all

lemma tiltPartition_pos (w m : I → ℝ) (hw : ∀ i,0≤w i) (hpos : 0<∑ i,w i) (b : ℝ) :
    0<tiltPartition w m b := by
  obtain ⟨i,_,hi⟩:=Finset.sum_pos_iff_of_nonneg (fun i _=>hw i) |>.mp hpos
  apply Finset.sum_pos'
  · intro j _; exact mul_nonneg (hw j) (Real.exp_pos _).le
  · exact ⟨i,Finset.mem_univ _,mul_pos hi (Real.exp_pos _)⟩

lemma tilt_tail_denominator (w m : I → ℝ) (hw : ∀ i,0≤w i) {b : ℝ} (hb : 0≤b) (a : ℝ) :
    Real.exp (b*a)*weightedTail w m a≤tiltPartition w m b := by
  rw [weightedTail,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : a≤ m i
  · rw [ite_eq_left hi]
    exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi hb)) (hw i))
  · rw [ite_eq_right hi,mul_zero]
    exact mul_nonneg (hw i) (Real.exp_pos _).le

lemma tilt_lower_numerator (w m : I → ℝ) (hw : ∀ i,0≤w i) {b : ℝ} (hb : 0≤b) (a : ℝ) :
    (∑ i,if m i<a then w i*Real.exp (b*m i) else 0)≤Real.exp (b*a)*∑ i,w i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : m i<a
  · rw [ite_eq_left hi]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi.le hb)) (hw i)).trans_eq (mul_comm _ _)
  · rw [ite_eq_right hi]
    exact mul_nonneg (Real.exp_pos _).le (hw i)

theorem tilt_tail_bound (w m : I → ℝ) (hw : ∀ i,0≤w i) (hpos : 0<∑ i,w i)
    {b L a c : ℝ} (hb : 0≤b) (hL : 0<L)
    (htail : L*(∑ i,w i)≤weightedTail w m c) :
    tiltLowerMass w m b a≤L⁻¹*Real.exp (b*(a-c)) := by
  have hD : Real.exp (b*c)*L*(∑ i,w i)≤tiltPartition w m b := by
    calc _ = Real.exp (b*c)*(L*(∑ i,w i)) := mul_assoc _ _ _
         _ ≤ Real.exp (b*c)*weightedTail w m c := mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
         _ ≤ _ := tilt_tail_denominator w m hw hb c
  have hDpos : 0<Real.exp (b*c)*L*(∑ i,w i) := mul_pos (mul_pos (Real.exp_pos _) hL) hpos
  unfold tiltLowerMass
  calc _ ≤ (Real.exp (b*a)*∑ i,w i)/(Real.exp (b*c)*L*∑ i,w i) :=
          div_le_div₀ (mul_nonneg (Real.exp_pos _).le hpos.le) (tilt_lower_numerator w m hw hb a) hDpos hD
       _ = L⁻¹*Real.exp (b*(a-c)) := by
         rw [mul_sub,Real.exp_sub]
         field_simp

lemma tilt_mean_lower (w m : I → ℝ) (hw : ∀ i,0≤w i) (hpos : 0<∑ i,w i)
    (b a S : ℝ) (hS : ∀ i,-S≤ m i) :
    a-(a+S)*tiltLowerMass w m b a≤
      (∑ i,w i*Real.exp (b*m i)*m i)/tiltPartition w m b := by
  have hZ:=tiltPartition_pos w m hw hpos b
  have hh : a*tiltPartition w m b-(a+S)*(∑ i,if m i<a then w i*Real.exp (b*m i) else 0)≤
      ∑ i,w i*Real.exp (b*m i)*m i := by
    rw [tiltPartition,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hp : 0≤w i*Real.exp (b*m i):=mul_nonneg (hw i) (Real.exp_pos _).le
    by_cases hi : m i<a
    · rw [ite_eq_left hi]
      nlinarith [mul_le_mul_of_nonneg_left (hS i) hp]
    · rw [ite_eq_right hi,mul_zero,sub_zero]
      exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hi) hp)
  unfold tiltLowerMass
  apply (le_div_iff₀ hZ).mpr
  calc _ = a*tiltPartition w m b-(a+S)*(∑ i,if m i<a then w i*Real.exp (b*m i) else 0) := by rw [sub_mul,mul_assoc,div_mul_cancel₀ _ hZ.ne']
       _ ≤ _ := hh

end Heisenberg.Selection
end
end

end OAI
