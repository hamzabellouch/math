import Mathlib
import OAI.Combinatorics.HoneycombCorridor.SpatialDecay

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def eventVisitMass (D : Finset Vertex) (t : ℝ) (v : Vertex) : ℝ := by
  classical
  exact ∑ w ∈ sourceExits D bottomSource,
    if reachesDistance t w ∧ v ∈ traced bottomSource w then criticalActivity^w.length else 0

theorem sourceExit_visit_sum (D : Finset Vertex) (w : List Bool)
    (hw : w ∈ sourceExits D bottomSource) :
    (∑ v ∈ D, if v ∈ traced bottomSource w then criticalActivity^w.length else 0) =
      (w.length : ℝ)*criticalActivity^w.length := by
  classical
  have hs := stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp hw).1
  have hset : D.filter (fun v => v ∈ traced bottomSource w) = (traced bottomSource w).toFinset := by
    ext v
    simp only [Finset.mem_filter,List.mem_toFinset]
    exact ⟨And.right,fun hv => ⟨hs.2 v hv,hv⟩⟩
  rw [← Finset.sum_filter,hset]
  simp only [Finset.sum_const, nsmul_eq_mul, List.toFinset_card_of_nodup hs.1,traced_length]

theorem lateralLengthMass_fubini (D : Finset Vertex) (t : ℝ) :
    lateralLengthMass D t = ∑ v ∈ D, eventVisitMass D t v := by
  classical
  unfold eventVisitMass
  rw [Finset.sum_comm]
  unfold lateralLengthMass
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ht : reachesDistance t w
  · simp only [ht,true_and,ite_true]
    exact (sourceExit_visit_sum D w hw).symm
  · simp only [ht,false_and,ite_false,Finset.sum_const_zero]

theorem eventVisitMass_le_lateral (D : Finset Vertex) (t : ℝ) (v : Vertex) :
    eventVisitMass D t v ≤ lateralMass D (max t |(position v).1|) := by
  classical
  unfold eventVisitMass lateralMass
  apply Finset.sum_le_sum
  intro w hw
  by_cases he : reachesDistance t w ∧ v ∈ traced bottomSource w
  · have hm : reachesDistance (max t |(position v).1|) w := by
      rcases le_total t |(position v).1| with h | h
      · exact ⟨v,he.2,by rw [max_eq_right h]⟩
      · rw [max_eq_left h]
        exact he.1
    simp [he,hm]
  · simp only [he,ite_false]
    split_ifs <;> first | exact le_rfl | exact pow_nonneg criticalActivity_pos.le _

theorem eventVisitMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) (v : Vertex) :
    eventVisitMass D t v ≤ tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
      Real.exp (-tailRate*|(position v).1|/(2*(h+1))) := by
  have hm := lateralMass_exp h hh D hD hg hstrip (max t |(position v).1|)
    (ht.trans (le_max_left _ _))
  have he : Real.exp (-tailRate*max t |(position v).1|/(h+1)) ≤
      Real.exp (-tailRate*t/(2*(h+1))) *
      Real.exp (-tailRate*|(position v).1|/(2*(h+1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha := le_max_left t |(position v).1|
    have hb := le_max_right t |(position v).1|
    have hH : (0 : ℝ) < (h : ℝ)+1 := by positivity
    have hf : -tailRate*max t |(position v).1| ≤
        -tailRate*(t + |(position v).1|)/2 := by
      nlinarith [mul_nonneg tailRate_pos.le (show 0 ≤ 2*max t |(position v).1| - t - |(position v).1| by linarith)]
    have hd := div_le_div_of_nonneg_right hf hH.le
    have heq : -tailRate*t/(2*(h+1)) + -tailRate*|(position v).1|/(2*(h+1)) =
        (-tailRate*(t + |(position v).1|)/2)/(h+1) := by
      field_simp
      ring
    rw [heq]
    exact hd
  calc
    _ ≤ lateralMass D (max t |(position v).1|) := eventVisitMass_le_lateral D t v
    _ ≤ tailConstant * Real.exp (-tailRate*max t |(position v).1|/(h+1)) := hm
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he tailConstant_pos.le

theorem lateralLengthMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    lateralLengthMass D t ≤ tailConstant*spatialConstant*((h : ℝ)+1)^2 *
      Real.exp (-(tailRate/2)*t/(h+1)) := by
  rw [lateralLengthMass_fubini]
  calc
    _ ≤ ∑ v ∈ D, tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
        Real.exp (-tailRate*|(position v).1|/(2*(h+1))) :=
      Finset.sum_le_sum (fun v _ => eventVisitMass_exp h hh D hD hg hstrip t ht v)
    _ = tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
        ∑ v ∈ D, Real.exp (-tailRate*|(position v).1|/(2*(h+1))) := by rw [Finset.mul_sum]
    _ ≤ tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
        (spatialConstant*((h : ℝ)+1)^2) :=
      mul_le_mul_of_nonneg_left (spatial_sum_exp_bound h D hstrip)
        (mul_nonneg tailConstant_pos.le (Real.exp_pos _).le)
    _ = _ := by
      have he : -tailRate*t/(2*(h+1)) = -(tailRate/2)*t/(h+1) := by
        field_simp
      rw [he]
      ring



theorem finite_lateral_tail : FiniteLateralTail := by
  let C := tailConstant*(1+spatialConstant)
  have hCp : 0 < C := mul_pos tailConstant_pos (by linarith [spatialConstant_pos])
  have hC : tailConstant ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg tailConstant_pos.le spatialConstant_pos.le]
  have hC' : tailConstant*spatialConstant ≤ C := by
    dsimp [C]
    linarith [tailConstant_pos]
  refine ⟨C,tailRate/2,hCp,div_pos tailRate_pos (by norm_num),?_⟩
  intro h D hh hD hg hstrip t ht
  have hH : (0 : ℝ) < (h : ℝ)+1 := by positivity
  constructor
  · have he : Real.exp (-tailRate*t/(h+1)) ≤ Real.exp (-(tailRate/2)*t/(h+1)) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hH.le
      nlinarith [mul_nonneg tailRate_pos.le ht]
    exact (lateralMass_exp h hh D hD hg hstrip t ht).trans
      (mul_le_mul hC he (Real.exp_pos _).le hCp.le)
  · apply (lateralLengthMass_exp h hh D hD hg hstrip t ht).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hhh : ((h : ℝ)+1)^2 ≤ ((h : ℝ)+1)*(h+t+1) := by
      nlinarith [mul_nonneg hH.le ht]
    calc
      _ ≤ C*((h : ℝ)+1)^2 := mul_le_mul_of_nonneg_right hC' (sq_nonneg _)
      _ ≤ C*(((h : ℝ)+1)*(h+t+1)) := mul_le_mul_of_nonneg_left hhh hCp.le
      _ = _ := by ring

end PolynomialVacuumBridge.Corridor

end

end OAI
