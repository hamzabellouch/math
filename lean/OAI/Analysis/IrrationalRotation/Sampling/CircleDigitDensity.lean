import OAI.Analysis.IrrationalRotation.Couplings.CircleDigitCoupling

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)

include hm ha ha' hb hb' in
lemma endpointLaw_eq_density (side : Bool) (l : Label) :
    endpointLaw side m a b l = baseLaw.withDensity
      (fun x => ENNReal.ofReal (endpointDensity side m a b l x)) := by
  have hm0 : 0 < m := by linarith
  cases l with
  | none => simp [endpointLaw, endpointDensity]
  | some i =>
    cases side
    · exact leftLaw_eq_withDensity (by linarith : 2 ≤ 2 * m)
        (width_pos hm0 ha) ha' (width_pos hm0 hb) hb' i
    · exact rightLaw_eq_withDensity (by linarith : 2 ≤ 2 * m)
        (width_pos hm0 ha) ha' (width_pos hm0 hb) hb' i

lemma endpointDensity_measurable (side : Bool) (m a b : ℝ) (l : Label) :
    Measurable (endpointDensity side m a b l) := by
  cases l with
  | none => exact measurable_const
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_measurable _ _

lemma endpointDensity_nonneg (side : Bool) (m a b : ℝ) (l : Label) (x : ℝ) :
    0 ≤ endpointDensity side m a b l x := by
  cases l with
  | none => norm_num [endpointDensity]
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_nonneg _ _ _

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma marginalDensity_bounds (side : Bool) (x : ℝ) :
    49 / 50 ≤ marginalDensity side κ m a b t x ∧
      marginalDensity side κ m a b t x ≤ 3 + 8 * κ ∧
      marginalDensity side κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hd (i : Fin 5) : 0 ≤ endpointDensity side m a b (some i) x ∧
      endpointDensity side m a b (some i) x ≤ componentVarianceBounds (2 * m) a b i := by
    cases side
    · exact leftDensity_bound (by linarith) ha0 ha' hb0 hb' i x
    · exact rightDensity_bound (by linarith) ha0 ha' hb0 hb' i x
  have hρa := rho_div_width_le hκ0 hm0 ha
  have hρb := rho_div_width_le hκ0 hm0 hb
  have hρa0 := rho_nonneg (m := m) (w := a) hκ0
  have hρb0 := rho_nonneg (m := m) (w := b) hκ0
  have hq := diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
  have htag0 : 0 ≤ t / m := div_nonneg ht0 hm0.le
  have htag : (t / m) * endpointDensity side m a b (some 4) x ≤ 2 := by
    calc
      _ ≤ (t / m) * (2 * m) := mul_le_mul_of_nonneg_left (hd 4).2 htag0
      _ = 2 * t := by field_simp
      _ ≤ 2 := by linarith
  have hw (w : ℝ) (v : ℝ) (hw0 : 0 < w) (hρ : rho κ m w / w ≤ κ)
      (hv : v ≤ 2 / w) : rho κ m w * v ≤ 2 * κ := by
    calc
      _ ≤ rho κ m w * (2 / w) := mul_le_mul_of_nonneg_left hv (rho_nonneg hκ0)
      _ = 2 * (rho κ m w / w) := by ring
      _ ≤ _ := by linarith
  have h0 := hw a _ ha0 hρa (hd 0).2
  have h1 := hw a _ ha0 hρa (hd 1).2
  have h2 := hw b _ hb0 hρb (hd 2).2
  have h3 := hw b _ hb0 hρb (hd 3).2
  have hp0 (i : Fin 5) : 0 ≤ componentProbabilities κ m a b t i *
      endpointDensity side m a b (some i) x :=
    mul_nonneg (componentProbabilities_nonneg hκ0 hm0 ht0 i) (hd i).1
  have hlo : 49 / 50 ≤ marginalDensity side κ m a b t x := by
    exact hq.1.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hp0 i)))
  have hup : marginalDensity side κ m a b t x ≤ 3 + 8 * κ := by
    unfold marginalDensity
    simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    change diagonalMass κ m a b t + (rho κ m a * endpointDensity side m a b (some 0) x +
      (rho κ m a * endpointDensity side m a b (some 1) x +
      (rho κ m b * endpointDensity side m a b (some 2) x +
      (rho κ m b * endpointDensity side m a b (some 3) x +
      t / m * endpointDensity side m a b (some 4) x)))) ≤ _
    linarith [hq.2]
  exact ⟨hlo, hup, by linarith⟩

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma ofReal_marginalDensity (side : Bool) (x : ℝ) :
    ENNReal.ofReal (marginalDensity side κ m a b t x) =
      labelMass κ m a b t none + ∑ i : Fin 5,
        labelMass κ m a b t (some i) *
          ENNReal.ofReal (endpointDensity side m a b (some i) x) := by
  have hm0 : 0 < m := by linarith
  apply ofReal_mixture_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i y
    exact endpointDensity_nonneg side m a b (some i) y

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_eq_integral (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) =
      ∫⁻ x in bin r d, ENNReal.ofReal (marginalDensity side κ m a b t x) ∂baseLaw := by
  have h := withDensity_finite_mixture baseLaw (labelMass κ m a b t none)
    (fun i : Fin 5 => labelMass κ m a b t (some i))
    (fun i x => ENNReal.ofReal (endpointDensity side m a b (some i) x))
    (fun i => (endpointDensity_measurable side m a b (some i)).ennreal_ofReal)
  simp_rw [← ofReal_marginalDensity hκ0 hκ hm ha ha' hb hb' ht0 ht side] at h
  have heval := congrArg (fun ν : Measure ℝ => ν (bin r d)) h
  rw [withDensity_apply _ (show MeasurableSet (bin r d) from measurableSet_Ico)] at heval
  rw [heval, Fintype.sum_option]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← endpointLaw_eq_density hm ha ha' hb hb' side (some i)]
  rfl

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_le_ten (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) ≤ 10 * baseLaw (bin r d) := by
  rw [digitWeight_total_eq_integral hκ0 hκ hm ha ha' hb hb' ht0 ht]
  calc
    _ ≤ ∫⁻ _x in bin r d, (10 : ℝ≥0∞) ∂baseLaw := by
      apply lintegral_mono
      intro x
      exact le_trans (ENNReal.ofReal_le_ofReal
        (marginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht side x).2.2.le)
        (by norm_num)
    _ = _ := by simp

end Invariant233.CircleDigitCoupling

end

end OAI
