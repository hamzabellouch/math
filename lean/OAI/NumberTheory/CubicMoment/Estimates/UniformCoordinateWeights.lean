import OAI.NumberTheory.CubicMoment.Estimates.IndependentMellinTail
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! Uniform joint Mellin moments from the actual common support and derivative
bounds of the coordinate weights. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellinMass_nonneg (W : ℝ → ℂ) : 0 ≤ zeroLineMellinMass W := by
  unfold zeroLineMellinMass
  positivity

lemma UniformLogWeights.zeroLine_moment {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, (∫ t : ℝ, |t|^A*‖zeroLineMellinWeight (W i) 1 t‖) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := h.mellin_norm_moment 0 A
  refine ⟨(1/(2*Real.pi))*C,by positivity,?_⟩
  intro i
  rw [zeroLineMellinWeight_moment (W i) (by norm_num) A]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Complex.ofReal_zero,zero_add] using hbound i 0 (by norm_num)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma independentMellinMoment_factorization (W : ι → ℝ → ℂ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (A : ℕ) :
    independentMellinMoment W A = ∑ i, ∏ j,
      (∫ t : ℝ, if j=i then |t|^A*‖zeroLineMellinWeight (W j) 1 t‖
        else ‖zeroLineMellinWeight (W j) 1 t‖) := by
  unfold independentMellinMoment mellinHeightPower
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ =>
    independentMellinWeight_coordinate_moment_integrable W (fun _ => 1) hW hpos hsm
      (fun _ => by norm_num) A i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_fintype_prod_volume_eq_prod (fun (j : ι) (t : ℝ) =>
    if j=i then |t|^A*‖zeroLineMellinWeight (W j) 1 t‖
      else ‖zeroLineMellinWeight (W j) 1 t‖)]
  apply integral_congr_ae
  filter_upwards with τ
  rw [independentMellinWeight,norm_prod]
  symm
  convert prod_one_coordinate (fun j => ‖zeroLineMellinWeight (W j) 1 (τ j)‖)
    i (|τ i|^A) using 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [hj]

/-- One bound controls the product L1 mass and the genuine joint tail moment
for every member of a uniformly smooth coordinate family. -/
theorem UniformLogWeights.coordinate_moments {γ : Type*} {W : γ → ι → ℝ → ℂ}
    (h : UniformLogWeights (fun z : γ × ι => W z.1 z.2)) (A : ℕ) :
    ∃ C J : ℝ, 0 ≤ C ∧ 0 ≤ J ∧ ∀ u : γ,
      (∏ i, zeroLineMellinMass (W u i)) ≤ C ∧ independentMellinMoment (W u) A ≤ J := by
  obtain ⟨C₀,hC₀,h₀⟩ := h.zeroLine_moment 0
  obtain ⟨C₁,hC₁,h₁⟩ := h.zeroLine_moment A
  let K := max C₀ C₁
  have hK : 0 ≤ K := hC₀.trans (le_max_left _ _)
  refine ⟨K^(Fintype.card ι),(Fintype.card ι:ℝ)*K^(Fintype.card ι),
    pow_nonneg hK _,by positivity,?_⟩
  intro u
  have hmass (i : ι) : zeroLineMellinMass (W u i) ≤ K := by
    have hh := (h₀ (u,i)).trans (le_max_left C₀ C₁)
    simp only [pow_zero,one_mul] at hh
    rw [zeroLineMellinWeight_mass (W u i) (Z := 1) (by norm_num)] at hh
    exact hh
  constructor
  · calc
      _ ≤ ∏ _i : ι, K := Finset.prod_le_prod₀ (fun i _ => zeroLineMellinMass_nonneg (W u i))
        (fun i _ => hmass i)
      _ = _ := by simp
  · rw [independentMellinMoment_factorization (W u) (fun i => h.compact (u,i))
        (fun i => h.positive (u,i)) (fun i => h.smooth (u,i)) A]
    calc
      _ ≤ ∑ _i : ι, K^(Fintype.card ι) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ∏ _j : ι, K := by
            apply Finset.prod_le_prod₀
            · intro j _
              exact integral_nonneg (fun t => by split_ifs <;> positivity)
            · intro j _
              by_cases hj : j=i
              · simp only [hj,ite_true]
                exact (h₁ (u,i)).trans (le_max_right _ _)
              · simp only [hj,ite_false]
                rw [zeroLineMellinWeight_mass (W u j) (Z := 1) (by norm_num)]
                exact hmass j
          _ = _ := by simp
      _ = _ := by simp

end CubicFirstMoment

end

end OAI
