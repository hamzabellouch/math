import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.dShellForm

namespace OAI

noncomputable section Reused_ShellInnerField

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  graphNuclear weightedMass weightedNuclear weightedPairs weightedCoreDensity
  oneBodySquareTotal SmoothMultiplier.oneBody weightedKinetic weightedGradient
  weightedFullDensity graphKineticPair sectorExcessOperator oneBodyGradientError

def rawInnerField {N : ℕ} (Z h : ℝ) (x : Configuration N) (y : Space) : ℝ :=
  Z/‖y‖ - ∑ j,if ‖x j‖ < h then (‖y-x j‖)⁻¹ else 0

def oneBodyInnerField {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (x : Configuration N) : ℝ :=
  ∑ i,p.value (x i)^2*rawInnerField Z h x (x i)

def weightedInnerPairs {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (h : ℝ) (i : Fin N) : ℝ :=
  ∑ s,∑ j,∫ x,if ‖x j‖ < h then
    p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i-x j‖) else 0

lemma graph_pair_integrable_all {N : ℕ} (F : fermionGraph N) (s : Spins N)
    (i j : Fin N) :
    Integrable (fun x => ‖graphComponent s none F x‖^2/‖x i-x j‖) := by
  by_cases hij : i=j
  · subst j; simp only [sub_self,norm_zero,div_zero]; exact integrable_zero _ _ _
  · exact graph_pair_integrable F s i j hij

lemma weightedInnerPairs_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (h : ℝ) (s : Spins N) (i j : Fin N) :
    Integrable (fun x => if ‖x j‖ < h then
      p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i-x j‖) else 0) := by
  exact (p.square_integrable i (graph_pair_integrable_all F s i j)).indicator
    (isOpen_lt (continuous_apply j |>.norm) continuous_const).measurableSet

lemma weightedInnerPairs_le {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (h : ℝ) (i : Fin N) :
    weightedInnerPairs p F h i ≤ weightedPairs F i (fun x => p.value (x i)^2) := by
  unfold weightedInnerPairs weightedPairs
  apply Finset.sum_le_sum; intro s _
  apply Finset.sum_le_sum; intro j _
  by_cases hij : i=j
  · subst j
    simp only [ne_eq,not_true_eq_false,sub_self,norm_zero,div_zero,mul_zero,
      ite_self,integral_zero,le_refl]
  · simp only [ite_eq_left hij]
    apply integral_mono (weightedInnerPairs_integrable p F h s i j)
      (p.square_integrable i (graph_pair_integrable F s i j hij))
    intro x
    dsimp only
    split_ifs
    · rfl
    · positivity

lemma innerField_density_arithmetic {I : Type*} [Fintype I]
    (w k : I → ℝ) (P : I → Prop) [DecidablePred P] (L : I → I → ℝ) (Z b : ℝ) :
    (∑ i,w i*(Z*k i-∑ j,if P j then L i j else 0))*b =
      ∑ i,(Z*(w i*(b*k i)) - ∑ j,if P j then w i*(b*L i j) else 0) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [mul_sub,sub_mul,Finset.mul_sum,Finset.sum_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl; intro j _
    split_ifs <;> ring

lemma oneBodyInnerField_density {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (F : fermionGraph N) (s : Spins N) (x : Configuration N) :
    oneBodyInnerField p Z h x*‖graphComponent s none F x‖^2 =
      ∑ i,(Z*(p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i‖)) -
        ∑ j,if ‖x j‖ < h then
          p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i-x j‖) else 0) := by
  simpa only [oneBodyInnerField,rawInnerField,div_eq_mul_inv] using
    innerField_density_arithmetic (fun i => p.value (x i)^2) (fun i => (‖x i‖)⁻¹)
      (fun j => ‖x j‖ < h) (fun i j => (‖x i-x j‖)⁻¹) Z (‖graphComponent s none F x‖^2)

lemma oneBodyInnerField_density_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (F : fermionGraph N) (s : Spins N) :
    Integrable (fun x => oneBodyInnerField p Z h x*‖graphComponent s none F x‖^2) := by
  simp_rw [oneBodyInnerField_density p Z h F s]
  apply integrable_finsetSum; intro i _
  exact ((p.square_integrable i (graph_nuclear_integrable F s i)).const_mul Z).sub
    (integrable_finsetSum Finset.univ (fun j _ => weightedInnerPairs_integrable p F h s i j))

lemma integral_sum_sub_sum {X I : Type*} [MeasurableSpace X] [Fintype I]
    {μ : Measure X} (f : I → X → ℝ) (g : I → I → X → ℝ)
    (hf : ∀ i, Integrable (f i) μ) (hg : ∀ i j, Integrable (g i j) μ) (Z : ℝ) :
    (∫ x,∑ i,(Z*f i x-∑ j,g i j x) ∂μ) =
      ∑ i,(Z*(∫ x,f i x ∂μ)-∑ j,∫ x,g i j x ∂μ) := by
  have hi (i : I) : Integrable (fun x => Z*f i x-∑ j,g i j x) μ :=
    (hf i |>.const_mul Z).sub (integrable_finsetSum Finset.univ (fun j _ => hg i j))
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_sub (hf i |>.const_mul Z)
    (integrable_finsetSum Finset.univ (fun j _ => hg i j)),integral_const_mul,
    integral_finsetSum Finset.univ (fun j _ => hg i j)]

lemma oneBodyInnerField_density_integral {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (F : fermionGraph N) (s : Spins N) :
    (∫ x,oneBodyInnerField p Z h x*‖graphComponent s none F x‖^2) =
      ∑ i,(Z*(∫ x,p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i‖)) -
        ∑ j,∫ x,if ‖x j‖ < h then
          p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i-x j‖) else 0) := by
  simp_rw [oneBodyInnerField_density p Z h F s]
  exact integral_sum_sub_sum _ _
    (fun i => p.square_integrable i (graph_nuclear_integrable F s i))
    (fun i j => weightedInnerPairs_integrable p F h s i j) Z

lemma oneBodyInnerField_raw_integral {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (F : fermionGraph N) :
    (∫ x,oneBodyInnerField p Z h x ∂formRawLaw (graphFormVector F)) =
      Z*(∑ i,weightedNuclear F i (fun x => p.value (x i)^2)) -
        ∑ i,weightedInnerPairs p F h i := by
  rw [formRawLaw_integral (graphFormVector_sobolev F).sobolevVector]
  simp only [formRawDensity,graphFormVector_value_eq,Finset.sum_mul]
  simp_rw [mul_comm (‖graphComponent _ none F _‖^2)]
  rw [integral_finsetSum _ (fun s _ => oneBodyInnerField_density_integrable p Z h F s)]
  simp only [oneBodyInnerField_density_integral p Z h F,Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  congr 1
  · congr 1
    unfold weightedNuclear
    exact Finset.sum_comm
  · unfold weightedInnerPairs
    exact Finset.sum_comm

theorem quantum_shell_inner_field_residual {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (p : SmoothMultiplier spaceDirections) (F : fermionGraph (N+1)) (h : ℝ)
    (hstep : energy Z (N+1)+lam ≤ energy Z N) :
    lam*weightedMass F (oneBodySquareTotal p).value ≤
      (1/2:ℝ)*oneBodyGradientError p F +
      (∫ x,oneBodyInnerField p Z h x ∂formRawLaw (graphFormVector F)) +
      (⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  have hh := quantum_oneBody_residual hZ p F hstep
  have hl := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    weightedInnerPairs_le p F h i
  have he := oneBodyInnerField_raw_integral p Z h F
  exact (show ∀ a b c d r z k : ℝ, a+b≤c+d+r → k≤a → z=c-k →
    b≤d+z+r by intros; linarith) _ _ _ _ _ _ _ hh hl he

theorem quantum_shell_inner_field {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (p : SmoothMultiplier spaceDirections) (F : fermionGraph (N+1)) (h : ℝ)
    (hn : ‖fermionGraphValue (N+1) F‖^2=1)
    (hF : formEnergy Z (graphFormVector F)=energy Z (N+1))
    (hstep : energy Z (N+1)+lam ≤ energy Z N) :
    lam*weightedMass F (oneBodySquareTotal p).value ≤
      (1/2:ℝ)*oneBodyGradientError p F +
      (∫ x,oneBodyInnerField p Z h x ∂formRawLaw (graphFormVector F)) := by
  have hh := quantum_shell_inner_field_residual hZ p F h hstep
  have he := ground_oneBody_residual_zero hZ p F hn hF
  exact (show ∀ a b r : ℝ, a≤b+r → r=0 → a≤b by intros; linarith)
    _ _ _ hh he

end CoulombAtom
end Reused_ShellInnerField

end OAI
