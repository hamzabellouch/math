import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SelectionNumerics

namespace OAI

noncomputable section Reused_ShellForm

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  graphNuclear weightedMass weightedNuclear weightedPairs weightedCoreDensity
  oneBodySquareTotal SmoothMultiplier.oneBody weightedKinetic weightedGradient
  weightedFullDensity graphKineticPair sectorExcessOperator

def oneBodyGradientError {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) : ℝ :=
  ∑ s,∑ i,∑ a,∫ x,(lineDeriv ℝ p.value (x i) (spaceDirections a))^2*
    ‖graphComponent s none F x‖^2

attribute [local irreducible] oneBodyGradientError

lemma oneBodySquareTotal_mass {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) :
    weightedMass F (oneBodySquareTotal p).value =
      ∑ i,weightedMass F (fun x => p.value (x i)^2) := by
  unfold weightedMass
  simp only [oneBodySquareTotal_integral p (Lp.memLp _).norm.integrable_sq]
  exact Finset.sum_comm

lemma oneBodySquareTotal_full {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z : ℝ) (F : fermionGraph N) :
    weightedFullDensity Z F (oneBodySquareTotal p).value =
      ∑ i,weightedFullDensity Z F (fun x => p.value (x i)^2) := by
  unfold weightedFullDensity
  simp only [oneBodySquareTotal_integral p
    ((graphFormVector_sobolev F).quantumEnergyDensity_integrable Z _)]
  exact Finset.sum_comm

lemma oneBodySquareTotal_kinetic {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) :
    weightedKinetic F (oneBodySquareTotal p).value =
      ∑ s,∑ i,∑ j,∑ a,∫ x,p.value (x i)^2*‖graphComponent s (some (j,a)) F x‖^2 := by
  rw [weightedKinetic_expand]
  simp only [oneBodySquareTotal_integral p (Lp.memLp _).norm.integrable_sq]
  apply Finset.sum_congr rfl; intro s _
  exact sum_rotate_three _

lemma oneBody_graphkinetic_lower {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (∑ j,∑ a,∫ x,p.value (x i)^2*‖graphComponent s (some (j,a)) F x‖^2) -
      (∑ a,∫ x,p.value (x i)^2*‖graphComponent s (some (i,a)) F x‖^2) -
      (∑ a,∫ x,(lineDeriv ℝ p.value (x i) (spaceDirections a))^2*
        ‖graphComponent s none F x‖^2) ≤
    ∑ j,∑ a,(⟪((p.oneBody i).apply ((p.oneBody i).apply (F.val s))).val (some (j,a)),
      graphComponent s (some (j,a)) F⟫_ℂ).re := by
  simpa only [graphComponent_apply] using oneBody_kinetic_lower p (F.val s) i

lemma oneBodySquareTotal_pairing_pack {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) :
    (∑ s,∑ i,∑ j,∑ a,(⟪((p.oneBody i).apply ((p.oneBody i).apply (F.val s))).val
      (some (j,a)),graphComponent s (some (j,a)) F⟫_ℂ).re) =
      graphKineticPair ((oneBodySquareTotal p).apply F) F := by
  unfold graphKineticPair
  simp only [oneBodySquareTotal_component,sum_inner,Complex.re_sum]
  apply Finset.sum_congr rfl; intro s _
  exact (sum_rotate_three _).symm

lemma shell_kinetic_sum_arithmetic {S I : Type*} [Fintype S] [Fintype I]
    (K D E G : S → I → ℝ) (Kt Dt Et Gt : ℝ)
    (hK : Kt=∑ s,∑ i,K s i) (hD : Dt=∑ s,∑ i,D s i)
    (hE : Et=∑ s,∑ i,E s i) (hG : Gt=∑ s,∑ i,G s i)
    (h : ∀ s i,K s i-D s i-E s i ≤ G s i) : Kt-Dt-Et ≤ Gt := by
  rw [hK,hD,hE,hG]
  simp only [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i _ => h s i

lemma oneBodySquareTotal_kinetic_lower {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) :
    weightedKinetic F (oneBodySquareTotal p).value -
      (∑ i,weightedGradient F (fun x => p.value (x i)^2) i) -
      oneBodyGradientError p F ≤ graphKineticPair ((oneBodySquareTotal p).apply F) F := by
  apply shell_kinetic_sum_arithmetic _ _ _ _ _ _ _ _
    (oneBodySquareTotal_kinetic p F) _ (show oneBodyGradientError p F = _ by
      unfold oneBodyGradientError; rfl) (oneBodySquareTotal_pairing_pack p F).symm
    (oneBody_graphkinetic_lower p F)
  unfold weightedGradient
  exact Finset.sum_comm

lemma shell_form_sum_arithmetic {ι : Type*} [Fintype ι]
    (D C K V P : ι → ℝ) (Z W G A Dt err : ℝ)
    (hD : ∀ i,D i=C i+(1/2:ℝ)*K i-Z*V i+P i)
    (hG : W-(∑ i,K i)-err ≤ G) (hDt : Dt=∑ i,D i)
    (hA : A=Dt+(1/2:ℝ)*(G-W)) :
    (∑ i,(C i-Z*V i+P i)) ≤ A+(1/2:ℝ)*err := by
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hD i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hs ⊢
  linarith

lemma oneBody_form_lower {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z : ℝ) (F : fermionGraph N) :
    (∑ i,(weightedCoreDensity Z F i (fun x => p.value (x i)^2) -
      Z*weightedNuclear F i (fun x => p.value (x i)^2) +
      weightedPairs F i (fun x => p.value (x i)^2))) ≤
      (⟪(oneBodySquareTotal p).apply F,coulombFormOperator Z N F⟫_ℂ).re +
        (1/2:ℝ)*oneBodyGradientError p F := by
  let C := p.bound.choose
  have hC : ∀ y, |p.value y| ≤ C := p.bound.choose_spec
  have hc (i : Fin N) : Continuous (fun x : Configuration N => p.value (x i)^2) :=
    (p.regular.continuous.comp (continuous_apply i)).pow 2
  have hb (i : Fin N) (x : Configuration N) : ‖p.value (x i)^2‖ ≤ C^2 := by
    rw [norm_pow,Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC (x i)) 2
  exact shell_form_sum_arithmetic _ _ _ _ _ Z _ _ _ _ _
    (fun i => weightedFullDensity_delete Z F i (fun x => p.value (x i)^2) (hc i) (hb i))
    (oneBodySquareTotal_kinetic_lower p F) (oneBodySquareTotal_full p Z F)
    ((oneBodySquareTotal p).form_weighted_packed Z F)

lemma energy_oneBody_core_price_le {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (p : SmoothMultiplier spaceDirections) (F : fermionGraph (N+1))
    (hstep : energy Z (N+1)+lam ≤ energy Z N) (i : Fin (N+1)) :
    (energy Z (N+1)+lam)*weightedMass F (fun x => p.value (x i)^2) ≤
      weightedCoreDensity Z F i (fun x => p.value (x i)^2) := by
  obtain ⟨C,hC⟩ := p.bound
  have hm := weightedMass_nonneg F (fun x : Configuration (N+1) => sq_nonneg (p.value (x i)))
  have hb (y : Space) : ‖p.value y^2‖ ≤ C^2 := by
    rw [norm_pow,Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC y) 2
  have hi := weighted_core_coordinate F hZ i (fun y => p.value y^2)
    (p.regular.continuous.pow 2) (fun y => sq_nonneg _) hb
  apply (mul_le_mul_of_nonneg_right hstep hm).trans
  simpa only [weightedMass,weightedCoreDensity] using hi

lemma shell_residual_cancellation {ι : Type*} [Fintype ι]
    (C V P M : ι → ℝ) (E lam Z A Mt r err : ℝ)
    (hC : ∀ i,(E+lam)*M i ≤ C i) (hM : Mt=∑ i,M i)
    (hA : r=A-E*Mt) (hL : (∑ i,(C i-Z*V i+P i)) ≤ A+(1/2:ℝ)*err) :
    (∑ i,P i)+lam*Mt ≤ Z*(∑ i,V i)+(1/2:ℝ)*err+r := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hC i
  rw [← Finset.mul_sum,← hM] at hs
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hL
  nlinarith

theorem quantum_oneBody_residual {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (p : SmoothMultiplier spaceDirections) (F : fermionGraph (N+1))
    (hstep : energy Z (N+1)+lam ≤ energy Z N) :
    (∑ i,weightedPairs F i (fun x => p.value (x i)^2)) +
      lam*weightedMass F (oneBodySquareTotal p).value ≤
    Z*(∑ i,weightedNuclear F i (fun x => p.value (x i)^2)) +
      (1/2:ℝ)*oneBodyGradientError p F +
      (⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  have he := sectorExcessOperator_pair Z ((oneBodySquareTotal p).apply F) F
  have hp := FermionMultiplier.value_weighted_pairing F (oneBodySquareTotal p)
  have he' := he.trans (congrArg (fun t : ℝ =>
    (⟪(oneBodySquareTotal p).apply F,coulombFormOperator Z (N+1) F⟫_ℂ).re-
      energy Z (N+1)*t) hp)
  exact shell_residual_cancellation _ _ _ _ _ _ _ _ _ _ _
    (fun i => energy_oneBody_core_price_le hZ p F hstep i)
    (oneBodySquareTotal_mass p F) he' (oneBody_form_lower p Z F)

lemma ground_oneBody_residual_zero {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (p : SmoothMultiplier spaceDirections) (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2=1)
    (hF : formEnergy Z (graphFormVector F)=energy Z N) :
    (⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z N F⟫_ℂ).re=0 := by
  have he := sectorExcessOperator_pair Z ((oneBodySquareTotal p).apply F) F
  have hp := FermionMultiplier.value_weighted_pairing F (oneBodySquareTotal p)
  have he' := he.trans (congrArg (fun t : ℝ =>
    (⟪(oneBodySquareTotal p).apply F,coulombFormOperator Z N F⟫_ℂ).re-
      energy Z N*t) hp)
  exact he'.trans ((congrArg (fun t : ℝ => t-energy Z N*weightedMass F
    (oneBodySquareTotal p).value) (ground_weighted_identity hZ F hn hF
      (oneBodySquareTotal p))).trans (sub_self _))

theorem quantum_ground_oneBody {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (p : SmoothMultiplier spaceDirections) (F : fermionGraph (N+1))
    (hn : ‖fermionGraphValue (N+1) F‖^2=1)
    (hF : formEnergy Z (graphFormVector F)=energy Z (N+1))
    (hstep : energy Z (N+1)+lam ≤ energy Z N) :
    lam*weightedMass F (oneBodySquareTotal p).value ≤
      (1/2:ℝ)*oneBodyGradientError p F +
        Z*(∑ i,weightedNuclear F i (fun x => p.value (x i)^2)) -
        (∑ i,weightedPairs F i (fun x => p.value (x i)^2)) := by
  have hh := quantum_oneBody_residual hZ p F hstep
  have hr := ground_oneBody_residual_zero hZ p F hn hF
  exact (show ∀ a b c d r : ℝ, a+b≤c+d+r → r=0 → b≤d+c-a by
    intros; linarith) _ _ _ _ _ hh hr

end CoulombAtom
end Reused_ShellForm

end OAI
