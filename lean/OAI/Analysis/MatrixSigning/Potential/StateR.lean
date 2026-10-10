import Mathlib
import OAI.Analysis.MatrixSigning.Potential.FaceValueDirectionVariations
import OAI.Analysis.MatrixSigning.Potential.StateIA
import OAI.Analysis.MatrixSigning.Potential.ResponseInputSub

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open Matrix CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction CurrentKS.Covariance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ} (p : LightPoint d N)

def R (y : Coordinates N) : ℝ := value p.ε (p.fixedPart+S p.A y) (eta 384 p.A y)
def tildeA (i : Fin N) : ℝ := p.l i*p.a i
def tildeB (i : Fin N) : ℝ := p.m i*p.b i
def resp (v : Covariance.E (2*N)) : Coordinates N := fun i => responseLin p.IB v i
def direction (v : Covariance.E (2*N)) : Coordinates N := fun i => p.resp v i/p.T i
def invEnergy (v : Covariance.E (2*N)) : ℝ := energy p.X p.Y p.P p.Q
  (sandwich p.X (responseInput p.A p.l (fstVec v)))
  (sandwich p.Y (responseInput p.A p.m (sndVec v)))

lemma tildeA_pos [NeZero d] (i : Fin N) : 0 < p.tildeA i := mul_pos (p.scales_pos i).2.1 (p.a_pos i)
lemma tildeB_pos [NeZero d] (i : Fin N) : 0 < p.tildeB i := mul_pos (p.scales_pos i).2.2 (p.b_pos i)
lemma wP_pos [NeZero d] (i : Fin N) : 0 < p.wP i := mul_pos (p.scales_pos i).2.1 (p.pp_pos i)
lemma wQ_pos [NeZero d] (i : Fin N) : 0 < p.wQ i := mul_pos (p.scales_pos i).2.2 (p.qq_pos i)
lemma multiplied_direction [NeZero d] (v : Covariance.E (2*N)) (i : Fin N) :
    p.T i*p.direction v i = p.resp v i := by
  exact mul_div_cancel₀ _ (p.scales_pos i).1.ne'

lemma R_first [NeZero d] (h : Coordinates N) :
    deriv (fun s => p.R (line p.x h s)) 0 = ∑ i, h i*(p.T i*(p.wP i-p.wQ i)) := by
  obtain ⟨_,_,_,_,hd,_⟩ := face_value_direction_variations (by norm_num : (0 : ℝ) ≤ 384) p.ε_pos
    p.A p.x h p.interior p.A_pos p.A_rank p.fixedPart 100 p.lower p.upper p.primal p.feasible p.minimal
    p.P p.Q p.P_pos.posSemidef p.Q_pos.posSemidef p.stationary_X p.stationary_Y
  change deriv (fun s => value p.ε (p.fixedPart+S p.A (line p.x h s)) (eta 384 p.A (line p.x h s))) 0 = _
  rw [hd]
  apply Finset.sum_congr rfl
  intro i _
  change h i*((1+384*psi₁ (p.x i)*p.b i)*p.pp i-(1-384*psi₁ (p.x i)*p.a i)*p.qq i) = _
  rw [← p.lT_eq i,← p.mT_eq i]
  dsimp only [wP,wQ]
  ring

lemma R_second [NeZero d] (v : Covariance.E (2*N)) (hv : constraintLin p.IA p.IB v = 0) :
    deriv (deriv (fun s => p.R (line p.x (p.direction v) s))) 0 ≤
      3*p.invEnergy v-192*negativeWeight p.A p.x (p.direction v) p.X p.Y p.P p.Q := by
  obtain ⟨U,V,hU,hV,_,hdd⟩ := face_value_direction_variations (by norm_num : (0 : ℝ) ≤ 384) p.ε_pos
    p.A p.x (p.direction v) p.interior p.A_pos p.A_rank p.fixedPart 100 p.lower p.upper p.primal p.feasible p.minimal
    p.P p.Q p.P_pos.posSemidef p.Q_pos.posSemidef p.stationary_X p.stationary_Y
  obtain ⟨hf,hg⟩ := constraints_responses p.IA p.IB v hv
  have hF : (fun i => fstVec v i)-(interaction 384 p.A p.m p.Y *ᵥ fun i => sndVec v i) = p.resp v := by
    funext i
    exact congrArg (fun w : Covariance.E N => w i) hf
  have hG : (fun i => sndVec v i)-(interaction 384 p.A p.l p.X *ᵥ fun i => fstVec v i) = -p.resp v := by
    funext i
    exact congrArg (fun w : Covariance.E N => w i) hg
  obtain ⟨rfl,rfl⟩ := identify_responses (by norm_num : (0 : ℝ) ≤ 384) p.ε_pos p.A p.x
    (p.direction v) (p.resp v) p.T p.l p.m (fstVec v) (sndVec v) (fun i => (p.interior i).le)
    p.A_pos p.A_rank p.X p.Y p.P p.Q U V p.X_pos p.Y_pos p.P_pos p.Q_pos p.stationary_X p.stationary_Y
    p.lm_eq p.lT_eq p.mT_eq (p.multiplied_direction v) hF hG hU hV
  simpa only [R,invEnergy,X,Y,show (384 : ℝ)/2 = 192 by norm_num] using hdd

lemma crossed_identity [NeZero d] (i : Fin N) :
    p.tildeA i*p.wQ i+p.tildeB i*p.wP i = psi (p.x i)*(p.b i*p.pp i+p.a i*p.qq i) := by
  dsimp only [tildeA,tildeB,wP,wQ]
  rw [← p.lm_eq i]
  ring

lemma negativeWeight_lower [NeZero d] (v : Covariance.E (2*N)) :
    (1/3 : ℝ)*(∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(p.resp v i)^2) ≤
      negativeWeight p.A p.x (p.direction v) p.X p.Y p.P p.Q := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change (1/3 : ℝ)*((p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(p.resp v i)^2) ≤
    kappa (p.x i)*(p.direction v i)^2*(p.b i*p.pp i+p.a i*p.qq i)
  rw [p.crossed_identity i]
  have h₁ : (1/3 : ℝ)*psi (p.x i) ≤ kappa (p.x i)/p.T i^2 := by
    have hh := (psi_bounds (p.interior i).le).2
    linarith [(p.kappa_bounds i).1]
  have hpos : 0 ≤ (p.b i*p.pp i+p.a i*p.qq i)*(p.resp v i)^2 := by
    have ha := (p.a_pos i).le; have hb := (p.b_pos i).le
    have hp := (p.pp_pos i).le; have hq := (p.qq_pos i).le
    positivity
  have hh := mul_le_mul_of_nonneg_right h₁ hpos
  dsimp only [direction]
  convert hh using 1 <;> first | rfl | ring

lemma R_second_rescaled [NeZero d] (v : Covariance.E (2*N)) (hv : constraintLin p.IA p.IB v = 0) :
    deriv (deriv (fun s => p.R (line p.x (p.direction v) s))) 0 ≤
      3*p.invEnergy v-64*(∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(p.resp v i)^2) := by
  have h₁ := p.R_second v hv
  have h₂ := p.negativeWeight_lower v
  linarith

lemma R_ensemble_curvature [NeZero d] {Γ : Covariance.Mat (2*N)}
    (hc : ∀ j, constraintLin p.IA p.IB (column (CFC.sqrt Γ) j) = 0)
    (he : (∑ j, p.invEnergy (column (CFC.sqrt Γ) j)) ≤
      16*(∑ i,(p.tildeA i*p.wP i+p.tildeB i*p.wQ i)*
        (∑ j,(p.resp (column (CFC.sqrt Γ) j) i)^2))) :
    (1/2 : ℝ)*(∑ j,deriv (deriv (fun s => p.R (line p.x (p.direction (column (CFC.sqrt Γ) j)) s))) 0) ≤
      24*(∑ i,(p.tildeA i*p.wP i+p.tildeB i*p.wQ i)*(∑ j,(p.resp (column (CFC.sqrt Γ) j) i)^2))-
      32*(∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(∑ j,(p.resp (column (CFC.sqrt Γ) j) i)^2)) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) fun j _ => p.R_second_rescaled (column (CFC.sqrt Γ) j) (hc j)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hh
  have hs : (∑ j,∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(p.resp (column (CFC.sqrt Γ) j) i)^2) =
      ∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(∑ j,(p.resp (column (CFC.sqrt Γ) j) i)^2) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hs] at hh
  linarith

end
end CurrentKS.State.LightPoint

end OAI
