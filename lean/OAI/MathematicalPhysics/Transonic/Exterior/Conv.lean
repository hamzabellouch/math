import OAI.MathematicalPhysics.Transonic.Exterior.Jet

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open PowerSeries Finset

def relative (b : ℕ → ℝ) (N j : ℕ) : ℝ := b j/b N
def pairValue (b : ℕ → ℝ) (N i j : ℕ) : ℝ := b (min i j)*relative b N (max i j)
def squareRatio (w : Series) (n : ℕ) : ℝ := coeff n (w^2)/coeff (n-1) w

def powerRatio (w : Series) (N k n : ℕ) : ℝ := coeff n (w^k)/coeff N w
def squareRRatio (w : Series) (n : ℕ) : ℝ :=
  (∑ i ∈ Ico 2 n, coeff i w*coeff (n+1-i) w)/coeff (n-1) w

lemma pairValue_eq (b : ℕ → ℝ) (N i j : ℕ) :
    pairValue b N i j=b i*b j/b N := by
  unfold pairValue relative
  rcases le_total i j with h|h
  · rw [min_eq_left h,max_eq_right h];ring
  · rw [min_eq_right h,max_eq_left h];ring

lemma relative_self {b : ℕ → ℝ} {N : ℕ} (h : b N≠0) : relative b N N=1 := by
  simp [relative,h]

lemma relative_step {b : ℕ → ℝ} (N j : ℕ) (h : b j≠0) (h' : b (j+1)≠0) :
    relative b N j = relative b N (j+1)/(b (j+1)/b j) := by
  unfold relative
  field_simp

lemma squareRatio_sum (w : Series) (h : coeff 0 w=0) (n : ℕ) :
    squareRatio w n = ∑ i ∈ Ico 1 n, pairValue (fun i => coeff i w) (n-1) i (n-i) := by
  unfold squareRatio
  rw [EulerFormal.coeff_square w h,Finset.sum_div]
  apply sum_congr rfl
  intro i hi
  rw [pairValue_eq]

lemma powerRatio_square {w : Series} {n N : ℕ} (h : coeff (n-1) w≠0) :
    powerRatio w N 2 n=squareRatio w n*relative (fun i => coeff i w) N (n-1) := by
  unfold powerRatio squareRatio relative
  field_simp

lemma powerRatio_cube (w : Series) (h : coeff 0 w=0) (N n : ℕ)
    (hn : ∀ j, 1≤j → j≤n-2 → coeff j w≠0) :
    powerRatio w N 3 n =
      ∑ i ∈ Ico 1 (n-1),
        pairValue (fun i => coeff i w) N i (n-i-1)*squareRatio w (n-i) := by
  unfold powerRatio
  rw [EulerFormal.coeff_cube w h,Finset.sum_div]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_Ico.mp hi
  rw [pairValue_eq]
  unfold squareRatio
  have hh := hn (n-i-1) (by omega) (by omega)
  field_simp

lemma powerRatio_fourth (w : Series) (h : coeff 0 w=0) (N n : ℕ)
    (hn : ∀ j, 1≤j → j≤n-3 → coeff j w≠0) :
    powerRatio w N 4 n =
      ∑ i ∈ Ico 2 (n-1),
        pairValue (fun i => coeff i w) N (i-1) (n-i-1)*
          squareRatio w i*squareRatio w (n-i) := by
  unfold powerRatio
  rw [EulerFormal.coeff_fourth w h,Finset.sum_div]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_Ico.mp hi
  rw [pairValue_eq]
  unfold squareRatio
  have hh := hn (n-i-1) (by omega) (by omega)
  have hh' := hn (i-1) (by omega) (by omega)
  field_simp

lemma squareRRatio_sum (w : Series) (n : ℕ) :
    squareRRatio w n =
      ∑ i ∈ Ico 2 n, pairValue (fun i => coeff i w) (n-1) i (n+1-i) := by
  unfold squareRRatio
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro i hi
  rw [pairValue_eq]

lemma powerRatio_low {w : Series} (h : coeff 0 w=0) {k n N : ℕ} (hn : n<k) :
    powerRatio w N k n=0 := by
  have hw : (X : Series)∣w := X_dvd_iff.mpr (by simpa using h)
  obtain ⟨v,rfl⟩ := hw
  unfold powerRatio
  rw [mul_pow,mul_comm,coeff_mul_X_pow']
  simp [not_le.mpr hn]

/-- The normalized scalar recurrence used for the exterior jet enclosure.
Unlike unnormalized coefficient arithmetic it cancels the largest jet scale. -/
def ratioStep (sigma kappa c : ℝ) (n : ℕ) (sq cu qu : ℕ → ℝ) (sr : ℝ) : ℝ :=
  p0 sigma*(n+1)*(sr-cu (n+1)/3)+
  p1 sigma*n*(sq n-cu n/3)+
  p2 sigma*(n-1)*(sq (n-1)-cu (n-1)/3)+
  p3 sigma*(n-2)*(sq (n-2)-cu (n-2)/3)+
  i11 kappa c+i20 kappa c*sq n+i21 kappa c*sq (n-1)+
  i30 kappa c*cu n+i31 kappa c*cu (n-1)+
  i40 kappa c*qu n+i41 kappa c*qu (n-1)

lemma normalized_recurrence (sigma kappa c s rho : ℝ) (w : Series)
    (hw0 : coeff 0 w=0) (hw1 : coeff 1 w=s) (he : residual sigma kappa c w=0)
    (hrho : rho*(2*(1-sigma)*s)=(1-c)*(2*kappa+3)-2*(1-sigma)*s)
    (n : ℕ) (hn : 2≤n) (hb : coeff (n-1) w≠0) :
    (2*(1-sigma)*s*(rho-n))*(coeff n w/coeff (n-1) w)=
      ratioStep sigma kappa c n (powerRatio w (n-1) 2) (powerRatio w (n-1) 3)
        (powerRatio w (n-1) 4) (squareRRatio w n) := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+2 := ⟨n-2,by omega⟩
  have hh := coefficient_equation sigma kappa c w k he
  have hs := EulerFormal.coeff_square_remainder w hw0 (k+2) (by omega)
  rw [hw1] at hs
  rw [show k+2+1=k+3 by omega] at hs
  rw [hs] at hh
  unfold ratioStep powerRatio squareRRatio p0 p1 p2 p3 i10 i11 i20 i21 i30 i31 i40 i41 at *
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,
    show k+2+1=k+3 by omega] at *
  push_cast
  field_simp
  linear_combination -3*hh+3*(coeff (k+2) w)*hrho

end SepticProfile.ExteriorJet

end
end

end OAI
