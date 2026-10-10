import Mathlib
import OAI.Probability.CriticalPercolation.Growth.RealSparseDoubling

namespace OAI

section
noncomputable section
namespace CriticalPercolation.HarmonicAnalysis

lemma coordinate_ratio_bounds (v₀ v₁ d₀ d₁ T : ℝ) (m : ℕ) (hm : 0 < m)
    (hv₀ : 0 < v₀) (hd₀ : 0 < d₀) (hvv : v₀ ≤ v₁) (hdd : d₀ ≤ d₁)
    (hT : 0 ≤ T) (hp : v₁^m*d₁ ≤ T^m*(v₀^m*d₀)) :
    v₁ ≤ T*v₀ ∧ d₁ ≤ T^m*d₀ := by
  have hv₁ := hv₀.trans_le hvv
  have hvm : 0 < v₀^m := pow_pos hv₀ m
  have hvm' := pow_le_pow_left₀ hv₀.le hvv m
  constructor
  · have hlow := mul_le_mul_of_nonneg_left hdd (pow_nonneg hv₁.le m)
    have hp' : v₁^m*d₀ ≤ (T*v₀)^m*d₀ := by
      calc
        _ ≤ _ := hlow
        _ ≤ _ := hp
        _ = _ := by rw [mul_pow]; ring
    have hh := (mul_le_mul_iff_left₀ hd₀).mp hp'
    exact (pow_le_pow_iff_left₀ hv₁.le (mul_nonneg hT hv₀.le) (by omega : m≠0)).mp hh
  · have hlow := mul_le_mul_of_nonneg_right hvm' (hd₀.le.trans hdd)
    apply (mul_le_mul_iff_right₀ hvm).mp
    calc
      _ ≤ _ := hlow
      _ ≤ _ := hp
      _ = _ := by ring

theorem paired_sparse_scales (V D : ℕ → ℝ) (hV : Monotone V) (hD : Monotone D)
    (hVp : ∀ n, 0 < V n) (hDp : ∀ n, 0 < D n)
    (m e : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
    (hpoly : ∀ R, ∃ n ≥ R, (V n)^m*D n ≤ C*(n:ℝ)^(m*e))
    (L : ℕ) (hL : 0 < L) (N : ℕ) :
    ∃ r R : ℕ, N ≤ r ∧ 1 ≤ R ∧ 6*r ≤ R ∧ 10^(2*L)*r ≤ R ∧
      V (7*r) ≤ (10:ℝ)^(4*(e+1))*V r ∧
      D (5*R) ≤ ((10:ℝ)^(4*(e+1)))^m*D R ∧
      V (R+r) ≤ ((10:ℝ)^(4*(e+1)))^L*V r := by
  let F : ℕ → ℝ := fun n => (V n)^m*D n
  have hF : Monotone F := by
    intro n k hnk
    exact mul_le_mul (pow_le_pow_left₀ (hVp n).le (hV hnk) m) (hD hnk)
      (hDp n).le (pow_nonneg (hVp k).le m)
  have hFp : ∀ n ≥ 0, 0 < F n := fun n _ => mul_pos (pow_pos (hVp n) m) (hDp n)
  let b : ℕ := 10^(4*L)
  have hb : 2 ≤ b := by
    have hh : (10:ℕ)^1 ≤ 10^(4*L) := Nat.pow_le_pow_right (by omega) (by omega)
    simpa only [pow_one] using (show 2 ≤ 10 from by omega).trans hh
  obtain ⟨a,ha,haF⟩ := sparse_real_doubling F hF 0 hFp C hC (m*e) b hb hpoly (max N 1)
  have haN : N ≤ a := by omega
  have ha1 : 1 ≤ a := by omega
  let z : ℕ → ℕ := fun i => 10^i*a
  have hzmono : Monotone z := by
    intro i j hij
    exact Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by omega) hij)
  have hz0 : z 0=a := by simp [z]
  have hzsucc (i : ℕ) : z (i+1)=10*z i := by dsimp [z]; rw [pow_succ]; ring
  have hz4 : z (4*L)=b*a := rfl
  let K : ℝ := (10:ℝ)^(4*(e+1))
  have hK : 0 < K := by dsimp [K]; positivity
  have hp : (V (z (4*L)))^m*D (z (4*L)) ≤ (K^L)^m*((V a)^m*D a) := by
    dsimp [F] at haF
    apply haF.trans
    have he : (b:ℝ)^(m*(e+1))=(K^L)^m := by
      dsimp [b,K]
      push_cast
      simp only [←pow_mul]
      congr 1
      ring
    rw [←he]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ b by omega)) (by nlinarith : m*e+1 ≤ m*(e+1)))
      (mul_nonneg (pow_nonneg (hVp a).le m) (hDp a).le)
  have haend : a ≤ z (4*L) := by simpa only [hz0] using hzmono (show 0 ≤ 4*L by omega)
  obtain ⟨hvend,hdend⟩ := coordinate_ratio_bounds (V a) (V (z (4*L)))
    (D a) (D (z (4*L))) (K^L) m hm (hVp a) (hDp a)
    (hV haend) (hD haend) (pow_nonneg hK.le L) hp
  have hVblock : V (z L) ≤ K^L*V (z 0) := by
    rw [hz0]
    exact (hV (hzmono (by omega))).trans hvend
  obtain ⟨i,hi,hiratio⟩ := exists_local_ratio (fun j => V (z j)) L hL K hK hVblock
  have hDblock : D (z (3*L+L)) ≤ (K^m)^L*D (z (3*L)) := by
    rw [show 3*L+L=4*L by omega]
    calc
      _ ≤ (K^L)^m*D a := hdend
      _ ≤ (K^L)^m*D (z (3*L)) := mul_le_mul_of_nonneg_left
        (hD (by simpa only [hz0] using hzmono (show 0 ≤ 3*L by omega))) (by positivity)
      _ = _ := by
        have he : (K^L)^m=(K^m)^L := by rw [←pow_mul K,←pow_mul K,Nat.mul_comm L m]
        rw [he]
  obtain ⟨j,hj,hjratio⟩ := exists_local_ratio (fun k => D (z (3*L+k))) L hL (K^m)
    (pow_pos hK m) hDblock
  let r := z i
  let R := z (3*L+j)
  have hsmall : 10^(2*L)*r ≤ R := by
    change 10^(2*L)*(10^i*a) ≤ 10^(3*L+j)*a
    rw [←mul_assoc,←pow_add]
    exact Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by omega) (by omega))
  have hr1 : 1 ≤ r := ha1.trans (by simpa only [hz0] using hzmono (show 0 ≤ i by omega))
  have h6 : 6 ≤ 10^(2*L) := by
    have hh : (10:ℕ)^1 ≤ 10^(2*L) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (by norm_num : 6 ≤ (10:ℕ)^1).trans hh
  have hrR : 6*r ≤ R := (Nat.mul_le_mul_right r h6).trans hsmall
  refine ⟨r,R,haN.trans (by simpa only [hz0] using hzmono (show 0 ≤ i by omega)),by omega,hrR,hsmall,?_,?_,?_⟩
  · apply (hV (show 7*r ≤ z (i+1) by rw [hzsucc]; change 7*r ≤ 10*r; omega)).trans
    exact hiratio
  · have hzlarge : z (3*L+(j+1))=10*R := by rw [show 3*L+(j+1)=(3*L+j)+1 by omega,hzsucc]
    apply (hD (show 5*R ≤ z (3*L+(j+1)) by rw [hzlarge]; omega)).trans
    exact hjratio
  · have hsum : R+r ≤ z (4*L) := by
      apply (show R+r ≤ 10*R by omega).trans
      rw [←hzsucc]
      exact hzmono (by omega)
    calc
      _ ≤ V (z (4*L)) := hV hsum
      _ ≤ K^L*V a := hvend
      _ ≤ K^L*V r := mul_le_mul_of_nonneg_left
        (hV (by simpa only [hz0] using hzmono (show 0 ≤ i by omega))) (by positivity)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
