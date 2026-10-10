import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Progress
noncomputable section
open scoped BigOperators

variable {n : ℕ}

def drift (T a b ω : ℝ) : ℝ := -24/T*(a-b)*ω

lemma drift_cancel {T a b z w ω : ℝ} (hT : T ≠ 0) :
    T*(z-w)*drift T a b ω+24*(a*z+b*w)*ω = 24*(a*w+b*z)*ω := by
  unfold drift
  field_simp
  ring

lemma drift_abs {T a b ω : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b) (hω : 0 ≤ ω) :
    |drift T a b ω| ≤ 24/T*(a+b)*ω := by
  unfold drift
  rw [abs_mul,abs_mul,abs_div,abs_of_pos hT,abs_of_nonneg hω]
  norm_num only [abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  have hd : |a-b| ≤ a+b := by rw [abs_le]; constructor <;> linarith
  gcongr

lemma drift_size {T a b ω C : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b) (hω : 0 ≤ ω)
    (hs : (a+b)/T ≤ (3/384 : ℝ)) (hC : ω ≤ C) : |drift T a b ω| ≤ C := by
  have h := drift_abs hT ha hb hω
  have hm := mul_le_mul_of_nonneg_right hs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) hω)
  have hC0 : 0 ≤ C := hω.trans hC
  have he : 24/T*(a+b)*ω = (a+b)/T*(24*ω) := by ring
  rw [he] at h
  nlinarith

lemma drift_penalty_bound {T a b ω ψ ψ' k : ℝ}
    (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b) (hω : 0 ≤ ω)
    (hψ : 0 < ψ) (hk : 0 ≤ k) (hp : |ψ'| ≤ ψ*k)
    (hs : T*(a+b) ≤ 2/(384*ψ)) :
    ψ'*drift T a b ω-(1/2 : ℝ)*k*ω/T^2 ≤ -(3/8 : ℝ)*k*ω/T^2 := by
  have h := drift_abs hT ha hb hω
  have h1 : ψ'*drift T a b ω ≤ |ψ'| *(24/T*(a+b)*ω) := by
    calc
      _ ≤ |ψ'*drift T a b ω| := le_abs_self _
      _ = |ψ'| *|drift T a b ω| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have h2 : |ψ'| *(24/T*(a+b)*ω) ≤ (ψ*k)*(24/T*(a+b)*ω) := by
    gcongr
  have hs' : ψ*T*(a+b) ≤ (1/192 : ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 384*ψ)).mp hs
    nlinarith
  have h3 : (ψ*k)*(24/T*(a+b)*ω) ≤ (1/8 : ℝ)*k*ω/T^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
    have he : (ψ*k)*(24/T*(a+b)*ω)*T^2 = 24*(ψ*T*(a+b))*(k*ω) := by
      field_simp
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hs' (mul_nonneg hk hω)
    nlinarith
  calc
    _ ≤ (1/8 : ℝ)*k*ω/T^2-(1/2 : ℝ)*k*ω/T^2 := sub_le_sub_right (h1.trans (h2.trans h3)) _
    _ = _ := by ring

lemma weighted_drift_nonpositive (T a b z w ω : Fin n → ℝ)
    (hT : ∀ i, T i ≠ 0) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hz : ∀ i, 0 ≤ z i) (hw : ∀ i, 0 ≤ w i) (hω : ∀ i, 0 ≤ ω i)
    {H : ℝ} (hH : H ≤ 24*(∑ i,(a i*z i+b i*w i)*ω i)-32*(∑ i,(a i*w i+b i*z i)*ω i)) :
    (∑ i,T i*(z i-w i)*drift (T i) (a i) (b i) (ω i))+H ≤ 0 := by
  have he : (∑ i,T i*(z i-w i)*drift (T i) (a i) (b i) (ω i))+
      24*(∑ i,(a i*z i+b i*w i)*ω i) = 24*(∑ i,(a i*w i+b i*z i)*ω i) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simpa only [mul_assoc] using (drift_cancel (a := a i) (b := b i) (z := z i) (w := w i) (ω := ω i) (hT i))
  have hn : 0 ≤ ∑ i,(a i*w i+b i*z i)*ω i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (add_nonneg (mul_nonneg (ha i) (hw i))
      (mul_nonneg (hb i) (hz i))) (hω i)
  linarith

lemma penalty_drift_quantitative (T a b ω ψ ψ' k : Fin n → ℝ)
    (hT : ∀ i, 0 < T i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hω : ∀ i, 0 ≤ ω i) (hψ : ∀ i, 0 < ψ i) (hk : ∀ i, 0 ≤ k i)
    (hp : ∀ i, |ψ' i| ≤ ψ i*k i) (hs : ∀ i, T i*(a i+b i) ≤ 2/(384*ψ i))
    (hlower : ∀ i, (1/3 : ℝ) ≤ k i/T i^2) :
    (∑ i,(ψ' i*drift (T i) (a i) (b i) (ω i)-(1/2 : ℝ)*k i*ω i/T i^2)) ≤
      -(1/8 : ℝ)*(∑ i,ω i) := by
  calc
    _ ≤ ∑ i,-(3/8 : ℝ)*k i*ω i/T i^2 := Finset.sum_le_sum fun i _ =>
      drift_penalty_bound (hT i) (ha i) (hb i) (hω i) (hψ i) (hk i) (hp i) (hs i)
    _ ≤ ∑ i,-(1/8 : ℝ)*ω i := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_right (hlower i) (hω i)
      have he : -(3/8 : ℝ)*k i*ω i/T i^2 = -(3/8 : ℝ)*((k i/T i^2)*ω i) := by ring
      rw [he]
      nlinarith
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma combine_progress {lam n C R P : ℝ} (hlam : 0 ≤ lam) (hC : 0 < C)
    (hR : R ≤ 0) (hP : P ≤ -n/(8*C)) : R+lam*P ≤ -lam*n/(8*C) := by
  have hDenom : 0 < 8 * C := by positivity
  apply (le_div_iff₀ hDenom).mpr
  have hProgress := mul_le_mul_of_nonneg_left ((le_div_iff₀ hDenom).mp hP) hlam
  have hRemainder := mul_nonpos_of_nonpos_of_nonneg hR hDenom.le
  nlinarith

end
end CurrentKS.Progress

end OAI
