import Mathlib
import OAI.Geometry.CAT0Fillings.Minimizers.CriticalEnergy

namespace OAI

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma critical_no_loss (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    {A B p S Λ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 2 < p)
    (hΛ : 0 ≤ Λ) (hΛS : Λ < S)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ)
    (hmin : ∀ u, Λ*(criticalNorm I p u)^2 ≤ energy I G A B u)
    (hsob : ∀ ε : ℝ, 0 < ε → ε < S → ∃ C ≥ (0:ℝ), ∀ u,
      (S-ε)*(criticalNorm I p u)^2 ≤ A*‖G u‖^2+C*‖I u‖^2)
    {u : ℕ → H} {v : H}
    (hu : ∀ j, criticalNorm I p (u j) = 1)
    (hQ : Tendsto (fun j => energy I G A B (u j)) atTop (𝓝 Λ))
    (hweak : ∀ w, Tendsto (fun j => inner ℝ (u j) w) atTop (𝓝 (inner ℝ v w)))
    (hstrong : Tendsto (fun j => I (u j)) atTop (𝓝 (I v)))
    (hae : ∀ᵐ x ∂μ, Tendsto (fun j => (I (u j)) x) atTop (𝓝 ((I v) x))) :
    criticalNorm I p v = 1 ∧ energy I G A B v = Λ := by
  have hp0 : 0 < p := by linarith
  have ha : 0 < 2/p := div_pos (by norm_num) hp0
  have ha1 : 2/p ≤ 1 := (div_le_one hp0).mpr hp.le
  have hS : 0 < S := hΛ.trans_lt hΛS
  have hmass := criticalMass_defect I (by linarith : 1 ≤ p) hm hu hae
  have ht := criticalMass_nonneg I p v
  have ht1 : criticalMass I p v ≤ 1 := by
    have hh := ge_of_tendsto' hmass (fun j => criticalMass_nonneg I p (u j-v))
    linarith
  have hdef := energy_defect I G A B hweak hQ
  have hIz : Tendsto (fun j => ‖I (u j-v)‖^2) atTop (𝓝 0) := by
    have hh := ((hstrong.sub_const (I v)).norm).pow 2
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),map_sub] using hh
  have hib (ε : ℝ) (hε : 0 < ε) (hεS : ε < S) :
      (S-ε)*(1-criticalMass I p v)^(2/p) ≤ Λ-energy I G A B v := by
    obtain ⟨C,hC,hb⟩ := hsob ε hε hεS
    have hl := (hmass.rpow_const (Or.inr ha.le)).const_mul (S-ε)
    have hr := hdef.add (hIz.const_mul C)
    simp only [mul_zero,add_zero] at hr
    apply le_of_tendsto_of_tendsto' hl hr
    intro j
    have hh := hb (u j-v)
    rw [criticalNorm_sq I hp0] at hh
    exact hh.trans (by dsimp [energy]; nlinarith [mul_nonneg hB (sq_nonneg ‖I (u j-v)‖)])
  have hlow := hmin v
  rw [criticalNorm_sq I hp0] at hlow
  have hcc := concentration_inequality ha ht ht1 hS hlow hib
  have hmass1 := no_loss ha1 hΛ hΛS ht ht1 hcc
  have hn2 := criticalNorm_sq I hp0 v
  rw [hmass1,Real.one_rpow] at hn2
  have hn1 : criticalNorm I p v = 1 := by
    nlinarith [criticalNorm_nonneg I p v]
  refine ⟨hn1,le_antisymm (energy_le_limit I G hA hB hweak hQ) ?_⟩
  have hh := hmin v
  simpa only [hn1,one_pow,mul_one] using hh

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {H : Type*} [AddCommGroup H] [Module ℝ H]

lemma normalized_infimum (N Q : H → ℝ)
    (hN : ∀ u, 0 ≤ N u) (hQ : ∀ u, 0 ≤ Q u)
    (hNs : ∀ c u, N (c • u) = |c| *N u)
    (hQs : ∀ c u, Q (c • u) = c^2*Q u)
    (v : H) (hv : 0 < N v) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ Λ ≤ Q v/(N v)^2 ∧
      (∀ u, Λ*(N u)^2 ≤ Q u) ∧
      ∃ u : ℕ → H, (∀ j, N (u j) = 1) ∧
        (∀ j, Q (u j) ≤ Q (u 0)) ∧ Tendsto (fun j => Q (u j)) atTop (𝓝 Λ) := by
  classical
  let C : Set ℝ := {q | ∃ u, N u = 1 ∧ Q u = q}
  have hunit {u : H} (hu : 0 < N u) : N ((N u)⁻¹ • u) = 1 := by
    rw [hNs,abs_of_pos (inv_pos.mpr hu),inv_mul_cancel₀ hu.ne']
  have hC : C.Nonempty := ⟨Q ((N v)⁻¹ • v),_,hunit hv,rfl⟩
  have hCb : BddBelow C := ⟨0,by rintro q ⟨u,hu,rfl⟩; exact hQ u⟩
  let Λ := sInf C
  have hΛ : 0 ≤ Λ := le_csInf hC (by rintro q ⟨u,hu,rfl⟩; exact hQ u)
  have hmin (u : H) : Λ*(N u)^2 ≤ Q u := by
    by_cases hu : N u = 0
    · simp only [hu,zero_pow (by decide : 2 ≠ 0),mul_zero]
      exact hQ u
    have hu' : 0 < N u := lt_of_le_of_ne (hN u) (Ne.symm hu)
    have hh : Λ ≤ Q ((N u)⁻¹ • u) := csInf_le hCb ⟨_,hunit hu',rfl⟩
    rw [hQs,inv_pow] at hh
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg (N u))
    calc
      Λ*(N u)^2 ≤ ((N u)^2)⁻¹*Q u*(N u)^2 := hh'
      _ = Q u := by rw [mul_assoc,mul_comm (Q u),←mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hu),one_mul]
  have hvb : Λ ≤ Q v/(N v)^2 := (le_div_iff₀ (sq_pos_of_pos hv)).mpr (hmin v)
  obtain ⟨a,haanti,halim,ha⟩ := exists_seq_tendsto_sInf hC hCb
  choose u huN huQ using ha
  refine ⟨Λ,hΛ,hvb,hmin,u,huN,fun j => ?_,?_⟩
  · simpa only [huQ] using haanti (show 0 ≤ j from Nat.zero_le j)
  · simpa only [huQ] using halim

end CAT0Fillings.AnalyticMinimizer
end

end OAI
