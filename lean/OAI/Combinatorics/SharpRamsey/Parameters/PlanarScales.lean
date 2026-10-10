import Mathlib
import OAI.Combinatorics.SharpRamsey.Planar.PlanarBudget

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales
open scoped Topology
noncomputable section

lemma even_order {σ P : ℝ} (hσ : 0<σ) (hP : 0<P) :
    ∃ p : ℕ,0<p ∧ Even p ∧ 10000*σ≤(p:ℝ)*P ∧ (p:ℝ)≤10000*σ/P+2 := by
  let p := 2*⌈5000*σ/P⌉₊
  have hn : 0≤5000*σ/P := by positivity
  have hl := Nat.le_ceil (5000*σ/P)
  have hu := Nat.ceil_lt_add_one hn
  have hp : (p:ℝ)=2*(⌈5000*σ/P⌉₊:ℝ) := by simp only [p,Nat.cast_mul,Nat.cast_ofNat]
  have hlo : 10000*σ≤(p:ℝ)*P := by
    have hh := mul_le_mul_of_nonneg_right hl hP.le
    have he : (5000*σ/P)*P=5000*σ := div_mul_cancel₀ _ hP.ne'
    rw [he] at hh
    rw [hp]
    nlinarith only [hh]
  refine ⟨p,?_,by dsimp [p]; exact even_two_mul _,hlo,?_⟩
  · have hpos : (0:ℝ)<p := by nlinarith only [hlo,hσ,hP]
    exact_mod_cast hpos
  · rw [hp]
    calc
      _ ≤ 2*(5000*σ/P+1) := (mul_lt_mul_of_pos_left hu (by norm_num : (0:ℝ)<2)).le
      _ = _ := by ring

lemma eventually_schedule {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      (R:ℝ)*exp (-(24/25:ℝ)*scaleL σ η D)≤1/10 := by
  have hh := ScaleSelection.eventually_polynomial_le_exp_rpow 40 (beta η) (9*beta η) (24/25)
    (by have := beta_pos hη; positivity) (by norm_num)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with σ hs hσ D R had
  have hR := R_bound hσ hη had
  have hL := (scale_bounds hσ hη had).1
  have he : 10*(R:ℝ)≤exp ((24/25:ℝ)*scaleL σ η D) := by
    calc
      _ ≤ 40*σ^beta η := by linarith
      _ ≤ exp ((24/25:ℝ)*σ^(9*beta η)) := hs
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right he (exp_pos (-(24/25:ℝ)*scaleL σ η D)).le
  have heq : exp ((24/25:ℝ)*scaleL σ η D)*exp (-(24/25:ℝ)*scaleL σ η D)=1 := by
    rw [←exp_add]; ring_nf; exact exp_zero
  rw [heq] at hm
  linarith

theorem eventually_budget {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      ∃ p h : ℕ,Budget σ (scaleP σ η D R) (Real.toNNReal (scaleL σ η D)) R p h := by
  filter_upwards [eventually_enumeration_budgets hη,
    eventually_pencil_scalar_budgets hη 400000,eventually_P_le_linear hη (1/12) (by norm_num),
    eventually_uniform_L hη (eventually_ge_atTop (100000000000000:ℝ)),
    eventually_uniform_R hη 400,eventually_schedule hη,eventually_ge_atTop (2:ℝ)]
    with σ he hp hu hl hr hs hσ D R had
  let L := scaleL σ η D
  let P := scaleP σ η D R
  have hL : 100000000000000≤L := hl D R had
  have hR : (400:ℝ)≤R := hr D R had
  have hL0 : 0≤L := by linarith
  have hLP : L≤P := by change L≤L*R; nlinarith
  have hP0 : 0<P := by linarith
  obtain ⟨p,hp0,hpe,hpl,hpu⟩ := even_order (by linarith : 0<σ) hP0
  obtain ⟨hLa,hcert,hshift,hpb,hps,h,hh,hR',hhs,hhr⟩ := he D R p 0 had hpu (by simpa only [Nat.cast_zero] using sq_nonneg σ)
  obtain ⟨hdiag,hpow,hsum,htwo,hvar⟩ := hp D R 0 had (by simpa only [Nat.cast_zero] using sq_nonneg σ)
  have hlu : (Real.toNNReal L:ℝ)=L := Real.coe_toNNReal _ hL0
  have hPu : P≤σ/12 := by simpa only [div_eq_mul_inv,mul_comm,one_mul] using hu D R had
  have hB : 2*exp (6*P)≤exp σ := by
    have h2 : 2≤exp (σ-6*P) := by have := add_one_le_exp (σ-6*P); linarith
    calc
      _ ≤ exp (σ-6*P)*exp (6*P) := mul_le_mul_of_nonneg_right h2 (exp_pos _).le
      _ = _ := by rw [←exp_add]; congr 1; ring
  change ∃ p h : ℕ,Budget σ P (Real.toNNReal L) R p h
  refine ⟨p,h,?_⟩
  constructor
  · exact hσ
  · exact hL.trans hLP
  · linarith
  · exact hB
  · rw [hlu]; rfl
  · rw [hlu]; linarith
  · exact hR'
  · exact hp0
  · exact hpe
  · exact hpl
  · simpa only [hlu] using hs D R had
  · exact hdiag
  · simpa only [hlu] using hpow
  · simpa only [hlu,Nat.cast_zero,zero_mul,add_zero] using hsum
  · exact htwo
  · simpa only [hlu] using hvar
  · exact hcert
  · exact hshift
  · exact hpb
  · exact hps
  · exact hh
  · exact hhs
  · exact hhr

end
end SharpLogRamsey.PlanarLearning

end

end OAI
