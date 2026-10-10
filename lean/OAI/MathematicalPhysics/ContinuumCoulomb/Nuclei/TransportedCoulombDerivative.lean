import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombFarCell
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! Fourth derivatives of the Coulomb integrand after the Moser map. The
estimate is local at a point and needs no regularity across the pole. -/

noncomputable section
namespace ContinuumCoulomb

theorem fourth_composite_norm_bound (f : Position → ℝ) (G : Position → Position) (x : Position)
    (hf : ContDiffAt ℝ 4 f (G x)) (hG : ContDiff ℝ 4 G) {C D : ℝ}
    (hC : ∀ k : ℕ, k ≤ 4 → ‖iteratedFDeriv ℝ k f (G x)‖ ≤ C)
    (hD : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) :
    ‖iteratedFDeriv ℝ 4 (f ∘ G) x‖ ≤ 24*C*D^4 := by
  obtain ⟨U,hU,hx,hfU⟩ := hf.contDiffOn' le_rfl (by norm_num)
  have hfU : ContDiffOn ℝ 4 f U := by simpa using hfU
  have hS : IsOpen (G ⁻¹' U) := hU.preimage hG.continuous
  have hc := norm_iteratedFDerivWithin_comp_le hfU hG.contDiffOn (n := 4) le_rfl
    hU.uniqueDiffOn hS.uniqueDiffOn (fun _ hy => hy) hx
    (fun k hk => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn (hf.of_le (by exact_mod_cast hk)) hx]
      exact hC k hk)
    (fun k hk hk' => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv (f := G) (x := x) (s := G ⁻¹' U) hS.uniqueDiffOn
        (hG.of_le (by exact_mod_cast hk')).contDiffAt hx]
      exact hD k hk hk')
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (f := f ∘ G) (x := x) (s := G ⁻¹' U) hS.uniqueDiffOn (hf.comp x hG.contDiffAt) hx] at hc
  norm_num only [Nat.factorial] at hc
  exact hc

theorem coulomb_kernel_jets_near_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (z : Position) (r : ℝ), 0 < r → r ≤ 1 → r ≤ ‖z‖ →
      ∀ k : ℕ, k ≤ 4 → ‖iteratedFDeriv ℝ k Coulomb.coulombKernel z‖ ≤ C/r^5 := by
  obtain ⟨C,hC,hbound⟩ := coulombKernel_derivative_decay
  refine ⟨C,hC,fun z r hr hr1 hz k hk => ?_⟩
  have hzne : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hz)
  have hb := hbound ⟨k,by omega⟩ z hzne
  apply (le_div_iff₀ (pow_pos hr 5)).mpr
  have hp : r^5 ≤ ‖z‖^(k+1) := by
    calc
      _ ≤ r^(k+1) := pow_le_pow_of_le_one hr.le hr1 (by omega)
      _ ≤ _ := pow_le_pow_left₀ hr.le hz _
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans hb

theorem transportedCoulomb_fourth_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (y x : Position) (r D : ℝ), 0 < r → r ≤ 1 → r ≤ ‖y-G x‖ →
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ‖iteratedFDeriv ℝ 4 (fun b => Coulomb.coulombKernel (y-G b)) x‖ ≤ 24*C*D^4/r^5 := by
  obtain ⟨C,hC,hbound⟩ := coulomb_kernel_jets_near_bound
  refine ⟨C,hC,fun G hG y x r D hr hr1 hdist hD => ?_⟩
  have hne : y-G x ≠ 0 := norm_pos_iff.mp (hr.trans_le hdist)
  have hf : ContDiffAt ℝ 4 (fun z => Coulomb.coulombKernel (y-z)) (G x) :=
    ((coulombKernel_contDiffAt hne).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)).comp (G x) (contDiffAt_const.sub contDiffAt_id)
  have hb := fourth_composite_norm_bound (fun z => Coulomb.coulombKernel (y-z)) G x hf hG
    (fun k hk => by rw [translatedCoulomb_derivative_norm]; exact hbound _ r hr hr1 hdist k hk) hD
  apply hb.trans_eq
  ring

theorem transportedCoulomb_cell_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (y b : Position) (h r D : ℝ), 0 ≤ h → 0 < r → r ≤ 1 →
      (∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ v ∈ Set.Icc (-1:ℝ) 1,
        ∀ z ∈ Set.Icc (-1:ℝ) 1, r ≤ ‖y-G (cubePoint b (h/2) x v z)‖) →
      (∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ v ∈ Set.Icc (-1:ℝ) 1,
        ∀ z ∈ Set.Icc (-1:ℝ) 1, ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
        ‖iteratedFDeriv ℝ k G (cubePoint b (h/2) x v z)‖ ≤ D^k) →
      |positionCellGauss b h (fun a => Coulomb.coulombKernel (y-G a))-
        positionCellIntegral b h (fun a => Coulomb.coulombKernel (y-G a))| ≤
        24*C*D^4*h^7/r^5 := by
  obtain ⟨C,hC,hbound⟩ := transportedCoulomb_fourth_bound
  refine ⟨C,hC,fun G hG y b h r D hh hr hr1 hdist hD => ?_⟩
  have hf (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (v : ℝ) (hv : v ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ContDiffAt ℝ 4 (fun a => Coulomb.coulombKernel (y-G a)) (cubePoint b (h/2) x v z) := by
    have hn : y-G (cubePoint b (h/2) x v z) ≠ 0 :=
      norm_pos_iff.mp (hr.trans_le (hdist x hx v hv z hz))
    have hi : ContDiffAt ℝ 4 (fun a => y-G a) (cubePoint b (h/2) x v z) :=
      contDiffAt_const.sub hG.contDiffAt
    exact ContDiffAt.comp (g := Coulomb.coulombKernel) (f := fun a : Position => y-G a)
      (cubePoint b (h/2) x v z) ((coulombKernel_contDiffAt hn).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)) hi
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have he := positionCellGauss_error_local (fun a => Coulomb.coulombKernel (y-G a)) b hh
    (by positivity : 0 ≤ 24*C*D^4/r^5) hf
    (fun x hx v hv z hz => hbound G hG y _ r D hr hr1 (hdist x hx v hv z hz) (hD x hx v hv z hz))
  apply he.trans_eq
  ring

end ContinuumCoulomb

end

end OAI
