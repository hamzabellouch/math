import OAI.NumberTheory.CubicMoment.Estimates.WideGramDecay

namespace OAI

/-! Finite seminorm control of the actual radial composition operator.
The constant is chosen before the test profile, as required for shrinking cells. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

theorem schwartz_wideGramExp_comp_seminorm (M : ℝ) (hM : 0 ≤ M) (n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : 𝓢(ℂ, ℂ)) (c : ℝ), 0 ≤ c → ∀ u : ℝ, |u| ≤ 2*M →
      (1+c)^K * ‖iteratedFDeriv ℝ n (fun v => F (c • gramExp v)) u‖ ≤
        C*((Finset.Iic (n+K,n)).sup
          (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) F := by
  obtain ⟨D, hD, hderiv⟩ := wideGramExp_deriv_bound M n
  refine ⟨(n.factorial:ℝ)*(Real.exp M)^(n+K)*2^(n+K)*D^n,by positivity,?_⟩
  intro F c hc u hu
  let L := n+K
  let S := (Finset.Iic (L,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  let H := (Real.exp M)^L * 2^L * S
  have hS : 0 ≤ S := by positivity
  have hH : 0 ≤ H := by positivity
  have hc1 : 0 < 1+c := by positivity
  have hC (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ ≤ H / (1+c)^L := by
    rw [le_div_iff₀' (pow_pos hc1 L)]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (L,n)) (k := L) (n := i) (le_refl L) hi F (c • gramExp u)
    calc
      _ ≤ (Real.exp M * (1+‖c • gramExp u‖))^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ := by
        gcongr
        exact wideGramExp_scale_growth hM hc hu
      _ = (Real.exp M)^L * ((1+‖c • gramExp u‖)^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖) := by rw [mul_pow]; ring
      _ ≤ (Real.exp M)^L * (2^L*S) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = H := by dsimp [H]; ring
  have hDb (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun v => c • gramExp v) u‖ ≤ ((1+c)*D)^i := by
    rw [iteratedFDeriv_const_smul_apply' (gramExp_contDiff.of_le (mod_cast le_top)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      _ ≤ c*D := mul_le_mul_of_nonneg_left (hderiv i hin u hu) hc
      _ ≤ (1+c)*D := by nlinarith
      _ ≤ ((1+c)*D)^i := le_self_pow₀ (by nlinarith) (by omega)
  have hb := norm_iteratedFDeriv_comp_le (F.smooth ⊤) (gramExp_contDiff.const_smul c)
    (n := n) (mod_cast le_top) u hC hDb
  calc
    _ ≤ (1+c)^K * ((n.factorial : ℝ)*(H/(1+c)^L)*((1+c)*D)^n) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (n.factorial : ℝ)*H*D^n := by
      dsimp [L]
      rw [pow_add, mul_pow]
      field_simp

    _ = _ := by dsimp [H,S,L]; ring

theorem wideAnnularLogSchwartz_seminorm_control (M : ℝ) (hM : 0 < M) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : 𝓢(ℂ, ℂ)) (c : ℝ), 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (wideAnnularLogSchwartz M hM F c) ≤
        C*((Finset.Iic (n+K,n)).sup
          (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) F := by
  choose C hC hraw using fun i => schwartz_wideGramExp_comp_seminorm M hM.le i K
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) * C (n-i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hC (n-i)).le)
  refine ⟨(2*M)^k*B+1,by positivity,?_⟩
  intro F c hc
  let S := ((Finset.Iic (n+K,n)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hS : 0 ≤ S := by positivity
  have hbound (i : ℕ) (hi : i ≤ n) (u : ℝ) (hu : |u| ≤ 2*M) :
      (1+c)^K*‖iteratedFDeriv ℝ i (fun v => F (c • gramExp v)) u‖ ≤ C i*S := by
    apply (hraw i F c hc u hu).trans
    apply mul_le_mul_of_nonneg_left _ (hC i).le
    have hsub : Finset.Iic (i+K,i) ⊆ Finset.Iic (n+K,n) := by
      intro p hp
      exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp)
        ⟨Nat.add_le_add_right hi K,hi⟩)
    exact Seminorm.le_def.mp (show
      ((Finset.Iic (i+K,i)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) ≤
      (Finset.Iic (n+K,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) from
        Finset.sup_mono hsub) F
  have hfinal : (1+c)^K*SchwartzMap.seminorm ℝ k n (wideAnnularLogSchwartz M hM F c) ≤
      (2*M)^k*B*S := by
    have hp : 0 < (1+c)^K := pow_pos (by positivity) _
    rw [← le_div_iff₀' hp]
    apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
    intro u
    by_cases hu : |u| ≤ 2*M
    · rw [le_div_iff₀' hp]
      have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (wideGramLogBump M hM).contDiff
        ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)) u (n := n) (mod_cast le_top)
      have hd' : (1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖ ≤ B*S := by
        calc
          _ ≤ (1+c)^K * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
                ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖ :=
            mul_le_mul_of_nonneg_left hd hp.le
          _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
                ((1+c)^K * ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ ≤ B*S := by
            rw [show B*S = ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*
            SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM)*C (n-i)*S by
              dsimp [B]; rw [Finset.sum_mul]]
            apply Finset.sum_le_sum
            intro i hi
            have hb : ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ ≤
                SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) := by
              have hb := SchwartzMap.le_seminorm ℝ 0 i (wideGramBumpSchwartz M hM) u
              rw [show (wideGramBumpSchwartz M hM : ℝ → ℝ) = ((wideGramLogBump M hM) : ℝ → ℝ) from rfl] at hb
              simpa only [pow_zero, one_mul] using hb
            simpa only [mul_assoc] using mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity))
              (hbound (n-i) (Nat.sub_le _ _) u hu) (by positivity) (by positivity)
      calc
        _ = ‖u‖^k * ((1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖) := by ring
        _ ≤ (2*M)^k * (B*S) := mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _)
          (by simpa only [Real.norm_eq_abs] using hu) k) hd' (by positivity) (by positivity)
        _ = _ := by ring
    · rw [wideAnnularLogSchwartz_deriv_zero M hM F c u n hu, norm_zero, mul_zero]
      positivity
  exact hfinal.trans (mul_le_mul_of_nonneg_right (by linarith) hS)

end CubicFirstMoment

end

end OAI
