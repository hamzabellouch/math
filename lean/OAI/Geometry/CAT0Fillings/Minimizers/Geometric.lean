import Mathlib
import OAI.Geometry.CAT0Fillings.Sobolev.Compact
import OAI.Geometry.CAT0Fillings.Sobolev.Constant
import OAI.Geometry.CAT0Fillings.Minimizers.NoLoss

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [IsFiniteMeasure μ] in
theorem exists_critical_minimizer [IsFiniteMeasure μ] (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    (hI : IsCompactOperator I) (hgraph : ∀ u, ‖u‖^2 = ‖I u‖^2+‖G u‖^2)
    {A B p S : ℝ} (hA : 0 < A) (hB : 0 < B) (hp : 2 < p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ)
    (hsob : ∀ ε : ℝ, 0 < ε → ε < S → ∃ C ≥ (0:ℝ), ∀ u,
      (S-ε)*(criticalNorm I p u)^2 ≤ A*‖G u‖^2+C*‖I u‖^2)
    (w : H) (hw : 0 < criticalNorm I p w)
    (hwS : energy I G A B w/(criticalNorm I p w)^2 < S) :
    ∃ v : H, criticalNorm I p v = 1 ∧ energy I G A B v < S ∧
      ∀ u, energy I G A B v*(criticalNorm I p u)^2 ≤ energy I G A B u := by
  obtain ⟨Λ,hΛ,hΛw,hmin,u,hu,hub,hQ⟩ := normalized_infimum (criticalNorm I p) (energy I G A B)
    (criticalNorm_nonneg I p) (energy_nonneg I G hA.le hB.le)
    (criticalNorm_smul I p) (energy_smul I G A B) w hw
  have hΛS : Λ < S := hΛw.trans_lt hwS
  let c := min A B
  have hc : 0 < c := lt_min hA hB
  have hcoerce (u : H) : c*‖u‖^2 ≤ energy I G A B u := by
    rw [hgraph]
    dsimp [energy]
    have h1 := mul_le_mul_of_nonneg_right (min_le_left A B) (sq_nonneg ‖G u‖)
    have h2 := mul_le_mul_of_nonneg_right (min_le_right A B) (sq_nonneg ‖I u‖)
    dsimp [c]
    nlinarith
  let M := Real.sqrt (energy I G A B (u 0)/c)
  have hM (j : ℕ) : ‖u j‖ ≤ M := by
    apply (Real.le_sqrt (norm_nonneg _) (div_nonneg (energy_nonneg I G hA.le hB.le _) hc.le)).mpr
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using (hcoerce (u j)).trans (hub j)
  obtain ⟨v,hv,s,hs,hweak,hstrong⟩ := exists_weak_strong_subsequence I hI u M hM
  obtain ⟨t,ht,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hstrong).exists_seq_tendsto_ae
  have hQ' := hQ.comp (hs.comp ht).tendsto_atTop
  have hw' (z : H) := (hweak z).comp ht.tendsto_atTop
  have hs' := hstrong.comp ht.tendsto_atTop
  obtain ⟨hNv,hQv⟩ := critical_no_loss I G hA.le hB.le hp hΛ hΛS hm hmin hsob
    (u := fun j => u (s (t j))) (fun j => hu (s (t j))) hQ' hw' hs' hae
  exact ⟨v,hNv,hQv ▸ hΛS,fun u => hQv ▸ hmin u⟩

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma constant_subthreshold {n : ℕ} (hn : 2 < n) {m : ℝ}
    (hm : 0 < m) (hms : m < sphereArea n) :
    (n:ℝ)*m/(m^(1/sobolevP n))^2 < (n:ℝ)*sphereArea n^(2/(n:ℝ)) := by
  have hn2 : (2:ℝ) < n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have he : 1-((1/sobolevP n)*2) = 2/(n:ℝ) := by
    dsimp [sobolevP]
    field_simp
    ring
  have heq : (n:ℝ)*m/(m^(1/sobolevP n))^2 = (n:ℝ)*m^(2/(n:ℝ)) := by
    rw [←Real.rpow_mul_natCast hm.le]
    rw [mul_div_assoc]
    conv_lhs => arg 2; arg 1; rw [←Real.rpow_one m]
    rw [←Real.rpow_sub hm]
    norm_num only [Nat.cast_ofNat]
    rw [he]
  rw [heq]
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hm.le hms (div_pos (by norm_num) hn0)) hn0

theorem extremal_critical_minimizer {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (hms : mass T < sphereArea (k+2)) (q : ChartGeometry hT.1)
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) :
    ∃ v : q.Sobolev,
      criticalNorm q.inclusion (sobolevP (k+2)) v = 1 ∧
      energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v <
        (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ)) ∧
      ∀ u, energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v *
        (criticalNorm q.inclusion (sobolevP (k+2)) u)^2 ≤
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) u := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hk0 : 0 < (k+2:ℝ)-2 := by linarith
  have hA : 0 < 4/((k+2:ℝ)-2) := div_pos (by norm_num) hk0
  have hB : 0 < (k+2:ℝ) := by positivity
  have hp : 2 < sobolevP (k+2) := by
    dsimp [sobolevP]
    push_cast
    exact (lt_div_iff₀ hk0).mpr (by linarith)
  let S := (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))
  have hsphere : 0 < sphereArea (k+2) := by
    unfold sphereArea
    exact mul_pos (by positivity) (omega_pos (by omega))
  have hS : 0 < S := mul_pos hB (Real.rpow_pos_of_pos hsphere _)
  obtain ⟨C,hC,hb⟩ := extremal_almost_sobolev hk hX hT hz hm q hd hr hfill hext
    (show 0 < S/2 by positivity) (show S/2 < S by linarith)
  have hcompact := q.inclusion_compact (Slicing.normalApprox_of_integral hT) hz hX hp
    (show 0 < S-S/2 by linarith) hA.le hC hb
  obtain ⟨D,hD,hclosed⟩ := extremal_closed_sobolev hk hX hT hz hm q hd hr hfill hext
    (show 0 < S/2 by positivity) (show S/2 < S by linarith)
  refine exists_critical_minimizer q.inclusion q.closedGradient hcompact q.sobolev_norm_sq
    hA hB hp (fun u => (hclosed u).1) ?_ (q.constant 1) ?_ ?_
  · intro ε hε hεS
    obtain ⟨C,hC,hb⟩ := extremal_closed_sobolev hk hX hT hz hm q hd hr hfill hext hε hεS
    exact ⟨C,hC,fun u => (hb u).2⟩
  · rw [q.criticalNorm_constant (by linarith : 0 < sobolevP (k+2))]
    simpa only [abs_one,one_mul] using Real.rpow_pos_of_pos hm (1/sobolevP (k+2))
  · rw [q.criticalNorm_constant (by linarith : 0 < sobolevP (k+2))]
    dsimp [energy]
    rw [q.closedGradient_constant,q.norm_inclusion_constant_sq]
    simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add,
      one_pow,one_mul,abs_one]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using constant_subthreshold (by omega : 2 < k+2) hm hms

end CAT0Fillings
end

end OAI
