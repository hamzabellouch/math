import Mathlib
import OAI.Geometry.CAT0Fillings.Minimizers.Minimum
import OAI.Geometry.CAT0Fillings.Radial.ClosedInequality
import OAI.Geometry.CAT0Fillings.Powers.PolynomialBound
import OAI.Geometry.CAT0Fillings.Euler.Contradiction

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem extremal_euler_powers {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (q : ChartGeometry hT.1)
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B))
    (v : q.Sobolev)
    (hv : ∀ᵐ x ∂currentMassMeasure hT.1, 0 ≤ q.inclusion v x)
    (heuler : ∀ ψ : q.Sobolev,
      (4/((k+2:ℝ)-2))*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+2:ℝ)*(∫ x, ((q.inclusion v) x)^(sobolevP (k+2)-1)*(q.inclusion ψ) x ∂currentMassMeasure hT.1)) :
    (∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (currentMassMeasure hT.1)) ∧
    (∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[currentMassMeasure hT.1] (fun x => (q.inclusion v x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w)) := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hk0 : 0 < (k+2:ℝ)-2 := by linarith
  have hp : 2 < sobolevP (k+2) := by
    dsimp [sobolevP]
    push_cast
    exact (lt_div_iff₀ hk0).mpr (by linarith)
  have hB : 0 < (k+2:ℝ) := by positivity
  have hsphere : 0 < sphereArea (k+2) := by
    unfold sphereArea
    exact mul_pos (by positivity) (omega_pos (by omega))
  let S := (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))
  have hS : 0 < S := mul_pos hB (Real.rpow_pos_of_pos hsphere _)
  obtain ⟨C,hC,hb⟩ := extremal_closed_sobolev hk hX hT hz hm q hd hr hfill hext
    (show 0 < S/2 by positivity) (show S/2 < S by linarith)
  exact q.closed_all_powers hz v hp (div_pos (by norm_num) hk0) hB
    (show 0 < S-S/2 by linarith) hC hv hb heuler

end CAT0Fillings
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
theorem normalized_extremal_contradiction {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (hms : mass T < sphereArea (k+2))
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hnorm : d*r*(mass T)^(r-1) = 1/(k+2:ℝ))
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) : False := by
  obtain ⟨q⟩ := exists_chartGeometry hX hT.1 hT.2.1
  obtain ⟨v,hv,hW,hWs,hE,heuler,hmin⟩ := extremal_normalized_minimum hk hX hT hz hm hms q hd hr hfill hext
  obtain ⟨hmom,hpow⟩ := extremal_euler_powers hk hX hT hz hm q hd hr hfill hext v hv heuler
  let β : ℝ := 1/((k+2:ℝ)-2)
  have hk0 : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have hb : 0 < β := by dsimp [β]; exact div_pos (by norm_num) (by linarith)
  have hnb : (k+2:ℝ)*β = 1+2*β := by dsimp [β]; simp only [add_sub_cancel_right]; field_simp [hk0.ne']
  have hp : sobolevP (k+2) = 2+4*β := by
    dsimp [sobolevP,β]
    push_cast
    simp only [add_sub_cancel_right]
    field_simp [hk0.ne']
    ring
  have ha : 4/((k+2:ℝ)-2) = 4*β := by dsimp [β]; ring
  have hψ : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+2:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂currentMassMeasure hT.1) := by
    intro ψ
    simpa only [hp,ha,show 2+4*β-1 = 1+4*β by ring] using heuler ψ
  have hrad (o : X) (g : X → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g)
      (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
      q.radialVariation o g ≤ (k+2:ℝ)*q.sweptMass o g := by
    have h := radial_inequality_of_extremal hX hT hz q hd.le (by linarith : 0 ≤ r) hm hext o hg hg0 hg1
    rw [hnorm] at h
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ (k+2:ℝ) by positivity)
    simpa only [←mul_assoc,mul_one_div_cancel (show (k+2:ℝ) ≠ 0 by positivity),one_mul] using hh
  apply q.euler_chord_contradiction hX (by omega) hz v hb ?_ hv hmom hpow ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hnb
  · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hψ
  · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hrad
  · rwa [hp] at hW
  · rwa [hp] at hWs
  · simpa only [hp,ha,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hE
  · simpa only [hp,ha,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hmin
end CAT0Fillings
end

end OAI
