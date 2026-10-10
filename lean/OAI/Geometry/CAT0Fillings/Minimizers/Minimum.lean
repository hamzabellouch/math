import Mathlib
import OAI.Geometry.CAT0Fillings.Minimizers.Normalization

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma sobolevP_ratio {n : ℕ} (hn : 2 < n) : (sobolevP n-2)/sobolevP n = 2/(n:ℝ) := by
  have hn2 : (2:ℝ) < n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn2' : (n:ℝ)-2 ≠ 0 := by linarith
  dsimp [sobolevP]
  field_simp
  ring

theorem extremal_normalized_minimizer {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (hms : mass T < sphereArea (k+2)) (q : ChartGeometry hT.1)
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) :
    ∃ v : q.Sobolev,
      (∀ᵐ x ∂currentMassMeasure hT.1, 0 ≤ (q.inclusion v) x) ∧
      0 < criticalMass q.inclusion (sobolevP (k+2)) v ∧
      criticalMass q.inclusion (sobolevP (k+2)) v < sphereArea (k+2) ∧
      energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v =
        (k+2:ℝ)*criticalMass q.inclusion (sobolevP (k+2)) v ∧
      (∀ ψ : q.Sobolev,
        (4/((k+2:ℝ)-2))*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
          (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
        (k+2:ℝ)*(∫ x, ((q.inclusion v) x)^(sobolevP (k+2)-1)*(q.inclusion ψ) x ∂currentMassMeasure hT.1)) := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hk0 : 0 < (k+2:ℝ)-2 := by linarith
  have hp : 2 < sobolevP (k+2) := by
    dsimp [sobolevP]
    push_cast
    exact (lt_div_iff₀ hk0).mpr (by linarith)
  have hB : 0 < (k+2:ℝ) := by positivity
  obtain ⟨u,hupos,hu,hQ,hsub,hmin,heuler⟩ :=
    extremal_nonnegative_euler hk hX hT hz hm hms q hd hr hfill hext
  apply normalize_euler q.inclusion q.closedGradient hp hB (hm.trans hms) u hu hupos hQ ?_ heuler
  simpa only [sobolevP_ratio (by omega : 2 < k+2),Nat.cast_add,Nat.cast_ofNat] using hsub

end CAT0Fillings
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma normalize_euler_minimum (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    {A p n σ : ℝ} (hp : 2 < p) (hn : 0 < n) (hσ : 0 < σ) (u : H)
    (hu : criticalNorm I p u = 1) (hupos : ∀ᵐ x ∂μ, 0 ≤ (I u) x)
    (hQ : 0 < energy I G A n u) (hsub : energy I G A n u < n*σ^((p-2)/p))
    (hmin : ∀ f : H, energy I G A n u*(criticalNorm I p f)^2 ≤ energy I G A n f)
    (heuler : ∀ ψ : H, A*inner ℝ (G u) (G ψ)+n*inner ℝ (I u) (I ψ) =
      energy I G A n u*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ)) :
    ∃ v : H,
      (∀ᵐ x ∂μ, 0 ≤ I v x) ∧ 0 < criticalMass I p v ∧ criticalMass I p v < σ ∧
      energy I G A n v = n*criticalMass I p v ∧
      (∀ ψ : H, A*inner ℝ (G v) (G ψ)+n*inner ℝ (I v) (I ψ) =
        n*(∫ x, (I v x)^(p-1)*(I ψ x) ∂μ)) ∧
      (∀ f : H, energy I G A n v*(criticalNorm I p f)^2 ≤
        energy I G A n f*(criticalNorm I p v)^2) := by
  let Λ := energy I G A n u
  let c := (Λ/n)^(1/(p-2))
  obtain ⟨hc,he1,he2,hcp,hcps⟩ := normalized_scalar hp hn hQ hσ hsub
  change 0 < c at hc
  change c*Λ = n*c^(p-1) at he1
  change c^2*Λ = n*c^p at he2
  change 0 < c^p at hcp
  change c^p < σ at hcps
  have hmass : criticalMass I p (c • u) = c^p := by
    rw [criticalMass_eq I (by linarith : 0 < p),criticalNorm_smul,hu,mul_one,abs_of_pos hc]
  refine ⟨c • u,?_,by simpa only [hmass] using hcp,by simpa only [hmass] using hcps,?_,?_,?_⟩
  · rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (I u),hupos] with x hx hp
    rw [hx]
    exact mul_nonneg hc.le hp
  · rw [energy_smul,hmass]
    exact he2
  · intro ψ
    have hi : (∫ x, (I (c • u) x)^(p-1)*(I ψ x) ∂μ) =
        c^(p-1)*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ) := by
      rw [←integral_const_mul,map_smul]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c (I u),hupos] with x hx hp
      rw [hx]
      change (c*(I u x))^(p-1)*(I ψ x) = _
      rw [Real.mul_rpow hc.le hp]
      ring
    rw [hi,map_smul,map_smul,real_inner_smul_left,real_inner_smul_left]
    calc
      A*(c*inner ℝ (G u) (G ψ))+n*(c*inner ℝ (I u) (I ψ)) =
          c*(A*inner ℝ (G u) (G ψ)+n*inner ℝ (I u) (I ψ)) := by ring
      _ = c*Λ*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ) := by rw [heuler]; ring
      _ = n*(c^(p-1)*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ)) := by rw [he1]; ring

  · intro f
    rw [energy_smul,criticalNorm_smul,hu,mul_one,abs_of_pos hc]
    have hh := mul_le_mul_of_nonneg_left (hmin f) (sq_nonneg c)
    nlinarith

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem extremal_normalized_minimum {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (hms : mass T < sphereArea (k+2)) (q : ChartGeometry hT.1)
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) :
    ∃ v : q.Sobolev,
      (∀ᵐ x ∂currentMassMeasure hT.1, 0 ≤ (q.inclusion v) x) ∧
      0 < criticalMass q.inclusion (sobolevP (k+2)) v ∧
      criticalMass q.inclusion (sobolevP (k+2)) v < sphereArea (k+2) ∧
      energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v =
        (k+2:ℝ)*criticalMass q.inclusion (sobolevP (k+2)) v ∧
      (∀ ψ : q.Sobolev,
        (4/((k+2:ℝ)-2))*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
          (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
        (k+2:ℝ)*(∫ x, ((q.inclusion v) x)^(sobolevP (k+2)-1)*(q.inclusion ψ) x ∂currentMassMeasure hT.1)) ∧
      (∀ f : q.Sobolev,
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v *
          (criticalNorm q.inclusion (sobolevP (k+2)) f)^2 ≤
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) f *
          (criticalNorm q.inclusion (sobolevP (k+2)) v)^2) := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hk0 : 0 < (k+2:ℝ)-2 := by linarith
  have hp : 2 < sobolevP (k+2) := by
    dsimp [sobolevP]
    push_cast
    exact (lt_div_iff₀ hk0).mpr (by linarith)
  have hB : 0 < (k+2:ℝ) := by positivity
  obtain ⟨u,hupos,hu,hQ,hsub,hmin,heuler⟩ :=
    extremal_nonnegative_euler hk hX hT hz hm hms q hd hr hfill hext
  apply normalize_euler_minimum q.inclusion q.closedGradient hp hB (hm.trans hms) u hu hupos hQ ?_ hmin heuler
  simpa only [sobolevP_ratio (by omega : 2 < k+2),Nat.cast_add,Nat.cast_ofNat] using hsub

end CAT0Fillings
end

end OAI
