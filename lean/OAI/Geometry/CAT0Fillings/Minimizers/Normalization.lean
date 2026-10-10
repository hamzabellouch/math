import Mathlib
import OAI.Geometry.CAT0Fillings.Minimizers.Geometric
import OAI.Geometry.CAT0Fillings.Minimizers.Nonnegative

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem extremal_nonnegative_euler {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
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
      criticalNorm q.inclusion (sobolevP (k+2)) v = 1 ∧
      0 < energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v ∧
      energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v <
        (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ)) ∧
      (∀ u, energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v *
        (criticalNorm q.inclusion (sobolevP (k+2)) u)^2 ≤
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) u) ∧
      (∀ ψ : q.Sobolev,
        (4/((k+2:ℝ)-2))*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
          (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v *
          (∫ x, ((q.inclusion v) x)^(sobolevP (k+2)-1)*(q.inclusion ψ) x ∂currentMassMeasure hT.1)) := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hk0 : 0 < (k+2:ℝ)-2 := by linarith
  have hA : 0 < 4/((k+2:ℝ)-2) := div_pos (by norm_num) hk0
  have hB : 0 < (k+2:ℝ) := by positivity
  have hp : 2 < sobolevP (k+2) := by
    dsimp [sobolevP]
    push_cast
    exact (lt_div_iff₀ hk0).mpr (by linarith)
  have hsphere : 0 < sphereArea (k+2) := by
    unfold sphereArea
    exact mul_pos (by positivity) (omega_pos (by omega))
  let S := (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))
  have hS : 0 < S := mul_pos hB (Real.rpow_pos_of_pos hsphere _)
  have hmem : ∀ w : q.Sobolev, MemLp (q.inclusion w)
      (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1) := by
    as_aux_lemma =>
      obtain ⟨C,hC,hb⟩ := extremal_closed_sobolev (k := k) (T := T)
        hk hX hT hz hm q hd hr hfill hext
        (show 0 < S/2 by positivity) (show S/2 < S by linarith)
      exact fun w => (hb w).1
  obtain ⟨u,hu,hus,hmin⟩ := extremal_critical_minimizer (k := k) (T := T)
    hk hX hT hz hm hms q hd hr hfill hext
  as_aux_lemma =>
    exact q.nonnegative_euler_of_minimum (k := k+1) (T := T)
      (A := 4/((k+2:ℝ)-2)) (B := k+2) (p := sobolevP (k+2)) (S := S)
      hA.le hB hp hmem u hu hus hmin

end CAT0Fillings
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma normalized_scalar {p n Λ σ : ℝ} (hp : 2 < p) (hn : 0 < n) (hΛ : 0 < Λ)
    (hσ : 0 < σ) (hsub : Λ < n*σ^((p-2)/p)) :
    let c := (Λ/n)^(1/(p-2))
    0 < c ∧ c*Λ = n*c^(p-1) ∧ c^2*Λ = n*c^p ∧ 0 < c^p ∧ c^p < σ := by
  let c := (Λ/n)^(1/(p-2))
  have hc : 0 < c := Real.rpow_pos_of_pos (div_pos hΛ hn) _
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-2 := by linarith
  have hcp : c^(p-2) = Λ/n := by
    dsimp [c]
    rw [←Real.rpow_mul (div_nonneg hΛ.le hn.le)]
    rw [one_div_mul_cancel hpm.ne',Real.rpow_one]
  have hcpm : c^(p-1) = c^(p-2)*c := by
    calc
      c^(p-1) = c^((p-2)+1) := by congr 1; ring
      _ = c^(p-2)*c^((1:ℝ)) := Real.rpow_add hc _ _
      _ = c^(p-2)*c := by rw [Real.rpow_one]
  have hcpa : c^p = c^(p-2)*c^2 := by
    rw [←Real.rpow_two,←Real.rpow_add hc]
    congr 1
    ring
  have he1 : c*Λ = n*c^(p-1) := by rw [hcpm,hcp]; field_simp
  have he2 : c^2*Λ = n*c^p := by rw [hcpa,hcp]; field_simp
  have hlt : c^(p-2) < σ^((p-2)/p) := by
    rw [hcp]
    exact (div_lt_iff₀ hn).mpr (by simpa only [mul_comm] using hsub)
  have hlt' := Real.rpow_lt_rpow (Real.rpow_nonneg hc.le _) hlt (div_pos hp0 hpm)
  rw [←Real.rpow_mul hc.le,←Real.rpow_mul hσ.le] at hlt'
  have hp1 : (p-2)*(p/(p-2)) = p := by field_simp
  have hp2 : ((p-2)/p)*(p/(p-2)) = 1 := by field_simp
  rw [hp1,hp2,Real.rpow_one] at hlt'
  exact ⟨hc,he1,he2,Real.rpow_pos_of_pos hc _,hlt'⟩

lemma normalize_euler (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    {A p n σ : ℝ} (hp : 2 < p) (hn : 0 < n) (hσ : 0 < σ) (u : H)
    (hu : criticalNorm I p u = 1) (hupos : ∀ᵐ x ∂μ, 0 ≤ (I u) x)
    (hQ : 0 < energy I G A n u) (hsub : energy I G A n u < n*σ^((p-2)/p))
    (heuler : ∀ ψ : H, A*inner ℝ (G u) (G ψ)+n*inner ℝ (I u) (I ψ) =
      energy I G A n u*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ)) :
    ∃ v : H,
      (∀ᵐ x ∂μ, 0 ≤ I v x) ∧ 0 < criticalMass I p v ∧ criticalMass I p v < σ ∧
      energy I G A n v = n*criticalMass I p v ∧
      (∀ ψ : H, A*inner ℝ (G v) (G ψ)+n*inner ℝ (I v) (I ψ) =
        n*(∫ x, (I v x)^(p-1)*(I ψ x) ∂μ)) := by
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
  refine ⟨c • u,?_,by simpa only [hmass] using hcp,by simpa only [hmass] using hcps,?_,?_⟩
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

end CAT0Fillings.AnalyticMinimizer
end

end OAI
