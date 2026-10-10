import Mathlib
import OAI.Analysis.Conductivity.Walls.WallHomogeneous

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

lemma wallParticularNumerator_derivative (d : E) {v r₁ r₂ : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂) (p : E × ℝ) :
    wallDerivative (wallParticularNumerator d v r₁ r₂) p=
      r₂ p-wallAlong d (wallPrimitive r₁) p*wallDerivative v p-
      2*wallPrimitive r₁ p*wallAlong d (wallDerivative v) p-r₁ p*wallAlong d v p := by
  have hA := wallPrimitive_smooth h₁
  have hG := wallParticularNumerator_smooth d hv h₁ h₂
  have hh := (wall_particular_flux_equations d hv h₁ h₂ p).2
  rw [wallAlong_mul d (hA.differentiable (by simp))
      ((wallDerivative_smooth hv).differentiable (by simp)),
    wallDerivative_add ((hA.mul (wallAlong_smooth d hv)).differentiable (by simp))
      (hG.differentiable (by simp)),
    wallDerivative_mul (hA.differentiable (by simp))
      ((wallAlong_smooth d hv).differentiable (by simp)),
    wallDerivative_primitive h₁,wall_mixed_commute d hv] at hh
  linarith

lemma wall_segment_mul {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    u*t∈Icc (0:ℝ) 1 := ⟨mul_nonneg hu.1 ht.1,by
    calc u*t ≤ 1*t := mul_le_mul_of_nonneg_right hu.2 ht.1
         _ ≤ 1 := by simpa only [one_mul] using ht.2⟩

lemma wallParticularNumerator_derivative_bound (d : E) {v r₁ r₂ : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂) {p : E × ℝ} {ε M δ : ℝ}
    (hε : 0≤ε) (hM : 0≤M) (hδ : |p.2|≤δ)
    (hr₁ : ∀ t∈Icc (0:ℝ) 1, |r₁ (p.1,t*p.2)|≤ε)
    (hr₂ : ∀ t∈Icc (0:ℝ) 1, |r₂ (p.1,t*p.2)|≤ε)
    (hder : ∀ t∈Icc (0:ℝ) 1, |wallAlong d r₁ (p.1,t*p.2)|≤ε)
    (hvz : ∀ t∈Icc (0:ℝ) 1, |wallDerivative v (p.1,t*p.2)|≤M)
    (hvs : ∀ t∈Icc (0:ℝ) 1, |wallAlong d v (p.1,t*p.2)|≤M)
    (hvsz : ∀ t∈Icc (0:ℝ) 1, |wallAlong d (wallDerivative v) (p.1,t*p.2)|≤M) :
    ∀ t∈Icc (0:ℝ) 1, |wallDerivative (wallParticularNumerator d v r₁ r₂) (p.1,t*p.2)|
      ≤ε*(1+M+3*δ*M) := by
  intro t ht
  have hδ0 : 0≤δ := (abs_nonneg _).trans hδ
  have htδ : |t*p.2|≤δ := by
    rw [abs_mul,abs_of_nonneg ht.1]
    calc t*|p.2|≤1*|p.2| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
         _ ≤δ := by simpa only [one_mul] using hδ
  have hA : |wallPrimitive r₁ (p.1,t*p.2)|≤δ*ε := by
    apply (wallPrimitive_abs_bound (fun u hu => ?_)).trans
      (mul_le_mul_of_nonneg_right htδ hε)
    simpa only [←mul_assoc] using hr₁ (u*t) (wall_segment_mul ht hu)
  have hAs : |wallAlong d (wallPrimitive r₁) (p.1,t*p.2)|≤δ*ε := by
    rw [wallAlong_primitive d h₁]
    apply (wallPrimitive_abs_bound (fun u hu => ?_)).trans
      (mul_le_mul_of_nonneg_right htδ hε)
    simpa only [←mul_assoc] using hder (u*t) (wall_segment_mul ht hu)
  rw [wallParticularNumerator_derivative d hv h₁ h₂]
  calc
    _ ≤ |r₂ (p.1,t*p.2)|+
      |wallAlong d (wallPrimitive r₁) (p.1,t*p.2)*wallDerivative v (p.1,t*p.2)|+
      |2*wallPrimitive r₁ (p.1,t*p.2)*wallAlong d (wallDerivative v) (p.1,t*p.2)|+
      |r₁ (p.1,t*p.2)*wallAlong d v (p.1,t*p.2)| := by
        have h₀ := abs_sub (r₂ (p.1,t*p.2))
          (wallAlong d (wallPrimitive r₁) (p.1,t*p.2)*wallDerivative v (p.1,t*p.2))
        have h₁ := abs_sub
          (r₂ (p.1,t*p.2)-wallAlong d (wallPrimitive r₁) (p.1,t*p.2)*wallDerivative v (p.1,t*p.2))
          (2*wallPrimitive r₁ (p.1,t*p.2)*wallAlong d (wallDerivative v) (p.1,t*p.2))
        have h₂ := abs_sub
          (r₂ (p.1,t*p.2)-wallAlong d (wallPrimitive r₁) (p.1,t*p.2)*wallDerivative v (p.1,t*p.2)-
            2*wallPrimitive r₁ (p.1,t*p.2)*wallAlong d (wallDerivative v) (p.1,t*p.2))
          (r₁ (p.1,t*p.2)*wallAlong d v (p.1,t*p.2))
        linarith
    _ ≤ ε+δ*ε*M+2*(δ*ε)*M+ε*M := by
      simp only [abs_mul,show |(2:ℝ)|=2 by norm_num]
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (hr₂ t ht) (mul_le_mul hAs (hvz t ht) (abs_nonneg _) (by positivity))
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hA (show (0:ℝ)≤2 by norm_num)) (hvsz t ht) (abs_nonneg _) (by positivity)
      · exact (mul_le_mul_of_nonneg_left (hvs t ht) (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (hr₁ t ht) hM)
    _ = ε*(1+M+3*δ*M) := by ring

theorem wall_particular_coefficient_bound (d : E) {v r₁ r₂ : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂) {p : E × ℝ} {ε M δ c : ℝ}
    (hε : 0≤ε) (hM : 0≤M) (hδ : |p.2|≤δ) (hc : 0<c)
    (hr₁ : ∀ t∈Icc (0:ℝ) 1, |r₁ (p.1,t*p.2)|≤ε)
    (hr₂ : ∀ t∈Icc (0:ℝ) 1, |r₂ (p.1,t*p.2)|≤ε)
    (hder : ∀ t∈Icc (0:ℝ) 1, |wallAlong d r₁ (p.1,t*p.2)|≤ε)
    (hvz : ∀ t∈Icc (0:ℝ) 1, |wallDerivative v (p.1,t*p.2)|≤M)
    (hvs : ∀ t∈Icc (0:ℝ) 1, |wallAlong d v (p.1,t*p.2)|≤M)
    (hvsz : ∀ t∈Icc (0:ℝ) 1, |wallAlong d (wallDerivative v) (p.1,t*p.2)|≤M)
    (hpos : ∀ t∈Icc (0:ℝ) 1,c≤wallDerivative (wallDerivative v) (p.1,t*p.2)) :
    |wallPrimitive r₁ p|≤δ*ε ∧
      |wallQuotient (wallParticularNumerator d v r₁ r₂) p/wallQuotient (wallDerivative v) p|
      ≤ε*(1+M+3*δ*M)/c := by
  refine ⟨(wallPrimitive_abs_bound hr₁).trans (mul_le_mul_of_nonneg_right hδ hε),?_⟩
  exact wall_ratio_abs_bound (wallDerivative_smooth hv) hc
    (wallParticularNumerator_derivative_bound d hv h₁ h₂ hε hM hδ hr₁ hr₂ hder hvz hvs hvsz) hpos

end ScalarConductivity

end
end

end OAI
