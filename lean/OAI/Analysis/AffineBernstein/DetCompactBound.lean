import Mathlib
import OAI.Analysis.AffineBernstein.DetBarrierPhase

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DetCompactBound
open Filter
open scoped Topology

/-- Maximum-principle determinant upper estimate on a literal compact negative
section. The compact section and gradient/depth bounds are geometric inputs;
no Hessian, determinant, ellipticity or derivative bound is assumed. -/
lemma affineMaximal_det_phase_bound {n : ℕ} {V Ω K : Set (Space n)}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hΩK : Ω ⊆ K) (hKV : K ⊆ V) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (hp : ∀ x ∈ V, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u) (hneg : ∀ x ∈ Ω, u x < 0)
    (hbd : ∀ x ∈ K, x ∉ Ω → u x = 0)
    {γ M D : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hsmall : γ*M ≤ 1/2) (hgrad : ∀ x ∈ Ω, gradientSquared u x ≤ M)
    (hdepth : ∀ x ∈ Ω, -u x ≤ D) {x : Space n} (hx : x ∈ Ω) :
    affineDetPhase u γ x ≤ (2*(n:ℝ)*(((n:ℝ)+2)/γ+M))^n * D^2 * Real.exp (γ*M/2) := by
  obtain ⟨y,hyK,hymax⟩ := hK.exists_isMaxOn ⟨x,hΩK hx⟩
    ((continuousOn_affineDetPhase hV hu γ).mono hKV)
  have hxy : affineDetPhase u γ x ≤ affineDetPhase u γ y := hymax (hΩK hx)
  have hyp : 0 < affineDetPhase u γ y :=
    (affineDetPhase_pos (hp x (hKV (hΩK hx))) (hneg x hx) γ).trans_le hxy
  have hy : y ∈ Ω := by
    by_contra h
    have hz : affineDetPhase u γ y = 0 := by
      simp [affineDetPhase,hbd y hyK h]
    rw [hz] at hyp
    exact (lt_irrefl 0) hyp
  have hmax : IsLocalMax (affineDetBarrier u ((n:ℝ)+2) γ) y := by
    filter_upwards [hΩ.mem_nhds hy] with z hz
    apply Real.exp_le_exp.mp
    rw [← affineDetPhase_eq_exp (hp z (hKV (hΩK hz))) (hneg z hz) γ,
      ← affineDetPhase_eq_exp (hp y (hKV hyK)) (hneg y hy) γ]
    exact hymax (hΩK hz)
  exact hxy.trans (affineDetPhase_peak_bound hΩ (hu.mono (hΩK.trans hKV))
    (fun z hz => hp z (hKV (hΩK hz))) hm hneg hy hγ hM hD hsmall
    (hgrad y hy) (hdepth y hy) hmax)

lemma affineDetPhase_ge_det_mul_depth {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (hn : u x < 0) {γ δ : ℝ} (hγ : 0 ≤ γ)
    (hδ : 0 < δ) (hdepth : δ ≤ -u x) :
    (hessian u x).det * δ^(n+2) ≤ affineDetPhase u γ x := by
  have hGE : 0 ≤ gradientEnergy u x := by
    unfold gradientEnergy
    positivity
  have hexp : 1 ≤ Real.exp (γ*gradientEnergy u x) := Real.one_le_exp_iff.mpr (mul_nonneg hγ hGE)
  unfold affineDetPhase
  calc
    _ ≤ (hessian u x).det * (-u x)^(n+2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hdepth _) hp.det_pos.le
    _ = ((hessian u x).det * (-u x)^(n+2))*1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp
      (mul_nonneg hp.det_pos.le (pow_nonneg (neg_nonneg.mpr hn.le) _))

lemma affineMaximal_det_upper_on_compact_section {n : ℕ} {V Ω K : Set (Space n)}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hΩK : Ω ⊆ K) (hKV : K ⊆ V) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (hp : ∀ x ∈ V, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u) (hneg : ∀ x ∈ Ω, u x < 0)
    (hbd : ∀ x ∈ K, x ∉ Ω → u x = 0)
    {M D δ : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hgrad : ∀ x ∈ Ω, gradientSquared u x ≤ M)
    (hdepth : ∀ x ∈ Ω, -u x ≤ D) {x : Space n} (hx : x ∈ Ω)
    (hxdepth : δ ≤ -u x) :
    (hessian u x).det ≤
      (2*(n:ℝ)*(((n:ℝ)+2)*(2*(M+1))+M))^n * D^2 *
        Real.exp (M/(4*(M+1))) / δ^(n+2) := by
  let γ : ℝ := 1/(2*(M+1))
  have hden : 0 < 2*(M+1) := by linarith
  have hγ : 0 < γ := one_div_pos.mpr hden
  have hsmall : γ*M ≤ 1/2 := by
    dsimp [γ]
    rw [one_div_mul_eq_div,div_le_iff₀ hden]
    linarith
  have hbound := affineMaximal_det_phase_bound hV hΩ hK hΩK hKV hu hp hm hneg hbd
    hγ hM hD hsmall hgrad hdepth hx
  have hlower := affineDetPhase_ge_det_mul_depth (hp x (hKV (hΩK hx))) (hneg x hx)
    hγ.le hδ hxdepth
  have he : γ*M/2 = M/(4*(M+1)) := by
    dsimp [γ]
    field_simp [ne_of_gt (show 0 < M + 1 by linarith)]
    ring
  rw [he] at hbound
  have hd : ((n:ℝ)+2)/γ = ((n:ℝ)+2)*(2*(M+1)) := by
    dsimp [γ]
    simp only [div_eq_mul_inv,one_mul,inv_inv]
  rw [hd] at hbound
  exact (le_div_iff₀ (pow_pos hδ _)).mpr (hlower.trans hbound)

end DetCompactBound


end
end AffineBernstein
end

end OAI
