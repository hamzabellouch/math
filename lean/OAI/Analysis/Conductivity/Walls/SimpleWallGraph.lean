import Mathlib
import OAI.Analysis.Conductivity.Walls.HadamardWall

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma realCLM_invertible {L : ℝ →L[ℝ] ℝ} (hL : L 1≠0) : L.IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · apply ContinuousLinearMap.ext_ring
    simp only [ContinuousLinearMap.comp_apply,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [←smul_eq_mul, map_smul,smul_eq_mul,inv_mul_cancel₀ hL]
  · apply ContinuousLinearMap.ext_ring
    simp only [ContinuousLinearMap.comp_apply,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    exact inv_mul_cancel₀ hL

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma real_section_hasDeriv {g : E × ℝ → ℝ} (hg : Differentiable ℝ g)
    (p : E) (z : ℝ) : HasDerivAt (fun t => g (p,t)) (wallDerivative g (p,z)) z := by
  simpa only [Function.comp_def,wallDerivative] using
    (hg (p,z)).hasFDerivAt.comp_hasDerivAt z ((hasDerivAt_const z p).prodMk (hasDerivAt_id z))

lemma real_section_strictMono {g : E × ℝ → ℝ} (hg : Differentiable ℝ g)
    {p : E} {a b : ℝ} (hd : ∀ z∈Icc a b, 0<wallDerivative g (p,z)) :
    StrictMonoOn (fun z => g (p,z)) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    ((hg.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn)
  intro z hz
  change 0<deriv (fun t => g (p,t)) z
  rw [(real_section_hasDeriv hg p z).deriv]
  exact hd z (interior_subset hz)

variable [CompleteSpace E]

theorem exists_smooth_simple_wall {g : E × ℝ → ℝ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) {U : Set E} (hU : IsOpen U)
    {a b : ℝ} (hab : a<b)
    (hleft : ∀ p∈U, g (p,a)<0) (hright : ∀ p∈U, 0<g (p,b))
    (hder : ∀ p∈U, ∀ z∈Icc a b, 0<wallDerivative g (p,z)) :
    ∃ ρ : E → ℝ, ContDiffOn ℝ (↑(⊤ : ℕ∞)) ρ U ∧
      (∀ p∈U, ρ p∈Ioo a b ∧ g (p,ρ p)=0) ∧
      ∀ p∈U, ∀ z∈Icc a b, g (p,z)=0 → z=ρ p := by
  classical
  have hd := hg.differentiable (by simp)
  have he (p : E) (hp : p∈U) : ∃ z∈Ioo a b, g (p,z)=0 := by
    obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc hab.le
      ((hg.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn (s := Icc a b))
      (show (0:ℝ)∈Icc (g (p,a)) (g (p,b)) from ⟨(hleft p hp).le,(hright p hp).le⟩)
    change g (p,z)=0 at hgz
    refine ⟨z,⟨lt_of_le_of_ne hz.1 ?_,lt_of_le_of_ne hz.2 ?_⟩,hgz⟩
    · intro h; subst z; linarith [hleft p hp]
    · intro h; subst z; linarith [hright p hp]
  choose ρ₀ hρ₀ using he
  let ρ : E → ℝ := fun p => if hp : p∈U then ρ₀ p hp else 0
  have hρ (p : E) (hp : p∈U) : ρ p∈Ioo a b ∧ g (p,ρ p)=0 := by
    simpa only [ρ,dite_eq_left hp] using hρ₀ p hp
  have huniq (p : E) (hp : p∈U) (z : ℝ) (hz : z∈Icc a b) (hgz : g (p,z)=0) : z=ρ p := by
    apply (real_section_strictMono hd (hder p hp)).injOn hz (Ioo_subset_Icc_self (hρ p hp).1)
    exact hgz.trans (hρ p hp).2.symm
  refine ⟨ρ,?_,hρ,huniq⟩
  intro p hp
  have hc : ContDiffAt ℝ (↑(⊤ : ℕ∞)) g (p,ρ p) := hg.contDiffAt
  have hinv : (fderiv ℝ g (p,ρ p) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    apply realCLM_invertible
    change wallDerivative g (p,ρ p)≠0
    exact (hder p hp (ρ p) (Ioo_subset_Icc_self (hρ p hp).1)).ne'
  let ψ := hc.implicitFunction (by simp) hinv
  have hψsmooth : ContDiffAt ℝ (↑(⊤ : ℕ∞)) ψ p := hc.contDiffAt_implicitFunction (by simp) hinv
  have hψself : ψ p=ρ p := hc.implicitFunction_apply_self (by simp) hinv
  have hψeq : ∀ᶠ q in 𝓝 p, g (q,ψ q)=0 := by
    have hh := hc.eventually_apply_implicitFunction (by simp) hinv
    simpa only [(hρ p hp).2] using hh
  have hψin : ∀ᶠ q in 𝓝 p, ψ q∈Ioo a b :=
    hψsmooth.continuousAt (isOpen_Ioo.mem_nhds (by simpa only [hψself] using (hρ p hp).1))
  have hident : ψ =ᶠ[𝓝 p] ρ := by
    filter_upwards [hU.mem_nhds hp,hψeq,hψin] with q hq he hi
    exact huniq q hq _ (Ioo_subset_Icc_self hi) he
  exact (hψsmooth.congr_of_eventuallyEq hident.symm).contDiffWithinAt

end ScalarConductivity

end
end

end OAI
