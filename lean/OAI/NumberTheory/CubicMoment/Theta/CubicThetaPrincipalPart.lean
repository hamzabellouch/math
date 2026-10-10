import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticPoleIsolation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticPole

namespace OAI

/-! The actual arithmetic pole has order exactly one. Subtracting its
computed spectral residue leaves an analytic germ. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

private lemma simple_pole_order {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a : ℂ} {R : E} (hf : MeromorphicAt f a) (hR : R≠0)
    (ht : Tendsto (fun z : ℂ => (z-a) • f z) (𝓝[≠] a) (𝓝 R)) :
    meromorphicOrderAt f a=(-1:ℤ) := by
  have ha : AnalyticAt ℂ (fun z : ℂ => z-a) a := analyticAt_id.sub analyticAt_const
  have hm := ha.meromorphicAt.smul hf
  have ho := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hm).mp ⟨R,hR,ht⟩
  change meromorphicOrderAt ((fun z : ℂ => z-a) • f) a=0 at ho
  rw [meromorphicOrderAt_smul ha.meromorphicAt hf,meromorphicOrderAt_id_sub_const] at ho
  cases h : meromorphicOrderAt f a with
  | top => simp [h] at ho
  | coe n =>
    rw [h] at ho
    have hn : (1:ℤ)+n=0 := by exact_mod_cast ho
    have he : n=(-1:ℤ) := by omega
    simp [he]

lemma cubicThetaPrincipalPart_removable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a : ℂ} {R : E} (hf : MeromorphicAt f a)
    (ht : Tendsto (fun z : ℂ => (z-a) • f z) (𝓝[≠] a) (𝓝 R)) :
    ∃ g : ℂ → E, AnalyticAt ℂ g a ∧
      (fun z => f z-(z-a)⁻¹ • R)=ᶠ[𝓝[≠] a] g := by
  have ha : AnalyticAt ℂ (fun z : ℂ => z-a) a := analyticAt_id.sub analyticAt_const
  have hp : MeromorphicAt (fun z : ℂ => (z-a)⁻¹ • R) a :=
    ha.meromorphicAt.inv.smul analyticAt_const.meromorphicAt
  apply cubicThetaSimpleResidue_removable (hf.sub hp)
  have hz : Tendsto (fun z : ℂ => (z-a) • f z-R) (𝓝[≠] a) (𝓝 0) := by
    simpa only [sub_self] using ht.sub (tendsto_const_nhds (x:=R))
  apply hz.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z-a≠0 := sub_ne_zero.mpr hz
  simp only [Pi.sub_apply,smul_sub,smul_smul,mul_inv_cancel₀ hne,one_smul]

theorem cubicThetaForcedResolvent_pole_order :
    meromorphicOrderAt cubicThetaForcedResolvent (4/3:ℂ)=(-1:ℤ) := by
  obtain ⟨R,hR,ht⟩ := cubicThetaForcedResolvent_nonzero_residue
  exact simple_pole_order (cubicThetaForcedResolvent_meromorphic (by norm_num)) hR ht

theorem cubicThetaForcedEnergy_principal_part :
    ∃ g : ℂ → cubicThetaGlobalEnergySpace, AnalyticAt ℂ g (4/3:ℂ) ∧
      (fun s => cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s)
        (cubicThetaForcingL2 s)-(s-4/3)⁻¹ • cubicThetaArithmeticResidueEnergy (4/3))
        =ᶠ[𝓝[≠] (4/3:ℂ)] g := by
  apply cubicThetaPrincipalPart_removable (cubicThetaForcedEnergy_meromorphic (by norm_num))
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
    cubicThetaForcedEnergy_residue (σ:=4/3) (by norm_num) (by norm_num)

theorem cubicThetaForcedResolvent_principal_part :
    ∃ g : ℂ → CubicThetaGlobalL2, AnalyticAt ℂ g (4/3:ℂ) ∧
      (fun s => cubicThetaForcedResolvent s-(s-4/3)⁻¹ •
        cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)))
        =ᶠ[𝓝[≠] (4/3:ℂ)] g := by
  apply cubicThetaPrincipalPart_removable (cubicThetaForcedResolvent_meromorphic (by norm_num))
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
    cubicThetaForcedResolvent_residue (σ:=4/3) (by norm_num) (by norm_num)

end CubicFirstMoment

end

end OAI
