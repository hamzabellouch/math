import OAI.Analysis.CircleDomains.Reflection.MovingCircleReflection
import OAI.Analysis.CircleDomains.Uniformization.MontelProof

namespace OAI

/-! Compactness of the explicit reflected maps on a fixed two-sided
collar. The bound is independent of the reciprocals of the target radii. -/
open Set Function Filter Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma exists_moving_circle_reflection_limit {U:Set ℂ} {f:ℕ → ℂ → ℂ}
    {c:ℕ → ℂ} {r:ℕ → ℝ} {M:ℝ}
    (hU:IsOpen U) (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U)
    (hr:∀n,0<r n)
    (hc:∀n,ContinuousOn (f n) (U∩{z | 1≤‖z‖}))
    (hd:∀n z,z∈U → 1<‖z‖ → DifferentiableAt ℂ (f n) z)
    (ho:∀n z,z∈U → 1≤‖z‖ → r n≤‖f n z-c n‖)
    (hb:∀n z,z∈U → ‖z‖=1 → ‖f n z-c n‖=r n)
    (hM:∀n,‖c n‖+r n≤M)
    (hf:∀n z,z∈U → 1≤‖z‖ → ‖f n z‖≤M) :
    ∃s:ℕ → ℕ, ∃F:ℂ → ℂ,StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => circleReflectionExtension (c (s n)) (r (s n)) (f (s n)))
        F atTop U ∧ DifferentiableOn ℂ F U := by
  have hhol (n:ℕ) : DifferentiableOn ℂ (circleReflectionExtension (c n) (r n) (f n)) U :=
    circleReflectionExtension_differentiableOn (hr n) hU hz hs (hc n) (hd n) (ho n) (hb n)
  obtain ⟨s,F,hsm,hlim⟩ := montelExhaustion (fun _ => U)
    (fun n => circleReflectionExtension (c n) (r n) (f n)) (fun _ => hU)
    (fun _ _ _ => Subset.refl _) hhol (by
      intro K hK hKU
      refine ⟨M,?_⟩
      intro n z _ hzU
      exact circleReflectionExtension_norm_le (hr n) hz hs (hM n)
        (fun z hzU hzo => ⟨ho n z hzU hzo,hf n z hzU hzo⟩) hzU)
  simp only [iUnion_const] at hlim
  exact ⟨s,F,hsm,hlim,hlim.differentiableOn (Eventually.of_forall (fun n => hhol (s n))) hU⟩

lemma moving_circle_reflection_limit_boundary {U:Set ℂ} {f:ℕ → ℂ → ℂ}
    {c:ℕ → ℂ} {r:ℕ → ℝ} {s:ℕ → ℕ} {F:ℂ → ℂ} {a:ℂ} {ρ:ℝ}
    (hr:∀n,0<r n) (hs:StrictMono s)
    (hlim:TendstoLocallyUniformlyOn
      (fun n => circleReflectionExtension (c (s n)) (r (s n)) (f (s n))) F atTop U)
    (hc:Tendsto c atTop (𝓝 a)) (hρ:Tendsto r atTop (𝓝 ρ))
    (hb:∀n z,z∈U → ‖z‖=1 → ‖f n z-c n‖=r n)
    {z:ℂ} (hz:z∈U) (hz1:‖z‖=1) : ‖F z-a‖=ρ := by
  have hp := hlim.tendsto_at hz
  have hnorm := (hp.sub (hc.comp hs.tendsto_atTop)).norm
  have he (n:ℕ) :
      ‖circleReflectionExtension (c (s n)) (r (s n)) (f (s n)) z-c (s n)‖=r (s n) := by
    rw [circleReflectionExtension_outer (hr (s n)) hz1.ge]
    exact hb (s n) z hz hz1
  apply tendsto_nhds_unique hnorm
  exact (hρ.comp hs.tendsto_atTop).congr' (Eventually.of_forall (fun n => (he n).symm))

end CircleDomainRigidity

end

end OAI
