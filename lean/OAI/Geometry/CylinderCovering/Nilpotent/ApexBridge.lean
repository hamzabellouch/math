import OAI.Geometry.CylinderCovering.Nilpotent.ApexPhysical
import OAI.Geometry.CylinderCovering.Nilpotent.FiniteDefinitions

namespace OAI

open Set MeasureTheory RuledApproximation

noncomputable section
namespace CylinderCovering.NilpotentApexNet

lemma physicalApexSweep_eq_image (h k ρ σ : ℝ) :
    physicalApexSweep h k ρ σ =
      firstPhysicalMap h '' Nilpotent.apexSweep (σ * k) ρ := by
  ext z
  constructor
  · rintro ⟨s, p, t, hs, hp, ht, htρ, rfl⟩
    refine ⟨vec3 s (p*t+s*(σ*k)*Nilpotent.v p) (t+s*(σ*k)*Nilpotent.w p),
      ⟨s,p,t,hs,hp,ht,htρ,rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, vec3, velocity, mul_assoc]
  · rintro ⟨z, ⟨s,p,t,hs,hp,ht,htρ,rfl⟩, rfl⟩
    refine ⟨s,p,t,hs,hp,ht,htρ,?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, vec3, velocity, mul_assoc]

theorem signed_apex_cover {h k ρ σ : ℝ} (hh : 0 < h) (hk : 0 ≤ k)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσ : |σ| ≤ 1) :
    HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap h '' Nilpotent.apexSweep (σ*k) ρ)
      (h * (16 * (1 + k / 2) ^ 2 * ρ)) := by
  have hc := physicalApex_hasFiniteCover hh hk hρ hρ1 hσ (IsometryEquiv.refl Space)
  change HasFiniteCover Cylinder.parallelogram (id '' physicalApexSweep h k ρ σ) _ at hc
  simpa only [image_id, physicalApexSweep_eq_image] using hc

theorem signed_apex_cover_budget {h k ρ σ ε : ℝ} (hh : 0 < h) (hk : 0 ≤ k)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσ : |σ| ≤ 1)
    (hbudget : 32 * (1 + k / 2) ^ 2 * ρ ≤ ε) :
    HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap h '' Nilpotent.apexSweep (σ*k) ρ) (h*ε/2) := by
  apply (signed_apex_cover hh hk hρ hρ1 hσ).mono Subset.rfl
  have hm := mul_le_mul_of_nonneg_left hbudget hh.le
  nlinarith

end CylinderCovering.NilpotentApexNet

end

end OAI
