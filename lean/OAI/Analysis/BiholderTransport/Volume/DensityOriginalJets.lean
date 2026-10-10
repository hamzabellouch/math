import Mathlib
import OAI.Analysis.BiholderTransport.Oscillation.SectionOscillation
import OAI.Analysis.BiholderTransport.Contact.IntrinsicCEMS
import OAI.Analysis.BiholderTransport.LinearAlgebra.TrueCenterMatrix

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section DensityOriginalJets
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance densityOriginalFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

local instance densityOriginalComplete (x:M) : CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x) :=
  FiniteDimensional.complete ℝ _

def OriginalCenterGood (u:M → ℝ) (χ:ℝ) (y:M) : Prop :=
  ∃p:TangentSpace 𝓘(ℝ,Model n) y,
  ∃A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y,
    NormalAlexandrovContact (n:=n) u y p A ∧
    (∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d) ∧
    χ≤expJacobian y p*(normalHessianOperator y p+A).det

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma OriginalCenterGood.of_contact {u:M → ℝ} {χ:ℝ} {y:M}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A)
    (hp:∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d)
    (hlo:χ≤expJacobian y p*|(normalHessianOperator y p+A).det|) :
    OriginalCenterGood (n:=n) u χ y := by
  have hs : ∀d e,inner ℝ ((normalHessianOperator y p+A) d) e=
      inner ℝ d ((normalHessianOperator y p+A) e) := normal_contact_matrix_symmetric hA
  have hdet : 0 < (normalHessianOperator y p+A).det :=
    symmetric_det_pos (A:=normalHessianOperator y p+A) hs hp
  exact ⟨p,A,hA,hp,by simpa only [abs_of_pos hdet] using hlo⟩

lemma exists_density_original_center_good {lam cap:ℝ} (hlam:0<lam) (hcap:lam≤cap) :
    ∃χ>0,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ᵐ y ∂metricVolume n,OriginalCenterGood (n:=n) uv.1 χ y := by
  obtain ⟨χ,_,hχ,_,H⟩:=minimizing_dualPair_uniform_intrinsic_cems (n:=n) (M:=M) hlam hcap
  refine ⟨χ,hχ,?_⟩
  intro x0 uv huv
  have hd:=densityDualClass_isDual huv
  obtain ⟨_,ρ0,ρ1,h0,h1,hmin⟩:=huv
  have Ha:=H ρ1 ρ0 h1 h0 uv.2 uv.1 ⟨hd.2,hd.1⟩ (dual_minimum_swap hmin)
  filter_upwards [Ha] with y hy
  obtain ⟨p,A,hA,hp,hlo,_⟩:=hy
  exact OriginalCenterGood.of_contact hA hp hlo
end DensityOriginalJets
end WeakMTWTransport

end
end

end OAI
