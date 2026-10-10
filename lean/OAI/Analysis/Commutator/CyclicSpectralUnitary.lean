import Mathlib
import OAI.Analysis.Commutator.CyclicSpectralNorm
import OAI.Analysis.Commutator.DecomposableOperator

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def orbitMap (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : C(Ω,ℂ) →ₗ[ℂ] H where
  toFun f := ρ f ξ
  map_add' f g := by simp
  map_smul' z f := by simp

def unitary (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (orbitMap ρ ξ)) : Lp ℂ 2 (measure ρ ξ) ≃ₗᵢ[ℂ] H :=
  (LinearEquiv.refl ℂ C(Ω,ℂ)).extendOfIsometry
    (ContinuousMap.toLp 2 (measure ρ ξ) ℂ).toLinearMap (orbitMap ρ ξ)
    (ContinuousMap.toLp_denseRange ℂ (measure ρ ξ) ℂ (p:=2) (by norm_num)) hd
    (fun f => (toLp_norm_eq ρ ξ f).symm)

lemma unitary_toLp (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (orbitMap ρ ξ)) (f : C(Ω,ℂ)) :
    unitary ρ ξ hd (ContinuousMap.toLp 2 (measure ρ ξ) ℂ f)=ρ f ξ := by
  exact LinearEquiv.extendOfIsometry_eq ..

variable (μ : Measure Ω)

def scalarMultiplier (f : C(Ω,ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  Decomposable.operator μ (fun x => (f x) • (1 : ℂ →L[ℂ] ℂ))
    (fun z => by
      change AEStronglyMeasurable (fun x => f x*z) μ
      exact (f.continuous.mul continuous_const).aestronglyMeasurable)
    (Eventually.of_forall (fun x => by
      simpa using f.norm_coe_le_norm x))

omit [T2Space Ω] in
lemma scalarMultiplier_ae (f : C(Ω,ℂ)) (v : Lp ℂ 2 μ) :
    scalarMultiplier μ f v=ᵐ[μ] fun x => f x*v x :=
  Decomposable.operator_ae ..

omit [T2Space Ω] in
lemma scalarMultiplier_toLp [IsFiniteMeasure μ] (f g : C(Ω,ℂ)) :
    scalarMultiplier μ f (ContinuousMap.toLp 2 μ ℂ g)=ContinuousMap.toLp 2 μ ℂ (f*g) := by
  apply Lp.ext
  filter_upwards [scalarMultiplier_ae μ f (ContinuousMap.toLp 2 μ ℂ g),
    ContinuousMap.coeFn_toLp (𝕜:=ℂ) (p:=2) μ g,ContinuousMap.coeFn_toLp (𝕜:=ℂ) (p:=2) μ (f*g)] with x hx hg hfg
  rw [hx,hg,hfg]
  rfl

lemma unitary_intertwines (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (orbitMap ρ ξ)) (f : C(Ω,ℂ)) (v : Lp ℂ 2 (measure ρ ξ)) :
    unitary ρ ξ hd (scalarMultiplier (measure ρ ξ) f v)=ρ f (unitary ρ ξ hd v) := by
  apply (ContinuousMap.toLp_denseRange ℂ (measure ρ ξ) ℂ (p:=2) (by norm_num)).induction_on v
    (p:=fun v => unitary ρ ξ hd (scalarMultiplier (measure ρ ξ) f v)=ρ f (unitary ρ ξ hd v))
  · apply isClosed_eq
    · exact (unitary ρ ξ hd).continuous.comp (scalarMultiplier (measure ρ ξ) f).continuous
    · exact (ρ f).continuous.comp (unitary ρ ξ hd).continuous
  · intro g
    rw [scalarMultiplier_toLp,unitary_toLp,unitary_toLp,map_mul]
    rfl

end Kadison.CyclicSpectral

end

end
end

end OAI
