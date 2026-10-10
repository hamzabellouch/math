import OAI.Analysis.JiangSu.Excision.ExcisionSoftCompression

namespace OAI

/-! Finite pure-state excision for arbitrary universes. The existing scalar
excision proof applies to both algebras in the tensor-ideal argument. -/

noncomputable section
namespace WeakPureInfiniteness
open scoped ComplexOrder ComplexStarModule
open PureStateExcision

variable {A I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype I]

theorem pure_state_finite_excision (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (a : I → A) {ε ρ : ℝ} (hε : 0<ε) (hρ : 0<ρ) :
    ∃ g : A, 0 ≤ g ∧ ‖g‖ ≤ 1 ∧ 1-ρ<(f g).re ∧
      ∀ i, ‖g*a i*g-f (a i) • (g*g)‖<ε := by
  let b : I×Bool → selfAdjoint A := fun p => if p.2 then ℑ (a p.1) else ℜ (a p.1)
  obtain ⟨g,hg,hgn,hfg,herr⟩ := PureStateExcision.pure_state_finite_selfadjoint_excision f hf1 hpure b
    (show 0<ε/2 by positivity) hρ
  refine ⟨g,hg,hgn,hfg,fun i => ?_⟩
  have hR := herr (i,false)
  have hI := herr (i,true)
  change ‖g*(ℜ (a i) : A)*g-f (ℜ (a i)) • (g*g)‖<ε/2 at hR
  change ‖g*(ℑ (a i) : A)*g-f (ℑ (a i)) • (g*g)‖<ε/2 at hI
  have he : g*a i*g-f (a i) • (g*g)=
      (g*(ℜ (a i) : A)*g-f (ℜ (a i)) • (g*g))+
      Complex.I • (g*(ℑ (a i) : A)*g-f (ℑ (a i)) • (g*g)) := by
    conv_lhs => rw [←realPart_add_I_smul_imaginaryPart (a i)]
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,map_add,map_smul,
      smul_eq_mul,add_smul,smul_sub,smul_smul]
    module
  rw [he]
  have hn := norm_add_le (g*(ℜ (a i) : A)*g-f (ℜ (a i)) • (g*g))
    (Complex.I • (g*(ℑ (a i) : A)*g-f (ℑ (a i)) • (g*g)))
  rw [norm_smul,Complex.norm_I,one_mul] at hn
  linarith


end WeakPureInfiniteness

end

end OAI
