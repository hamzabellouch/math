import Mathlib
import OAI.Probability.SKValue.Processes.VariableTestLaw
import OAI.Probability.SKValue.Gaussian.SplitJets

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue

theorem IsDiffusion.literal_coercivity {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) (t:Ioo (0:ℝ) 1) :
    (1/1000:ℝ)*(∫ z,(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4 ∂W.μ) ≤
      ∫ z,(spatialJet (γ.coeff t) (phi W γ t) 3 (X t z))^2-
        12*spatialJet (γ.coeff t) (phi W γ t) 1 (X t z)*(spatialJet (γ.coeff t) (phi W γ t) 2 (X t z))^2+
        6*(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4 ∂W.μ := by
  let J:=fun n k ↦ spatialJet (γ.coeff t+(gridDelta n:ℝ)) (splitTerminal γ t n) k
  let j:=fun k ↦ spatialJet (γ.coeff t) (phi W γ t) k
  have hJ (n k:ℕ):BoundedSmooth (J n k) := (splitTerminal_smooth γ t n).spatialJet_boundedSmooth _ _
  have hj (k:ℕ):BoundedSmooth (j k) :=
    ((phi_evolution W γ ⟨t.property.1.le,t.property.2⟩).slices t ⟨t.property.1.le,le_rfl⟩).spatialJet_boundedSmooth _ _
  have hl (k:ℕ):BoundedUniformLimit (fun n ↦ J n k) (j k) := split_spatialJet_limit W γ t k
  have hl4:=hX.splitResponse_varying t (fun n ↦ (hJ n 1).pow 4) ((hj 1).pow 4) ((hl 1).pow 4)
  have hpoly:BoundedUniformLimit (fun n x ↦ J n 3 x^2-12*J n 1 x*(J n 2 x)^2+6*(J n 1 x)^4)
      (fun x ↦ j 3 x^2-12*j 1 x*(j 2 x)^2+6*(j 1 x)^4) :=
    (((hl 3).pow 2).sub (((BoundedUniformLimit.const 12).mul (hl 1)).mul ((hl 2).pow 2))).add
      ((BoundedUniformLimit.const 6).mul ((hl 1).pow 4))
  have hlp:=hX.splitResponse_varying t
    (fun n ↦ (((hJ n 3).pow 2).sub (((hJ n 1).const_mul 12).mul ((hJ n 2).pow 2))).add (((hJ n 1).pow 4).const_mul 6))
    ((((hj 3).pow 2).sub (((hj 1).const_mul 12).mul ((hj 2).pow 2))).add (((hj 1).pow 4).const_mul 6)) hpoly
  exact le_of_tendsto_of_tendsto (hl4.const_mul (1/1000:ℝ)) hlp
    (Eventually.of_forall (fun n ↦ split_profile_coercivity γ t n))
end SKValue

end

end OAI
