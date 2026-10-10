import OAI.Probability.DilutedSpin.IntegratedFiniteUpper
import OAI.Probability.DilutedSpin.RealEncoding

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower PrescribedTree Set
open scoped NNReal BigOperators
variable {N q : ℕ} [NeZero N]

lemma finiteHierarchy_pressure_le (M : Model (q+1)) (hM : Admissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (hζ : FiniteHierarchy (r+1) ζ)
    (m : Fin r → ℝ) (hm : Exponents m) : pressure M N ≤ functional M r ζ m := by
  obtain ⟨n,hn,T,V,hT⟩ := finiteHierarchy_realization (r+1) ζ hζ
  let a : Fin n := ⟨0,hn⟩
  have h := finiteTrial_pressure_le (N := N) M hM a r T.1 T.2 (fun b y => V (b,y)) m hm
  have he : finiteTrialLaw r T.1 T.2 (fun b y => V (b,y))=ζ := hT
  rwa [he] at h

lemma pressure_le_functional (M : Model (q+1)) (hM : Admissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    pressure M N ≤ functional M r ζ m := by
  have hc : IsClosed {ζ : Hierarchy (r+1) | pressure M N ≤ functional M r ζ m} :=
    isClosed_le continuous_const (functional_continuous M m (fun d => (hm.2 d).1)
      hM.interaction_integrable hM.field_integrable)
  have hs : {ζ : Hierarchy (r+1) | FiniteHierarchy (r+1) ζ} ⊆
      {ζ : Hierarchy (r+1) | pressure M N ≤ functional M r ζ m} := by
    intro η hη
    exact finiteHierarchy_pressure_le M hM r η hη m hm
  exact closure_minimal hs hc ((finiteHierarchy_dense (r+1)) ζ)

end DilutedSpinGlass

end

end OAI
