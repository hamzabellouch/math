import OAI.NumberTheory.Ostmann.Construction.InitialEtaDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta

variable (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (aux : ι → PrimeSource) (b s : ℕ)

theorem jointPrior_mass (x : JointSample giant bulk spectator aux b s) :
    (jointPrior giant bulk spectator aux b s).mass x =
      ∏i,(tupleSource giant bulk spectator aux b s i).law.mass (tupleSample x i) := by
  simp only [jointPrior,halfListPrior,FinitePrior.pair,primeGroupPrior,dependentProductPrior,
    Fintype.prod_prod_type,Fintype.prod_bool,Fintype.prod_sum_type,Fintype.prod_unique,
    tupleSource,halfSource,tupleSample,halfSample,halfAt,Bool.false_eq_true,ite_false,ite_true]
  ring

theorem tupleEquiv_cmean
    (f : ((i : Position b s ι) → (tupleSource giant bulk spectator aux b s i).Sample) → ℂ) :
    (jointPrior giant bulk spectator aux b s).cmean (fun x => f (tupleEquiv giant bulk spectator aux b s x)) =
      (dependentProductPrior (fun i => (tupleSource giant bulk spectator aux b s i).law)).cmean f := by
  unfold FinitePrior.cmean
  simp only [jointPrior_mass,dependentProductPrior]
  exact (tupleEquiv giant bulk spectator aux b s).sum_comp
    (fun z => (((∏i,(tupleSource giant bulk spectator aux b s i).law.mass (z i)):ℝ):ℂ)*f z)

theorem tupleEquiv_mean
    (f : ((i : Position b s ι) → (tupleSource giant bulk spectator aux b s i).Sample) → ℝ) :
    (jointPrior giant bulk spectator aux b s).mean (fun x => f (tupleEquiv giant bulk spectator aux b s x)) =
      (dependentProductPrior (fun i => (tupleSource giant bulk spectator aux b s i).law)).mean f := by
  unfold FinitePrior.mean
  simp only [jointPrior_mass,dependentProductPrior]
  exact (tupleEquiv giant bulk spectator aux b s).sum_comp
    (fun z => (∏i,(tupleSource giant bulk spectator aux b s i).law.mass (z i))*f z)

end Ostmann.Construction.InitialEta

end

end OAI
