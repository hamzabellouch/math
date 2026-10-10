import OAI.Combinatorics.SharpThreshold.Quantile
import OAI.Combinatorics.SharpThreshold.MeanEndpoints

namespace OAI

noncomputable section
namespace Problem313

theorem graphQuantile_eq_unitQuantile {n : ℕ} (f : GraphConfig n → Bool) (a : ℝ) :
    graphQuantile a f = unitQuantile (fun p => graphMean p f) a := rfl

theorem graphMean_graphQuantile {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    graphMean (graphQuantile a f) f = a :=
  unitQuantile_eq_level (continuous_graphMean f)
    (graphMean_zero_of_increasing_nontrivial hmono hnt)
    (graphMean_one_of_increasing_nontrivial hmono hnt) ha0 ha1

theorem graphQuantile_mem_Ioo {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    graphQuantile a f ∈ Set.Ioo (0 : ℝ) 1 :=
  unitQuantile_mem_Ioo (continuous_graphMean f)
    (graphMean_zero_of_increasing_nontrivial hmono hnt)
    (graphMean_one_of_increasing_nontrivial hmono hnt) ha0 ha1

theorem graphQuantile_strictMonoOn {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    StrictMonoOn (fun a => graphQuantile a f) (Set.Icc (0 : ℝ) 1) :=
  unitQuantile_strictMonoOn (continuous_graphMean f)
    (graphMean_zero_of_increasing_nontrivial hmono hnt)
    (graphMean_one_of_increasing_nontrivial hmono hnt)

end Problem313

end

end OAI
