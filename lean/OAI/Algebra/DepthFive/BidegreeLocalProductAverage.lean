import OAI.Algebra.DepthFive.BidegreeCompositionReindex
import OAI.Algebra.DepthFive.LocalProductAverage

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

theorem bidegree_average_eq_partitionCompositionMean
    {σ : Type*} [Fintype σ] [DecidableEq σ] (side : σ → Bool) (a b : ℕ)
    [Fintype {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)}]
    (f : (σ → ℕ) → ℝ) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)}, f d.val) /
      (Fintype.card {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)} : ℝ) =
        partitionCompositionMean side f a b := by
  unfold partitionCompositionMean
  unfold joinOccupation
  exact bidegree_average_eq_double_antidiag side a b f

namespace LocalMoments

/-- The second-moment occupation estimate on the actual canonical source
exponent subtype, presented in the same local coordinates as the four paths. -/
theorem bidegree_average_layered_localProduct_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (derivative : ι → Bool)
    [Nonempty {x : ι × κ // derivative x.1 = true}]
    [Nonempty {x : ι × κ // ¬ derivative x.1 = true}]
    (a b : ℕ)
    [Fintype {d : (ι × κ) →₀ ℕ //
      Finsupp.weight (bidegreeWeight (fun x => derivative x.1)) d = (a, b)}]
    (layers : Finset ι) (p q r : ι → κ) :
    (∑ d : {d : (ι × κ) →₀ ℕ //
        Finsupp.weight (bidegreeWeight (fun x => derivative x.1)) d = (a, b)},
      ∏ t ∈ layers, localPolynomial (derivative t) (fun x => d.val (t, x))
        (p t) (q t) (r t)) /
      (Fintype.card {d : (ι × κ) →₀ ℕ //
        Finsupp.weight (bidegreeWeight (fun x => derivative x.1)) d = (a, b)} : ℝ) ≤
      ∏ t ∈ layers, localGeometricMass (derivative t)
        (if derivative t = true then
          (a : ℝ) / Fintype.card {x : ι × κ // derivative x.1 = true}
        else (b : ℝ) / Fintype.card {x : ι × κ // ¬ derivative x.1 = true})
        (p t) (q t) (r t) := by
  have heq := bidegree_average_eq_partitionCompositionMean
    (fun x : ι × κ => derivative x.1) a b
    (fun M => ∏ t ∈ layers, localPolynomial (derivative t) (fun x => M (t, x))
      (p t) (q t) (r t))
  exact heq.trans_le (partitionCompositionMean_layered_restrict_le derivative a b layers p q r)

end LocalMoments
end Problem335

end

end OAI
