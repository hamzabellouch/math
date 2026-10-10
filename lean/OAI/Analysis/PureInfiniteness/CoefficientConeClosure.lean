import OAI.Analysis.Nuclearity.UnitizedCoefficientConvexity
import OAI.Analysis.PureInfiniteness.PointNormFiniteCriterion

namespace OAI

/-! The actual coefficient cone and its point-norm closure are invariant
under output compressions. Thus approximating the inclusion suffices for
all relatively approximately inner maps, as in KR02 Lemma 7.19. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D I : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [Fintype I]

lemma unitizedSandwich_output_compression (a b : Unitization ℂ D) (x w : D) :
    unitizedSandwich (a * (w : Unitization ℂ D)) x (b * (w : Unitization ℂ D)) =
      star w * unitizedSandwich a x b * w := by
  apply Unitization.inr_injective (R := ℂ)
  simp only [inr_unitizedSandwich, Unitization.inr_mul, Unitization.inr_star,
    star_mul, mul_assoc]

lemma unitizedCoefficientEnlargement_output_compression (T : B → D)
    (a : I → Unitization ℂ D) (c : I → B) (w : D) (b : B) :
    unitizedCoefficientEnlargement T (fun i => a i * (w : Unitization ℂ D)) c b =
      star w * unitizedCoefficientEnlargement T a c b * w := by
  simp only [unitizedCoefficientEnlargement, unitizedSandwich_output_compression,
    Finset.mul_sum, Finset.sum_mul]

def outputCompression (w : D) (T : B → D) : B → D := fun b => star w * T b * w

omit [Fintype I] [NonUnitalCStarAlgebra B] in
lemma outputCompression_continuous (w : D) :
    Continuous (outputCompression (B := B) w) :=
  continuous_pi fun b => (continuous_const.mul (continuous_apply b)).mul continuous_const

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder B] (U : Ultrafilter ℕ)

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

omit [Fintype I] in
lemma finiteUnitizedAbelianCoefficientCone_outputCompression (β : B →⋆ₙₐ[ℂ] N)
    {T : B → N} (hT : T ∈ finiteUnitizedAbelianCoefficientCone U β) (w : N) :
    outputCompression w T ∈ finiteUnitizedAbelianCoefficientCone U β := by
  obtain ⟨n, m, V, hi, hp, hc, a, c, hv⟩ := hT
  refine ⟨n, m, V, hi, hp, hc, (fun p => a p * (w : Unitization ℂ N)), c, ?_⟩
  intro b
  simp only [unitizedCoefficientEnlargement_output_compression, ← Finset.mul_sum,
    ← Finset.sum_mul]
  exact congrArg (fun z => star w * z * w) (hv b)

omit [Fintype I] in
lemma coefficientConeClosure_outputCompression (β : B →⋆ₙₐ[ℂ] N)
    {T : B → N} (hT : T ∈ closure (finiteUnitizedAbelianCoefficientCone U β)) (w : N) :
    outputCompression w T ∈ closure (finiteUnitizedAbelianCoefficientCone U β) :=
  map_mem_closure (outputCompression_continuous w) hT
    (fun _ h => finiteUnitizedAbelianCoefficientCone_outputCompression U β h w)

omit [Fintype I] in
theorem coefficientConeClosure_of_approximatelyInnerAlong (β : B →⋆ₙₐ[ℂ] N)
    (hβ : (β : B → N) ∈ closure (finiteUnitizedAbelianCoefficientCone U β))
    {T : B → N} (hT : ApproximatelyInnerAlong β T) :
    T ∈ closure (finiteUnitizedAbelianCoefficientCone U β) := by
  let K := (unitizedCoefficientCone U β).closure
  have hzero : (0 : B → N) ∈ K :=
    subset_closure (finiteUnitizedAbelianCoefficientCone_zero U β)
  have hsum {n : ℕ} (w : Fin n → N) :
      (∑ i, outputCompression (w i) β) ∈ K := by
    apply Finset.sum_induction
    · exact fun _ _ hi hs => K.add_mem hi hs
    · exact hzero
    · exact fun i _ => coefficientConeClosure_outputCompression U β hβ (w i)
  rw [← closure_closure (s := finiteUnitizedAbelianCoefficientCone U β)]
  apply mem_closure_of_finite_approximation
  intro F ε hε
  obtain ⟨n, w, hw⟩ := hT F ε hε
  refine ⟨∑ i, outputCompression (w i) β, hsum w, ?_⟩
  intro b hb
  simpa only [Finset.sum_apply, outputCompression] using hw b hb

end WeakPureInfiniteness

end

end OAI
