import OAI.Probability.InvariantIsing.Cavity.CavityGaussianContinuity
import Mathlib.Topology.TietzeExtension

namespace OAI

/-! Joint weak continuity of Gaussian marks and their finite overlap
labels, including singular covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace InvariantIsing

variable {a L : Type*} [Fintype a] [DecidableEq a] [MetricSpace L]

lemma cavity_gaussian_joint_test_tendsto
    (l : ℕ → L) (l₀ : L) (hl : Tendsto l atTop (𝓝 l₀))
    (S : ℕ → Matrix a a ℝ) (S₀ : Matrix a a ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hS₀ : S₀.PosSemidef)
    (hlim : Tendsto S atTop (𝓝 S₀)) (F : L × EuclideanSpace ℝ a →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, F (l n, z) ∂multivariateGaussian 0 (S n)) atTop
      (𝓝 (∫ z, F (l₀, z) ∂multivariateGaussian 0 S₀)) := by
  have hrep (x : L) (A : Matrix a a ℝ) :
      (∫ z, F (x, z) ∂multivariateGaussian 0 A) =
        ∫ z : EuclideanSpace ℝ a, F (x, (CFC.sqrt A).toEuclideanLin z) ∂stdGaussian _ := by
    rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop)]
    simp only [zero_add]
    rfl
  simp_rw [hrep]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.comp (continuous_const.prodMk
      (CFC.sqrt (S n)).toEuclideanLin.continuous_of_finiteDimensional)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun z => F.norm_coe_le_norm _)
  · exact ae_of_all _ fun z => F.continuous.tendsto _ |>.comp
      (hl.prodMk_nhds ((cavity_matrix_action_continuous z).tendsto _ |>.comp
        (cavity_sqrt_tendsto S S₀ hS hS₀ hlim)))

lemma cavity_gaussian_joint_test_extension (F : L × EuclideanSpace ℝ a →ᵇ ℝ) :
    ∃ G : L × Matrix a a ℝ →ᵇ ℝ, ∀ l S, S.PosSemidef →
      G (l, S) = ∫ z, F (l, z) ∂multivariateGaussian 0 S := by
  let s : Set (L × Matrix a a ℝ) := {p | p.2.PosSemidef}
  have hs : IsClosed s := Matrix.posSemidef_is_closed.preimage continuous_snd
  let g : s → ℝ := fun p => ∫ z, F (p.1.1, z) ∂multivariateGaussian 0 p.1.2
  have hg : Continuous g := by
    apply continuous_iff_seqContinuous.mpr
    intro p p₀ hp
    exact cavity_gaussian_joint_test_tendsto (fun n => (p n).1.1) p₀.1.1
      ((continuous_fst.comp continuous_subtype_val).tendsto _ |>.comp hp)
      (fun n => (p n).1.2) p₀.1.2 (fun n => (p n).2) p₀.2
      ((continuous_snd.comp continuous_subtype_val).tendsto _ |>.comp hp) F
  have hgb (p : s) : ‖g p‖ ≤ ‖F‖ := by
    have hb := norm_integral_le_of_norm_le_const
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ a) p.1.2)
      (f := fun z => F (p.1.1, z)) (C := ‖F‖)
      (ae_of_all _ fun z => F.norm_coe_le_norm _)
    simpa only [probReal_univ, mul_one] using hb
  let b : s →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g hg ‖F‖ hgb
  obtain ⟨G, _, hG⟩ := b.exists_norm_eq_domRestrict_eq_of_closed hs
  refine ⟨G, fun l S hS => ?_⟩
  exact congrArg (fun f : s →ᵇ ℝ => f ⟨(l, S), hS⟩) hG

theorem cavity_gaussian_joint_expectation_tendsto [MeasurableSpace L] [BorelSpace L]
    (P : ℕ → ProbabilityMeasure (L × Matrix a a ℝ))
    (P₀ : ProbabilityMeasure (L × Matrix a a ℝ))
    (hP : Tendsto P atTop (𝓝 P₀))
    (hS : ∀ n, ∀ᵐ p ∂(P n : Measure (L × Matrix a a ℝ)), p.2.PosSemidef)
    (hS₀ : ∀ᵐ p ∂(P₀ : Measure (L × Matrix a a ℝ)), p.2.PosSemidef)
    (F : L × EuclideanSpace ℝ a →ᵇ ℝ) :
    Tendsto (fun n => ∫ p, ∫ z, F (p.1, z) ∂multivariateGaussian 0 p.2
        ∂(P n : Measure (L × Matrix a a ℝ))) atTop
      (𝓝 (∫ p, ∫ z, F (p.1, z) ∂multivariateGaussian 0 p.2
        ∂(P₀ : Measure (L × Matrix a a ℝ)))) := by
  obtain ⟨G, hG⟩ := cavity_gaussian_joint_test_extension F
  have he (Q : ProbabilityMeasure (L × Matrix a a ℝ))
      (hQ : ∀ᵐ p ∂(Q : Measure (L × Matrix a a ℝ)), p.2.PosSemidef) :
      (∫ p, ∫ z, F (p.1, z) ∂multivariateGaussian 0 p.2
        ∂(Q : Measure (L × Matrix a a ℝ))) = ∫ p, G p ∂(Q : Measure (L × Matrix a a ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hQ] with p hp
    exact (hG p.1 p.2 hp).symm
  simp_rw [he _ hS₀, he _ (hS _)]
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP G

end InvariantIsing

end

end OAI
