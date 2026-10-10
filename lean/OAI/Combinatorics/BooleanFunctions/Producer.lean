import OAI.Combinatorics.BooleanFunctions.Rounding
import OAI.Combinatorics.BooleanFunctions.FiniteCLT

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Producer
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT MomentTransfer GaussianGain
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem normalized_moments_tendsto (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) (k : Fin 3) :
    Tendsto (fun n => ∫ x, (normalizedSum T n x)^(k:ℕ) ∂uniformMeasure (Fin n → α)) atTop
      (𝓝 (∫ x : ℝ, x^(k:ℕ) ∂gaussianReal 0 1)) := by
  fin_cases k
  · simp only [pow_zero,integral_const,probReal_univ,one_smul]
    exact tendsto_const_nhds
  · simp only [pow_one,integral_uniform,average_normalizedSum T h0,
      integral_id_gaussianReal]
    exact tendsto_const_nhds
  · change Tendsto (fun n => ∫ x, (normalizedSum T n x)^2 ∂uniformMeasure (Fin n → α)) atTop
      (𝓝 (∫ x : ℝ, x^2 ∂gaussianReal 0 1))
    rw [gaussian_sq_integral]
    have he : (fun n => ∫ x, (normalizedSum T n x)^2 ∂uniformMeasure (Fin n → α)) =ᶠ[atTop]
        (fun _ => (1:ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [integral_uniform,average_normalizedSum_sq T h0 h1 hn]
    exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem exists_soft_gain (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    ∃ n : ℕ, 0 < n ∧
      (∀ i : Leaves, 0 < average (fun x => leafTest i (normalizedSum T n x))) ∧
      eta < SoftEvent.deficit (normalizedSum T n)
        ((∑ i, means (SoftEvent.rawMoments (normalizedSum T n)
          (fun i x => leafTest i (normalizedSum T n x))) i)-1)
        (SoftEvent.softWeight (fun i x => selectorTest i (normalizedSum T n x))
          (fun i x => leafTest i (normalizedSum T n x))) := by
  have hc := uniform_clt T h0 h1
  have hp := eventually_positive_gain (fun n => uniformMeasure (Fin n → α))
    (normalizedSum T) (fun n => measurable_of_finite _) hc
    (fun n k => Integrable.of_finite) (normalized_moments_tendsto T h0 h1)
  obtain ⟨n,hn,hp⟩ := ((eventually_gt_atTop 0).and hp).exists
  have hl (i : Leaves) : 0 < average (fun x => leafTest i (normalizedSum T n x)) := by
    simpa only [moments,Fin.val_zero,pow_zero,mul_one,integral_uniform] using hp.1 i
  refine ⟨n,hn,hl,?_⟩
  have hs := SoftEvent.soft_deficit_eq_gain
    (fun i x => selectorTest i (normalizedSum T n x))
    (fun i x => leafTest i (normalizedSum T n x)) (fun i => (hl i).ne')
    (normalizedSum T n) (average_normalizedSum T h0 n) (average_normalizedSum_sq T h0 h1 hn)
  rw [hs]
  have he : (moments (uniformMeasure (Fin n → α)) (normalizedSum T n) leafTest) =
      SoftEvent.rawMoments (normalizedSum T n) (fun i x => leafTest i (normalizedSum T n x)) := by
    funext k i
    exact integral_uniform _
  have he' : (moments (uniformMeasure (Fin n → α)) (normalizedSum T n) selectorTest) =
      SoftEvent.rawMoments (normalizedSum T n) (fun i x => selectorTest i (normalizedSum T n x)) := by
    funext k i
    exact integral_uniform _
  rw [he,he'] at hp
  convert hp.2 using 1
  congr 1


theorem exists_table_gain [Fintype β] (F : α → β) (t : β → ℝ)
    (h0 : average (fun a => t (F a)) = 0)
    (h1 : average (fun a => (t (F a))^2) = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ b : ℝ, ∃ S : (Fin n → β) → Leaves,
      ∃ L : Leaves → (Fin n → β) → Bool,
      eta < SoftEvent.deficit (normalizedSum (fun a => t (F a)) n) b
        (fun x => if TableRounding.tableEvent S L
          ((fun j => F (x.1 j)),fun i j => F (x.2 i j)) then 1 else 0) := by
  obtain ⟨n,hn,_,hg⟩ := exists_soft_gain (fun a => t (F a)) h0 h1
  let b := (∑ i, means (SoftEvent.rawMoments (normalizedSum (fun a => t (F a)) n)
          (fun i x => leafTest i (normalizedSum (fun a => t (F a)) n x))) i)-1
  have he (x : Fin n → α) : normalizedSum t n (fun j => F (x j)) =
      normalizedSum (fun a => t (F a)) n x := rfl
  obtain ⟨S,L,hSL⟩ := TableRounding.exists_event_deficit
    (fun (i : Leaves) (y : Fin n → β) => selectorTest i (normalizedSum t n y))
    (fun (i : Leaves) (y : Fin n → β) => leafTest i (normalizedSum t n y))
    (fun y => SmoothSelector.weight_sum gridN step (normalizedSum t n y))
    (fun i y => SmoothSelector.weight_nonneg gridN step i (normalizedSum t n y))
    (fun i y => SmoothGaussian.tent_nonneg _ _ _)
    (fun i y => SmoothGaussian.tent_le_one width_pos _ _)
    (fun x : Fin n → α => fun j => F (x j))
    (normalizedSum (fun a => t (F a)) n) b eta (by simpa only [he] using hg)
  exact ⟨n,hn,b,S,L,hSL⟩

end Producer
end SquareRootDegree

end

end OAI
