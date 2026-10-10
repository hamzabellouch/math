import OAI.Probability.PosteriorReplicas.Geometry.FrameTubes

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma replica_integral_of_affine_moment {ν : Measure E} [IsFiniteMeasure ν]
    (m n : ℕ) (p : E) (C : ℝ≥0∞)
    (hmoment : ∀ L : AffineSubspace ℝ E, ∀ (_ : Nonempty L),
      Module.finrank ℝ L.direction < n →
      ∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ m) ∂ν ≤ C) :
    ∫⁻ v : Fin n → E, PosteriorRegression.replicaWeight m p v ∂Measure.pi (fun _ => ν) ≤ C^n := by
  induction n with
  | zero => simp [PosteriorRegression.replicaWeight]
  | succ n ih =>
    have hinner (v : Fin n → E) :
        ∫⁻ x, PosteriorRegression.replicaWeight m p (Fin.snoc v x) ∂ν ≤
          PosteriorRegression.replicaWeight m p v * C := by
      simp_rw [PosteriorRegression.replicaWeight_snoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      gcongr
      apply hmoment _ inferInstance
      rw [AffineSubspace.direction_mk']
      have hdim := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simpa only [AffineSubspace.direction_mk', Fintype.card_fin, Nat.lt_succ_iff, Set.finrank] using hdim
    calc
      _ = ∫⁻ v : Fin n → E, ∫⁻ x, PosteriorRegression.replicaWeight m p (Fin.snoc v x) ∂ν
          ∂Measure.pi (fun _ => ν) := PosteriorRegression.lintegral_pi_snoc ν _
            (PosteriorRegression.measurable_replicaWeight m p (n+1))
      _ ≤ ∫⁻ v : Fin n → E, PosteriorRegression.replicaWeight m p v * C
          ∂Measure.pi (fun _ => ν) := lintegral_mono hinner
      _ = (∫⁻ v : Fin n → E, PosteriorRegression.replicaWeight m p v
          ∂Measure.pi (fun _ => ν)) * C := lintegral_mul_const _
            (PosteriorRegression.measurable_replicaWeight m p n)
      _ ≤ C^n * C := mul_le_mul' (ih (fun L hL hdim => hmoment L hL (by omega))) le_rfl
      _ = _ := (pow_succ _ _).symm

lemma ae_replica_independent_of_affine_null {ν : Measure E} [IsFiniteMeasure ν]
    (p : E) (n : ℕ)
    (hnull : ∀ L : AffineSubspace ℝ E, ∀ (_ : Nonempty L),
      Module.finrank ℝ L.direction < n → ν L = 0) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), LinearIndependent ℝ (fun j => v j - p) := by
  suffices h : ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0 by
    filter_upwards [h] with v hv
    apply Matrix.linearIndependent_of_det_gram_ne_zero
    rw [PosteriorRegression.det_gram_eq_prod_gramSchmidt]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ n ih =>
    rw [PosteriorRegression.ae_pi_snoc ν (PosteriorRegression.measurableSet_gramSchmidt_ne_zero p (n+1))]
    filter_upwards [ih (fun L hL hdim => hnull L hL (by omega))] with v hv
    let L := AffineSubspace.mk' p (Submodule.span ℝ (Set.range (fun i : Fin n => v i - p)))
    have hdim : Module.finrank ℝ L.direction < n + 1 := by
      dsimp only [L]
      rw [AffineSubspace.direction_mk']
      have hh := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simpa only [Fintype.card_fin, Nat.lt_succ_iff, Set.finrank] using hh
    have ha : ∀ᵐ x ∂ν, x ∉ L := by
      rw [ae_iff]
      simpa using hnull L inferInstance hdim
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [PosteriorRegression.norm_gramSchmidt_sub_eq_affine_infDist, PosteriorRegression.image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((L.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨p, AffineSubspace.self_mem_mk' _ _⟩).mp hx)
    | cast j => simpa only [PosteriorRegression.gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

end Generic

lemma base_affine_null {d : ℕ} (hd : 3 ≤ d) (base : BaseLaw)
    (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    (hL : Module.finrank ℝ L.direction < d) : (base.measure d) L = 0 := by
  let C := ENNReal.ofReal (baseProjectionConstant base d 1) * 2
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hb (n : ℕ) : (base.measure d) L ≤ C * ENNReal.ofReal ((1/2 : ℝ)^n) := by
    calc
      _ ≤ (base.measure d) {x | Metric.infDist x L ≤ (1/2 : ℝ)^n} := by
        apply measure_mono
        intro x hx
        simp only [Set.mem_ofPred_eq, Metric.infDist_zero_of_mem hx]
        positivity
      _ ≤ _ := by simpa [C] using base_affine_tube hd base L (by omega) (r := (1/2 : ℝ)^n) (by positivity)
  have hlim : Tendsto (fun n : ℕ => C * ENNReal.ofReal ((1/2 : ℝ)^n)) atTop (nhds 0) := by
    have h := ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1))
    simpa using ENNReal.Tendsto.const_mul h (Or.inr hC)
  exact le_antisymm (ge_of_tendsto' hlim hb) bot_le

lemma base_affine_inverse_bound {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hm : 1 ≤ m) (base : BaseLaw) (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    (hL : Module.finrank ℝ L.direction < m) :
    ∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ k) ∂base.measure d ≤
      1 + (ENNReal.ofReal (baseProjectionConstant base d (k+1)) * 2^(k+1)) * 2^(k+1) := by
  let : NeZero d := ⟨by omega⟩
  have h := PosteriorRegression.inverse_moment_of_tube_bound (base.measure d)
    (fun x => Metric.infDist x L) k (Metric.continuous_infDist_pt _).measurable
    (fun _ => Metric.infDist_nonneg)
    (ENNReal.ofReal (baseProjectionConstant base d (k+1)) * 2^(k+1))
    (fun r hr _ => base_affine_tube (by omega) base L (by omega) hr)
  simpa only [measure_univ] using h

lemma base_replica_inverse_finite {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hm : 1 ≤ m) (base : BaseLaw) (p : Vec d) :
    (∫⁻ v : Fin m → Vec d, ENNReal.ofReal
      ((Real.sqrt (Matrix.gram ℝ (fun j => v j - p)).det)⁻¹ ^ k)
        ∂Measure.pi (fun _ => base.measure d)) < ∞ := by
  let : NeZero d := ⟨by omega⟩
  let C : ℝ≥0∞ := 1 + (ENNReal.ofReal (baseProjectionConstant base d (k+1)) * 2^(k+1)) * 2^(k+1)
  have h := replica_integral_of_affine_moment k m p C
    (fun L _ hL => base_affine_inverse_bound hd hm base L hL)
  simp only [PosteriorRegression.replicaWeight_eq_det] at h
  exact lt_of_le_of_lt h (by dsimp [C]; finiteness)

end PosteriorReplicas
end

end OAI
