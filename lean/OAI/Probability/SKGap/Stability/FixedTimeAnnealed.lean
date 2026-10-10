import Mathlib
import OAI.Probability.SKGap.Localization.PlantedTilt
import OAI.Probability.SKGap.Localization.PlantedMarginalLaw

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
local instance annealedMatrixMeasurable : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
local instance annealedMatrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

def gibbsObservationBad (j A K ε c ρ t : ℝ) (s : Spin n) : Set (Disorder n × Field n) :=
  {p | (coupling p.1,(fun i=>t*spinValue (s i)+p.2 i))∈literalBadPair j A K ε c ρ}

lemma measurableSet_gibbsObservationBad (j A K ε c ρ t : ℝ) (s : Spin n) :
    MeasurableSet (gibbsObservationBad j A K ε c ρ t s) := by
  have hmap : Continuous (fun p : Disorder n × Field n=>
      (coupling p.1,(fun i=>t*spinValue (s i)+p.2 i)) :
      Disorder n × Field n→Matrix (Fin n) (Fin n) ℝ × Field n) :=
    (continuous_coupling.comp continuous_fst).prodMk (by fun_prop)
  have hmmap : Measurable (fun p : Disorder n × Field n=>
      (coupling p.1,(fun i=>t*spinValue (s i)+p.2 i)) :
      Disorder n × Field n→Matrix (Fin n) (Fin n) ℝ × Field n) := hmap.measurable
  exact (measurableSet_literalBadPair j A K ε c ρ).preimage hmmap

def conditionalSpinFailure (j A K ε c ρ t : ℝ) (s : Spin n) (J : Disorder n) : ℝ≥0∞ :=
  (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))
    ((Prod.mk J) ⁻¹' gibbsObservationBad j A K ε c ρ t s)

lemma measurable_conditionalSpinFailure (j A K ε c ρ t : ℝ) (s : Spin n) :
    Measurable (conditionalSpinFailure j A K ε c ρ t s) :=
  measurable_measure_prodMk_left (measurableSet_gibbsObservationBad j A K ε c ρ t s)
lemma conditionalSpinFailure_le_one (j A K ε c ρ t : ℝ) (s : Spin n) (J : Disorder n) :
    conditionalSpinFailure j A K ε c ρ t s J ≤ 1 := prob_le_one

def fixedTimeFailureENN (j A K ε c ρ t : ℝ) (J : Disorder n) : ℝ≥0∞ :=
  ∑ s : Spin n, ENNReal.ofReal (mass J 0 s)*conditionalSpinFailure j A K ε c ρ t s J

lemma measurable_fixedTimeFailureENN (j A K ε c ρ t : ℝ) :
    Measurable (fixedTimeFailureENN (n:=n) j A K ε c ρ t) := by
  apply Finset.measurable_sum
  intro s _
  have hm : Measurable (fun J : Disorder n=>mass J 0 s) := by
    simpa only [sqrt_one,one_mul] using scaled_spin_mass_measurable 1 s
  exact hm.ennreal_ofReal.mul (measurable_conditionalSpinFailure j A K ε c ρ t s)

lemma fixedTimeFailureENN_le_one (j A K ε c ρ t : ℝ) (J : Disorder n) :
    fixedTimeFailureENN j A K ε c ρ t J ≤ 1 := by
  calc
    _ ≤ ∑ s : Spin n, ENNReal.ofReal (mass J 0 s)*1 :=
      Finset.sum_le_sum (fun s _=>mul_le_mul_right (conditionalSpinFailure_le_one j A K ε c ρ t s J) _)
    _ = 1 := by
      simp only [mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun s _=>mass_nonneg J 0 s),sum_mass,ENNReal.ofReal_one]

lemma planted_spin_failure_integral (s : Spin n) (r j A K ε c ρ t : ℝ) :
    (∫⁻ g : Disorder n,conditionalSpinFailure j A K ε c ρ t s (plantedEdges r s g)
      ∂gaussianCoordinates (Edge n)) =
    ((gaussianCoordinates (Edge n)).prod (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      {p | (coupling (plusPlantedEdges r p.1),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ} := by
  let E := (Prod.map (plantedEdges r s) id) ⁻¹' gibbsObservationBad j A K ε c ρ t s
  have hE : MeasurableSet E := (measurableSet_gibbsObservationBad j A K ε c ρ t s).preimage
    ((show Measurable (plantedEdges r s) by unfold plantedEdges;fun_prop).prodMap measurable_id)
  have he := Measure.prod_apply (μ:=gaussianCoordinates (Edge n))
      (ν:=Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)) hE
  exact he.symm.trans (gauged_fixed_time_probability s r j A K ε c ρ t)

theorem fixed_time_size_bias_identity (β A K ε c ρ t : ℝ) :
    (∫⁻ J : Disorder n,
      ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
        fixedTimeFailureENN (β^2) A K ε c ρ t J ∂disorderLaw β n) =
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      (erasedPlantedRootBad n (β^2) A K ε c ρ t) := by
  rw [show fixedTimeFailureENN (n:=n) (β^2) A K ε c ρ t =
    (fun J=>∑ s,ENNReal.ofReal (mass J 0 s)*conditionalSpinFailure (β^2) A K ε c ρ t s J) from rfl]
  rw [planted_disorder_joint_tilt β _ (fun s=>measurable_conditionalSpinFailure (β^2) A K ε c ρ t s)]
  have he (s : Spin n) :
    (∫⁻ g : Disorder n,conditionalSpinFailure (β^2) A K ε c ρ t s
      (fun e=>sqrt (β^2/(n:ℝ))*g e+β^2/(n:ℝ)*spinValue (s e.1.1)*spinValue (s e.1.2))
      ∂gaussianCoordinates (Edge n)) =
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      (erasedPlantedRootBad n (β^2) A K ε c ρ t) :=
    (planted_spin_failure_integral s _ _ _ _ _ _ _ _).trans
      (plus_planted_marginal_probability (sq_nonneg β) A K ε c ρ t)
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc]
  have hc : (Fintype.card (Spin n):ℝ) ≠ 0 := by positivity
  have hh : ENNReal.ofReal (1/(Fintype.card (Spin n):ℝ))*(Fintype.card (Spin n):ℝ≥0∞)=1 := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity : (0:ℝ)≤1/(Fintype.card (Spin n):ℝ))]
    simp
  rw [hh,one_mul]

theorem annealed_fixed_time_root_stability {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
    ∃ A K ε c ρ a : ℝ, 1<A ∧ 2*β<K ∧ β*A<1 ∧
      0<ε ∧ 0<c ∧ 0<ρ ∧ 0<a ∧ ∃ N : ℕ, 0<N ∧ ∀ n≥N, ∀ t∈Icc 0 T,
      (∫⁻ J : Disorder n,
        ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
          fixedTimeFailureENN (β^2) A K ε c ρ t J ∂disorderLaw β n) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,N,hN,hp⟩ :=
    zero_diagonal_fixed_time_root_stability (sq_pos_of_pos hβ) (by nlinarith : β^2<1) hT
  rw [sqrt_sq hβ.le] at hK hsub
  refine ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,N,hN,?_⟩
  intro n hn t ht
  rw [fixed_time_size_bias_identity,← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hp n hn t ht)
end SKGap.ObservationBridge

end
end

end OAI
