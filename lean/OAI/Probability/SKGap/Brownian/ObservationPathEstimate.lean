import Mathlib
import OAI.Probability.SKGap.Brownian.BrownianMesh
import OAI.Probability.SKGap.Localization.FixedTimeQuenched

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open MeasureTheory ProbabilityTheory Real Set SKGap.PathBridge Matrix
open scoped BigOperators ENNReal NNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0→Ω→ℝ} {n : ℕ}

lemma brownian_fixed_time_probability (hB : IsBrownianReal B P)
    (j A K ε c ρ : ℝ) (t : ℝ≥0) (σ : Spin n) (J : Disorder n) :
    (Measure.pi (fun _ : Fin n=>P)).real
      {ω | (coupling J,observationField B σ t ω)∈literalBadPair j A K ε c ρ} =
        (conditionalSpinFailure j A K ε c ρ (t:ℝ) σ J).toReal := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm := (hB.hasLaw_eval t).aemeasurable
  have hp := Measure.pi_map_pi (ι:=Fin n) (fun _=>hm)
  simp_rw [(hB.hasLaw_eval t).map_eq] at hp
  have ha : AEMeasurable (fun ω : Fin n→Ω=>fun i=>B t (ω i)) (Measure.pi (fun _ : Fin n=>P)) :=
    AEMeasurable.of_eval (fun i=>hm.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i))
  have hs := (measurableSet_gibbsObservationBad j A K ε c ρ (t:ℝ) σ).preimage
    (measurable_const.prodMk measurable_id : Measurable (Prod.mk J))
  have hh := map_measureReal_apply_of_aemeasurable ha hs
  rw [hp] at hh
  unfold observationField conditionalSpinFailure
  rw [Real.toNNReal_coe]
  exact hh.symm

def conditionalPathFailure (P : Measure Ω) (B : ℝ≥0→Ω→ℝ)
    (j A K ε c ρ T : ℝ) (σ : Spin n) (J : Disorder n) : ℝ :=
  (Measure.pi (fun _ : Fin n=>P)).real
    {ω | operatorBound K (coupling J) ∧ ∃ t : ℝ≥0,(t:ℝ)≤T ∧
      rootBad j A ε c ρ (coupling J) (observationField B σ t ω)}

def pathFailure (P : Measure Ω) (B : ℝ≥0→Ω→ℝ)
    (j A K ε c ρ T : ℝ) (J : Disorder n) : ℝ :=
  ∑ σ : Spin n,mass J 0 σ*conditionalPathFailure P B j A K ε c ρ T σ J

def meshCertificate (n m : ℕ) (δ : ℝ≥0) (j A K ε c ρ : ℝ) (J : Disorder n) : ℝ :=
  (∑ k : Fin m,fixedTimeFailure n j A K ε c ρ ((k:ℝ)*(δ:ℝ)) J)+(m:ℝ)*exp (-(n:ℝ))

lemma measurable_meshCertificate (n m : ℕ) (δ : ℝ≥0) (j A K ε c ρ : ℝ) :
    Measurable (meshCertificate n m δ j A K ε c ρ) := by
  unfold meshCertificate
  exact (Finset.measurable_sum _ (fun k _=>measurable_fixedTimeFailure _ _ _ _ _ _ _ _)).add_const _

lemma meshCertificate_nonneg (n m : ℕ) (δ : ℝ≥0) (j A K ε c ρ : ℝ) (J : Disorder n) :
    0 ≤ meshCertificate n m δ j A K ε c ρ J := by
  unfold meshCertificate
  exact add_nonneg (Finset.sum_nonneg (fun _ _=>fixedTimeFailure_nonneg _ _ _ _ _ _ _ _ _)) (by positivity)

lemma fixedTimeFailure_as_sum (j A K ε c ρ t : ℝ) (J : Disorder n) :
    fixedTimeFailure n j A K ε c ρ t J =
      ∑ σ : Spin n,mass J 0 σ*(conditionalSpinFailure j A K ε c ρ t σ J).toReal := by
  unfold fixedTimeFailure fixedTimeFailureENN
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro σ _
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (mass_nonneg J 0 σ)]
  · intro σ _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top (conditionalSpinFailure_le_one j A K ε c ρ t σ J))

theorem observation_path_certificate {T ρ : ℝ} (hT : 0<T) (hρ : 0<ρ)
    (hB : IsBrownianReal B P) :
    ∃ m : ℕ, 0 < m ∧ ∃ δ : ℝ≥0, 0<δ ∧ (m:ℝ)*(δ:ℝ)=T ∧
      (∀ k : Fin m,(k:ℝ)*(δ:ℝ)∈Icc 0 T) ∧
      ∀ n,∀ j A K ε c : ℝ,∀ J : Disorder n,
        pathFailure P B j A K ε c (ρ/2) T J ≤ meshCertificate n m δ j A K ε c ρ J := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨m,hm,δ,hδ,he,hk,hprob,hinc⟩ := observation_root_mesh_inclusion hT hρ hB
  refine ⟨m,hm,δ,hδ,he,hk,fun n j A K ε c J=>?_⟩
  have hσ (σ : Spin n) : conditionalPathFailure P B j A K ε c (ρ/2) T σ J ≤
      (∑ k : Fin m,(conditionalSpinFailure j A K ε c ρ ((k:ℝ)*(δ:ℝ)) σ J).toReal)+
        (m:ℝ)*exp (-(n:ℝ)) := by
    have hp := measureReal_mono (hinc n j A K ε c (coupling J) σ) (measure_ne_top (Measure.pi (fun _ : Fin n=>P)) _)
    apply hp.trans
    apply (measureReal_union_le _ _).trans
    have hh := measureReal_iUnion_fintype_le (μ:=Measure.pi (fun _ : Fin n=>P))
      (fun k : Fin m=>{ω | (coupling J,observationField B σ ((k:ℝ≥0)*δ) ω)∈literalBadPair j A K ε c ρ})
    have hr (k : Fin m) := brownian_fixed_time_probability hB j A K ε c ρ ((k:ℝ≥0)*δ) σ J
    simp only [NNReal.coe_mul,NNReal.coe_natCast] at hr
    apply (add_le_add (hprob n) hh).trans_eq
    simp_rw [hr]
    ring
  unfold pathFailure meshCertificate
  calc
    _ ≤ ∑ σ : Spin n,mass J 0 σ*((∑ k : Fin m,
        (conditionalSpinFailure j A K ε c ρ ((k:ℝ)*(δ:ℝ)) σ J).toReal)+(m:ℝ)*exp (-(n:ℝ))) :=
      Finset.sum_le_sum (fun σ _=>mul_le_mul_of_nonneg_left (hσ σ) (mass_nonneg J 0 σ))
    _ = _ := by
      simp_rw [mul_add,Finset.mul_sum]
      rw [Finset.sum_add_distrib,Finset.sum_comm,← Finset.sum_mul,sum_mass,one_mul]
      simp_rw [fixedTimeFailure_as_sum]
end SKGap.ObservationBridge

end
end

section

noncomputable section
namespace SKGap.ObservationBridge
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal Topology

lemma partitionSizeBias_integral (β : ℝ) (n : ℕ) :
    (∫ J : Disorder n,partitionSizeBias β n J ∂disorderLaw β n)=1 := by
  unfold partitionSizeBias
  rw [integral_div]
  apply div_self
  rw [disorder_partition_mean]
  exact (gaussianSpinPartition_mean_pos (by positivity)).ne'

lemma weighted_meshCertificate_integrable (β : ℝ) (n m : ℕ) (δ : ℝ≥0) (j A K ε c ρ : ℝ) :
    Integrable (fun J=>partitionSizeBias β n J*meshCertificate n m δ j A K ε c ρ J)
      (disorderLaw β n) := by
  simp_rw [meshCertificate,mul_add,Finset.mul_sum]
  exact (integrable_finsetSum _ (fun k _=>weighted_fixedTimeFailure_integrable β n j A K ε c ρ _)).add
    ((partitionSizeBias_integrable β n).mul_const _)

lemma weighted_meshCertificate_integral (β : ℝ) (n m : ℕ) (δ : ℝ≥0) (j A K ε c ρ : ℝ) :
    (∫ J : Disorder n,partitionSizeBias β n J*meshCertificate n m δ j A K ε c ρ J ∂disorderLaw β n)=
      (∑ k : Fin m,∫ J : Disorder n,partitionSizeBias β n J*
        fixedTimeFailure n j A K ε c ρ ((k:ℝ)*(δ:ℝ)) J ∂disorderLaw β n)+(m:ℝ)*exp (-(n:ℝ)) := by
  simp_rw [meshCertificate,mul_add,Finset.mul_sum]
  rw [integral_add (integrable_finsetSum _ (fun k _=>weighted_fixedTimeFailure_integrable β n j A K ε c ρ _))
    ((partitionSizeBias_integrable β n).mul_const _)]
  rw [integral_finsetSum _ (fun k _=>weighted_fixedTimeFailure_integrable β n j A K ε c ρ _),
    integral_mul_const,partitionSizeBias_integral,one_mul]

theorem quenched_observation_path_stability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0→Ω→ℝ}
    (hB : IsBrownianReal B P) {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
    ∃ A K ε c ρ a : ℝ, 1<A ∧ 2*β<K ∧ β*A<1 ∧
      0<ε ∧ 0<c ∧ 0<ρ ∧ 0<a ∧
      ∃ V : (n : ℕ)→Disorder n→ℝ,
        (∀ n,Measurable (V n)) ∧ (∀ n J,0≤V n J) ∧
        (∀ n J,pathFailure P B (β^2) A K ε c ρ T J ≤ V n J) ∧
        Tendsto (fun n=>(disorderLaw β n).real {J | exp (-a*(n:ℝ)) < V n J}) atTop (𝓝 0) := by
  obtain ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,N,hN,hann⟩ :=
    annealed_fixed_time_root_stability hβ hβ1 hT
  obtain ⟨m,hm,δ,hδ,he,hk,hpath⟩ := observation_path_certificate hT hρ hB
  let b := min a 1
  have hb : 0<b := lt_min ha zero_lt_one
  refine ⟨A,K,ε,c,ρ/2,b/4,hA,hK,hsub,hε,hc,half_pos hρ,by positivity,
    (fun n=>meshCertificate n m δ (β^2) A K ε c ρ),
    (fun n=>measurable_meshCertificate _ _ _ _ _ _ _ _ _),
    (fun n J=>meshCertificate_nonneg _ _ _ _ _ _ _ _ _ _),
    (fun n J=>hpath n (β^2) A K ε c J),?_⟩
  apply exponential_size_bias_transfer (C:=2*(m:ℝ)) (disorderLaw β) (partitionSizeBias β)
    (fun n=>meshCertificate n m δ (β^2) A K ε c ρ)
    (fun n J=>(partitionSizeBias_pos β n J).le)
    (fun n J=>meshCertificate_nonneg _ _ _ _ _ _ _ _ _ _)
    (fun n=>weighted_meshCertificate_integrable _ _ _ _ _ _ _ _ _ _) hb (by positivity)
  · exact disorder_partition_lower_tail hβ hβ1 (by positivity)
  · filter_upwards [eventually_ge_atTop N] with n hn
    rw [weighted_meshCertificate_integral]
    have ha' : exp (-a*(n:ℝ)) ≤ exp (-b*(n:ℝ)) := by
      apply exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (Nat.cast_nonneg n)
    have h1' : exp (-(n:ℝ)) ≤ exp (-b*(n:ℝ)) := by
      apply exp_le_exp.mpr
      have hb1 : b≤1 := min_le_right _ _
      nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    calc
      _ ≤ (∑ _k : Fin m,exp (-b*(n:ℝ)))+(m:ℝ)*exp (-b*(n:ℝ)) := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro k _
          exact (weighted_fixedTimeFailure_integral_bound β n A K ε c ρ ((k:ℝ)*(δ:ℝ)) _
            (exp_pos _).le (hann n hn _ (hk k))).trans ha'
        · exact mul_le_mul_of_nonneg_left h1' (Nat.cast_nonneg m)
      _ = _ := by simp;ring
end SKGap.ObservationBridge

end
end

end OAI
