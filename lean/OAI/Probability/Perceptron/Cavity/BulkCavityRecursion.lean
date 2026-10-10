import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityFullEvaluation
import OAI.Probability.Perceptron.Cascade.BulkRPCCoupling

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def roundedCavityPair (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ)
    {K a : ℝ} (ha0 : 0 ≤ a) (haK : a ≤ K) (j : ℕ) :
    Fin ((strictRoundModel (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j).depth+1) → BulkPairRange K :=
  fun i => continuousCavityProfile η B ha0 haK
    (roundTimeValue (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j i)

lemma roundedCavityPair_conditions (n d : ℕ) (η : Measure Time) [IsProbabilityMeasure η]
    {B K a : ℝ} (hB : B < 1) (ha0 : 0 ≤ a) (haK : a ≤ K) (j : ℕ) :
    (∀ i, 0 ≤ cavityPairProfile n d (roundedCavityPair η B ha0 haK j) 0 i) ∧
    (∀ i, Monotone (fun l => cavityPairProfile n d (roundedCavityPair η B ha0 haK j) l i)) ∧
    (∀ i, cavityPairProfile n d (roundedCavityPair η B ha0 haK j)
      (Fin.last _) i ≤ cavityPairDiagonal n d (cavityTrueDiagonal ha0 haK) i) := by
  have h0 := fun l => continuousCavityProfile_nonneg η B ha0 haK
    (roundTimeValue (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j l)
  have hD := fun l => continuousCavityProfile_le_diagonal η B ha0 haK
    (roundTimeValue (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j l)
  refine ⟨?_,?_,?_⟩
  · intro i; cases i with
    | inl i => exact (h0 0).2
    | inr i => exact (h0 0).1
  · intro i; cases i with
    | inl i => exact (continuousCavityProfile_mono η hB ha0 haK).comp (roundTimeValue_mono _ j)
    | inr i => exact fun l m h => roundTimeValue_mono _ j h
  · intro i; cases i with
    | inl i => exact (hD (Fin.last _)).2
    | inr i => exact (hD (Fin.last _)).1

def roundedCavityLog (n d : ℕ) (f : ℝ →ᵇ ℝ) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ) {K a : ℝ}
    (ha0 : 0 ≤ a) (haK : a ≤ K) (j : ℕ) : ℝ :=
  let F := unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let k := (strictRoundModel F j).depth
  let p := roundedCavityPair η B ha0 haK j
  let D := cavityTrueDiagonal ha0 haK
  ∫ y,finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
    (gaussianLinearMarkStep (fun l=>diagonalMark (profileGaussianStep (cavityPairProfile n d p) l))) k
    (stepCumulative (strictRoundModel F j).weight)
    (fun t=>Real.log (cavityDiagonalAverage
      (fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i))
      (cavitySingleTest n d f Λ hΛ) (t 0)))
    (fun _=>diagonalMark (profileGaussianRoot (cavityPairProfile n d p)) y)
    ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))

theorem bulk_cavity_rounded_recursion (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ)
    (hv : ∀ n p,1≤v n p) {C : ℝ} (hC : 0≤C) (hvC : ∀ n p,|v n (p+1)|≤C)
    (hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ→ℕ) (hs : StrictMono s) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n=>((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (ho : Tendsto (fun n=>bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M n+2:ℕ):ℝ)/(n+1:ℕ)*‖g.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hf : Tendsto (fun n=>bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK (s n))) atTop (𝓝 μ)) :
    ∃ a : ℝ, ∃ ha0 : 0 ≤ a, ∃ haK : a ≤ K, a ≤ α*‖g.d1‖^2 ∧
      ∀ n d (Λ : ℝ) (hΛ : 1 ≤ Λ),
      Tendsto (fun j => cavityBulkLog n d (s j) (M (s j)+2) g (v (s j)) Λ hΛ -
        roundedCavityLog n d g.f Λ hΛ (markedTimePair K μ)
          ((α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)) ha0 haK j) atTop (𝓝 0) := by
  obtain ⟨a,ha0,haK,haA,hrpc⟩ := bulk_marked_rpc_coupling M g v hv hC hvC hdO hdF s hs
    α hα hd ν ho K hK0 (fun j => hK (s j)) μ hf
  refine ⟨a,ha0,haK,haA,?_⟩
  intro n d Λ hΛ
  let η := markedTimePair K μ
  let F := unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let B := (α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
  have hA := mul_nonneg hα (sq_nonneg ‖g.d1‖)
  have hB : B < 1 := (div_lt_one (by linarith : 0 < 1+α*‖g.d1‖^2)).mpr (by linarith)
  have hp j := roundedCavityPair_conditions n d η hB ha0 haK j
  exact cavity_joint_array_recursion_limit n d (fun m => M m+2) g v Λ hΛ K hK s hf
    (fun j => (strictRoundModel F j).depth) (roundedCavityPair η B ha0 haK)
    (fun _ => cavityTrueDiagonal ha0 haK) (fun j => stepCumulative (strictRoundModel F j).weight)
    (fun j => (hp j).1) (fun j => (hp j).2.1) (fun j => (hp j).2.2)
    (fun j => stepCumulative_strictMono _ (strictRoundModel F j).weight_pos)
    (fun j => stepCumulative_pos _ (strictRoundModel F j).weight_pos)
    (fun j => stepCumulative_lt_one _ (strictRoundModel F j).weight_pos (strictRoundModel F j).weight_sum) hrpc



def roundedCavityValue (n d : ℕ) (g : Jet3) (P : Measure BrownianPath)
    (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ) {K a : ℝ}
    (ha0 : 0≤a) (haK : a≤K) (j : ℕ) : ℝ :=
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let M:=strictRoundModel F j
  (n+1:ℕ)*(a/2+finiteSphericalFieldValue n M.depth M.weight
    (fun l=>(roundedCavityPair η B ha0 haK j l).2.val/2))+
    d*controlValue P g.f (weightedStepTrial M.weight (roundTimeValue F j)
      (fun l=>(M.weight_pos l).le) M.weight_sum)

theorem roundedCavity_uncap (n d : ℕ) (g : Jet3) (P : Measure BrownianPath)
    [IsProbabilityMeasure P] (hBrow : IsBrownianReal brownianEval P)
    (η : Measure Time) [IsProbabilityMeasure η] {B K a : ℝ} (hB : B<1)
    (ha0 : 0≤a) (haK : a≤K) (j : ℕ) {Λ : ℝ} (hΛ : 1≤Λ) :
    0≤roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j ∧
    roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j≤
      Real.exp (2*((d:ℝ)*‖g.f‖))/Λ*Real.exp (2*(n+1:ℕ)*a) := by
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let M:=strictRoundModel F j
  let p:=roundedCavityPair η B ha0 haK j
  let D:=cavityTrueDiagonal ha0 haK
  let Q:=cavityPairProfile n d p
  let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-Q (Fin.last M.depth) i)
  let z:=stepCumulative M.weight
  have hp:=roundedCavityPair_conditions n d η hB ha0 haK j
  have hfull:=cavityLabel_full_value n d p D hp.1 hp.2.1 hp.2.2
    (roundTimeValue F j) (fun l=>rfl) rfl M.weight M.weight_pos M.weight_sum
    (roundTimeValue_mono F j) g P hBrow
  have hcap:=cavityLabelPartitionLaw_log_recursion n d M.depth g.f Λ hΛ σ Q z
    (stepCumulative_strictMono M.weight M.weight_pos)
    (stepCumulative_pos M.weight M.weight_pos)
    (stepCumulative_lt_one M.weight M.weight_pos M.weight_sum)
  rw [cavityLabelPartitionLaw_integral _ _ _ _ _ _ _ _ _ Real.log Real.measurable_log] at hcap
  have he:=cavityLabel_uncap_annealed n d p D hp.1 hp.2.1 hp.2.2 g.f z hΛ
  have hi:=cavityLabel_full_log_integrable n d p D hp.1 hp.2.1 hp.2.2 g.f z
  have hc:=cavityLabel_capped_log_integrable n d M.depth g.f Λ hΛ σ Q z
  have hint : (∫ t,Real.log (cavityLabelFullPartition n d M.depth g.f σ Q t)-
      Real.log (cavityLabelPartition n d M.depth g.f Λ hΛ σ Q t)
      ∂(indexedCascadeBaseLaw M.depth z : Measure (IndexedCascadeBase M.depth)).prod countableGaussianLaw)=
      roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j := by
    rw [integral_sub hi hc,hfull,hcap]
    rfl
  change _ ∧ _ at he
  exact ⟨by rw [←hint]; exact he.2.1,by rw [←hint]; exact he.2.2⟩
end SphericalPerceptronFreeEnergy

end

end OAI
