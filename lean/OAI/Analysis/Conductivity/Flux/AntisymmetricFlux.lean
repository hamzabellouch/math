import Mathlib
import OAI.Analysis.Conductivity.Branching.CascadeGeometry
import OAI.Analysis.Conductivity.Branching.CascadeStreams

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (f : E → ℝ) (x : E) : ℝ := fderiv ℝ f x v

lemma direction_C1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v : E) : ContDiff ℝ 1 (direction v f) := by
  exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

lemma direction_commute {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v w x : E) :
    direction v (direction w f) x = direction w (direction v f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞)+1≤2 by norm_num)).contDiffAt.differentiableAt (by norm_num)
  unfold direction
  rw [fderiv_clm_apply hd (differentiableAt_const _),fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) v w

lemma direction_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : Differentiable ℝ f) (v x : E) :
    direction v (fun x => -f x) x = -direction v f x := by
  change (fderiv ℝ (-f) x) v = -(fderiv ℝ f x) v
  rw [(hf x).hasFDerivAt.neg.fderiv]
  rfl

theorem antisymmetric_potential_divergence {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (v : ι → E) (S : ι → ι → E → ℝ)
    (hS : ∀ i j, ContDiff ℝ 2 (S i j))
    (ha : ∀ i j, S i j = fun x => -S j i x) (x : E) :
    ∑ i, direction (v i) (fun y => ∑ j, direction (v j) (S i j) y) x = 0 := by
  have hsum (i : ι) :
      direction (v i) (fun y => ∑ j, direction (v j) (S i j) y) x =
      ∑ j, direction (v i) (direction (v j) (S i j)) x := by
    change (fderiv ℝ (fun y => ∑ j, direction (v j) (S i j) y) x) (v i) = _
    rw [fderiv_fun_sum (fun j _ => (direction_C1 (hS i j) (v j)).contDiffAt.differentiableAt (by norm_num))]
    simp [direction]
  simp_rw [hsum]
  have he (i j : ι) : direction (v i) (direction (v j) (S i j)) x =
      -direction (v j) (direction (v i) (S j i)) x := by
    rw [direction_commute (hS i j),ha i j]
    have hn : direction (v i) (fun x => -S j i x) = fun x => -direction (v i) (S j i) x := by
      funext y
      exact direction_neg ((hS j i).differentiable (by norm_num)) _ _
    rw [hn]
    exact direction_neg ((direction_C1 (hS j i) _).differentiable (by norm_num)) _ _
  have heq : (∑ i, ∑ j, direction (v i) (direction (v j) (S i j)) x) =
      -(∑ i, ∑ j, direction (v i) (direction (v j) (S i j)) x) := by
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2,i,2,j]; rw [he]
    simp only [Finset.sum_neg_distrib]
  linarith

lemma boundedSmooth_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    BoundedSmooth (fun _ : E => (0:ℝ)) :=
  BoundedSmooth.of_compact contDiff_const (HasCompactSupport.intro isCompact_empty (fun _ _ => rfl))

lemma geometric_finite_C2 {ι : Type*} [Fintype ι] {f : ι → Coord3 → ℝ}
    (hf : ∀ i, BoundedSmooth (f i)) (select : ℕ → ι)
    {q : ℝ} (hq : 0 ≤ q) (hqsmall : 4*q<1) (A k : ℝ) (center : ℕ → Coord3) :
    ContDiff ℝ 2 (fun x => ∑' j : ℕ, (A*q^j)*f (select j) ((k*2^j) • (x-center j))) := by
  apply geometric_scaled_C2 (fun j => (hf (select j)).1) _ hq hqsmall A k center
  intro n
  choose C hC hb using fun i => (hf i).2 n
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),fun j x => ?_⟩
  exact (hb (select j) x).trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))

def cascadePotentialMother (L K : ℝ) (a b i j : Fin 3) (x : Coord3) : ℝ :=
  ((if i=0 ∧ j=a then cascadeBaseStream L K a x else 0) +
    (if i=a ∧ j=b then cascadeCrossStream L K a b x else 0)) -
  ((if j=0 ∧ i=a then cascadeBaseStream L K a x else 0) +
    (if j=a ∧ i=b then cascadeCrossStream L K a b x else 0))

lemma cascadePotentialMother_antisymm (L K : ℝ) (a b i j : Fin 3) :
    cascadePotentialMother L K a b i j = fun x => -cascadePotentialMother L K a b j i x := by
  funext x
  unfold cascadePotentialMother
  ring

lemma cascadePotentialMother_bounded {L K : ℝ} (hL : 0 < L) (a b i j : Fin 3) :
    BoundedSmooth (cascadePotentialMother L K a b i j) := by
  unfold cascadePotentialMother
  have hb := cascadeBaseStream_bounded (K := K) hL a
  have hc := cascadeCrossStream_bounded (K := K) hL a b
  apply BoundedSmooth.sub <;> apply BoundedSmooth.add
  all_goals split <;> first | exact hb | exact hc | exact boundedSmooth_zero

def cascadePotential (L K k A : ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  ∑' n : ℕ, (A*cascadeRatio L K^n)*
    cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j
      ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n))

lemma cascadePotential_C2 {L K : ℝ} (hL : 1 ≤ L) (hK : 0 < K) (k A : ℝ) (i j : Fin 3) :
    ContDiff ℝ 2 (cascadePotential L K k A i j) := by
  exact geometric_finite_C2
    (f := fun ab : Fin 3 × Fin 3 => cascadePotentialMother L K ab.1 ab.2 i j)
    (fun ab => cascadePotentialMother_bounded (lt_of_lt_of_le (by norm_num) hL) ab.1 ab.2 i j)
    (fun n => (cascadeAxis n,cascadeAxis (n+1)))
    (cascadeRatio_pos L K).le (cascadeRatio_small hL hK) A k
    (cascadeCenter (cascadeLength L K) k)

lemma cascadePotential_antisymm (L K k A : ℝ) (i j : Fin 3) :
    cascadePotential L K k A i j = fun x => -cascadePotential L K k A j i x := by
  funext x
  unfold cascadePotential
  simp_rw [cascadePotentialMother_antisymm L K _ _ i j, mul_neg,tsum_neg]

def cascadeFlux (L K k A : ℝ) (x : Coord3) (i : Fin 3) : ℝ :=
  ∑ j, direction (Pi.single j 1) (cascadePotential L K k A i j) x

lemma cascadeFlux_C1 {L K : ℝ} (hL : 1 ≤ L) (hK : 0 < K) (k A : ℝ) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => cascadeFlux L K k A x i) := by
  apply ContDiff.sum
  intro j _
  exact direction_C1 (cascadePotential_C2 hL hK k A i j) _

theorem cascadeFlux_divergence {L K : ℝ} (hL : 1 ≤ L) (hK : 0 < K) (k A : ℝ) (x : Coord3) :
    ∑ i, direction (Pi.single i 1) (fun y => cascadeFlux L K k A y i) x = 0 :=
  antisymmetric_potential_divergence (fun i => Pi.single i 1) (cascadePotential L K k A)
    (cascadePotential_C2 hL hK k A) (cascadePotential_antisymm L K k A) x

end ScalarConductivity

end

end OAI
