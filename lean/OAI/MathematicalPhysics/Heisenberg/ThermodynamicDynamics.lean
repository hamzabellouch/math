import OAI.MathematicalPhysics.Heisenberg.LocalDynamics

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace IsometricLimits
variable {E : Type*} [MetricSpace E] [CompleteSpace E]

theorem limit_on_dense (F : ℕ → E → E) (hF : ∀ n, Isometry (F n))
    (s : Set E) (hs : Dense s)
    (hlim : ∀ x ∈ s, ∃ y, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds y)) :
    ∀ x, ∃ y, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds y) := by
  intro x
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨a, ha, hax⟩ := hs.exists_dist_lt x (by linarith : 0 < ε/3)
  obtain ⟨b, hb⟩ := hlim a ha
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hb.cauchySeq (ε/3) (by linarith)
  refine ⟨N, fun n hn m hm => ?_⟩
  calc
    dist (F n x) (F m x) ≤ dist (F n x) (F n a) + dist (F n a) (F m a) +
        dist (F m a) (F m x) := dist_triangle4 _ _ _ _
    _ = dist x a + dist (F n a) (F m a) + dist a x := by
      rw [(hF n).dist_eq, (hF m).dist_eq]
    _ < ε := by have := hN n hn m hm; rw [dist_comm a x]; linarith

omit [CompleteSpace E] in

theorem limit_iterate (F : ℕ → E → E) (f : E → E) (hF : ∀ n, Isometry (F n))
    (hlim : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (k : ℕ) (x : E) :
    Filter.Tendsto (fun n => (F n)^[k] x) Filter.atTop (nhds (f^[k] x)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum := (tendsto_iff_dist_tendsto_zero.mp ih).add
      (tendsto_iff_dist_tendsto_zero.mp (hlim (f^[k] x)))
    rw [add_zero] at hsum
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) ?_ hsum
    intro n
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      _ ≤ dist (F n ((F n)^[k] x)) (F n (f^[k] x)) +
          dist (F n (f^[k] x)) (f (f^[k] x)) := dist_triangle _ _ _
      _ = _ := by rw [(hF n).dist_eq]

omit [CompleteSpace E] in

theorem all_times (g : ℕ → ℝ → E → E)
    (hg : ∀ n t, Isometry (g n t))
    (hzero : ∀ n x, g n 0 x = x)
    (hadd : ∀ n s t x, g n (s+t) x = g n s (g n t x))
    (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ∀ t : ℝ, |t| < δ → ∀ x, ∃ y,
      Filter.Tendsto (fun n => g n t x) Filter.atTop (nhds y)) :
    ∀ t : ℝ, ∀ x, ∃ y, Filter.Tendsto (fun n => g n t x) Filter.atTop (nhds y) := by
  intro t x
  obtain ⟨N, hN⟩ := exists_nat_gt (|t|/δ)
  have hN0 : (0 : ℝ) < N := (div_nonneg (abs_nonneg _) hδ.le).trans_lt hN
  let a : ℝ := t/N
  have ha : |a| < δ := by
    dsimp [a]
    rw [abs_div, abs_of_pos hN0, div_lt_iff₀ hN0]
    have := (div_lt_iff₀ hδ).mp hN
    nlinarith
  choose f hf using hsmall a ha
  have hi (n k : ℕ) (x : E) : (g n a)^[k] x = g n ((k : ℝ)*a) x := by
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      have heq : ((k+1 : ℕ) : ℝ)*a = a+(k : ℝ)*a := by push_cast; ring
      rw [heq, hadd]
  refine ⟨f^[N] x, ?_⟩
  have hh := limit_iterate (fun n => g n a) f (fun n => hg n a) hf N x
  simpa only [hi, a, mul_div_cancel₀ t (ne_of_gt hN0)] using hh

end IsometricLimits

namespace Heisenberg

private theorem clm_topologicalRing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsTopologicalRing (E →L[ℂ] E) := inferInstance

local instance (d ℓ : ℕ) : IsTopologicalRing (QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) :=
  clm_topologicalRing

lemma finiteDynamics_generator (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t A = NormedSpace.exp ((t : ℂ) • finiteGenerator d ℓ Λ) A := by
  rw [finiteGenerator, SpinEvolution.exp_generator]
  simp only [finiteDynamics, mul_comm (t : ℂ) Complex.I]

theorem dynamics_converges (d ℓ : ℕ) : DynamicsConverges d ℓ := by
  let C : ℝ := 8*d*bondBound d ℓ
  have hC : 0 ≤ C := (finiteGenerator_localDecomposition d ℓ (box d 0)).nonneg
  let δ : ℝ := 1/(C+1)
  have hδ : 0 < δ := one_div_pos.mpr (by linarith)
  have hs : ∀ t : ℝ, |t| < δ → ∀ A : QuasiLocal d ℓ, ∃ B,
      Filter.Tendsto (fun n => finiteDynamics d ℓ (box d n) t A) Filter.atTop (nhds B) := by
    intro t ht
    apply IsometricLimits.limit_on_dense (fun n => finiteDynamics d ℓ (box d n) t)
      (fun n => finiteDynamics_isometry _ _ _ _) (localCore d ℓ) (localCore_dense d ℓ)
    intro A hA
    obtain ⟨F,hF⟩ := localCore_finite_support hA
    have hz : ‖(t : ℂ)‖*C < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h := (lt_div_iff₀ (by linarith : 0 < C+1)).mp ht
      nlinarith [abs_nonneg t]
    have hh := SpinEvolution.local_exponential_converges
      (fun n => finiteGenerator d ℓ (box d n)) (SupportedOnAtMost d ℓ) C
      (fun n => finiteGenerator_localDecomposition d ℓ (box d n)) F.card A
      ⟨F,Nat.le_succ _,hF⟩ (t : ℂ) hz (local_coefficients_stabilize F hF)
    simpa only [← finiteDynamics_generator] using hh
  have hall := IsometricLimits.all_times (fun n => finiteDynamics d ℓ (box d n))
    (fun n t => finiteDynamics_isometry _ _ _ _)
    (fun n A => finiteDynamics_zero _ _ _ _)
    (fun n s t A => finiteDynamics_group _ _ _ _ _ _) δ hδ hs
  intro t A
  exact tendsto_nhds_limUnder (hall t A)

end Heisenberg

open Filter Topology Metric
namespace EquicontinuousLimits

section
variable {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable {φ : Filter ι} [φ.NeBot]

theorem locallyUniform {F : ι → X → Y} {f : X → Y}
    (he : Equicontinuous F) (hf : ∀ x, Tendsto (fun i => F i x) φ (𝓝 (f x))) :
    TendstoLocallyUniformly F f φ := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  obtain ⟨δ,hδ,hd⟩ := Metric.equicontinuousAt_iff.mp (he x) (ε/4) (by positivity)
  refine ⟨ball x δ,ball_mem_nhds x hδ,?_⟩
  filter_upwards [Metric.tendsto_nhds.mp (hf x) (ε/4) (by positivity)] with i hi
  intro y hy
  have hh : dist (f x) (f y) ≤ ε/4 :=
    le_of_tendsto ((hf x).dist (hf y)) (Filter.Eventually.of_forall fun j => (hd y hy j).le)
  have htriangle := dist_triangle (f y) (f x) (F i y)
  have htriangle' := dist_triangle (f x) (F i x) (F i y)
  rw [dist_comm (F i x) (f x)] at hi
  rw [dist_comm (f y) (f x)] at htriangle
  exact lt_of_le_of_lt htriangle (by linarith [hd y hy i])

end

variable {ι X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {φ : Filter ι} [φ.NeBot]

omit [φ.NeBot] in

theorem apply_varying {L : ι → E →L[ℂ] ℂ} {l : E →L[ℂ] ℂ}
    {C : ℝ} (hC : ∀ i, ‖L i‖ ≤ C) (hL : ∀ A, Tendsto (fun i => L i A) φ (𝓝 (l A)))
    {v : ι → E} {w : E} (hv : Tendsto v φ (𝓝 w)) :
    Tendsto (fun i => L i (v i)) φ (𝓝 (l w)) := by
  have hdiff : Tendsto (fun i => L i (v i-w)) φ (𝓝 0) := by
    apply squeeze_zero_norm (a := fun i => C*‖v i-w‖)
    · intro i
      exact ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _))
    · simpa using (tendsto_const_nhds (x := C)).mul ((hv.sub (tendsto_const_nhds (x := w))).norm)
  have hh := hdiff.add (hL w)
  simpa only [map_sub,sub_add_cancel,zero_add] using hh

theorem equicontinuous_apply {L : ι → E →L[ℂ] ℂ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ i, ‖L i‖ ≤ C) {F : ι → X → E}
    (he : Equicontinuous F) : Equicontinuous (fun i x => L i (F i x)) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  have hp : 0 < C+1 := by linarith
  obtain ⟨δ,hδ,hd⟩ := Metric.equicontinuousAt_iff.mp (he x) (ε/(C+1)) (div_pos hε hp)
  refine ⟨δ,hδ,fun y hy i => ?_⟩
  have hb : dist (L i (F i x)) (L i (F i y)) ≤ C*dist (F i x) (F i y) := by
    rw [dist_eq_norm,dist_eq_norm,← map_sub]
    exact ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _))
  have hh := (lt_div_iff₀ hp).mp (hd y hy i)
  exact hb.trans_lt (by nlinarith [(dist_nonneg : 0 ≤ dist (F i x) (F i y))])

end EquicontinuousLimits
open scoped NNReal
namespace SpinEvolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma exponential_derivative (D : E →L[ℂ] E) (A : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • D) A)
      (NormedSpace.exp ((t : ℂ) • D) (D A)) t := by
  let : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _
  have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) D t
  have he := ((ContinuousLinearMap.apply ℂ E A).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s : ℝ => NormedSpace.exp (s • D) A)
    ((NormedSpace.exp (t • D) * D) A) t at he
  have hr (s : ℝ) : (s : ℂ) • D = s • D := IsScalarTower.algebraMap_smul ℂ s D
  simpa only [hr,mul_apply_eq_comp] using he

end SpinEvolution

open scoped NNReal
namespace Heisenberg

lemma finiteDynamics_hasDerivAt (d ℓ : ℕ) (Λ : Finset (Site d))
    (A : QuasiLocal d ℓ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => finiteDynamics d ℓ Λ s A)
      (finiteDynamics d ℓ Λ t (finiteGenerator d ℓ Λ A)) t := by
  simpa only [← finiteDynamics_generator] using
    SpinEvolution.exponential_derivative (finiteGenerator d ℓ Λ) A t

lemma finiteDynamics_local_lipschitz {d ℓ : ℕ} {A : QuasiLocal d ℓ}
    (hA : A ∈ localCore d ℓ) :
    ∃ M : ℝ≥0, ∀ Λ : Finset (Site d), LipschitzWith M (fun t => finiteDynamics d ℓ Λ t A) := by
  obtain ⟨F,hF⟩ := localCore_finite_support hA
  let C : ℝ := 8*d*bondBound d ℓ
  have hC : 0 ≤ C := (finiteGenerator_localDecomposition d ℓ ∅).nonneg
  let M : ℝ≥0 := ⟨C*(F.card+1)*‖A‖, by positivity⟩
  refine ⟨M,fun Λ => lipschitzWith_of_nnnorm_deriv_le
    (fun t => (finiteDynamics_hasDerivAt d ℓ Λ A t).differentiableAt) ?_⟩
  intro t
  rw [(finiteDynamics_hasDerivAt d ℓ Λ A t).deriv]
  change ‖finiteDynamics d ℓ Λ t (finiteGenerator d ℓ Λ A)‖ ≤ M
  rw [norm_finiteDynamics]
  obtain ⟨r,g,hg,_,hbound⟩ := (finiteGenerator_localDecomposition d ℓ Λ).split F.card A
    ⟨F,Nat.le_succ _,hF⟩
  rw [hg]
  exact (norm_sum_le _ _).trans hbound

lemma finiteDynamics_equicontinuous (d ℓ : ℕ) (A : QuasiLocal d ℓ) :
    Equicontinuous (fun Λ : Finset (Site d) => fun t : ℝ => finiteDynamics d ℓ Λ t A) := by
  intro t
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨B,hB,hAB⟩ := (localCore_dense d ℓ).exists_dist_lt A (show 0 < ε/8 by positivity)
  obtain ⟨M,hM⟩ := finiteDynamics_local_lipschitz hB
  have hp : 0 < (4:ℝ)*(M+1) := by positivity
  refine ⟨ε/(4*(M+1)),div_pos hε hp,?_⟩
  intro s hs Λ
  have hl := (hM Λ).dist_le_mul t s
  have htime : dist t s < ε/(4*(M+1)) := by simpa [dist_comm] using hs
  have ht : (M:ℝ)*dist t s < ε/4 := by
    have hm : 0 ≤ (M:ℝ) := M.property
    have hh := (lt_div_iff₀ hp).mp htime
    nlinarith [(dist_nonneg : 0 ≤ dist t s)]
  calc
    dist (finiteDynamics d ℓ Λ t A) (finiteDynamics d ℓ Λ s A) ≤
        dist (finiteDynamics d ℓ Λ t A) (finiteDynamics d ℓ Λ t B) +
        dist (finiteDynamics d ℓ Λ t B) (finiteDynamics d ℓ Λ s B) +
        dist (finiteDynamics d ℓ Λ s B) (finiteDynamics d ℓ Λ s A) := dist_triangle4 _ _ _ _
    _ = dist A B + dist (finiteDynamics d ℓ Λ t B) (finiteDynamics d ℓ Λ s B) + dist B A := by
      rw [(finiteDynamics_isometry d ℓ Λ t).dist_eq,(finiteDynamics_isometry d ℓ Λ s).dist_eq]
    _ < ε := by rw [dist_comm B A]; linarith

theorem dynamics_locallyUniform (d ℓ : ℕ) (A : QuasiLocal d ℓ) :
    TendstoLocallyUniformly (fun n t => finiteDynamics d ℓ (box d n) t A)
      (fun t => dynamics d ℓ t A) Filter.atTop := by
  apply EquicontinuousLimits.locallyUniform
  · intro t
    exact (finiteDynamics_equicontinuous d ℓ A t).comp (fun n => box d n)
  · intro t
    exact dynamics_converges d ℓ t A

end Heisenberg
end

end OAI
