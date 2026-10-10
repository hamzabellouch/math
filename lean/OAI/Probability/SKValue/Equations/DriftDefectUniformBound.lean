import Mathlib
import OAI.Probability.SKValue.Equations.AestronglyMeasurableInitialMax
import OAI.Probability.SKValue.Equations.BrownianIncrementIndepPast

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology NNReal ENNReal BigOperators

lemma driftDefect_uniform_bound {T : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} (hT : 0≤T)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hu : ∀ t∈Icc (0 : ℝ) T, ∀ x, |u t x|≤1)
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t∈Icc (0 : ℝ) T, X t=W t+∫ s in (0 : ℝ)..t, γ s*u s (X s)) :
    driftDefect T N γ u X W≤2*T*γ T := by
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hG : 0≤γ T := hγ0.trans (hγ ht0 htT hT)
  by_cases hN : N=0
  · subst N
    simp only [driftDefect, Fin.sum_univ_zero]
    positivity
  have hNpos : 0<N := Nat.pos_of_ne_zero hN
  have hδ : 0≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN
  have hmesh : (N : ℝ)*stepSize T N=T := by dsimp [stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+stepSize T N := by
    dsimp [meshTime]; push_cast; ring
  have hγpos (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : 0≤γ t :=
    hγ0.trans (hγ ht0 ht ht.1)
  have hgb (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |γ t*u t (X t)|≤γ T := by
    rw [abs_mul,abs_of_nonneg (hγpos t ht)]
    calc
      γ t*|u t (X t)|≤γ t*1 := mul_le_mul_of_nonneg_left (hu t ht _) (hγpos t ht)
      _ ≤ γ T := by simpa only [mul_one] using hγ ht htT ht.2
  have hlocal (i : Fin N) :
      |X (meshTime T N (i+1))-X (meshTime T N i)-
        (W (meshTime T N (i+1))-W (meshTime T N i))-
        stepSize T N*γ (meshTime T N i)*u (meshTime T N i) (X (meshTime T N i))|≤
      2*stepSize T N*γ T := by
    let a := meshTime T N i
    let b := meshTime T N (i+1)
    have ha := htime i i.isLt.le
    have hb := htime (i+1) (by omega)
    have hlen : b-a=stepSize T N := by dsimp [a,b]; rw [hsucc]; ring
    have hab : a≤b := by linarith
    have hsub : Icc a b⊆Icc (0 : ℝ) T := Icc_subset_Icc ha.1 hb.2
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun s ↦ γ s*u s (X s)) (C:=γ T) (a:=a) (b:=b)
      (fun s hs ↦ by
        rw [Real.norm_eq_abs]
        rw [uIoc_of_le hab] at hs
        exact hgb s (hsub ⟨hs.1.le,hs.2⟩))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), hlen] at hi
    have hdiff : X b-X a-(W b-W a)=∫ s in a..b, γ s*u s (X s) := by
      rw [hX b hb,hX a ha]
      have he := intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_substrip hT hint ht0 hb)
        (intervalIntegrable_substrip hT hint ht0 ha)
      linear_combination he
    change |X b-X a-(W b-W a)-stepSize T N*γ a*u a (X a)|≤_
    rw [hdiff]
    have hic := (abs_sub _ _).trans (add_le_add hi (show
        |stepSize T N*γ a*u a (X a)|≤ stepSize T N*γ T from by
      rw [mul_assoc,abs_mul,abs_of_nonneg hδ]
      exact mul_le_mul_of_nonneg_left (hgb a ha) hδ))
    linarith
  calc
    driftDefect T N γ u X W≤∑ _i : Fin N, 2*stepSize T N*γ T :=
      Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = 2*T*γ T := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      linear_combination (2*γ T)*hmesh

lemma driftDefect_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ} {γ : ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    (hT : 0≤T) (hUm : ∀ t∈Icc (0 : ℝ) T, Continuous (u t))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ) :
    AEStronglyMeasurable (fun ω ↦ driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω)) μ := by
  unfold driftDefect
  apply Finset.aestronglyMeasurable_fun_sum
  intro i _
  have ha := mesh_time_mem_total hT (show (i : ℕ)≤N from i.isLt.le)
  have hb := mesh_time_mem_total hT (show (i : ℕ)+1≤N from i.isLt)
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using ((((hXM _ hb).sub (hXM _ ha)).sub ((hWM _ hb).sub (hWM _ ha))).sub
    (((hUm _ ha).comp_aestronglyMeasurable (hXM _ ha)).const_mul
      (stepSize T N*γ (meshTime T N i)))).norm

lemma driftDefect_integral_tendsto {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {T L : ℝ} {u : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {X W : ℝ → Ω → ℝ} (hT : 0≤T) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hu : ∀ t∈Icc (0 : ℝ) T, ∀ x, |u t x|≤1)
    (hUm : ∀ t∈Icc (0 : ℝ) T, Continuous (u t))
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤L*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) :
    Tendsto (fun N ↦ ∫ ω, driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have H := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω ↦ 2*T*γ T)
    (Eventually.of_forall (fun N ↦ driftDefect_aestronglyMeasurable hT hUm hXM hWM (N:=N)))
    (Eventually.of_forall (fun N ↦ hpaths.mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (driftDefect_nonneg T N γ u _ _)]
      exact driftDefect_uniform_bound hT hγ hγ0 hu hω.2.1 hω.2.2)))
    (integrable_const _) (hpaths.mono (fun ω hω ↦
      driftDefect_tendsto hT hL hγ hγ0 hu hLip hω.1 hω.2.1 hω.2.2))
  simpa only [integral_zero] using H

end SKValue

end

end OAI
