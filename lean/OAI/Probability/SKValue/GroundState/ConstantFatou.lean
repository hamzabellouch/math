import Mathlib
import OAI.Probability.SKValue.GroundState.EmpiricalEnergyLimit
import OAI.Probability.SKValue.GroundState.EmpiricalCalculus
import OAI.Probability.SKValue.GroundState.GaussianTranspose

namespace OAI

section

open MeasureTheory Filter Set
open scoped Topology
namespace SKValueG

theorem constant_limit_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ) (C : ℕ → ℝ) (L M : ℝ)
    (hi : ∀ n,Integrable (f n) μ) (hn : ∀ n,∀ᵐ ω ∂μ,0≤f n ω)
    (ht : ∀ᵐ ω ∂μ,Tendsto (fun n ↦ f n ω) atTop (𝓝 L))
    (hC : ∀ n,(∫ ω,f n ω ∂μ)≤C n) (hCt : Tendsto C atTop (𝓝 M)) : L≤M := by
  have ha : ∀ᵐ ω ∂μ,(∀ n,0≤f n ω) ∧ Tendsto (fun n ↦ f n ω) atTop (𝓝 L) :=
    (ae_all_iff.mpr hn).and ht
  obtain ⟨ω,hω⟩ := ha.exists
  have hL : 0≤L := ge_of_tendsto hω.2 (Eventually.of_forall hω.1)
  have hlim : Tendsto (fun n ↦ ∫ ω,min (f n ω) L ∂μ) atTop (𝓝 L) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ ↦ L)
      (fun n ↦ (hi n).aestronglyMeasurable.inf (aestronglyMeasurable_const (b:=L)))
      (integrable_const L) (fun n ↦ (hn n).mono (fun ω hω ↦ by
        change |min (f n ω) L|≤L
        rw [abs_of_nonneg (le_min hω hL)]
        exact min_le_right _ _))
      (ht.mono (fun ω hω ↦ by simpa using hω.min tendsto_const_nhds))
    simpa using h
  apply le_of_tendsto_of_tendsto hlim hCt
  apply Eventually.of_forall
  intro n
  apply (integral_mono ((hi n).inf (integrable_const L)) (hi n) (fun _ ↦ min_le_left _ _)).trans
  exact hC n

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

theorem predictable_coefficients_le_groundState (K : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → Bool)
    (hm : ∀ i,Measurable (f i))
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (hL : ∀ i<K,MemLp (f i) 2 (gaussianProduct (Fin (K+1))))
    (hu : ∀ i<K,(∫ y,(f i y)^2 ∂gaussianProduct (Fin (K+1)))=1)
    (ho : ∀ i j,i<j → j<K →(∫ y,f i y*f j y ∂gaussianProduct (Fin (K+1)))=0)
    (hFm : Measurable F) :
    (∑ j : Fin K,(∫ y,f j y*spin (F y) ∂gaussianProduct (Fin (K+1)))*
      (∫ y,spin (F y)*y ⟨j.val+1,by omega⟩ ∂gaussianProduct (Fin (K+1))))≤groundStateValue := by
  let μ := gaussianProduct (Fin (K+1))
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let S := fun y ↦ spin (F y)
  let Z := fun (j : Fin K) (y : Fin (K+1) → ℝ) ↦ y ⟨j.val+1,by omega⟩
  let e := fun n x ↦ ∑ j : Fin K,empiricalColumnEnergy K n f x S j
  let c := fun n (x : ℕ → (Fin (K+1) → ℝ)) ↦
    ∑ j : Fin K,(1+‖empiricalVector (Z j) x n‖^2)
  let L := ∑ j : Fin K,(∫ y,f j y*S y ∂μ)*(∫ y,S y*Z j y ∂μ)
  have hSm : Measurable S := (measurable_of_finite spin).comp hFm
  have hS : ∀ y,(S y)^2=1 := fun y ↦ spin_sq (F y)
  have hZ (j : Fin K) : Integrable (fun y ↦ (Z j y)^2) μ := by
    simpa only [sq,Pi.mul_def] using (gaussian_coordinate_memLp (⟨j.val+1,by omega⟩ : Fin (K+1))).integrable_mul
      (gaussian_coordinate_memLp (⟨j.val+1,by omega⟩ : Fin (K+1)))
  have hci (n : ℕ) : Integrable (c n) P :=
    integrable_finsetSum _ (fun j _ ↦ (integrable_const 1).add
      (empirical_norm_sq_integrable μ (Z j) (hZ j) n))
  have hei (n : ℕ) : Integrable (e n) P := by
    apply integrable_finsetSum
    intro j hj
    apply ((integrable_const 1).add (empirical_norm_sq_integrable μ (Z j) (hZ j) n)).mono'
      (empiricalColumnEnergy_measurable K n f S hm hSm j).aestronglyMeasurable
    exact Eventually.of_forall (fun x ↦ empiricalColumnEnergy_bound K n f S hS x j.isLt)
  have hen (n : ℕ) (x) : 0≤e n x+c n x := by
    change 0≤(∑ j : Fin K,empiricalColumnEnergy K n f x S j)+
      ∑ j : Fin K,(1+‖empiricalVector (Z j) x n‖^2)
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro j hj
    have hh := (abs_le.mp (empiricalColumnEnergy_bound K n f S hS x j.isLt)).1
    linarith
  have hct (n : ℕ) (hn : 0<n) : (∫ x,c n x ∂P)=2*(K : ℝ) := by
    rw [show c n=(fun x ↦ ∑ j : Fin K,(1+‖empiricalVector (Z j) x n‖^2)) from rfl,
      integral_finsetSum]
    · have hh (j : Fin K) : (∫ x,(1+‖empiricalVector (Z j) x n‖^2) ∂P)=2 := by
        rw [integral_add (integrable_const 1) (empirical_norm_sq_integrable μ (Z j) (hZ j) n)]
        rw [empirical_norm_sq_integral μ (Z j) (hZ j) hn]
        rw [gaussian_coordinate_sq_mean]
        norm_num [P]
      simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    · intro j hj
      exact (integrable_const 1).add (empirical_norm_sq_integrable μ (Z j) (hZ j) n)
  have heL : ∀ᵐ x ∂P,Tendsto (fun n ↦ e n x) atTop (𝓝 L) := by
    have hh : ∀ᵐ x ∂P,∀ j : Fin K,Tendsto
        (fun n ↦ empiricalColumnEnergy K n f x S j) atTop
        (𝓝 ((∫ y,f j y*S y ∂μ)*(∫ y,S y*Z j y ∂μ))) := by
      apply ae_all_iff.mpr
      intro j
      exact empiricalColumnEnergy_ae_tendsto K f S hm ha hL hu ho hSm hS j.isLt
    exact hh.mono (fun x hx ↦ tendsto_finsetSum (s:=Finset.univ) (fun j _ ↦ hx j))
  have hcL : ∀ᵐ x ∂P,Tendsto (fun n ↦ c n x) atTop (𝓝 (2*(K : ℝ))) := by
    have hh : ∀ᵐ x ∂P,∀ j : Fin K,Tendsto
        (fun n ↦ ‖empiricalVector (Z j) x n‖) atTop (𝓝 1) := by
      apply ae_all_iff.mpr
      intro j
      exact empirical_norm_tendsto_one μ (Z j) (measurable_pi_apply _) (hZ j)
        (gaussian_coordinate_sq_mean _)
    filter_upwards [hh] with x hx
    have ht := tendsto_finsetSum (s:=Finset.univ)
      (fun j _ ↦ (tendsto_const_nhds (x:=(1 : ℝ))).add ((hx j).pow 2))
    simpa [c,two_mul] using ht
  have hb := constant_limit_integral_le (μ:=P)
    (fun n x ↦ e (n+1) x+c (n+1) x)
    (fun n ↦ groundStateSequence (n+1)+2*(K : ℝ)) (L+2*(K : ℝ))
    (groundStateValue+2*(K : ℝ))
    (fun n ↦ (hei (n+1)).add (hci (n+1)))
    (fun n ↦ Eventually.of_forall (hen (n+1)))
    ((heL.and hcL).mono (fun x hx ↦ (hx.1.add hx.2).comp (tendsto_add_atTop_nat 1)))
    (fun n ↦ by
      rw [integral_add (hei (n+1)) (hci (n+1)),hct (n+1) (by omega)]
      apply add_le_add_left
      convert empirical_finite_spin_lower K f F hm ha hFm (show 0<n+1 by omega) using 1
      apply integral_congr_ae
      filter_upwards [] with x
      exact Fin.sum_univ_eq_sum_range (fun j ↦ empiricalColumnEnergy K (n+1) f x S j) K)
    ((groundStateSequence_tendsto.comp (tendsto_add_atTop_nat 1)).add_const _)
  exact (add_le_add_iff_right (2*(K : ℝ))).mp hb

end SKValueG

end

end OAI
