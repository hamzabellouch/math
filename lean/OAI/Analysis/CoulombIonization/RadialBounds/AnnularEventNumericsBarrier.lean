import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ActualSimultaneousCapBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_AnnularEventNumerics_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation

lemma annularOffsetMass_rescale {D u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u^3*annularOffsetMass D u = 1+Real.sqrt (D*u^7) := by
  have hh : u^3 ≤ 1 := pow_le_one₀ hu.le hu1
  have hmax : max (1/u^3) 1 = 1/u^3 :=
    max_eq_left ((le_div_iff₀ (pow_pos hu 3)).mpr (by simpa using hh))
  unfold annularOffsetMass
  rw [hmax,mul_add,mul_one_div_cancel (pow_ne_zero _ hu.ne'),
    ←Real.sqrt_sq (by positivity : 0 ≤ u^3),←Real.sqrt_mul (sq_nonneg (u^3))]
  congr 2
  ring

lemma annularOffsetMass_tendsto {ι : Type*} {l : Filter ι} {u D : ι → ℝ}
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0))
    (hD : Tendsto (fun i => D i*(u i)^7) l (𝓝 0)) :
    Tendsto (fun i => (u i)^3*annularOffsetMass (D i) (u i)) l (𝓝 1) := by
  have hh : Tendsto (fun i => 1+Real.sqrt (D i*(u i)^7)) l (𝓝 1) := by
    simpa using hD.sqrt.const_add 1
  apply hh.congr'
  filter_upwards [hu,hu0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi hi1
  exact (annularOffsetMass_rescale hi hi1.le).symm

lemma annular_count_margin_eventually {ι : Type*} {l : Filter ι} {u D : ι → ℝ}
    {C T : ℝ} (hCT : C < T^2)
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0))
    (hD : Tendsto (fun i => D i*(u i)^7) l (𝓝 0)) :
    ∀ᶠ i in l, C*(annularOffsetMass (D i) (u i))^2 < (T/(u i)^3)^2 := by
  have hm := annularOffsetMass_tendsto hu hu0 hD
  have hh := ((hm.pow 2).const_mul C).eventually_lt
    (tendsto_const_nhds (x := T^2)) (by simpa using hCT)
  filter_upwards [hu,hh] with i hui hi
  have hscale : (u i)^6*(T/(u i)^3)^2 = T^2 := by field_simp
  apply (mul_lt_mul_iff_right₀ (pow_pos hui 6)).mp
  rw [hscale]
  nlinarith only [hi]

lemma polynomial_annular_count_margin_eventually {ι : Type*} {l : Filter ι}
    {u : ι → ℝ} {C T δ : ℝ} (n : ℕ) (hCT : C < T^2)
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0)) :
    ∀ᶠ i in l, C*(annularOffsetMass
      (dyadicUniformEventBudget (u i) ((u i)^n) δ) (u i))^2 < (T/(u i)^3)^2 := by
  apply annular_count_margin_eventually hCT hu hu0
  have hh := (polynomial_probability_budget_tendsto n (v := 7) (by norm_num) δ).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hu0,hu⟩)
  simpa only [Function.comp_def,Real.rpow_ofNat] using hh

lemma observation_annular_noise_eventually {ι : Type*} {l : Filter ι}
    {u : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0)) :
    ∀ᶠ i in l, Real.sqrt 3*(u i)^(101/100:ℝ) ≤ a*(u i) := by
  have hell : ∀ᶠ i in l, 0 ≤ (u i)^(101/100:ℝ) ∧
      (u i)^(101/100:ℝ) ≤ 1*(u i)^(101/100:ℝ) := by
    filter_upwards [hu] with i hi
    exact ⟨Real.rpow_nonneg hi.le _,by simp⟩
  have hh : Tendsto (fun i => Real.sqrt 3*((u i)^(101/100:ℝ)/(u i))) l (𝓝 0) := by
    simpa only [mul_zero] using
      (observation_relative_tendsto (E := 1) zero_le_one hu hu0 hell).const_mul (Real.sqrt 3)
  filter_upwards [hu,hh.eventually (gt_mem_nhds ha)] with i hui hi
  rw [←mul_div_assoc] at hi
  exact (div_le_iff₀ hui).mp hi.le

end Work_AnnularEventNumerics_barrier_scope

section Work_ActualAnnularGood_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

 theorem exists_actual_annular_good_constant {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∃ T : ℝ, 0 < T ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)}
      {j : ∀ i, Fin (K i)} {δ : ℝ},
      Tendsto s l (𝓝 0) →
      (∀ᶠ i in l, 0 < r₀ i ∧ (2:ℝ)^(j i).val*r₀ i ≤ s i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        TailTiltState (Z i) (lam i) (r₀ i) (K i)
          (tailPolynomialThreshold (r₀ i)) δ (F i)) →
      ∀ᶠ i in l,
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
          {z | T/((2:ℝ)^(j i).val*r₀ i)^3 <
            observedAnnularCount (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k)
              (j i) (alpha*((2:ℝ)^(j i).val*r₀ i)) (beta*((2:ℝ)^(j i).val*r₀ i)) z} <
          ((2:ℝ)^(j i).val*r₀ i)^40 := by
  obtain ⟨C,hC,hcount⟩ := exists_tail_state_annular_count_constant (beta := beta) ha
  let T : ℝ := 2*C+1
  have hT : 0 < T := by dsimp [T]; linarith
  have hCT : C < T^2 := by dsimp [T]; nlinarith [sq_nonneg C]
  refine ⟨T,hT,?_⟩
  intro ι l r₀ s Z lam N K F j δ hs0 hband hstate
  let u := fun i => (2:ℝ)^(j i).val*r₀ i
  have hu : ∀ᶠ i in l, 0 < u i := by
    filter_upwards [hband] with i hi
    exact mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) _) hi.1
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le)
    (hband.mono fun _ hi => hi.2) hs0
  have hlarge := polynomial_annular_count_margin_eventually (δ := δ) 40 hCT hu hu0
  have hnoiseA := observation_annular_noise_eventually (by linarith : 0 < alpha/2) hu hu0
  have hnoiseB := observation_annular_noise_eventually hb hu hu0
  filter_upwards [hband,hstate,hlarge,hnoiseA,hnoiseB,
    hu0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hi hFi hli hAi hBi hui1
  have hui : 0 < u i := mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) _) hi.1
  have hp : tailPolynomialThreshold (r₀ i) (j i).castSucc = (u i)^40 := by
    unfold tailPolynomialThreshold
    exact min_eq_right (pow_le_one₀ hui.le hui1.le)
  have hell : dyadicObservationWidth (r₀ i) (j i) = (u i)^(101/100:ℝ) := by
    unfold dyadicObservationWidth u
    norm_num
  have hh := hcount hFi.1 hFi.2.1 hi.1 hFi.2.2
    (j i).castSucc (j i) (by rfl) (u i) (T/(u i)^3) hui (by positivity)
    (by rw [hell]; linarith only [hAi]) (by rw [hell]; exact hBi)
    (by simpa only [Fin.val_castSucc,hp] using hli)
  simpa only [Fin.val_castSucc,hp,Measure.real] using hh

end Work_ActualAnnularGood_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

 theorem exists_actual_uniform_annular_good_constant {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∃ T : ℝ, 0 < T ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
          {z | T/((2:ℝ)^j.val*r₀ i)^3 <
            observedAnnularCount (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k)
              j (alpha*((2:ℝ)^j.val*r₀ i)) (beta*((2:ℝ)^j.val*r₀ i)) z} <
          ((2:ℝ)^j.val*r₀ i)^40 := by
  obtain ⟨T,hT,hcount⟩ := exists_actual_annular_good_constant ha hb
  refine ⟨T,hT,?_⟩
  intro ι l r₀ s Z lam N K F δ hs0 hr₀ hstate
  have hpoly : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i)
        (tailPolynomialThreshold (r₀ i)) δ (F i) := by
    filter_upwards [hr₀,hstate] with i hri hi
    exact ⟨hi.1,hi.2.1,hi.2.2.to_tailTiltState hri (tailPolynomialThreshold_pos hri)
      (fun _ => tinyProbabilityFloor_le_polynomial hi.1 (by positivity))⟩
  let A : ι → Type := fun i => {j : Fin (K i) // (2:ℝ)^j.val*r₀ i ≤ s i}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  have ht : Tendsto π L l := tendsto_comap
  have hb' : ∀ᶠ q in L, 0 < r₀ (π q) ∧ (2:ℝ)^q.2.1.val*r₀ (π q) ≤ s (π q) := by
    filter_upwards [ht.eventually hr₀] with q hq
    exact ⟨hq,q.2.2⟩
  have hh := hcount (F := fun q : Σ i, A i => F (π q)) (j := fun q => q.2.1)
    (hs0.comp ht) hb' (ht.eventually hpoly)
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro j hj
  exact hi ⟨i,⟨j,hj⟩⟩ rfl

end CoulombAtom

end

end OAI
