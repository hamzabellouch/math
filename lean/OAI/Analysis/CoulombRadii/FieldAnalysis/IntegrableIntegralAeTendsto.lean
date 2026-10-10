import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Translate

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma integrable_and_integral_le_of_ae_tendsto {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {F : ℕ → A → ℝ} {f : A → ℝ} {u : ℕ → ℝ} {C : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hFn : ∀ n x, 0 ≤ F n x)
    (hfn : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hb : ∀ n, (∫ x, F n x ∂μ) ≤ u n) (hu : Tendsto u atTop (𝓝 C)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hmeas : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).1) ht
  have hfat : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hF n).aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun n => ENNReal.ofReal (u n)) atTop := by
        apply liminf_le_liminf (hv := isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
          (hu := (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩).isCoboundedUnder_ge)
        exact Eventually.of_forall fun n => by
          rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Eventually.of_forall (hFn n))]
          exact ENNReal.ofReal_le_ofReal (hb n)
      _ = ENNReal.ofReal C := ((ENNReal.continuous_ofReal.tendsto _).comp hu).liminf_eq
  have hf : Integrable f μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hfn _)]
    exact hfat.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hf, ?_⟩
  have hC : 0 ≤ C := ge_of_tendsto' hu fun n => (integral_nonneg (hFn n)).trans (hb n)
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rwa [ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hfn)]

lemma pi_exhaustion {A : Type*} {s : ℕ → Set A} (hs : Monotone s)
    (hU : (⋃ k, s k) = univ) (n : ℕ) :
    (⋃ k, (univ.pi fun _ : Fin n => s k)) = univ := by
  ext z
  simp only [mem_iUnion, mem_univ_pi, mem_univ, iff_true]
  have hx (i : Fin n) : ∃ k, z i ∈ s k := by
    have hi : z i ∈ ⋃ k, s k := by rw [hU]; trivial
    simpa only [mem_iUnion] using hi
  choose k hk using hx
  refine ⟨Finset.univ.sup k, fun i => hs (Finset.le_sup (f := k) (Finset.mem_univ i)) (hk i)⟩

lemma density_power_exhaustion {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) {s : ℕ → Set A}
    (hs : ∀ k, MeasurableSet (s k)) (hmono : Monotone s) (hU : (⋃ k, s k) = univ)
    {p : ℝ} (hp : 0 < p) {u : ℕ → ℝ} {C : ℝ}
    (hi : ∀ k, Integrable (fun x => (firstParticleDensity (μ := μ.restrict (s k)) f x)^p)
      (μ.restrict (s k)))
    (hb : ∀ k, (∫ x, (firstParticleDensity (μ := μ.restrict (s k)) f x)^p ∂(μ.restrict (s k))) ≤ u k)
    (hu : Tendsto u atTop (𝓝 C)) :
    Integrable (fun x => (firstParticleDensity (μ := μ) f x)^p) μ ∧
    (∫ x, (firstParticleDensity (μ := μ) f x)^p ∂μ) ≤ C := by
  let F (k : ℕ) : A → ℝ := (s k).indicator
    (fun x => (firstParticleDensity (μ := μ.restrict (s k)) f x)^p)
  have hdn {ν : Measure A} (x : A) : 0 ≤ firstParticleDensity (μ := ν) f x :=
    mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  have hn (k) (x) : 0 ≤ F k x :=
    indicator_nonneg (fun _ _ => Real.rpow_nonneg (hdn _) p) x
  apply integrable_and_integral_le_of_ae_tendsto
    (F := F) (u := u) (fun k => (integrable_indicator_iff (hs k)).mpr (hi k)) hn
    (fun x => Real.rpow_nonneg (hdn x) p)
    ?_ (fun k => by simpa only [F, integral_indicator (hs k)] using hb k) hu
  have hslice := (firstFiber_memLp hf).norm.integrable_sq.prod_left_ae
  filter_upwards [hslice] with x hx
  have hset : (⋃ k, (univ.pi fun _ : Fin n => s k)) = univ := pi_exhaustion hmono hU n
  have hlim := tendsto_setIntegral_of_monotone
    (fun k => MeasurableSet.univ_pi (fun _ : Fin n => hs k))
    (fun k l hkl z hz i _ => hmono hkl (hz i (mem_univ i)))
    (f := fun y => ‖firstFiber f (y,x)‖^2) (μ := Measure.pi fun _ : Fin n => μ)
    (by simpa only [hset, integrableOn_univ] using hx)
  simp only [hset, Measure.restrict_univ, Measure.restrict_pi_pi] at hlim
  have hd : Tendsto (fun k => firstParticleDensity (μ := μ.restrict (s k)) f x) atTop
      (𝓝 (firstParticleDensity (μ := μ) f x)) := hlim.const_mul _
  have hpw := hd.rpow_const (Or.inr hp.le)
  have hex : ∃ k, x ∈ s k := by
    have hi : x ∈ ⋃ k, s k := by rw [hU]; trivial
    simpa only [mem_iUnion] using hi
  obtain ⟨k,hk⟩ := hex
  apply hpw.congr'
  filter_upwards [eventually_ge_atTop k] with l hl
  simp only [F, indicator_of_mem (hmono hl hk)]

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma spinCubeEquiv_full_measurePreserving (n : ℕ) :
    MeasurePreserving (spinCubeEquiv n) (Measure.pi fun _ : Fin n => spinSpaceMeasure)
      (Measure.count.prod volume) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow (Fin 2) (Fin 3 → ℝ) (Fin n)
    (fun _ => Measure.count) (fun _ => volume)
  rw [measure_pi_count] at h1
  have h2 := (MeasurePreserving.id (Measure.count : Measure (Spins n))).prod
    (measurePreserving_const_uncurry (I := Fin n) (J := Fin 3) (volume : Measure ℝ))
  exact h2.comp h1

lemma H1Vector.spinSpace_memLp {n : ℕ} (ψ : H1Vector n) :
    MemLp (fun sx : Spins n × ((Fin n × Fin 3) → ℝ) =>
      ψ.value sx.1 (WithLp.toLp 2 sx.2)) 2 (Measure.count.prod volume) := by
  have hi (s : Spins n) : MemLp (fun t : Spins n => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Spins n) _ => tensorPair_memLp (hi s)
    ((ψ.value_L2 s).comp_measurePreserving (PiLp.volume_preserving_toLp _)))
  convert H using 1
  funext sx
  simp only [ite_mul, one_mul, zero_mul]
  simp

lemma H1Vector.cubeState_full_memLp {n : ℕ} (ψ : H1Vector n) :
    MemLp (cubeState ψ) 2 (Measure.pi fun _ : Fin n => spinSpaceMeasure) :=
  ψ.spinSpace_memLp.comp_measurePreserving (spinCubeEquiv_full_measurePreserving n)

lemma cubeState_full_mass {n : ℕ} (ψ : H1Vector n) :
    (∫ z, ‖cubeState ψ z‖^2 ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = mass ψ := by
  change (∫ z, ‖ψ.value ((spinCubeEquiv n) z).1 (WithLp.toLp 2 ((spinCubeEquiv n) z).2)‖^2
    ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = mass ψ
  rw [(spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => ‖ψ.value sx.1 (WithLp.toLp 2 sx.2)‖^2)]
  rw [integral_prod _ ψ.spinSpace_memLp.norm.integrable_sq, integral_count]
  unfold mass
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume from
    PiLp.volume_preserving_toLp _).integral_comp' (fun x => ‖ψ.value s x‖^2)

lemma centeredSpinCube_monotone : Monotone centeredSpinCube := by
  intro R S hRS x hx
  simp only [centeredSpinCube, mem_prod, mem_univ, true_and, mem_univ_pi, mem_Ioc] at *
  intro i
  obtain ⟨h1,h2⟩ := hx i
  constructor <;> linarith

lemma centeredSpinCube_exhaustion : (⋃ k : ℕ, centeredSpinCube (k+1)) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨k,hk⟩ := exists_nat_gt (‖x.2‖ : ℝ)
  refine ⟨k, ?_⟩
  simp only [centeredSpinCube, mem_prod, mem_univ, true_and, mem_univ_pi, mem_Ioc]
  intro i
  have hi : |x.2 i| ≤ ‖x.2‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x.2 i
  have h := abs_le.mp hi
  constructor <;> linarith

theorem global_spin_density_power_bound {n : ℕ} (ψ : H1Vector (n+1))
    (hψ : Antisymmetric ψ) (hm : mass ψ ≤ 1) :
    Integrable (fun x => (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) x)^(5/3:ℝ))
      spinSpaceMeasure ∧
    (∫ x, (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) x)^(5/3:ℝ)
      ∂spinSpaceMeasure) ≤ (8192/(3*Real.pi^2))*kinetic ψ := by
  apply density_power_exhaustion ψ.cubeState_full_memLp
    (s := fun k : ℕ => centeredSpinCube (k+1)) (fun k => centeredSpinCube_measurable _)
    (fun k l h => centeredSpinCube_monotone (by exact_mod_cast Nat.add_le_add_right h 1))
    centeredSpinCube_exhaustion (by norm_num : (0:ℝ) < 5/3)
    (u := fun k : ℕ => (64/(k+1:ℝ)^2)*((n+1:ℕ):ℝ)+(8192/(3*Real.pi^2))*kinetic ψ)
    (fun k => (centered_density_power_bound ψ hψ hm (by positivity : (0:ℝ)<k+1)).1)
    (fun k => (centered_density_power_bound ψ hψ hm (by positivity : (0:ℝ)<k+1)).2)
  have ht : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hi := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ((tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp ht)).const_mul 64
  convert (hi.mul_const ((n+1:ℕ):ℝ)).add_const ((8192/(3*Real.pi^2))*kinetic ψ) using 1 <;>
    simp [Function.comp_apply, div_eq_mul_inv]

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
