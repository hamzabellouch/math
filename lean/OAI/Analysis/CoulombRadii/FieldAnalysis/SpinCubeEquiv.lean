import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.CubeLabelEquiv

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb
lemma measurePreserving_const_uncurry {I J A : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry I J A).symm
      (Measure.pi fun _ : I => Measure.pi fun _ : J => μ)
      (Measure.pi fun _ : I × J => μ) := by
  refine ⟨(MeasurableEquiv.curry I J A).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [(MeasurableEquiv.curry I J A).symm.map_apply]
  have he : (MeasurableEquiv.curry I J A).symm ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i,j))) := by
    ext x
    simp only [mem_preimage, mem_univ_pi, MeasurableEquiv.curry_symm_apply]
    exact ⟨fun h i j => h (i,j), fun h p => h p.1 p.2⟩
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]

lemma measure_pi_count {I A : Type*} [Fintype I] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    (Measure.pi fun _ : I => (Measure.count : Measure A)) = Measure.count := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

noncomputable def spinCubeEquiv (n : ℕ) :
    (Fin n → (Fin 2 × (Fin 3 → ℝ))) ≃ᵐ (Spins n × ((Fin n × Fin 3) → ℝ)) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) (Fin 3 → ℝ) (Fin n)).trans
    ((MeasurableEquiv.refl (Spins n)).prodCongr (MeasurableEquiv.curry (Fin n) (Fin 3) ℝ).symm)

lemma spinCubeEquiv_measurePreserving (n : ℕ) (b : ℝ) :
    MeasurePreserving (spinCubeEquiv n) (Measure.pi fun _ : Fin n => spinCubeMeasure b)
      (Measure.count.prod (finiteCubeMeasure b (Fin n × Fin 3))) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow (Fin 2) (Fin 3 → ℝ) (Fin n)
    (fun _ => Measure.count) (fun _ => cubeMeasure b 3)
  rw [measure_pi_count] at h1
  have h2 := (MeasurePreserving.id (Measure.count : Measure (Spins n))).prod
    (measurePreserving_const_uncurry (I := Fin n) (J := Fin 3) (volume.restrict (Ioc 0 b)))
  exact h2.comp h1

instance finiteCubeMeasure_isFinite (b : ℝ) (I : Type*) [Fintype I] :
    IsFiniteMeasure (finiteCubeMeasure b I) := by
  unfold finiteCubeMeasure
  infer_instance
instance spinCubeMeasure_isFinite (b : ℝ) : IsFiniteMeasure (spinCubeMeasure b) := by
  unfold spinCubeMeasure
  infer_instance

noncomputable def cubeState {n : ℕ} (ψ : H1Vector n)
    (z : Fin n → (Fin 2 × (Fin 3 → ℝ))) : ℂ :=
  ψ.value (fun i => (z i).1) (WithLp.toLp 2 (fun ij => (z ij.1).2 ij.2))

lemma H1Vector.spinCube_memLp {n : ℕ} (ψ : H1Vector n) (b : ℝ) :
    MemLp (fun sx : Spins n × ((Fin n × Fin 3) → ℝ) =>
      ψ.value sx.1 (WithLp.toLp 2 sx.2)) 2
      (Measure.count.prod (finiteCubeMeasure b (Fin n × Fin 3))) := by
  classical
  have hi (s : Spins n) : MemLp (fun t : Spins n => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Spins n) _ =>
    tensorPair_memLp (hi s) (ψ.cube_memLp b s))
  convert H using 1
  funext sx
  simp only [ite_mul, one_mul, zero_mul]
  simp

lemma H1Vector.cubeState_memLp {n : ℕ} (ψ : H1Vector n) (b : ℝ) :
    MemLp (cubeState ψ) 2 (Measure.pi fun _ : Fin n => spinCubeMeasure b) :=
  (ψ.spinCube_memLp b).comp_measurePreserving (spinCubeEquiv_measurePreserving n b)

lemma cubeState_mass {n : ℕ} (ψ : H1Vector n) (b : ℝ) :
    (∫ z, ‖cubeState ψ z‖^2 ∂(Measure.pi fun _ : Fin n => spinCubeMeasure b)) = cubeMass ψ b := by
  have H := (spinCubeEquiv_measurePreserving n b).integral_comp'
    (fun sx => ‖ψ.value sx.1 (WithLp.toLp 2 sx.2)‖^2)
  change (∫ z, ‖cubeState ψ z‖^2 ∂(Measure.pi fun _ : Fin n => spinCubeMeasure b)) = _ at H
  rw [H, integral_prod _ ((ψ.spinCube_memLp b).norm.integrable_sq), integral_count]
  rfl

lemma cubeState_antisymmetric {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ) (b : ℝ) :
    ProductAntisymmetric (μ := spinCubeMeasure b) (cubeState ψ) := by
  intro p
  have hs (s : Spins n) : ∀ᵐ x ∂(finiteCubeMeasure b (Fin n × Fin 3)),
      ψ.value (s ∘ p) (permute p (WithLp.toLp 2 x)) =
        ((p.sign : ℤ) : ℂ) * ψ.value s (WithLp.toLp 2 x) :=
    ((PiLp.volume_preserving_toLp (Fin n × Fin 3)).quasiMeasurePreserving.ae (hψ p s)).filter_mono
      (ae_mono (finiteCubeMeasure_le_volume b))
  have hall := (ae_all_iff.mpr hs)
  have hp := (Measure.quasiMeasurePreserving_snd (μ := (Measure.count : Measure (Spins n)))).ae hall
  have ht := (spinCubeEquiv_measurePreserving n b).quasiMeasurePreserving.ae hp
  filter_upwards [ht] with z hz
  exact hz (fun i => (z i).1)

lemma spinCube_tensor_delta {n : ℕ} (b : ℝ) (a : Fin n → SpinMode)
    (sx : Spins n × ((Fin n × Fin 3) → ℝ)) :
    (∏ i, spinCubeMode b (a i) ((spinCubeEquiv n).symm sx i)) =
      (if sx.1 = (cubeLabelEquiv n a).1 then (1:ℂ) else 0) *
        finiteCubeMode b (cubeLabelEquiv n a).2 sx.2 := by
  classical
  change (∏ i, (if sx.1 i = (a i).1 then (1:ℂ) else 0) *
    ∏ j, neumannMode b ((a i).2 j) (sx.2 (i,j))) = _
  rw [Finset.prod_mul_distrib]
  have he : (∏ i, if sx.1 i = (a i).1 then (1:ℂ) else 0) =
      if sx.1 = (cubeLabelEquiv n a).1 then 1 else 0 := by
    by_cases h : sx.1 = (cubeLabelEquiv n a).1
    · simp only [h, cubeLabelEquiv, Equiv.coe_fn_mk, ite_true, Finset.prod_const_one]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ := Function.ne_iff.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact ite_eq_right hi
  rw [he]
  congr 1
  simp only [finiteCubeMode, Fintype.prod_prod_type, cubeLabelEquiv, Equiv.coe_fn_mk]

lemma cubeState_coefficient {n : ℕ} (ψ : H1Vector n) (b : ℝ) (a : Fin n → SpinMode) :
    scalarCoefficient (μ := spinCubeMeasure b) (cubeState ψ) (spinCubeMode b) a =
      cubeFermionCoefficient ψ b a := by
  classical
  unfold scalarCoefficient
  rw [← (spinCubeEquiv_measurePreserving n b).symm.integral_comp']
  simp only [spinCube_tensor_delta]
  have he (sx : Spins n × ((Fin n × Fin 3) → ℝ)) :
      star ((if sx.1 = (cubeLabelEquiv n a).1 then (1:ℂ) else 0) *
        finiteCubeMode b (cubeLabelEquiv n a).2 sx.2) * cubeState ψ ((spinCubeEquiv n).symm sx) =
      (if sx.1 = (cubeLabelEquiv n a).1 then (1:ℂ) else 0) *
        (star (finiteCubeMode b (cubeLabelEquiv n a).2 sx.2) *
          ψ.value (cubeLabelEquiv n a).1 (WithLp.toLp 2 sx.2)) := by
    by_cases h : sx.1 = (cubeLabelEquiv n a).1
    · simp only [ite_eq_left h, one_mul]
      change star _ * ψ.value sx.1 (WithLp.toLp 2 sx.2) = _
      rw [h]
    · simp only [ite_eq_right h, zero_mul, star_zero]
  simp_rw [he]
  rw [integral_prod_mul (fun s : Spins n => if s = (cubeLabelEquiv n a).1 then (1:ℂ) else 0)
    (fun x => star (finiteCubeMode b (cubeLabelEquiv n a).2 x) *
      ψ.value (cubeLabelEquiv n a).1 (WithLp.toLp 2 x)), integral_count]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_mul]
  rfl

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end OAI
