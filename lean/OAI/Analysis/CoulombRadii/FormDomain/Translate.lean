import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.CubeMassMass

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
namespace Coulomb
lemma weak_partial_translate {n : ℕ} (ψ : H1Vector n) (c : Configuration n)
    (s : Spins n) (a : Fin n × Fin 3) (φ : Configuration n → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, ψ.value s (x+c) * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
      -(∫ x, ψ.gradient s a (x+c) * (φ x : ℂ)) := by
  let Φ : Configuration n → ℝ := fun y => φ (y-c)
  have HΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hφ.comp (contDiff_id.sub contDiff_const)
  have HC : HasCompactSupport Φ := by
    simpa only [Φ, Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
      hcφ.comp_homeomorph (Homeomorph.addRight (-c))
  have Hd (y : Configuration n) : fderiv ℝ Φ y = fderiv ℝ φ (y-c) := by
    change fderiv ℝ (φ ∘ (fun y => id y - c)) y = _
    rw [fderiv_comp y (hφ.differentiable (by simp)).differentiableAt
      (differentiable_id.sub_const c).differentiableAt]
    simp only [fderiv_sub_const, id_eq, fderiv_fun_id, ContinuousLinearMap.comp_id]
  have H := ψ.weak_partial s a Φ HΦ HC
  simp_rw [Hd] at H
  have mp := measurePreserving_add_right (volume : Measure (Configuration n)) c
  rw [← (show MeasurePreserving (MeasurableEquiv.addRight c) volume volume from mp).integral_comp' (fun y => ψ.value s y *
    (fderiv ℝ φ (y-c) (EuclideanSpace.single a 1) : ℂ)),
    ← (show MeasurePreserving (MeasurableEquiv.addRight c) volume volume from mp).integral_comp' (fun y => ψ.gradient s a y * (Φ y : ℂ))] at H
  simpa only [Φ, MeasurableEquiv.coe_addRight, add_sub_cancel_right] using H

noncomputable def H1Vector.translate {n : ℕ} (ψ : H1Vector n) (c : Configuration n) :
    H1Vector n where
  value := fun s x => ψ.value s (x+c)
  gradient := fun s a x => ψ.gradient s a (x+c)
  value_L2 := fun s => (ψ.value_L2 s).comp_measurePreserving
    (measurePreserving_add_right volume c)
  partial_L2 := fun s a => (ψ.partial_L2 s a).comp_measurePreserving
    (measurePreserving_add_right volume c)
  weak_partial := weak_partial_translate ψ c

lemma permute_add {n : ℕ} (p : Equiv.Perm (Fin n)) (x c : Configuration n) :
    permute p (x+c) = permute p x + permute p c := by
  ext ij
  rfl

lemma mass_translate {n : ℕ} (ψ : H1Vector n) (c : Configuration n) :
    mass (ψ.translate c) = mass ψ := by
  unfold mass H1Vector.translate
  congr 1
  funext s
  exact integral_add_right_eq_self (fun x => ‖ψ.value s x‖^2) c

lemma kinetic_translate {n : ℕ} (ψ : H1Vector n) (c : Configuration n) :
    kinetic (ψ.translate c) = kinetic ψ := by
  unfold kinetic H1Vector.translate
  congr 2
  funext s
  congr 1
  funext a
  exact integral_add_right_eq_self (fun x => ‖ψ.gradient s a x‖^2) c

noncomputable def commonShift {n : ℕ} (t : Fin 3 → ℝ) : Configuration n :=
  WithLp.toLp 2 (fun ij => t ij.2)

lemma Antisymmetric.translate_common {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ)
    (t : Fin 3 → ℝ) : Antisymmetric (ψ.translate (commonShift t)) := by
  intro p s
  have H := (measurePreserving_add_right (volume : Measure (Configuration n))
    (commonShift t)).quasiMeasurePreserving.ae (hψ p s)
  filter_upwards [H] with x hx
  simpa only [H1Vector.translate, permute_add, show permute p (commonShift t) = commonShift t from rfl] using hx

noncomputable def spinSpaceMeasure : Measure (Fin 2 × (Fin 3 → ℝ)) := Measure.count.prod volume
instance spinSpaceMeasure_sigmaFinite : SigmaFinite spinSpaceMeasure := by
  unfold spinSpaceMeasure
  infer_instance

def centeredSpinCube (R : ℝ) : Set (Fin 2 × (Fin 3 → ℝ)) :=
  univ ×ˢ (univ.pi fun _ : Fin 3 => Ioc (-R) R)
lemma centeredSpinCube_measurable (R : ℝ) : MeasurableSet (centeredSpinCube R) :=
  MeasurableSet.univ.prod (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))

noncomputable def centeredSpinMeasure (R : ℝ) : Measure (Fin 2 × (Fin 3 → ℝ)) :=
  spinSpaceMeasure.restrict (centeredSpinCube R)
instance centeredSpinMeasure_sigmaFinite (R : ℝ) : SigmaFinite (centeredSpinMeasure R) := by
  unfold centeredSpinMeasure
  infer_instance

noncomputable def spinShift (t : Fin 3 → ℝ) :
    (Fin 2 × (Fin 3 → ℝ)) ≃ᵐ (Fin 2 × (Fin 3 → ℝ)) :=
  (MeasurableEquiv.refl (Fin 2)).prodCongr (MeasurableEquiv.addRight t)

lemma spinShift_measurePreserving (t : Fin 3 → ℝ) :
    MeasurePreserving (spinShift t) spinSpaceMeasure spinSpaceMeasure :=
  (MeasurePreserving.id Measure.count).prod (measurePreserving_add_right volume t)

lemma spinCubeMeasure_eq_restrict (b : ℝ) : spinCubeMeasure b =
    spinSpaceMeasure.restrict (univ ×ˢ (univ.pi fun _ : Fin 3 => Ioc 0 b)) := by
  unfold spinCubeMeasure spinSpaceMeasure cubeMeasure
  rw [← Measure.restrict_pi_pi]
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  rfl

lemma shift_centeredCube_measurePreserving (R : ℝ) :
    MeasurePreserving (spinShift (fun _ => -R)) (spinCubeMeasure (2*R)) (centeredSpinMeasure R) := by
  have he : (spinShift (fun _ => -R)) ⁻¹' centeredSpinCube R =
      univ ×ˢ (univ.pi fun _ : Fin 3 => Ioc 0 (2*R)) := by
    ext x
    simp only [centeredSpinCube, mem_preimage, mem_prod, mem_univ, true_and, mem_univ_pi,
      mem_Ioc]
    change (∀ i, -R < x.2 i + -R ∧ x.2 i + -R ≤ R) ↔
      (∀ i, 0 < x.2 i ∧ x.2 i ≤ 2*R)
    constructor <;> intro h i <;> obtain ⟨h1,h2⟩ := h i <;> constructor <;> linarith
  refine ⟨(spinShift _).measurable, ?_⟩
  rw [spinCubeMeasure_eq_restrict, ← he, ← MeasurableEquiv.restrict_map,
    (spinShift_measurePreserving _).map_eq]
  rfl

lemma firstParticleDensity_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite ν] (e : A ≃ᵐ B)
    (he : MeasurePreserving e μ ν) {n : ℕ} (f : (Fin (n+1) → B) → ℂ) (x : A) :
    firstParticleDensity (μ := μ) (fun z => f (e ∘ z)) x =
      firstParticleDensity (μ := ν) f (e x) := by
  let E : (Fin n → A) ≃ᵐ (Fin n → B) := MeasurableEquiv.piCongrRight (fun _ => e)
  have hE : MeasurePreserving E (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν) :=
    measurePreserving_pi _ _ (fun _ => he)
  unfold firstParticleDensity
  congr 1
  rw [← hE.integral_comp' (fun y => ‖firstFiber f (y,e x)‖^2)]
  congr 1
  funext y
  have harg : e ∘ Fin.cons x y = Fin.cons (e x) (E y) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simp only [firstFiber, harg]

lemma cubeState_translate {n : ℕ} (ψ : H1Vector n) (t : Fin 3 → ℝ)
    (z : Fin n → (Fin 2 × (Fin 3 → ℝ))) :
    cubeState (ψ.translate (commonShift t)) z = cubeState ψ ((spinShift t) ∘ z) := rfl

theorem centered_density_power_bound {n : ℕ} (ψ : H1Vector (n+1)) (hψ : Antisymmetric ψ)
    (hm : mass ψ ≤ 1) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x => (firstParticleDensity (μ := centeredSpinMeasure R) (cubeState ψ) x)^(5/3:ℝ))
      (centeredSpinMeasure R) ∧
    (∫ x, (firstParticleDensity (μ := centeredSpinMeasure R) (cubeState ψ) x)^(5/3:ℝ)
      ∂(centeredSpinMeasure R)) ≤ (64/R^2)*((n+1:ℕ):ℝ) + (8192/(3*Real.pi^2))*kinetic ψ := by
  have H := cube_density_power_bound (ψ.translate (commonShift (fun _ => -R)))
    (hψ.translate_common _) (by rwa [mass_translate]) (show 0 < 2*R by positivity)
  have hd (x) : firstParticleDensity (μ := spinCubeMeasure (2*R))
      (cubeState (ψ.translate (commonShift (fun _ => -R)))) x =
      firstParticleDensity (μ := centeredSpinMeasure R) (cubeState ψ) (spinShift (fun _ => -R) x) := by
    rw [show cubeState (ψ.translate (commonShift (fun _ => -R))) =
      (fun z => cubeState ψ ((spinShift (fun _ => -R)) ∘ z)) from
      funext (cubeState_translate ψ (fun _ => -R))]
    exact firstParticleDensity_equiv (spinShift (fun _ => -R))
      (shift_centeredCube_measurePreserving R) (cubeState ψ) x
  simp_rw [hd] at H
  refine ⟨?_, ?_⟩
  · exact ((shift_centeredCube_measurePreserving R).integrable_comp_emb
      (spinShift _).measurableEmbedding).mp H.1
  · have H2 := H.2
    rw [(shift_centeredCube_measurePreserving R).integral_comp'
      (fun x => (firstParticleDensity (μ := centeredSpinMeasure R) (cubeState ψ) x)^(5/3:ℝ)),
      kinetic_translate] at H2
    convert H2 using 1
    ring

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
