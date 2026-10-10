import OAI.Geometry.NodalSets.Waves.FiniteGaussianMap
import OAI.Geometry.NodalSets.Waves.SeededGaussianJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι]

abbrev JetSpace := EuclideanSpace ℝ (Fin 5)

def normalizedRealJet (f : Coord → ℝ) (N S : ℝ) (x : Coord) : JetSpace :=
  WithLp.toLp 2 (Fin.cons (Real.exp (-N*S)*f x)
    (fun i : Fin 4 ↦ Real.exp (-N*S)*N⁻¹*fderiv ℝ f x (Pi.single i 1)))

lemma normalizedRealJet_inner (f : Coord → ℝ) (N S : ℝ) (x : Coord) (v : JetSpace) :
    ⟪v,normalizedRealJet f N S x⟫ =
      Real.exp (-N*S)*(v 0*f x+N⁻¹*fderiv ℝ f x (Fin.tail (WithLp.ofLp v))) := by
  have he : Fin.tail (WithLp.ofLp v) = ∑ i : Fin 4, (v i.succ) • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply,Fin.tail]
  rw [he,map_sum]
  simp only [map_smul,smul_eq_mul]
  simp only [normalizedRealJet,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring

def jetWaveCoefficients (V : ι → Coord → ℂ) (N S : ℝ) (x : Coord) : Fin 5 → ι → ℂ :=
  Fin.cons (fun i ↦ dualWaveCoefficient N (V i) S x 1 0)
    (fun j i ↦ dualWaveCoefficient N (V i) S x 0 (Pi.single j 1))

lemma gaussianWaveField_normalizedJet (V : ι → Coord → ℂ) (N S : ℝ) (x : Coord)
    (hV : ∀ i, DifferentiableAt ℝ (V i) x) (a : ι × Fin 2 → ℝ) :
    normalizedRealJet (gaussianWaveField V a) N S x =
      pairJetMap (jetWaveCoefficients V N S x) (WithLp.toLp 2 a) := by
  ext k
  rw [pairJetMap_apply]
  refine Fin.cases ?_ (fun j ↦ ?_) k
  · simpa [normalizedRealJet,jetWaveCoefficients] using
      gaussianWaveField_dual V a x 0 hV N S 1
  · simpa [normalizedRealJet,jetWaveCoefficients,mul_assoc] using
      gaussianWaveField_dual V a x (Pi.single j 1) hV N S 0

lemma normalizedRealJet_add (f g : Coord → ℝ) (N S : ℝ) (x : Coord)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    normalizedRealJet (fun y ↦ f y+g y) N S x =
      normalizedRealJet f N S x+normalizedRealJet g N S x := by
  ext k
  refine Fin.cases ?_ (fun j ↦ ?_) k
  · simp [normalizedRealJet,mul_add]
  · simp [normalizedRealJet,fderiv_fun_add hf hg,mul_add]

lemma seeded_gaussian_jet_eq (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (N S : ℝ) (x : Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x)
    (hs : DifferentiableAt ℝ seed x) (a : ι × Fin 2 → ℝ) :
    normalizedRealJet (fun y ↦ seed y+gaussianWaveField V a y) N S x =
      normalizedRealJet seed N S x+
        pairJetMap (jetWaveCoefficients V N S x) (WithLp.toLp 2 a) := by
  rw [normalizedRealJet_add _ _ _ _ _ hs (gaussianWaveField_differentiable V a x hV),
    gaussianWaveField_normalizedJet V N S x hV]

lemma seeded_gaussian_jet_law (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (N S : ℝ) (x : Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x)
    (hs : DifferentiableAt ℝ seed x) :
    (gaussianPairs (ι := ι)).map (fun a ↦
      normalizedRealJet (fun y ↦ seed y+gaussianWaveField V a y) N S x) =
      (stdGaussian (EuclideanSpace ℝ (ι × Fin 2))).map
        (fun z ↦ normalizedRealJet seed N S x+pairJetMap (jetWaveCoefficients V N S x) z) := by
  simp_rw [seeded_gaussian_jet_eq V seed N S x hV hs]
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma seeded_gaussian_jet_variance (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (N S : ℝ) (x : Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x)
    (hs : DifferentiableAt ℝ seed x) (v : JetSpace) :
    Var[fun a : ι × Fin 2 → ℝ ↦
      ⟪v,normalizedRealJet (fun y ↦ seed y+gaussianWaveField V a y) N S x⟫; gaussianPairs] =
      ‖(pairJetMap (jetWaveCoefficients V N S x)).adjoint v‖^2 := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by
    unfold gaussianPairs
    infer_instance
  simp_rw [seeded_gaussian_jet_eq V seed N S x hV hs,inner_add_right]
  rw [variance_const_add (by fun_prop)]
  exact variance_gaussianMap_inner _ v

end
end Yau.Geometry

end OAI
