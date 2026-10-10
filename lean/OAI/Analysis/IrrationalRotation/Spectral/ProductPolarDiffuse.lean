import OAI.Analysis.IrrationalRotation.Spectral.ProductWeightPolar
import OAI.Analysis.IrrationalRotation.Analysis.PurePointDiffuse
import OAI.Analysis.IrrationalRotation.Analysis.OrbitFiberNull
import OAI.Analysis.IrrationalRotation.Product.ProductOrbitFiberNull

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem polarConjugate_multiplier_hasCountablyAtomicSpectralType
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hcount : ∃ R : Set ℝ, R.Countable ∧ ∀ᵐ x ∂baseMeasure, f x ∈ R)
    (n : ℤ) :
    HasCountablyAtomicSpectralType
      (polarConjugate shiftOperator
        (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb) n) := by
  obtain ⟨R, hR, hmem⟩ := hcount
  let S : Set ℂ := Complex.ofReal '' R
  have hS : S.Countable := hR.image _
  refine ⟨S, hS, ?_⟩
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hbasis (v : Fiber) (k : ℤ) : inner ℂ (b k) v = v k :=
    (b.repr_apply_apply v k).symm
  have hmeas (k : ℤ) : Measurable (fun x => (f (rotationIterate θ (k - n) x) : ℂ)) :=
    hf.complex_ofReal.comp (rotationIterate_measurePreserving_polar θ (k - n)).measurable
  have hrange (k : ℤ) :
      ∀ᵐ x ∂baseMeasure, (f (rotationIterate θ (k - n) x) : ℂ) ∈ S := by
    filter_upwards [(rotationIterate_measurePreserving_polar θ (k - n)).quasiMeasurePreserving.ae hmem]
      with x hx
    exact Set.mem_image_of_mem Complex.ofReal hx
  apply MultiplicationPurePoint.topologicalClosure_iSup_eigenspace_eq_top_of_basis b
    (fun k x => (f (rotationIterate θ (k - n) x) : ℂ)) hmeas hS hrange
  intro v k
  simpa only [hbasis] using
    (polarConjugate_multiplier_coordinate_ae θ _ C hC hf.complex_ofReal hb n v).mono
      (fun x hx => hx k)

theorem coefficient_fiber_null_of_orbit_fiber_null
    (θ : ℕ → ℝ) (f : Base → ℝ)
    (hnull : ∀ z : ℤ → ℝ,
      baseMeasure {x | ∀ n : ℤ, f (rotationIterate θ n x) = z n} = 0)
    (ev : ℤ → ℂ) (k : ℤ) :
    baseMeasure {x | ∀ n : ℤ, (f (rotationIterate θ (k - n) x) : ℂ) = ev n} = 0 := by
  apply measure_mono_null _ (hnull (fun m => (ev (k - m)).re))
  intro x hx m
  have h := congrArg Complex.re (hx (k - m))
  simpa only [sub_sub_cancel, Complex.ofReal_re] using h

theorem jointEigenspace_polarConjugates_eq_bot_of_null_fibers
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hnull : ∀ z : ℤ → ℝ,
      baseMeasure {x | ∀ n : ℤ, f (rotationIterate θ n x) = z n} = 0)
    (ev : ℤ → ℂ) :
    jointEigenspace (polarConjugate shiftOperator
      (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb)) ev = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have heigen := mem_jointEigenspace.mp hv
  have hcoord : ∀ n : ℤ, ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (f (rotationIterate θ (k - n) x) : ℂ) * v x k = ev n * v x k := by
    intro n
    filter_upwards [polarConjugate_multiplier_coordinate_ae θ _ C hC
      hf.complex_ofReal hb n v, Lp.coeFn_smul (ev n) v] with x hx hs k
    have h := congrArg (fun w : Hilbert => w x k) (heigen n)
    rw [hx, hs] at h
    exact h
  have havoid : ∀ k : ℤ, ∀ᵐ x ∂baseMeasure,
      ¬ ∀ n : ℤ, (f (rotationIterate θ (k - n) x) : ℂ) = ev n := by
    intro k
    exact measure_eq_zero_iff_ae_notMem.mp
      (coefficient_fiber_null_of_orbit_fiber_null θ f hnull ev k)
  have hvzero : v = 0 := by
    apply Lp.ext
    filter_upwards [ae_all_iff.mpr hcoord, ae_all_iff.mpr havoid,
      Lp.coeFn_zero Fiber 2 baseMeasure] with x hx hav hz
    rw [hz]
    apply lp.ext
    funext k
    change v x k = 0
    by_contra hvk
    apply hav k
    intro n
    exact mul_right_cancel₀ hvk (hx n k)
  exact hvzero

theorem fullPolarAlgebra_multiplier_diffuse_of_null_fibers
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hcount : ∃ R : Set ℝ, R.Countable ∧ ∀ᵐ x ∂baseMeasure, f x ∈ R)
    (hnull : ∀ z : ℤ → ℝ,
      baseMeasure {x | ∀ n : ℤ, f (rotationIterate θ n x) = z n} = 0) :
    IsDiffuseVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator
        (multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb)) := by
  apply generated_isDiffuse_of_purePoint_no_jointEigenvectors
  · exact fullPolarAlgebra_multiplier_abelian θ f C hC hf hb
  · exact polarConjugate_multiplier_hasCountablyAtomicSpectralType θ f C hC hf hb hcount
  · exact jointEigenspace_polarConjugates_eq_bot_of_null_fibers θ f C hC hf hb hnull

theorem fullPolarAlgebra_weight_diffuse
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    IsDiffuseVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c)) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  obtain ⟨S, hS, -, hmem⟩ := ae_weight_mem_countable θ c
    (fun i => ⟨(hadm.1 i).1.le, (hadm.1 i).2.1⟩)
    (fun i => (hadm.1 i).2.2.le) hadm.2.1
  exact fullPolarAlgebra_multiplier_diffuse_of_null_fibers θ (weight θ c) 1
    (by norm_num) (measurable_weight θ c) (weight_complex_norm_le_one θ c)
    ⟨S, hS, hmem⟩ (weight_rotation_joint_fiber_measure_zero θ c hadm hdiv)

end Invariant233.ProductModel

end

end OAI
