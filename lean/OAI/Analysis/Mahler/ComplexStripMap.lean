import OAI.Analysis.Mahler.StripVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

def complexToReal (z : Fin n → ℂ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => (z i).re,fun i => (z i).im)

def realToComplex (z : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℂ :=
  fun i => (z.1 i : ℂ)+(z.2 i : ℂ)*I

lemma realToComplex_complexToReal (z : Fin n → ℂ) : realToComplex (complexToReal z) = z := by
  funext i
  exact Complex.re_add_im (z i)

lemma complexToReal_realToComplex (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    complexToReal (realToComplex z) = z := by
  apply Prod.ext <;> funext i <;> simp [complexToReal,realToComplex]

noncomputable def complexRealLinearEquiv : (Fin n → ℂ) ≃ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) where
  toFun := complexToReal
  invFun := realToComplex
  left_inv := realToComplex_complexToReal
  right_inv := complexToReal_realToComplex
  map_add' z w := by apply Prod.ext <;> funext i <;> simp [complexToReal]
  map_smul' c z := by apply Prod.ext <;> funext i <;> simp [complexToReal]

noncomputable def complexRealEquiv : (Fin n → ℂ) ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  complexRealLinearEquiv.toContinuousLinearEquiv

/-- The explicit separation of real and imaginary coordinates preserves
standard Lebesgue measure exactly, with no normalization factor. -/
lemma volume_preserving_complexToReal : MeasurePreserving (complexToReal (n := n)) := by
  have hp := volume_preserving_pi (ι := Fin n) (fun _ => Complex.volume_preserving_equiv_real_prod)
  have h := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).comp hp
  simpa [Function.comp_def,complexToReal,MeasurableEquiv.arrowProdEquivProdArrow,
    Equiv.arrowProdEquivProdArrow] using! h

noncomputable def complexRow (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) :
    (Fin n → ℂ) →L[ℂ] ℂ := ∑ i, (A j i : ℂ) • ContinuousLinearMap.proj i

lemma complexRow_apply (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (z : Fin n → ℂ) :
    complexRow A j z = ∑ i, (A j i : ℂ)*z i := by simp [complexRow]

lemma complexRow_re (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (z : Fin n → ℂ) :
    (complexRow A j z).re = measurement A (complexToReal z).1 j := by
  simp [complexRow_apply,measurement,complexToReal]

lemma complexRow_im (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (z : Fin n → ℂ) :
    (complexRow A j z).im = measurement A (complexToReal z).2 j := by
  simp [complexRow_apply,measurement,complexToReal]

lemma complexRow_eq_stripCoordinate (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (z : Fin n → ℂ) :
    complexRow A j z = stripCoordinate A (complexToReal z) j := by
  apply Complex.ext <;> simp [stripCoordinate,complexRow_re,complexRow_im]

noncomputable def complexStripDomain (A : Matrix (Fin N) (Fin n) ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, complexRow A j z ∈ Omega}

lemma complexStripDomain_eq_preimage (A : Matrix (Fin N) (Fin n) ℝ) :
    complexStripDomain A = complexToReal ⁻¹' stripDomain A := by
  ext z
  simp only [complexStripDomain,stripDomain,mem_ofPred_eq,Set.mem_preimage,complexRow_eq_stripCoordinate]

lemma isOpen_complexStripDomain (A : Matrix (Fin N) (Fin n) ℝ) : IsOpen (complexStripDomain A) := by
  rw [complexStripDomain_eq_preimage]
  exact (isOpen_stripDomain A).preimage complexRealEquiv.continuous

lemma zero_mem_complexStripDomain (A : Matrix (Fin N) (Fin n) ℝ) : 0 ∈ complexStripDomain A := by
  intro j
  simpa using zero_mem_Omega

noncomputable def specialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (z : Fin n → ℂ) : Fin N → ℂ :=
  fun j => inverseF (complexRow A j z)^m

/-- The holomorphic map used in the mass inequality. -/
theorem differentiableOn_specialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    DifferentiableOn ℂ (specialMap A m) (complexStripDomain A) := by
  apply differentiableOn_pi.mpr
  intro j
  have hr : DifferentiableOn ℂ (complexRow A j) (complexStripDomain A) :=
    (complexRow A j).differentiable.differentiableOn
  have hmaps : MapsTo (complexRow A j) (complexStripDomain A) Omega := fun z hz => hz j
  exact (differentiableOn_inverseF.comp hr hmaps).pow m

lemma complexRow_injective (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) :
    Function.Injective (fun z : Fin n → ℂ => fun j => complexRow A j z) := by
  intro z w h
  have hre : (complexToReal z).1 = (complexToReal w).1 := by
    apply hA
    funext j
    simpa [complexRow_re] using congrArg Complex.re (congrFun h j)
  have him : (complexToReal z).2 = (complexToReal w).2 := by
    apply hA
    funext j
    simpa [complexRow_im] using congrArg Complex.im (congrFun h j)
  have he := Prod.ext hre him
  exact complexRealLinearEquiv.injective he

/-- The actual map has precisely one common zero on its actual domain. -/
theorem specialMap_eq_zero_iff (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {z : Fin n → ℂ} (hz : z ∈ complexStripDomain A) : specialMap A m z = 0 ↔ z = 0 := by
  constructor
  · intro hf
    apply complexRow_injective A hA
    funext j
    have hp : inverseF (complexRow A j z)^m = 0 := congrFun hf j
    have h0 : inverseF (complexRow A j z) = 0 := by
      by_contra hn
      exact (pow_ne_zero m hn) hp
    simpa using (inverseF_eq_zero_iff (hz j)).mp h0
  · rintro rfl
    funext j
    simp [specialMap,inverseF_zero,hm.ne']

end SymmetricMahler

end OAI
