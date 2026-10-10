import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteBoxMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedManufacturedResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedNuclearError
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteCoefficientCorrection
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCorrectedMatrixError

namespace OAI

/-! Actual corrected one-body matrix entries, including the singular nuclear
error. Finite change of basis preserves the quantitative entrywise estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem finiteTwoIndexChange_error {m : ℕ} (A F T : Fin m → Fin m → ℝ)
    {ε : ℝ} (hA : ∀ i j, |A i j| ≤ 2)
    (herror : ∀ i j, |F i j-T i j| ≤ ε) (i j : Fin m) :
    |finiteTwoIndexChange A F i j-finiteTwoIndexChange A T i j| ≤ 4*(m:ℝ)^2*ε := by
  have hb (p q : Fin m) : |(A i p*A j q)*(F p q-T p q)| ≤ 4*ε := by
    rw [abs_mul,abs_mul]
    have hc := mul_le_mul (hA i p) (hA j q) (abs_nonneg _) (by norm_num)
    have he := mul_le_mul hc (herror p q) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2*2)
    simpa only [show (2:ℝ)*2=4 by norm_num] using he
  unfold finiteTwoIndexChange
  simp only [← Finset.sum_sub_distrib,← mul_sub]
  calc
    _ ≤ ∑ p, ∑ q, |(A i p*A j q)*(F p q-T p q)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _p : Fin m, ∑ _q : Fin m, 4*ε :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hb p q))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem integral_finite_bilinear {m : ℕ} (f r : Fin m → Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => f i x*r j x)) (a b : Fin m → ℝ) :
    (∫ x, (∑ i, a i*f i x)*(∑ j, b j*r j x)) =
      ∑ i, ∑ j, (a i*b j)*(∫ x, f i x*r j x) := by
  have hi (i j : Fin m) : Integrable (fun x => (a i*b j)*(f i x*r j x)) :=
    (hI i j).const_mul _
  have he (x : Position) : (∑ i, a i*f i x)*(∑ j, b j*r j x) =
      ∑ i, ∑ j, (a i*b j)*(f i x*r j x) := by
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  simp only [integral_const_mul]

def correctedManufacturedOneBodyMatrix (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∫ x, correctedLocalizedMode freq u i x*correctedManufacturedResidual rho H S freq scale u j x

theorem correctedManufacturedOneBodyMatrix_eq {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (i j : Fin m) :
    correctedManufacturedOneBodyMatrix rho H S freq scale u i j =
      finiteTwoIndexChange (correctedLocalizedCoefficients u)
        (manufacturedRawOneBodyMatrix rho H S freq scale u) i j := by
  exact integral_finite_bilinear _ _ (fun p q =>
    (continuumLocalizedMode_memLp hfreq (u p)).integrable_mul
      (manufacturedOrbitalResidual_memLp hrho hH hS hfreq scale u hδ hcoeff q)) _ _

theorem correctedManufacturedOneBodyMatrix_error {rho H S freq D ε B : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hε : 0 ≤ ε) (herror : ∀ j, (∫ x, finiteBoxOrbitalResidual rho H S freq scale u j x^2) ≤ ε^2)
    (hB : 0 ≤ B) (hbound : ∀ i j, |localizedCorrectedOneBodyMatrix freq scale u i j| ≤ B)
    (i j : Fin m) :
    |correctedManufacturedOneBodyMatrix rho H S freq scale u i j-
      localizedCorrectedOneBodyMatrix freq scale u i j| ≤
      4*(m:ℝ)^2*ε+(m:ℝ)^2*(4*(2*m*localizedOverlapBound D)*B) := by
  have ha := fun p q => (correctedLocalizedCoefficients_entries u hsep hs p q).2
  have hnear : 0 ≤ 2*(m:ℝ)*localizedOverlapBound D :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) (localizedOverlapBound_nonnegative D)
  have he (p q : Fin m) : |manufacturedRawOneBodyMatrix rho H S freq scale u p q-
      localizedCorrectedOneBodyMatrix freq scale u p q| ≤ ε := by
    have hh := (manufacturedRawOneBodyMatrix_error_integral hrho hH.le hS hfreq scale u hδ hcoeff p q).trans (herror q)
    nlinarith [abs_nonneg (manufacturedRawOneBodyMatrix rho H S freq scale u p q-
      localizedCorrectedOneBodyMatrix freq scale u p q)]
  rw [correctedManufacturedOneBodyMatrix_eq hrho hH.le hS.le hfreq scale u hδ hcoeff]
  exact (abs_sub_le _ (finiteTwoIndexChange (correctedLocalizedCoefficients u)
    (localizedCorrectedOneBodyMatrix freq scale u) i j) _).trans (add_le_add
      (finiteTwoIndexChange_error _ _ _ ha he i j)
      (finiteTwoIndexChange_bound _ _ hnear hB ha
        (fun p q => (correctedLocalizedCoefficients_entries u hsep hs p q).1) hbound i j))

def correctedNuclearOneBodyMatrix (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (F : Position → ℝ) (i j : Fin m) : ℝ :=
  correctedManufacturedOneBodyMatrix rho H S freq scale u i j+
    ∫ x, F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x

theorem correctedNuclearOneBodyMatrix_error {rho H S freq D ε ν B : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    {scale : ℝ} (hscale : scale ≠ 0) {m : ℕ} (u : Fin m → PlanarPosition)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hε : 0 ≤ ε) (herror : ∀ j, (∫ x, finiteBoxOrbitalResidual rho H S freq scale u j x^2) ≤ ε^2)
    (hB : 0 ≤ B) (hbound : ∀ i j, |localizedCorrectedOneBodyMatrix freq scale u i j| ≤ B)
    (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x))
    (hF : ∀ i j, |∫ x, F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x| ≤ ν) (i j : Fin m) :
    |scale*correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
      localizedOneBodyTarget scale freq u i j| ≤
      |scale| *(4*(m:ℝ)^2*ε+(m:ℝ)^2*(4*(2*m*localizedOverlapBound D)*B)+4*(m:ℝ)^2*ν)+
        (|scale| *m*planarWellMatrixConstant+
          (m:ℝ)^2*localizedCountertermBound freq*planarWellMatrixConstant)*Real.exp (-(19/10:ℝ)*D)+
        (m:ℝ)^2*localizedCountertermBound freq*
          (PlanarSobolev.wellBound*planarOverlapConstant)*Real.exp (-(9/10:ℝ)*D) := by
  have hm := correctedManufacturedOneBodyMatrix_error hrho hH hS hfreq
    scale u hδ hcoeff hsep hs hε herror hB hbound i j
  have hn := (correctedLocalizedMode_nuclear_error u hsep hs F hI hF i j).2
  have ht := localizedCorrectedOneBodyMatrix_error hfreq hscale u hsep i j
  have he : |correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
      localizedCorrectedOneBodyMatrix freq scale u i j| ≤
      4*(m:ℝ)^2*ε+(m:ℝ)^2*(4*(2*m*localizedOverlapBound D)*B)+4*(m:ℝ)^2*ν := by
    unfold correctedNuclearOneBodyMatrix
    have hid : correctedManufacturedOneBodyMatrix rho H S freq scale u i j+
        (∫ x, F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x)-
        localizedCorrectedOneBodyMatrix freq scale u i j =
        (correctedManufacturedOneBodyMatrix rho H S freq scale u i j-
          localizedCorrectedOneBodyMatrix freq scale u i j)+
          (∫ x, F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x) := by ring
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add hm hn)
  calc
    _ ≤ |scale*(correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
          localizedCorrectedOneBodyMatrix freq scale u i j)|+
          |scale*localizedCorrectedOneBodyMatrix freq scale u i j-localizedOneBodyTarget scale freq u i j| := by
      have hid : scale*correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
          localizedOneBodyTarget scale freq u i j =
          scale*(correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
            localizedCorrectedOneBodyMatrix freq scale u i j)+
            (scale*localizedCorrectedOneBodyMatrix freq scale u i j-localizedOneBodyTarget scale freq u i j) := by ring
      rw [hid]
      exact abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      have hh := add_le_add (mul_le_mul_of_nonneg_left he (abs_nonneg scale)) ht
      convert hh using 1
      ring

end ContinuumCoulomb

end

end OAI
