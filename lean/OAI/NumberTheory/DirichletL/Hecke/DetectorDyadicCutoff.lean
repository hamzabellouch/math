import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicProfiles
import OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesCutoffs

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open HeckeDetectorProfiles

lemma exists_positive_annular : ∃ W : ℝ→ℂ,
    ContDiff ℝ ∞ W ∧ Function.support W⊆Icc (1/4) (9/4) ∧
    ∀ x : ℝ, 0≤x → W x=DyadicTransfer.annularCutoff cutoff x := by
  obtain ⟨g,hgc,hgs,hgone,hgsupp,hgzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff 3 (by norm_num)
  let W : ℝ→ℂ := fun x => g (4*x-5)*DyadicTransfer.annularCutoff cutoff x
  have hs : ContDiff ℝ ∞ (DyadicTransfer.annularCutoff cutoff) :=
    (cutoff.smooth ⊤).sub ((cutoff.smooth ⊤).comp (by fun_prop))
  refine ⟨W,(hgs.comp (by fun_prop)).mul hs,?_,?_⟩
  · intro x hx
    have hg : g (4*x-5)≠0 := (mul_ne_zero_iff.mp hx).1
    have hh := hgsupp (subset_tsupport g hg)
    constructor <;> norm_num at hh <;> linarith [hh.1,hh.2]
  · intro x hx
    by_cases hh : DyadicTransfer.annularCutoff cutoff x=0
    · simp [W,hh]
    have ha := HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx 0
      (by simpa using hh)
    norm_num at ha
    have hg : g (4*x-5)=1 := hgone _ (abs_le.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩)
    simp only [W,hg,one_mul]

def positiveAnnular : ℝ→ℂ := Classical.choose exists_positive_annular

lemma positiveAnnular_smooth : ContDiff ℝ ∞ positiveAnnular :=
  (Classical.choose_spec exists_positive_annular).1

lemma positiveAnnular_support : Function.support positiveAnnular⊆Icc (1/4) (9/4) :=
  (Classical.choose_spec exists_positive_annular).2.1

lemma positiveAnnular_eq (x : ℝ) (hx : 0≤x) :
    positiveAnnular x=DyadicTransfer.annularCutoff cutoff x :=
  (Classical.choose_spec exists_positive_annular).2.2 x hx

lemma positiveAnnular_zero (x : ℝ) (hx : 2≤x) : positiveAnnular x=0 := by
  rw [positiveAnnular_eq x (by linarith)]
  exact DyadicTransfer.annularCutoff_eq_zero_of_two_le cutoff cutoff_zero hx

theorem actual_profile_bounds :
    ∃ C : ℕ→ℝ, (∀ j, 0<C j) ∧
      (∀ j : ℕ, ∀ σ : ℝ, σ∈Icc (-2) 2 → ∀ t : ℝ,
        (1+|t|)^j*‖mellin positiveAnnular ((σ : ℂ)+t*Complex.I)‖≤C j) ∧
      (∀ j : ℕ, ∀ Dstar D : ℝ, 0<Dstar → 0≤D → D≤4*Dstar →
        ∀ σ : ℝ, σ∈Icc (-2) 2 → ∀ t : ℝ,
        (1+|t|)^j*‖mellin (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)
          ((σ : ℂ)+t*Complex.I)‖≤C j) :=
  exists_profile_bounds cutoff positiveAnnular (cutoff.smooth ⊤) positiveAnnular_smooth
    (1/4) (9/4) (by norm_num) positiveAnnular_support (-2) 2

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI
