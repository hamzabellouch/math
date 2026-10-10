import OAI.Probability.DilutedSpin.MarkerVariance

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {Z : Type} [MeasurableSpace Z]

noncomputable def mixedVariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ) : ℝ :=
  (∫ z, (P z).expect (fun w => (F z w)^2) ∂μ) - (∫ z, (P z).expect (F z) ∂μ)^2

lemma mixedVariance_eq_centered (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hF : Integrable (fun z => (P z).expect (F z)) μ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ) :
    mixedVariance μ Ω P F = ∫ z, (P z).expect
      (fun w => (F z w-(∫ z, (P z).expect (F z) ∂μ))^2) ∂μ := by
  let c := ∫ z, (P z).expect (F z) ∂μ
  have he (z : Z) : (P z).expect (fun w => (F z w-c)^2)=
      (P z).expect (fun w => (F z w)^2) - 2*c*(P z).expect (F z)+c^2 := by
    calc
      _ = (P z).expect (fun w => (F z w)^2-(2*c)*F z w+c^2) :=
        (P z).expect_congr (fun w => by ring)
      _ = _ := by simp only [expect_add,expect_sub,expect_mul_left,expect_const]
  change _=∫ z, (P z).expect (fun w => (F z w-c)^2) ∂μ
  simp_rw [he]
  have hm : Integrable (fun z => 2*c*(P z).expect (F z)) μ := hF.const_mul (2*c)
  have hd : Integrable (fun z => (P z).expect (fun w => (F z w)^2)-2*c*(P z).expect (F z)) μ := hFsq.sub hm
  rw [integral_add hd (integrable_const _),
    integral_sub hFsq hm,integral_const_mul,integral_const]
  simp only [probReal_univ,one_smul]
  unfold mixedVariance
  dsimp only [c]
  ring

lemma mixedVariance_nonneg (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hF : Integrable (fun z => (P z).expect (F z)) μ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ) :
    0 ≤ mixedVariance μ Ω P F := by
  rw [mixedVariance_eq_centered μ Ω P F hF hFsq]
  exact integral_nonneg (fun z => (P z).expect_nonneg (fun _ => sq_nonneg _))

lemma mixedVariance_le_one (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ)
    (hF : ∀ z w, |F z w|≤1) : mixedVariance μ Ω P F≤1 := by
  have he : ∀ z, (P z).expect (fun w => (F z w)^2)≤1 := by
    intro z
    exact ((P z).expect_mono (fun w => (sq_le_one_iff_abs_le_one _).mpr (hF z w))).trans_eq
      ((P z).expect_const 1)
  have h := integral_mono hFsq (integrable_const (1:ℝ)) he
  simp only [integral_const,probReal_univ,one_smul] at h
  unfold mixedVariance
  linarith [sq_nonneg (∫ z, (P z).expect (F z) ∂μ)]

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance rootOverlapVarianceDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

noncomputable def overlapVariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) : ℝ :=
  FiniteLaw.mixedVariance μ (fun z => Sample (Ω z) S)
    (fun z => S.sampleLaw (K z)) (fun z => treeOverlap S (V z))

noncomputable def markerDefect (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (A : PrescribedTree n) (r : ℕ) (K : (z : Z) → KernelTower (Ω z) (n+1+r))
    (V : (z : Z) → FinitePath (Ω z) (n+1+r) → Fin N → ℝ) : ℝ :=
  (∫ z, forkPairMean A r (K z) (V z) ∂μ) -
    (∫ z, ((stem (unary A) r).sampleLaw (K z)).expect (treeOverlap (stem (unary A) r) (V z)) ∂μ)^2

/-- Root and prefix randomness are both retained. The square root is taken
only after integrating the actual conditional energy. -/
theorem overlapVariance_le_marker (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (A : PrescribedTree n) (r : ℕ)
    (K : (z : Z) → KernelTower (Ω z) (n+1+r))
    (V : (z : Z) → FinitePath (Ω z) (n+1+r) → Fin N → ℝ)
    (hsq : Integrable (fun z => unarySquareMean A r (K z) (V z)) μ)
    (hpair : Integrable (fun z => forkPairMean A r (K z) (V z)) μ)
    (hE : Integrable (fun z => shapeEnergyAt A r (K z) (V z)) μ)
    (hEs : Integrable (fun z => Real.sqrt (shapeEnergyAt A r (K z) (V z))) μ) :
    overlapVariance μ Ω (stem (unary A) r) K V ≤
      Real.sqrt (∫ z, shapeEnergyAt A r (K z) (V z) ∂μ)+|markerDefect μ Ω A r K V| := by
  have h := integral_mono (hsq.sub hpair) hEs
    (fun z => marker_conditional_variance_le A r (K z) (V z))
  simp only [Pi.sub_apply] at h
  rw [integral_sub hsq hpair] at h
  have he := integral_sqrt_le_sqrt_integral μ _ hE hEs (fun z => shapeEnergyAt_nonneg A r (K z) (V z))
  have hd := le_abs_self (markerDefect μ Ω A r K V)
  unfold overlapVariance FiniteLaw.mixedVariance markerDefect unarySquareMean at *
  linarith

lemma concrete_marker_covariance_eq_defect (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (A : PrescribedTree n) (r : ℕ) (a : (stem (unary A) r).Leaf)
    (K : (z : Z) → KernelTower (Ω z) (n+1+r)) (m : Fin (n+1+r+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last (n+1+r))=1)
    (V : (z : Z) → FinitePath (Ω z) (n+1+r) → Fin N → ℝ) :
    matrixRootCovariance μ Ω (stem (markerFork A) r) (stem (unary A) r)
      (markerColorTarget A r) K m
      (List.ofFn (fun c : Fin (Fintype.card A.Leaf) => (some c : Option (Fin (Fintype.card A.Leaf))))).reverse a
      (fun z => spatialProduct (fun c x i => match c with | none => 1 | some _ => V z x i))
      (fun z => treeOverlap (stem (unary A) r) (V z)) =
    partialKappa (stem (markerFork A) r) m (Finset.univ.image (markerColorTarget A r)) *
      markerDefect μ Ω A r K V := by
  have h := concrete_marker_covariance μ Ω A r a K m hm hp hend V
  simp_rw [markerOld_overlap,markerFresh_overlap] at h
  unfold markerDefect forkPairMean
  exact h

end DilutedSpinGlass.PrescribedTree

end

end OAI
