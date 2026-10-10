import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeSmoothWeights
import OAI.NumberTheory.CubicMoment.Estimates.UniformWeightCoordinates

namespace OAI

/-! A single uniform smooth family for the actual distinguished-prime
weights in each large-row norm piece. Both scale ratios are capped only
after proving that the cap leaves the weight unchanged. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def distinguishedSmoothWeight (r : ℝ × ℝ) (x : ℝ) : ℂ :=
  semiprimeSmoothWeight r.2 x-semiprimeSmoothWeight r.1 x

lemma distinguishedSmoothWeight_low (r : ℝ × ℝ) {x : ℝ} (hx : x < 1) :
    distinguishedSmoothWeight r x = 0 := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_low _ hx,sub_self]

lemma distinguishedSmoothWeight_high (r : ℝ × ℝ) {x : ℝ} (hx : 2 < x) :
    distinguishedSmoothWeight r x = 0 := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_high _ hx,sub_self]

lemma distinguishedSmoothWeight_norm (r : ℝ × ℝ) (x : ℝ) :
    ‖distinguishedSmoothWeight r x‖ ≤ 1 := by
  have he : distinguishedSmoothWeight r x = normPartitionWeight x*
      ((primeDetectorCutoff (r.1*x)-primeDetectorCutoff (r.2*x):ℝ):ℂ) := by
    simp only [distinguishedSmoothWeight,semiprimeSmoothWeight,Complex.ofReal_sub]
    ring
  have hb : |primeDetectorCutoff (r.1*x)-primeDetectorCutoff (r.2*x)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [primeDetectorCutoff_nonneg (r.1*x),
      primeDetectorCutoff_nonneg (r.2*x),primeDetectorCutoff_le_one (r.1*x),
      primeDetectorCutoff_le_one (r.2*x)]
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (normPartitionWeight_norm x) hb (abs_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

lemma distinguishedSmoothWeight_capped (r : ℝ × ℝ) (x : ℝ) :
    distinguishedSmoothWeight (min r.1 2,min r.2 2) x =
      distinguishedSmoothWeight r x := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_capped]

lemma distinguishedSmoothWeight_contDiff :
    ContDiff ℝ ∞ (Function.uncurry distinguishedSmoothWeight) := by
  change ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
    normPartitionWeight z.2*(1-(primeDetectorCutoff (z.1.2*z.2):ℂ))-
      normPartitionWeight z.2*(1-(primeDetectorCutoff (z.1.1*z.2):ℂ)))
  have hn : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => normPartitionWeight z.2) :=
    normPartitionWeight_smooth.comp contDiff_snd
  have h₁ : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      (primeDetectorCutoff (z.1.1*z.2):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (primeDetectorCutoff_smooth.comp ((contDiff_fst.fst).mul contDiff_snd))
  have h₂ : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      (primeDetectorCutoff (z.1.2*z.2):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (primeDetectorCutoff_smooth.comp ((contDiff_fst.snd).mul contDiff_snd))
  exact (hn.mul (contDiff_const.sub h₂)).sub (hn.mul (contDiff_const.sub h₁))

lemma distinguishedSmoothWeight_support (r : ℝ × ℝ) :
    Function.support (distinguishedSmoothWeight r) ⊆ Function.support normPartitionWeight := by
  intro x hx
  change normPartitionWeight x ≠ 0
  intro hn
  apply hx
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight,hn,zero_mul,sub_self]

def compactDistinguishedSmoothWeights : UniformLogWeights
    (fun r : (Icc (0:ℝ) 2) ×ˢ (Icc (0:ℝ) 2) => distinguishedSmoothWeight r) :=
  uniformLogWeights_compactParameter _ (isCompact_Icc.prod isCompact_Icc)
    distinguishedSmoothWeight normPartitionWeight normPartitionWeight_compact
    normPartitionWeight_positive_support normPartitionWeight_smooth distinguishedSmoothWeight_contDiff
    (fun r _ => distinguishedSmoothWeight_support r)

def distinguishedSmoothWeights :
    UniformLogWeights (fun r : Ici (0:ℝ) × Ici (0:ℝ) =>
      distinguishedSmoothWeight ((r.1:ℝ),(r.2:ℝ))) := by
  let c : Ici (0:ℝ) × Ici (0:ℝ) → (Icc (0:ℝ) 2) ×ˢ (Icc (0:ℝ) 2) := fun r =>
    ⟨(min (r.1:ℝ) 2,min (r.2:ℝ) 2),
      ⟨⟨le_min r.1.property (by norm_num),min_le_right _ _⟩,
        ⟨le_min r.2.property (by norm_num),min_le_right _ _⟩⟩⟩
  have he : (fun r : Ici (0:ℝ) × Ici (0:ℝ) => distinguishedSmoothWeight (c r)) =
      (fun r => distinguishedSmoothWeight ((r.1:ℝ),(r.2:ℝ))) := by
    funext r x
    change distinguishedSmoothWeight (min (r.1:ℝ) 2,min (r.2:ℝ) 2) x =
      distinguishedSmoothWeight ((r.1:ℝ),(r.2:ℝ)) x
    exact distinguishedSmoothWeight_capped ((r.1:ℝ),(r.2:ℝ)) x
  rw [←he]
  exact compactDistinguishedSmoothWeights.reindex c

lemma distinguishedSmoothWeight_at_prime {A : ℝ} (hA : 0 < A)
    (w z : ℝ) (p : Eisenstein) :
    distinguishedSmoothWeight (A/w,A/z) (norm p/A) =
      normPartitionWeight (norm p/A)*distinguishedPrimeWeight primeDetectorCutoff w z p := by
  have he (r : ℝ) : (A/r)*(norm p/A) = norm p/r := by
    simp only [div_eq_mul_inv]
    calc
      A*r⁻¹*(norm p*A⁻¹) = (A*A⁻¹)*(norm p*r⁻¹) := by ring
      _ = norm p*r⁻¹ := by rw [mul_inv_cancel₀ hA.ne',one_mul]
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight,he,distinguishedPrimeWeight]
  push_cast
  ring

def largePrimeSmoothWeight (r : Ici (0:ℝ) × Ici (0:ℝ)) (distinguished : Bool) : ℝ → ℂ :=
  if distinguished then distinguishedSmoothWeight ((r.1:ℝ),(r.2:ℝ))
  else semiprimeSmoothWeight r.1

def largePrimeSmoothWeights : UniformLogWeights
    (fun z : (Ici (0:ℝ) × Ici (0:ℝ)) × Bool => largePrimeSmoothWeight z.1 z.2) := by
  apply UniformLogWeights.finiteCoordinates
  intro b
  cases b
  · exact semiprimeSmoothWeights.reindex (fun r : Ici (0:ℝ) × Ici (0:ℝ) => r.1)
  · exact distinguishedSmoothWeights

end CubicFirstMoment

end

end OAI
