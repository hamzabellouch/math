import Mathlib
import OAI.Probability.SKGap.Matrix.RealSymmetricResolventUnit
import OAI.Probability.SKGap.Brownian.PathDiagonal

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def expectedCutoff (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (D C : Matrix ι ι ℝ) (r : ℝ) (i : ι) : ℝ :=
  ∫ g, realTruncatedK f R hR D C (goeMatrix r g) i i
    ∂(Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))

noncomputable def cutoffErrorOne (f : 𝓢(ℝ,ℂ)) (r R lo hi : ℝ)
    (D C : Matrix ι ι ℝ) : ℝ :=
  let b := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
  let L := Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C))
  let Lπ : ℝ≥0 := L*(⟨sqrt (2*r),sqrt_nonneg _⟩ *
    (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
  let T : ℝ≥0 := (⟨sqrt (Fintype.card ι)*opNorm (D*D),
    mul_nonneg (sqrt_nonneg _) (norm_nonneg _)⟩*L)*⟨sqrt (2*r),sqrt_nonneg _⟩+1
  (Fintype.card ι:ℝ)*(sqrt (2*r)*(Lπ:ℝ)+r*(2*b*opNorm (D*D)*b))*
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet r R lo hi D C)ᶜ+
    r*(b*((2*Real.exp (π^2/8))*(T:ℝ))+b*opNorm (D*D)*b)

noncomputable def cutoffErrorTwo (f : 𝓢(ℝ,ℂ)) (r R lo hi : ℝ)
    (d c : ι → ℝ) (i : ι) : ℝ :=
  let b := ComplexMatrix.kBound f R (liftMatrix (diagonal d)) (liftMatrix (diagonal c))
  let p := (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
    (truncationGoodSet r R lo hi (diagonal d) (diagonal c))ᶜ
  (b+1+|(d i)^2*c i| *b)*p+
    (|(d i)^2| *b)*(Fintype.card ι:ℝ)*sqrt (2*r)*sqrt p

lemma integrated_diagonal_trace (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (d c : ι → ℝ) (r : ℝ) :
    (∫ g, trace (realTruncatedK f R hR (diagonal d) (diagonal c) (goeMatrix r g)*
      (diagonal d*diagonal d))
      ∂(Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))) =
      ∑ b, (d b)^2*expectedCutoff f R hR (diagonal d) (diagonal c) r b := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let K := fun g => realTruncatedK f R hR (diagonal d) (diagonal c) (goeMatrix r g)
  let B := ComplexMatrix.kBound f R (liftMatrix (diagonal d)) (liftMatrix (diagonal c))
  have hc : Continuous K := (realTruncatedK_lipschitz f hR _ _ (diagonal_transpose _) (diagonal_transpose _)).continuous.comp
    (goeMatrix_pi_lipschitz r).continuous
  have hi (b : ι) : Integrable (fun g => K g b b) μ :=
    Integrable.mono' (integrable_const B) (hc.matrix_elem b b).aestronglyMeasurable
      (ae_of_all _ (fun g => by
        rw [Real.norm_eq_abs]
        exact (matrix_entry_le_opNorm _ b b).trans
          (realTruncatedK_opNorm f hR _ _ _ (diagonal_transpose _) (diagonal_transpose _))))
  have he (g : MatrixCoordinates ι → ℝ) : trace (K g*(diagonal d*diagonal d)) =
      ∑ b, (d b)^2*K g b b := by
    rw [diagonal_mul_diagonal]
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [show (fun g => trace (realTruncatedK f R hR (diagonal d) (diagonal c) (goeMatrix r g)*
    (diagonal d*diagonal d))) = (fun g => ∑ b, (d b)^2*K g b b) from funext he]
  rw [integral_finsetSum _ (fun b _ => (hi b).const_mul _)]
  simp only [integral_const_mul,expectedCutoff,K,μ]

omit [Fintype ι] [DecidableEq ι] in
lemma combine_resolvent_loops {k w r a c t e₁ e₂ : ℝ}
    (h₁ : |w-r*t*k| ≤ e₁) (h₂ : |k-(1+a*(w-c*k))| ≤ e₂) :
    |k-1-a*(r*t-c)*k| ≤ e₂+|a| *e₁ := by
  have he : k-1-a*(r*t-c)*k = (k-(1+a*(w-c*k)))+a*(w-r*t*k) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add h₂ (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)))

theorem actual_cutoff_self_consistency (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (d c : ι → ℝ) (i : ι) :
    let k := expectedCutoff f R hR (diagonal d) (diagonal c) r
    |k i-1-(d i)^2*(r*(∑ b, (d b)^2*k b)-c i)*k i| ≤
      cutoffErrorTwo f r R lo hi d c i+
        |(d i)^2| *cutoffErrorOne f r R lo hi (diagonal d) (diagonal c) := by
  intro k
  have h₁ := realTruncatedK_first_loop f hlo hf hR hr (diagonal d) (diagonal c)
    (diagonal_transpose _) (diagonal_transpose _) i
  have h₂ := realTruncatedK_second_loop f hlo hf hR hr d c i
  dsimp only at h₁ h₂
  rw [integrated_diagonal_trace f hR d c r] at h₁
  exact combine_resolvent_loops h₁ h₂

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma cutoffErrorOne_bound (f : 𝓢(ℝ,ℂ)) {j R lo hi A B L p : ℝ}
    (D C : Matrix ι ι ℝ) (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hb : ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C) ≤ B)
    (hl : ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C) ≤ L)
    (hd : opNorm (D*D) ≤ A)
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi D C)ᶜ ≤ p) :
    cutoffErrorOne f (j/(Fintype.card ι:ℝ)) R lo hi D C ≤
      (2*j*L*((Fintype.card ι:ℝ)^2+Fintype.card ι)+2*j*B*A*B)*p+
      (j/(Fintype.card ι:ℝ))*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B) := by
  let n : ℝ := Fintype.card ι
  let r := j/n
  let b := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
  let ℓ : ℝ := (Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C)) : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hr : 0 ≤ r := div_nonneg hj hn.le
  have hd0 : 0 ≤ opNorm (D*D) := norm_nonneg _
  have hb0 : 0 ≤ b := by
    have hh := (ComplexMatrix.g_constants_nonneg f hR 1 1 (liftMatrix D) (liftMatrix D)).1
    dsimp [b,ComplexMatrix.kBound]
    exact add_nonneg zero_le_one (mul_nonneg hh (add_nonneg hR (norm_nonneg _)))
  have hl0 : 0 ≤ ℓ := NNReal.coe_nonneg _
  have hl' : ℓ ≤ L := by
    have hh : Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C)) ≤ (⟨L,hL⟩ : ℝ≥0) := Real.toNNReal_le_iff_le_coe.mpr hl
    exact_mod_cast hh
  have hp0 : 0 ≤ p := (measureReal_nonneg).trans hp
  have hnr : n*r = j := by dsimp [r]; field_simp
  have hs : sqrt n*sqrt (2*r)=sqrt (2*j) := by
    rw [← sqrt_mul hn.le]
    congr 1
    nlinarith [hnr]
  have hT : sqrt n*opNorm (D*D)*ℓ*sqrt (2*r)+1 ≤ A*L*sqrt (2*j)+1 := by
    calc
      _ = opNorm (D*D)*ℓ*(sqrt n*sqrt (2*r))+1 := by ring
      _ ≤ _ := by rw [hs]; gcongr
  have hdim : (((Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^
      (1/(2:ℝ≥0∞)).toReal : ℝ≥0) : ℝ) ≤ n^2+n := by
    have hh := NNReal.coe_le_coe.mpr (matrixCoordinates_dimension_bound (ι := ι))
    simpa only [NNReal.coe_add,NNReal.coe_pow,NNReal.coe_natCast,n] using hh
  have hfirst : n*(sqrt (2*r)*(ℓ*(sqrt (2*r)*
      (((Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal : ℝ≥0) : ℝ)))+
      r*(2*b*opNorm (D*D)*b)) ≤ 2*j*L*(n^2+n)+2*j*B*A*B := by
    calc
      _ ≤ n*(sqrt (2*r)*(L*(sqrt (2*r)*(n^2+n)))+r*(2*B*A*B)) := by gcongr
      _ = _ := by
        have hh := sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr)
        calc
          _ = n*(L*(n^2+n)*(sqrt (2*r)^2)+r*(2*B*A*B)) := by ring
          _ = 2*(n*r)*L*(n^2+n)+2*(n*r)*B*A*B := by rw [hh]; ring
          _ = _ := by rw [hnr]
  unfold cutoffErrorOne
  dsimp only
  simp only [NNReal.coe_mul,NNReal.coe_add,NNReal.coe_one]
  change n*(sqrt (2*r)*(ℓ*(sqrt (2*r)*_))+r*(2*b*opNorm (D*D)*b))*_+
    r*(b*((2*Real.exp (π^2/8))*(sqrt n*opNorm (D*D)*ℓ*sqrt (2*r)+1))+b*opNorm (D*D)*b) ≤ _
  apply add_le_add
  · exact mul_le_mul hfirst hp measureReal_nonneg (by positivity)
  · apply mul_le_mul_of_nonneg_left _ hr
    apply add_le_add
    · rw [← mul_assoc]
      gcongr
    · gcongr

lemma cutoffErrorTwo_bound (f : 𝓢(ℝ,ℂ)) {j R lo hi A B p : ℝ}
    (d c : ι → ℝ) (i : ι) (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hb : ComplexMatrix.kBound f R (liftMatrix (diagonal d)) (liftMatrix (diagonal c)) ≤ B)
    (hd : (d i)^2 ≤ A) (hc : |c i| ≤ j*A)
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi (diagonal d) (diagonal c))ᶜ ≤ p) :
    cutoffErrorTwo f (j/(Fintype.card ι:ℝ)) R lo hi d c i ≤
      (B+1+A*(j*A)*B)*p+A*B*(Fintype.card ι:ℝ)*sqrt (2*j)*sqrt p := by
  have hn : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hr : j/(Fintype.card ι:ℝ) ≤ j := by
    exact div_le_self hj hn
  have hb0 : 0 ≤ ComplexMatrix.kBound f R (liftMatrix (diagonal d)) (liftMatrix (diagonal c)) := by
    have hh := (ComplexMatrix.g_constants_nonneg f hR 1 1 (liftMatrix (diagonal d)) (liftMatrix (diagonal d))).1
    exact add_nonneg zero_le_one (mul_nonneg hh (add_nonneg hR (norm_nonneg _)))
  have hdc : |(d i)^2*c i| ≤ A*(j*A) := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul hd hc (abs_nonneg _) hA
  have hp0 : 0 ≤ p := measureReal_nonneg.trans hp
  unfold cutoffErrorTwo
  dsimp only
  rw [abs_of_nonneg (sq_nonneg (d i))]
  gcongr
end SKGap
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
