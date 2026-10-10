import OAI.Analysis.TriangularHilbert.InitialPlane

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sum_energy_replaceZero_jump (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    |(∑ v, energy (starGram (weightedArray (replaceZero A B) g) v))-
      (∑ v, energy (starGram (weightedArray (replaceZero A C) g) v))| ≤
      3/2 * ∑ i, ∑ j, ‖B i j-C i j‖*g 0 i*g 1 j*jumpSlicing A g i j := by
  have h0 := energy_replaceZero_jump_zero A B C hB hC g hg
  have h1 := energy_replaceZero_jump_one A B C hB hC g hg
  have h2 : energy (starGram (weightedArray (replaceZero A B) g) 2) =
      energy (starGram (weightedArray (replaceZero A C) g) 2) := by
    simp only [starGram,rowStar_replaceZero_two A B C g]
  rw [Fin.sum_univ_three,Fin.sum_univ_three,h2]
  have he : ∀ a b c d e : ℝ, a+b+c-(d+e+c) = (a-d)+(b-e) := by intros; ring
  rw [he]
  apply (abs_add_le _ _).trans ((add_le_add h0 h1).trans_eq _)
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold jumpSlicing
  ring
end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def jumpExpectation (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (σ : Three → ℝ) (i j : ι) : ℝ :=
  2*(∑ m, ‖A 0 i m‖^2*(h*density (2*σ 1) (u j-u m)))+
  2*(∑ m, ‖A 0 m j‖^2*(h*density (2*σ 0) (u i-u m)))+
  (∑ m, ‖A 2 m i‖^2*(h*density (σ 0+σ 1+σ 2) (u i+u j+u m)))+
  (∑ m, ‖A 1 j m‖^2*(h*density (σ 0+σ 1+σ 2) (u i+u j+u m)))

omit [DecidableEq ι] in
lemma heat_jumpSlice_integrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) (i j : ι) :
    Integrable (fun z : ℝ×ℝ => heatWeights h u (chart 2 0 z) σ 0 i*
      heatWeights h u (chart 2 0 z) σ 1 j*jumpSlicing A (heatWeights h u (chart 2 0 z) σ) i j) := by
  have hX := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 i m‖^2) σ hσ 1
  have hY := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 m j‖^2) σ hσ 0
  have hH := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 2 m i‖^2) σ hσ 2
  have hK := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 1 j m‖^2) σ hσ 2
  have hi : Integrable (fun z : ℝ×ℝ =>
    2*(weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 0 i m‖^2*weight h (u m) (chart 2 0 z 1) (σ 1))+
    2*(weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 0 m j‖^2*weight h (u m) (chart 2 0 z 0) (σ 0))+
    (weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 2 m i‖^2*weight h (u m) (chart 2 0 z 2) (σ 2))+
    (weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 1 j m‖^2*weight h (u m) (chart 2 0 z 2) (σ 2))) :=
    (((hX.const_mul 2).add (hY.const_mul 2)).add hH).add hK
  convert hi using 1
  ext z
  simp only [heatWeights,jumpSlicing]
  ring

omit [DecidableEq ι] in
lemma planeIntegral_heat_jumpSlice (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) (i j : ι) :
    planeIntegral (fun p => heatWeights h u p σ 0 i*heatWeights h u p σ 1 j*
      jumpSlicing A (heatWeights h u p σ) i j) 0 = h^2*jumpExpectation A h u σ i j := by
  have hX := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 i m‖^2) σ hσ 1
  have hY := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 m j‖^2) σ hσ 0
  have hH := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 2 m i‖^2) σ hσ 2
  have hK := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 1 j m‖^2) σ hσ 2
  have he (p : Three → ℝ) : heatWeights h u p σ 0 i*heatWeights h u p σ 1 j*
      jumpSlicing A (heatWeights h u p σ) i j =
    2*(weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 0 i m‖^2*weight h (u m) (p 1) (σ 1))+
    2*(weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 0 m j‖^2*weight h (u m) (p 0) (σ 0))+
    (weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 2 m i‖^2*weight h (u m) (p 2) (σ 2))+
    (weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 1 j m‖^2*weight h (u m) (p 2) (σ 2)) := by
    unfold heatWeights jumpSlicing; ring
  simp_rw [he]
  unfold planeIntegral
  erw [integral_add (((hX.const_mul 2).add (hY.const_mul 2)).add hH) hK,
    integral_add ((hX.const_mul 2).add (hY.const_mul 2)) hH,
    integral_add (hX.const_mul 2) (hY.const_mul 2),integral_const_mul,integral_const_mul]
  have hXI := weight_slice_one_integral hh (u i) (u j) 0 u (fun m => ‖A 0 i m‖^2) σ hσ
  have hYI := weight_slice_zero_integral hh (u i) (u j) 0 u (fun m => ‖A 0 m j‖^2) σ hσ
  have hHI := weight_slice_two_integral hh (u i) (u j) u (fun m => ‖A 2 m i‖^2) σ hσ
  have hKI := weight_slice_two_integral hh (u i) (u j) u (fun m => ‖A 1 j m‖^2) σ hσ
  unfold planeIntegral at hXI hYI hHI hKI
  erw [hXI,hYI,hHI,hKI]
  unfold jumpExpectation
  ring

lemma totalPlaneEnergy_replaceZero_jump (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) :
    |totalPlaneEnergy (replaceZero A B) h u 0 σ-totalPlaneEnergy (replaceZero A C) h u 0 σ| ≤
      3/2*h^2*∑ i, ∑ j, ‖B i j-C i j‖*jumpExpectation A h u σ i j := by
  have hE (M : Three → Matrix ι ι ℂ) : Integrable (fun z : ℝ×ℝ => ∑ v, heatEnergy M h u (chart 2 0 z) σ v) :=
    integrable_finsetSum _ (fun v _ => (heatPlane_integrable M hh u 0 hσ).energy 2 v)
  have hj (i j : ι) : Integrable (fun z : ℝ×ℝ => ‖B i j-C i j‖*(heatWeights h u (chart 2 0 z) σ 0 i*
      heatWeights h u (chart 2 0 z) σ 1 j*jumpSlicing A (heatWeights h u (chart 2 0 z) σ) i j)) :=
    (heat_jumpSlice_integrable A hh u hσ i j).const_mul _
  have hJ := integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hj i j))
  have hb := (abs_integral_le_integral_abs (f := fun z : ℝ×ℝ => (∑ v, heatEnergy (replaceZero A B) h u (chart 2 0 z) σ v)-
      (∑ v, heatEnergy (replaceZero A C) h u (chart 2 0 z) σ v))).trans
    (integral_mono ((hE _).sub (hE _)).abs (hJ.const_mul (3/2)) (fun z => by
      simpa only [heatEnergy,heatArray,mul_assoc] using
        sum_energy_replaceZero_jump A B C hB hC (heatWeights h u (chart 2 0 z) σ)
          (fun v i => (weight_pos hh (hσ v) _ _).le)))
  rw [integral_sub (hE _) (hE _),integral_finsetSum _ (fun v _ => (heatPlane_integrable (replaceZero A B) hh u 0 hσ).energy 2 v),
    integral_finsetSum _ (fun v _ => (heatPlane_integrable (replaceZero A C) hh u 0 hσ).energy 2 v)] at hb
  change |totalPlaneEnergy (replaceZero A B) h u 0 σ-totalPlaneEnergy (replaceZero A C) h u 0 σ| ≤ _ at hb
  apply hb.trans_eq
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hj i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hj _ j),integral_const_mul]
  change 3/2*(∑ i, ∑ j, ‖B i j-C i j‖*planeIntegral (fun p =>
    heatWeights h u p σ 0 i*heatWeights h u p σ 1 j*jumpSlicing A (heatWeights h u p σ) i j) 0) = _
  simp_rw [planeIntegral_heat_jumpSlice A hh u hσ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end
end TriangularHilbert.Heat
end

end OAI
