import OAI.Analysis.FreeEntropy.GUESelection

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped Classical Topology ENNReal
namespace FiniteEntropySeparation
 def heatCoordinates {n d : ℕ} (a : MatrixCoordinates n d) (u : ℝ) (x : MatrixIndex n d → ℝ) : MatrixCoordinates n d :=
  a+(Real.sqrt u/Real.sqrt d) • WithLp.toLp 2 x
 theorem hermitianMatrix_heatCoordinates {n d : ℕ} (a : MatrixCoordinates n d) (u : ℝ) (x : MatrixIndex n d → ℝ) (i : Fin n) :
    hermitianMatrix (heatCoordinates a u x) i = heatMatrix (hermitianMatrix a) u x i := by
  rw [heatCoordinates,hermitianMatrix_add,hermitianMatrix_smul]
  simp only [heatMatrix,gueMatrix,← smul_assoc,smul_eq_mul,coordinateMatrix]
  congr 1
  ext j k
  simp [Matrix.smul_apply,smul_eq_mul,Complex.real_smul,div_eq_mul_inv]
 theorem matrixMoment_heatCoordinates {n d : ℕ} (a : MatrixCoordinates n d) (u : ℝ) (x : MatrixIndex n d → ℝ) (w : List (Fin n)) :
    matrixMoment (heatCoordinates a u x) w = matrixTraceWord (heatMatrix (hermitianMatrix a) u x) w := by
  simp only [matrixMoment,matrixTraceWord,matrixWord]
  rw [show hermitianMatrix (heatCoordinates a u x)=heatMatrix (hermitianMatrix a) u x from funext (hermitianMatrix_heatCoordinates a u x)]
 theorem heatMatrix_norm_le {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) {R : ℝ}
    (hA : ∀i,matrixOpNorm (A i)≤R) (u : ℝ) (x : MatrixIndex n d → ℝ)
    (hx : ∀i,matrixOpNorm (gueMatrix x i)≤64) (i : Fin n) :
    matrixOpNorm (heatMatrix A u x i)≤R+Real.sqrt u*64 := by
  apply (matrixOpNorm_add _ _).trans
  rw [matrixOpNorm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact add_le_add (hA i) (mul_le_mul_of_nonneg_left (hx i) (Real.sqrt_nonneg _))
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem heat_microstates_probability {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    (a : (k:ℕ) → MatrixCoordinates n (D k)) {R : ℝ} (hA : ∀k i,matrixOpNorm (hermitianMatrix (a k) i)≤R)
    (u : ℝ) (hMom : ∀w (ε:ℝ), 0<ε → Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real
      {x | ε≤‖matrixTraceWord (heatMatrix (hermitianMatrix (a k)) u x) w-wordMoment τ X w‖}) atTop (𝓝 0))
    (m : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in atTop, (1/2:ℝ≥0∞) ≤ productGaussian (MatrixIndex n (D k))
      (heatCoordinates (a k) u ⁻¹' microstates τ X (R+Real.sqrt u*64) m (D k) ε) := by
  let W := (List.finite_length_le (Fin n) m).toFinset
  let E (k : ℕ) : Set (MatrixIndex n (D k) → ℝ) :=
    (⋃ i ∈ (univ : Finset (Fin n)), {x | 64 < matrixOpNorm (gueMatrix x i)}) ∪
    (⋃ w ∈ W, {x | ε≤‖matrixTraceWord (heatMatrix (hermitianMatrix (a k)) u x) w-wordMoment τ X w‖})
  have hn : Tendsto (fun k => ∑ i : Fin n, (productGaussian (MatrixIndex n (D k))).real {x | 64 < matrixOpNorm (gueMatrix x i)}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ (fun i _ => gueMatrix_norm_probability_tendsto hD0 hD i)
  have hw : Tendsto (fun k => ∑ w ∈ W, (productGaussian (MatrixIndex n (D k))).real {x | ε ≤ ‖matrixTraceWord (heatMatrix (hermitianMatrix (a k)) u x) w-wordMoment τ X w‖}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum W (fun w _ => hMom w ε hε)
  have ht : Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real (E k)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa using hn.add hw)
    intro k
    exact (measureReal_union_le _ _).trans (add_le_add (measureReal_biUnion_finset_le _ _) (measureReal_biUnion_finset_le _ _))
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with k hk
  have hb : (E k)ᶜ ⊆ heatCoordinates (a k) u ⁻¹' microstates τ X (R+Real.sqrt u*64) m (D k) ε := by
    intro x hx
    simp only [mem_compl_iff,E,Set.mem_union,mem_iUnion,Finset.mem_univ,exists_prop,true_and,not_or,not_exists] at hx
    refine ⟨?_,?_⟩
    · intro i
      rw [hermitianMatrix_heatCoordinates]
      exact heatMatrix_norm_le _ (hA k) u x (fun i => le_of_not_gt (hx.1 i)) i
    · intro w hw
      rw [matrixMoment_heatCoordinates]
      exact lt_of_not_ge (fun hh => hx.2 w ⟨by simpa [W] using hw,hh⟩)
  apply le_trans _ (measure_mono hb)
  have hu : (1:ℝ) ≤ (productGaussian (MatrixIndex n (D k))).real (E k)+(productGaussian (MatrixIndex n (D k))).real ((E k)ᶜ) := by
    simpa [measureReal_def] using measureReal_union_le (μ := productGaussian (MatrixIndex n (D k))) (E k) (E k)ᶜ
  have hc : (1/2:ℝ) ≤ (productGaussian (MatrixIndex n (D k))).real ((E k)ᶜ) := by linarith
  rw [← ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top _ _)]
  simpa [measureReal_def] using hc
end FiniteEntropySeparation

end

end OAI
