import OAI.Analysis.FreeEntropy.TensorMatrixModels

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FiniteEntropySeparation
 section Generic
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem chiCutoff_lower_of_heat_models {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    (a : (k:ℕ) → MatrixCoordinates n (D k)) {R : ℝ} (hR : 0≤R)
    (hA : ∀k i,matrixOpNorm (hermitianMatrix (a k) i)≤R)
    {u : ℝ} (hu : 0<u) (hMom : ∀w (ε:ℝ), 0<ε → Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real
      {x | ε≤‖matrixTraceWord (heatMatrix (hermitianMatrix (a k)) u x) w-wordMoment τ X w‖}) atTop (𝓝 0)) :
    (((n:ℝ)/2*Real.log u-Real.log 2:ℝ):EReal) ≤ chiCutoff τ X (R+Real.sqrt u*64) := by
  apply le_iInf
  intro m
  apply le_iInf
  intro ε
  have hp := heat_microstates_probability τ X hD0 hD a hA u hMom m ε.property
  let F : ℕ → EReal := fun d => ((((d+1:ℕ):ℝ)^2)⁻¹:ℝ)*
    (volume (microstates τ X (R+Real.sqrt u*64) m (d+1) ε.val)).log+((n:ℝ)/2*Real.log (d+1):ℝ)
  have hD' := (tendsto_sub_atTop_nat 1).comp hD
  apply le_trans _ (hD'.limsup_comp_le_limsup (u := F))
  apply le_limsup_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [hp] with k hk
  have hv := gaussian_affine_volume (a k) (r := Real.sqrt u/Real.sqrt (D k))
    (div_pos (Real.sqrt_pos.mpr hu) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hD0 k))))
    (microstates τ X (R+Real.sqrt u*64) m (D k) ε.val) hk
  have he : F (D k-1) = ((((D k:ℝ)^2)⁻¹:ℝ):EReal)*
    (volume (microstates τ X (R+Real.sqrt u*64) m (D k) ε.val)).log+(((n:ℝ)/2*Real.log (D k):ℝ):EReal) := by
    have hn : D k-1+1=D k := Nat.sub_add_cancel (hD0 k)
    have hc : ((D k-1:ℕ):ℝ)+1=(D k:ℝ) := by exact_mod_cast hn
    simp only [F,hn,hc]
    rw [hn]
  change _ ≤ F (D k-1)
  rw [he]
  apply normalized_log_lower n (D k) (hD0 k) hu
    (ne_of_lt (microstates_volume_lt_top τ X _ (by positivity) _ _ _))
  simpa only [Fintype.card_prod,Fintype.card_fin,mul_assoc] using hv
 end Generic
 namespace Model
 theorem chiCutoff_lower (p : ℕ) [NeZero p] (hp : 2≤p) {h : ℝ} (hh : 0<h) :
    ((((p+1:ℕ):ℝ)/2*Real.log h-Real.log 2:ℝ):EReal) ≤ chiCutoff (τ p) (X p h) (64+Real.sqrt h*64) := by
  obtain ⟨D,A,hD0,hD,hA,hAH,hM⟩ := exists_tensor_matrix_models p hp
  let a := fun k => matrixCoordinatesOfHermitian (A k)
  have ha (k : ℕ) : hermitianMatrix (a k)=A k := funext (hermitianMatrix_coordinatesOfHermitian (A k) (hAH k))
  apply chiCutoff_lower_of_heat_models (τ p) (X p h) hD0 hD a (by norm_num : (0:ℝ)≤64)
    (fun k i => by rw [ha]; exact hA k i) hh
  intro w ε hε
  simp only [ha]
  exact FreeTensor.heatMatrix_probability_tendsto hD0 hD A (by norm_num) hA ∅ (C p)
    (C_mem_background p ∅) (initialIndex p) (initialIndex_injective p) (fun i => Set.notMem_empty _) hM h w hε
 theorem chi_gt_bot (p : ℕ) [NeZero p] (hp : 2≤p) {h : ℝ} (hh : 0<h) :
    (⊥:EReal)<chi (τ p) (X p h) := by
  have hl := chiCutoff_lower p hp hh
  have hu : chiCutoff (τ p) (X p h) (64+Real.sqrt h*64) ≤ chi (τ p) (X p h) :=
    le_iSup_of_le ⟨64+Real.sqrt h*64,by positivity⟩ le_rfl
  exact (EReal.bot_lt_coe _).trans_le (hl.trans hu)
 end Model
end FiniteEntropySeparation

end

end OAI
