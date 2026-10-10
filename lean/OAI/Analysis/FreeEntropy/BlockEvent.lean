import OAI.Analysis.FreeEntropy.MatrixRotationBounds

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped Matrix.Norms.L2Operator ENNReal
namespace FiniteEntropySeparation
variable {p d n : ℕ}
 theorem matrixCoordinatesOfHermitian_continuous :
    Continuous (matrixCoordinatesOfHermitian : (Fin n → Matrix (Fin d) (Fin d) ℂ) → MatrixCoordinates n d) := by
  unfold matrixCoordinatesOfHermitian
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  rintro ⟨i,j,k⟩
  dsimp only
  split_ifs <;> fun_prop
 theorem rotateCoordinates_continuous_joint :
    Continuous (fun z : unitary (Matrix (Fin d) (Fin d) ℂ) × MatrixCoordinates n d => rotateCoordinates z.1 z.2) := by
  unfold rotateCoordinates
  apply matrixCoordinatesOfHermitian_continuous.comp
  apply continuous_pi
  intro i
  exact ((continuous_subtype_val.comp continuous_fst).star.mul ((hermitianMatrix_continuous i).comp continuous_snd)).mul
    (continuous_subtype_val.comp continuous_fst)
 def blockEvent (p d : ℕ) (r M : ℝ) : Set (MatrixCoordinates (p+1) d) :=
    {a | ‖a‖≤M ∧ ∃f : Fin d → Fin p,balancedBlocks f ∧
      ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖}
 theorem blockEvent_isClosed (hd : 0<d) (r M : ℝ) : IsClosed (blockEvent p d r M) := by
  have : CompactSpace (unitary (Matrix (Fin d) (Fin d) ℂ)) := isCompact_iff_compactSpace.mp (isCompact_unitary_matrix hd)
  have hf (f : Fin d → Fin p) : IsClosed {a : MatrixCoordinates (p+1) d |
      ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} := by
    have hh : IsClosed {z : unitary (Matrix (Fin d) (Fin d) ℂ) × MatrixCoordinates (p+1) d |
        r≤‖coordinateMask (blockMask f) (rotateCoordinates z.1 z.2)‖} :=
      isClosed_le continuous_const ((coordinateMask_continuous _).comp rotateCoordinates_continuous_joint).norm
    convert isClosedMap_snd_of_compactSpace _ hh using 1
    ext a
    simp only [Set.mem_ofPred_eq,Set.mem_image,Prod.exists]
    constructor
    · rintro ⟨U,hU⟩; exact ⟨U,a,hU,rfl⟩
    · rintro ⟨U,b,hU,rfl⟩; exact ⟨U,hU⟩
  have he : blockEvent p d r M = {a | ‖a‖≤M} ∩
      ⋃ f : Fin d → Fin p, ⋃ (_ : balancedBlocks f),
        {a | ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} := by
    ext a; simp [blockEvent]
  rw [he]
  exact (isClosed_le continuous_norm continuous_const).inter (isClosed_iUnion_of_finite (fun f => isClosed_iUnion_of_finite (fun _ => hf f)))
 theorem blockEvent_subset_net (hd : 0<d) {r M ε : ℝ} (hε : 0≤ε)
    (s : Finset (unitary (Matrix (Fin d) (Fin d) ℂ)))
    (hs : ∀U : unitary (Matrix (Fin d) (Fin d) ℂ),∃V∈s,matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))≤ε) :
    blockEvent p d r M ⊆ ⋃ f : Fin d → Fin p, ⋃ (_ : balancedBlocks f), ⋃ V∈s,
      {a | r-2*ε*M≤‖coordinateMask (blockMask f) (rotateCoordinates V a)‖} := by
  intro a ha
  obtain ⟨haM,f,hf,U,hU⟩ := ha
  obtain ⟨V,hV,hUV⟩ := hs U
  refine mem_iUnion.mpr ⟨f,mem_iUnion.mpr ⟨hf,mem_iUnion.mpr ⟨V,mem_iUnion.mpr ⟨hV,?_⟩⟩⟩⟩
  have hh := coordinateMask_norm_sub (blockMask f) (rotateCoordinates U a) (rotateCoordinates V a)
  have hr := rotateCoordinates_sub_norm hd U V a
  have hb : 2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*‖a‖≤2*ε*M := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hUV (by norm_num)) haM (norm_nonneg _) (by positivity)
  have hh' := (abs_le.mp (hh.trans (hr.trans hb))).2
  dsimp at *
  linarith
 theorem normalLaw_rotated_mask_tail {s r : ℝ} (hs : 0<s) (hr : 0≤r)
    (f : Fin d → Fin p) (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (normalLaw s) {a | r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} ≤
      ENNReal.ofReal (Real.exp (-r^2/(4*s))*Real.sqrt 2^(blockMask f).card) := by
  have hm := normalLaw_measurePreserving s (rotateLinearIsometryEquiv (n := p+1) U)
  have hE : MeasurableSet {a : MatrixCoordinates (p+1) d | r≤‖coordinateMask (blockMask f) a‖} :=
    (isClosed_le continuous_const (coordinateMask_continuous _).norm).measurableSet
  have he := hm.measure_preimage hE.nullMeasurableSet
  change (normalLaw s) {a | r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} = _ at he
  rw [he]
  exact normalLaw_coordinateMask_tail _ hs hr
 theorem blockEvent_gaussian_bound (hd : 0<d) {s r M ε : ℝ} (hs : 0<s) (hε : 0<ε)
    (hr : 0≤r-2*ε*M) :
    (normalLaw s) (blockEvent p d r M) ≤ ENNReal.ofReal
      ((p:ℝ)^d*(1+2/ε)^(2*d^2)*Real.exp (-(r-2*ε*M)^2/(4*s))*Real.sqrt 2^(2*d^2)) := by
  classical
  obtain ⟨S,hS,hcard⟩ := unitary_matrix_net hd hε
  have hsub := blockEvent_subset_net (p := p) (r := r) (M := M) hd hε.le S hS
  let K : ℝ := Real.exp (-(r-2*ε*M)^2/(4*s))*Real.sqrt 2^(2*d^2)
  have hK : 0≤K := by dsimp [K]; positivity
  have hbound (f : Fin d → Fin p) (hf : balancedBlocks f) (V : unitary (Matrix (Fin d) (Fin d) ℂ)) :
      (normalLaw s) {a | r-2*ε*M≤‖coordinateMask (blockMask f) (rotateCoordinates V a)‖}≤ENNReal.ofReal K := by
    apply (normalLaw_rotated_mask_tail hs hr f V).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact pow_le_pow_right₀ (by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg (2:ℝ)] : (1:ℝ)≤Real.sqrt 2) (blockMask_card_le f hf)
  calc
    _ ≤ ∑f : Fin d → Fin p, ∑V∈S,ENNReal.ofReal K := by
      apply (measure_mono hsub).trans
      apply (measure_iUnion_fintype_le _ _).trans
      apply sum_le_sum
      intro f _
      by_cases hf : balancedBlocks f
      · have he : (⋃ (_ : balancedBlocks f), ⋃ V∈S, {a : MatrixCoordinates (p+1) d | r-2*ε*M≤‖coordinateMask (blockMask f) (rotateCoordinates V a)‖}) = ⋃ V∈S, {a : MatrixCoordinates (p+1) d | r-2*ε*M≤‖coordinateMask (blockMask f) (rotateCoordinates V a)‖} := by ext a; simp [hf]
        rw [he]
        exact (measure_biUnion_finset_le S _).trans (sum_le_sum (fun V _ => hbound f hf V))
      · simp [hf]
    _ = ENNReal.ofReal ((p:ℝ)^d*(S.card:ℝ)*K) := by
      simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fun,Fintype.card_fin]
      simp only [ENNReal.ofReal_mul (show 0≤(p:ℝ)^d by positivity), ENNReal.ofReal_pow (show (0:ℝ)≤p by positivity), ENNReal.ofReal_natCast, Nat.cast_pow, ENNReal.ofReal_mul (show (0:ℝ)≤S.card by positivity), mul_assoc]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity : 0≤(p:ℝ)^d)) hK
      simpa [K,mul_assoc] using hh
end FiniteEntropySeparation

end

end OAI
