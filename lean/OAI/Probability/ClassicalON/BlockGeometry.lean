import OAI.Probability.ClassicalON.OrthogonalAverage

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Classical
namespace ClassicalON

abbrev ThreeBlock (k : ℕ) := WithLp 2 (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin k))

def splitThree (k : ℕ) : EuclideanSpace ℝ (Fin (3+k)) ≃ₗᵢ[ℝ] ThreeBlock k :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSumFinEquiv.symm : Fin (3+k) ≃ Fin 3 ⊕ Fin k)).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 3 ⊕ Fin k => ℝ))

def blockHead (k : ℕ) (s : Spin (3+k)) : EuclideanSpace ℝ (Fin 3) := (splitThree k s.val).fst
def blockTail (k : ℕ) (s : Spin (3+k)) : EuclideanSpace ℝ (Fin k) := (splitThree k s.val).snd
def blockRadius (k : ℕ) (s : Spin (3+k)) : ℝ := ‖blockHead k s‖

theorem blockRadius_nonneg (k : ℕ) (s : Spin (3+k)) : 0≤blockRadius k s := norm_nonneg _

theorem blockRadius_le_one (k : ℕ) (s : Spin (3+k)) : blockRadius k s≤1 := by
  have h := WithLp.norm_fst_le _ (splitThree k s.val)
  simpa only [blockRadius,blockHead,LinearIsometryEquiv.norm_map,spin_norm] using h

theorem block_norm_sq (k : ℕ) (s : Spin (3+k)) : blockRadius k s^2+‖blockTail k s‖^2=1 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (splitThree k s.val)
  simpa only [blockRadius,blockHead,blockTail,LinearIsometryEquiv.norm_map,spin_norm,one_pow] using h.symm

theorem block_inner (k : ℕ) (s t : Spin (3+k)) :
    ⟪s.val,t.val⟫_ℝ=⟪blockHead k s,blockHead k t⟫_ℝ+⟪blockTail k s,blockTail k t⟫_ℝ := by
  rw [← (splitThree k).inner_map_map]
  rfl

theorem blockHead_first (k : ℕ) (s : Spin (3+k)) : (blockHead k s) 0=s.val ⟨0,by omega⟩ := rfl

theorem continuous_blockHead (k : ℕ) : Continuous (blockHead k) :=
  (WithLp.continuous_fst _ _ _).comp ((splitThree k).continuous.comp continuous_subtype_val)
theorem continuous_blockTail (k : ℕ) : Continuous (blockTail k) :=
  (WithLp.continuous_snd _ _ _).comp ((splitThree k).continuous.comp continuous_subtype_val)
theorem continuous_blockRadius (k : ℕ) : Continuous (blockRadius k) := (continuous_blockHead k).norm

def blockDirection (k : ℕ) (s : Spin (3+k)) : Spin 3 :=
  if h : blockHead k s=0 then cylindricalSpin ⊤ true 0 else
  ⟨(blockRadius k s)⁻¹ • blockHead k s,by
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (blockRadius_nonneg k s))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)⟩

theorem block_head_direction (k : ℕ) (s : Spin (3+k)) :
    blockRadius k s • (blockDirection k s).val=blockHead k s := by
  unfold blockDirection
  split_ifs with h
  · simp only [blockRadius,h,norm_zero,zero_smul]
  · have hn : blockRadius k s ≠ 0 := norm_ne_zero_iff.mpr h
    simp only [smul_smul,mul_inv_cancel₀ hn,one_smul]

def blockFiber (k : ℕ) (s : Spin (3+k)) (t : Spin 3) : Spin (3+k) :=
  ⟨(splitThree k).symm (WithLp.toLp 2 (blockRadius k s • t.val,blockTail k s)),by
    rw [Metric.mem_sphere,dist_zero_right,LinearIsometryEquiv.norm_map]
    have he := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (blockRadius k s • t.val,blockTail k s))
    have hn := block_norm_sq k s
    simp only [WithLp.fst,WithLp.snd,norm_smul,Real.norm_of_nonneg (blockRadius_nonneg k s),spin_norm,mul_one] at he
    nlinarith [norm_nonneg (WithLp.toLp 2 (blockRadius k s • t.val,blockTail k s))]⟩

@[simp] theorem blockHead_fiber (k : ℕ) (s : Spin (3+k)) (t : Spin 3) :
    blockHead k (blockFiber k s t)=blockRadius k s • t.val := by
  simp [blockHead,blockFiber]
@[simp] theorem blockTail_fiber (k : ℕ) (s : Spin (3+k)) (t : Spin 3) :
    blockTail k (blockFiber k s t)=blockTail k s := by
  simp [blockTail,blockFiber]

theorem blockFiber_inner (k : ℕ) (s q : Spin (3+k)) (t u : Spin 3) :
    ⟪(blockFiber k s t).val,(blockFiber k q u).val⟫_ℝ=
      blockRadius k s*blockRadius k q*⟪t.val,u.val⟫_ℝ+⟪blockTail k s,blockTail k q⟫_ℝ := by
  rw [block_inner,blockHead_fiber,blockHead_fiber,blockTail_fiber,blockTail_fiber]
  simp only [real_inner_smul_left,real_inner_smul_right]
  ring

theorem continuous_blockFiber (k : ℕ) : Continuous (Function.uncurry (blockFiber k)) := by
  apply Continuous.subtype_mk
  apply (splitThree k).symm.continuous.comp
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.comp
    ((((continuous_blockRadius k).comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)).prodMk
      ((continuous_blockTail k).comp continuous_fst))

def blockRotation (k : ℕ) (Q : SpinOrthogonal 3) :
    EuclideanSpace ℝ (Fin (3+k)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (3+k)) :=
  ((splitThree k).trans (LinearIsometryEquiv.withLpProdCongr 2 (Unitary.linearIsometryEquiv Q) (.refl ℝ _))).trans (splitThree k).symm

def blockRotateSpin (k : ℕ) (Q : SpinOrthogonal 3) (s : Spin (3+k)) : Spin (3+k) :=
  spinRotation (blockRotation k Q) s

theorem blockRotateSpin_fiber (k : ℕ) (Q : SpinOrthogonal 3) (s : Spin (3+k)) :
    blockRotateSpin k Q s=blockFiber k s (orthogonalSpin Q (blockDirection k s)) := by
  apply Subtype.ext
  apply (splitThree k).injective
  change splitThree k ((splitThree k).symm _)=splitThree k ((splitThree k).symm _)
  simp only [LinearIsometryEquiv.apply_symm_apply]
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · change (Unitary.linearIsometryEquiv Q) (blockHead k s)=
      blockRadius k s • ((Unitary.linearIsometryEquiv Q) (blockDirection k s).val)
    rw [← map_smul,block_head_direction]
  · rfl

theorem continuous_blockRotateSpin (k : ℕ) : Continuous (Function.uncurry (blockRotateSpin k)) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : SpinOrthogonal 3×Spin (3+k) =>
    (splitThree k).symm (WithLp.toLp 2 (((p.1:SpinOperator 3) (blockHead k p.2)),blockTail k p.2)))
  apply (splitThree k).symm.continuous.comp
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.comp
  exact ((continuous_subtype_val.comp continuous_fst).clm_apply ((continuous_blockHead k).comp continuous_snd)).prodMk
    ((continuous_blockTail k).comp continuous_snd)

end ClassicalON

end

end OAI
