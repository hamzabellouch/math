import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.ConcreteLimit
import OAI.Analysis.JiangSu.DimensionDrop.TraceScalarization

namespace OAI

noncomputable section


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

omit [DecidableEq I] in
lemma matrixTrace_mul_comm (a b : CStarMatrix I I ℂ) : matrixTrace (a*b)=matrixTrace (b*a) :=
  Matrix.trace_mul_comm (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b)

lemma matrixTrace_unitary (u : unitary (CStarMatrix I I ℂ)) (a : CStarMatrix I I ℂ) :
    matrixTrace (unitaryConjugation u a)=matrixTrace a := by
  change matrixTrace ((u:CStarMatrix I I ℂ)*a*star (u:CStarMatrix I I ℂ))=_
  rw [matrixTrace_mul_comm,←mul_assoc (star (u:CStarMatrix I I ℂ)),u.2.1,one_mul]

omit [DecidableEq I] [DecidableEq J] in
lemma matrixTrace_reindex (e : I≃J) (a : CStarMatrix I I ℂ) :
    matrixTrace (CStarMatrix.reindexₐ ℂ ℂ e a)=matrixTrace a := by
  change (∑ i:J,a (e.symm i) (e.symm i))=∑ i:I,a i i
  exact Equiv.sum_comp e.symm (fun i => a i i)

lemma matrixTrace_blockDiagonal (a : K → CStarMatrix I I ℂ) :
    matrixTrace (blockDiagonalHom a)=∑ k,matrixTrace (a k) := by
  change (∑ i:I×K,(Matrix.blockDiagonal (fun k => CStarMatrix.ofMatrix.symm (a k))) i i)=_
  simp only [Matrix.blockDiagonal_apply,ite_true]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  rfl

variable {p q P Q : ℕ} [NeZero p] [NeZero q]

omit [NeZero p] [NeZero q] in
lemma normalizedTrace_connecting (ξ : K → C(Interval,Interval))
    (e : ((Fin p×Fin q)×K)≃(Fin P×Fin Q))
    (u₀ u₁ : unitary (TensorMat P Q)) (f : C(Interval,TensorMat p q)) (t : Interval) :
    normalizedTracePath (connectingAmbient ξ e u₀ u₁ f) t =
      (Fintype.card K : ℂ)⁻¹*∑ k,normalizedTracePath f (ξ k t) := by
  change (Fintype.card (Fin P×Fin Q) : ℂ)⁻¹*
    matrixTrace (unitaryConjugation ((finiteMatrixUnitaryPath u₀ u₁) t)
      (CStarMatrix.reindexₐ ℂ ℂ e (blockDiagonalHom (fun k => f (ξ k t)))))=_
  rw [matrixTrace_unitary,matrixTrace_reindex,matrixTrace_blockDiagonal]
  have hc := Fintype.card_congr e
  rw [←hc,Fintype.card_prod,Nat.cast_mul,mul_inv_rev]
  simp only [normalizedTracePath,LinearMap.coe_mk,AddHom.coe_mk,ContinuousMap.coe_mk,←Finset.mul_sum]
  ring

variable (m : Multiplicities p q)

omit [NeZero p] [NeZero q] in
lemma spectralIndex_card : Fintype.card (SpectralIndex m)=m.k*m.l := by
  simpa only [SpectralIndex,Fintype.card_sum,Fintype.card_fin,Nat.add_assoc] using m.total

def spectralTransfer (z : C(Interval,ℂ)) : C(Interval,ℂ) :=
  ((m.k*m.l : ℕ):ℂ)⁻¹ •
    ((m.lower:ℂ) • (z.comp lowerEigenvalue)+
      (m.upper:ℂ) • (z.comp upperEigenvalue)+(m.residual:ℂ) • z)

omit [NeZero p] [NeZero q] in
lemma normalizedTrace_concreteStep (f : DimensionDrop p q) :
    normalizedTracePath (concreteStep m f).val=spectralTransfer m (normalizedTracePath f.val) := by
  apply ContinuousMap.ext
  intro t
  change normalizedTracePath (connectingAmbient _ _ _ _ f.val) t=_
  rw [normalizedTrace_connecting,spectralIndex_card]
  simp [spectralTransfer,Fintype.sum_sum_type,spectralFamily,
    ContinuousMap.id_apply,add_assoc]

end JiangSuConstruction


namespace JiangSuConstruction
variable {p q : ℕ} (m : Multiplicities p q)

lemma lowerEigenvalue_dist (s t : Interval) :
    dist (lowerEigenvalue s) (lowerEigenvalue t)=dist s t/2 := by
  change |(s:ℝ)/2-(t:ℝ)/2|=|(s:ℝ)-(t:ℝ)|/2
  rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
lemma upperEigenvalue_dist (s t : Interval) :
    dist (upperEigenvalue s) (upperEigenvalue t)=dist s t/2 := by
  change |((s:ℝ)+1)/2-((t:ℝ)+1)/2|=|(s:ℝ)-(t:ℝ)|/2
  have h : ((s:ℝ)+1)/2-((t:ℝ)+1)/2=((s:ℝ)-(t:ℝ))/2 := by ring
  rw [h,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]

lemma spectralTransfer_difference_bound (z : C(Interval,ℂ)) (s t : Interval) :
    ‖spectralTransfer m z s-spectralTransfer m z t‖ ≤
      ((m.k*m.l:ℕ):ℝ)⁻¹ *
      (m.lower*‖z (lowerEigenvalue s)-z (lowerEigenvalue t)‖+
       m.upper*‖z (upperEigenvalue s)-z (upperEigenvalue t)‖+
       m.residual*‖z s-z t‖) := by
  have h : spectralTransfer m z s-spectralTransfer m z t=
      ((m.k*m.l:ℕ):ℂ)⁻¹ *
      ((m.lower:ℂ)*(z (lowerEigenvalue s)-z (lowerEigenvalue t))+
       (m.upper:ℂ)*(z (upperEigenvalue s)-z (upperEigenvalue t))+
       (m.residual:ℂ)*(z s-z t)) := by
    simp only [spectralTransfer,ContinuousMap.smul_apply,ContinuousMap.add_apply,
      ContinuousMap.comp_apply,smul_eq_mul]
    ring
  rw [h,norm_mul,norm_inv,Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ (‖(m.lower:ℂ)*(z (lowerEigenvalue s)-z (lowerEigenvalue t))‖+
       ‖(m.upper:ℂ)*(z (upperEigenvalue s)-z (upperEigenvalue t))‖)+
       ‖(m.residual:ℂ)*(z s-z t)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by simp only [norm_mul,Complex.norm_natCast]

theorem spectralTransfer_affine_modulus (z : C(Interval,ℂ)) {ε L : ℝ}
    (hL : 0≤L) (hz : ∀ s t, ‖z s-z t‖≤ε+L*dist s t) :
    ∀ s t, ‖spectralTransfer m z s-spectralTransfer m z t‖≤
      ε+((7/8:ℝ)*L)*dist s t := by
  intro s t
  have hN : (0:ℝ)<((m.k*m.l:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos m.k_pos m.l_pos
  have htot : (m.lower:ℝ)+m.upper+m.residual=((m.k*m.l:ℕ):ℝ) := by exact_mod_cast m.total
  have hlo : ((m.k*m.l:ℕ):ℝ)≤8*(m.lower:ℝ) := by exact_mod_cast m.lower_mass
  have hup : ((m.k*m.l:ℕ):ℝ)≤8*(m.upper:ℝ) := by exact_mod_cast m.upper_mass
  have hs := hz (lowerEigenvalue s) (lowerEigenvalue t)
  have ht := hz (upperEigenvalue s) (upperEigenvalue t)
  rw [lowerEigenvalue_dist] at hs
  rw [upperEigenvalue_dist] at ht
  have hn : 0≤L*dist s t := mul_nonneg hL dist_nonneg
  calc
    _ ≤ _ := spectralTransfer_difference_bound m z s t
    _ ≤ ((m.k*m.l:ℕ):ℝ)⁻¹ * ((m.lower:ℝ)*(ε+L*(dist s t/2))+
       (m.upper:ℝ)*(ε+L*(dist s t/2))+(m.residual:ℝ)*(ε+L*dist s t)) := by
      gcongr
      exact hz s t
    _ ≤ ε+((7/8:ℝ)*L)*dist s t := by
      rw [inv_mul_le_iff₀ hN]
      have hm : ((m.k*m.l:ℕ):ℝ)/8-((m.lower:ℝ)+m.upper)/2 ≤ 0 := by linarith
      calc
        _ = ((m.k*m.l:ℕ):ℝ)*(ε+7/8*L*dist s t)+
            (((m.k*m.l:ℕ):ℝ)/8-((m.lower:ℝ)+m.upper)/2)*(L*dist s t) := by
          rw [←htot]
          ring
        _ ≤ _ := add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hm hn)

theorem continuous_affine_modulus (z : C(Interval,ℂ)) {ε : ℝ} (hε : 0<ε) :
    ∃ L : ℝ, 0≤L ∧ ∀ s t, ‖z s-z t‖≤ε+L*dist s t := by
  have hu : UniformContinuous z := CompactSpace.uniformContinuous_of_continuous z.continuous
  obtain ⟨δ,hδ,hz⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨2*‖z‖/δ,by positivity,?_⟩
  intro s t
  by_cases hst : dist s t<δ
  · have h := (hz hst).le
    rw [dist_eq_norm] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have hst' : δ≤dist s t := le_of_not_gt hst
    have hb : ‖z s-z t‖≤2*‖z‖ := by
      calc _ ≤ ‖z s‖+‖z t‖ := norm_sub_le _ _
           _ ≤ ‖z‖+‖z‖ := add_le_add (z.norm_coe_le_norm s) (z.norm_coe_le_norm t)
           _ = _ := by ring
    have hd : 2*‖z‖≤(2*‖z‖/δ)*dist s t := by
      calc _ = (2*‖z‖/δ)*δ := by field_simp
           _ ≤ _ := mul_le_mul_of_nonneg_left hst' (by positivity)
    exact hb.trans (hd.trans (le_add_of_nonneg_left hε.le))

end JiangSuConstruction


namespace JiangSuConstruction
open Filter
open scoped Topology CStarAlgebra ComplexOrder

local instance stagePNeZero (n : ℕ) : NeZero (stagePair n).p := ⟨(stagePair n).p_pos.ne'⟩
local instance stageQNeZero (n : ℕ) : NeZero (stagePair n).q := ⟨(stagePair n).q_pos.ne'⟩

def scalarIterates (n : ℕ) (z : C(Interval,ℂ)) : ℕ → C(Interval,ℂ)
  | 0 => z
  | k+1 => spectralTransfer (canonicalMultiplicities (stagePair (n+k)).p_pos
      (stagePair (n+k)).q_pos) (scalarIterates n z k)

lemma normalizedTrace_stageStep (n : ℕ) (f : StageAlgebra n) :
    normalizedTracePath (stageStep n f).val=
      spectralTransfer (canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos)
        (normalizedTracePath f.val) :=
  normalizedTrace_concreteStep _ f

lemma normalizedTrace_sequence (n k : ℕ) (f : StageAlgebra n) :
    normalizedTracePath (concreteSystem.map (Nat.le_add_right n k) f).val=
      scalarIterates n (normalizedTracePath f.val) k := by
  induction k with
  | zero =>
    change normalizedTracePath (SequentialCStar.sequenceHom stageStep (le_refl n) f).val=_
    rw [SequentialCStar.sequenceHom_self]
    rfl
  | succ k ih =>
    change normalizedTracePath (SequentialCStar.sequenceHom stageStep
      ((Nat.le_add_right n k).trans (Nat.le_succ (n+k))) f).val=_
    rw [SequentialCStar.sequenceHom_succ,normalizedTrace_stageStep]
    change spectralTransfer _ (normalizedTracePath (concreteSystem.map (Nat.le_add_right n k) f).val)=_
    rw [ih]
    rfl

lemma scalarIterates_affine_modulus (n : ℕ) (z : C(Interval,ℂ)) {ε L : ℝ}
    (hL : 0≤L) (hz : ∀ s t, ‖z s-z t‖≤ε+L*dist s t) (k : ℕ) :
    ∀ s t, ‖scalarIterates n z k s-scalarIterates n z k t‖≤
      ε+((7/8:ℝ)^k*L)*dist s t := by
  induction k with
  | zero => simpa only [scalarIterates,pow_zero,one_mul] using hz
  | succ k ih =>
    have h := spectralTransfer_affine_modulus
      (canonicalMultiplicities (stagePair (n+k)).p_pos (stagePair (n+k)).q_pos)
      (scalarIterates n z k) (mul_nonneg (pow_nonneg (by norm_num) _) hL) ih
    simpa only [scalarIterates,pow_succ',mul_assoc] using h

lemma interval_dist_le_one (s t : Interval) : dist s t≤1 := by
  change |(s:ℝ)-(t:ℝ)|≤1
  rw [abs_le]
  constructor <;> linarith [s.2.1,s.2.2,t.2.1,t.2.2]

theorem scalarIterates_oscillation (n : ℕ) (z : C(Interval,ℂ)) {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ, ∀ s t, ‖scalarIterates n z k s-scalarIterates n z k t‖<ε := by
  obtain ⟨L,hL,hz⟩ := continuous_affine_modulus z (half_pos hε)
  have ht : Tendsto (fun k : ℕ => (7/8:ℝ)^k*L) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤7/8)
      (by norm_num : (7/8:ℝ)<1)).mul_const L
  obtain ⟨k,hk⟩ := (ht.eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨k,fun s t => ?_⟩
  have hb := scalarIterates_affine_modulus n z hL hz k s t
  have hc : ((7/8:ℝ)^k*L)*dist s t≤(7/8:ℝ)^k*L :=
    mul_le_of_le_one_right (mul_nonneg (pow_nonneg (by norm_num) _) hL) (interval_dist_le_one s t)
  linarith

end JiangSuConstruction

end

end OAI
