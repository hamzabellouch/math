import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropPartitionWeights
import OAI.Analysis.JiangSu.DimensionDrop.ConcreteLimit

namespace OAI


noncomputable section
namespace OriginalJiangSu
open JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

attribute [local instance] stageSemiring

lemma system_step (n : ℕ) (f : Stage n) :
    system.map (Nat.le_succ n) f=stageStep n f := by
  change SequentialCStar.sequenceHom stageStep _ f=stageStep n f
  rw [SequentialCStar.sequenceHom_succ stageStep (le_refl n),SequentialCStar.sequenceHom_self]

end OriginalJiangSu

end


noncomputable section
namespace OriginalJiangSu
open JiangSuConstruction
open Pureness

universe v
local instance (priority := 2000) stageSemiringNuclear (n : ℕ) : Semiring (Stage n) :=
  (inferInstance : CStarAlgebra (Stage n)).toSemiring

theorem nuclear : IsNuclear.{0,v} Algebra := by
  apply system.nuclear
  intro n
  let : NeZero (pair n).p := ⟨by have := (pair n).p_gt; omega⟩
  let : NeZero (pair n).q := ⟨by have := (pair n).q_gt; omega⟩
  exact dimensionDrop_nuclear

end OriginalJiangSu



namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

lemma connectingAmbient_eval_zero {p q P Q : ℕ} {ρ : Type*}
    [Fintype ρ] [DecidableEq ρ] (ξ : ρ → C(Interval,Interval))
    (e : ((Fin p×Fin q)×ρ)≃(Fin P×Fin Q)) (u₀ u₁ : unitary (TensorMat P Q))
    (f : C(Interval,TensorMat p q)) (t : Interval)
    (h : connectingAmbient ξ e u₀ u₁ f t=0) (j : ρ) : f (ξ j t)=0 := by
  change unitaryConjugation (A := TensorMat P Q) ((finiteMatrixUnitaryPath u₀ u₁) t)
    (CStarMatrix.reindexₐ ℂ ℂ e (blockDiagonalHom (fun j => f (ξ j t))))=0 at h
  have h' := (unitaryConjugation_injective (A := TensorMat P Q) ((finiteMatrixUnitaryPath u₀ u₁) t))
    (h.trans (map_zero _).symm)
  have h'' := (CStarMatrix.reindexₐ ℂ ℂ e).injective (h'.trans (map_zero _).symm)
  have h''' := blockDiagonalHom_injective (h''.trans (map_zero _).symm)
  exact congrFun h''' j

lemma concreteStep_eval_zero {p q : ℕ} (m : Multiplicities p q)
    (f : DimensionDrop p q) (t : Interval)
    (h : (concreteStep m f).val t=0) (j : SpectralIndex m) :
    f.val (spectralFamily m j t)=0 :=
  connectingAmbient_eval_zero _ _ _ _ _ _ h j

lemma stageStep_lower_zero (n : ℕ) (f : StageAlgebra n) (t : Interval)
    (h : (stageStep n f).val t=0) : f.val (lowerEigenvalue t)=0 := by
  let m := canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos
  have hl : 0 < m.lower := by
    rw [m.lower_eq]
    exact Nat.mul_pos (Nat.mul_pos (stagePair n).p_pos m.k_pos) m.gamma_pos
  exact concreteStep_eval_zero m f t h (Sum.inl ⟨0,hl⟩)

lemma stageStep_upper_zero (n : ℕ) (f : StageAlgebra n) (t : Interval)
    (h : (stageStep n f).val t=0) : f.val (upperEigenvalue t)=0 := by
  let m := canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos
  have hu : 0 < m.upper := by
    rw [m.upper_eq]
    exact Nat.mul_pos (Nat.mul_pos (stagePair n).q_pos m.l_pos) m.delta_pos
  exact concreteStep_eval_zero m f t h (Sum.inr (Sum.inl ⟨0,hu⟩))

lemma concreteSystem_step (n : ℕ) (f : StageAlgebra n) :
    concreteSystem.map (Nat.le_succ n) f=stageStep n f := by
  change SequentialCStar.sequenceHom stageStep _ f=stageStep n f
  rw [SequentialCStar.sequenceHom_succ stageStep (le_refl n),SequentialCStar.sequenceHom_self]

end JiangSuConstruction

end


noncomputable section
namespace OriginalJiangSu
open JiangSuConstruction

lemma step_eval_zero {p q : ℕ} (m : Multiplicities p q)
    (f : DimensionDrop p q) (t : Interval)
    (h : (step m f).val t=0) (j : Index m) : f.val (family m j t)=0 :=
  connectingAmbient_eval_zero _ _ _ _ _ _ h j

lemma step_lower_zero (n : ℕ) (f : Stage n) (t : Interval)
    (h : (stageStep n f).val t=0) : f.val (lowerEigenvalue t)=0 :=
  step_eval_zero (multiplicities (pair n)) f t h
    (Sum.inl ⟨0,(multiplicities (pair n)).lower_pos⟩)
lemma step_upper_zero (n : ℕ) (f : Stage n) (t : Interval)
    (h : (stageStep n f).val t=0) : f.val (upperEigenvalue t)=0 :=
  step_eval_zero (multiplicities (pair n)) f t h
    (Sum.inr (Sum.inl ⟨0,(multiplicities (pair n)).upper_pos⟩))

end OriginalJiangSu



namespace OriginalJiangSu
open JiangSuConstruction

lemma eigenvalue_zero_net (k : ℕ) : ∀ n m (hnm : n ≤ m),m-n=k →
    ∀ x t : Interval,∃ s : Interval, |s.val-x.val|≤(1/2:ℝ)^k ∧
      ∀ f : Stage n,(system.map hnm f).val t=0 → f.val s=0 := by
  induction k with
  | zero =>
    intro n m hnm hlen x t
    have hmn : m=n := by omega
    subst m
    refine ⟨t,?_,?_⟩
    · simp only [pow_zero,abs_le]
      constructor <;> linarith [t.property.1,t.property.2,x.property.1,x.property.2]
    · intro f hf
      simpa only [system.identity] using hf
  | succ k ih =>
    intro n m hnm hlen x t
    have hsucc : n+1 ≤ m := by omega
    have hlen' : m-(n+1)=k := by omega
    by_cases hx : x.val≤1/2
    · let y : Interval := ⟨2*x.val,by constructor <;> linarith [x.property.1]⟩
      obtain ⟨s,hs,hzero⟩ := ih (n+1) m hsucc hlen' y t
      refine ⟨lowerEigenvalue s,?_,?_⟩
      · change |s.val/2-x.val|≤(1/2:ℝ)^(k+1)
        calc
          |s.val/2-x.val|=|s.val-y.val|/2 := by
            change |s.val/2-x.val|=|s.val-2*x.val|/2
            rw [←abs_of_pos (by norm_num : (0:ℝ)<2),←abs_div]
            congr 1
            ring
          _ ≤ (1/2:ℝ)^k/2 := div_le_div_of_nonneg_right hs (by norm_num)
          _ = (1/2:ℝ)^(k+1) := by rw [pow_succ]; ring
      · intro f hf
        apply step_lower_zero n f s
        apply hzero
        rw [←system_step,system.composition]
        exact hf
    · let y : Interval := ⟨2*x.val-1,by constructor <;> linarith [x.property.2]⟩
      obtain ⟨s,hs,hzero⟩ := ih (n+1) m hsucc hlen' y t
      refine ⟨upperEigenvalue s,?_,?_⟩
      · change |(s.val+1)/2-x.val|≤(1/2:ℝ)^(k+1)
        calc
          |(s.val+1)/2-x.val|=|s.val-y.val|/2 := by
            change |(s.val+1)/2-x.val|=|s.val-(2*x.val-1)|/2
            rw [←abs_of_pos (by norm_num : (0:ℝ)<2),←abs_div]
            congr 1
            ring
          _ ≤ (1/2:ℝ)^k/2 := div_le_div_of_nonneg_right hs (by norm_num)
          _ = (1/2:ℝ)^(k+1) := by rw [pow_succ]; ring
      · intro f hf
        apply step_upper_zero n f s
        apply hzero
        rw [←system_step,system.composition]
        exact hf

lemma eventually_fiberwise_nonzero (n : ℕ) (f : Stage n) (hf : f≠0) :
    ∃ (m : ℕ) (h : n ≤ m),∀ t : Interval,(system.map h f).val t≠0 := by
  have hx : ∃ x : Interval,f.val x≠0 := by
    by_contra h
    apply hf
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact not_not.mp (not_exists.mp h x)
  obtain ⟨x,hx⟩ := hx
  have hopen : IsOpen {s : Interval | f.val s≠0} := f.val.continuous.isOpen_preimage _ isOpen_ne
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hopen x hx
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨k,hk⟩ := (hp.eventually (gt_mem_nhds hδ)).exists
  refine ⟨n+k,Nat.le_add_right n k,?_⟩
  intro t ht
  obtain ⟨s,hs,hzero⟩ := eigenvalue_zero_net k n (n+k) (Nat.le_add_right n k) (by omega) x t
  apply hball (show s∈Metric.ball x δ from ?_) (hzero f ht)
  change |s.val-x.val|<δ
  exact hs.trans_lt hk

end OriginalJiangSu

end

end OAI
