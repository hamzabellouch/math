import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodNormal

namespace OAI

namespace ConvexSkorokhod

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def NormalPartitionCondition (B : Body E) (u k : ℝ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m →
    ∀ y : ℕ → E, (∀ j < m, y j ∈ B.carrier) → normalPartition u k y m ≤ ε

end ConvexSkorokhod

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

omit [CompleteSpace E]

lemma uniform_grid_mem (m j : ℕ) (hm : 0 < m) (hj : j ≤ m) :
    (j:ℝ)/m∈Icc (0:ℝ) 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  refine ⟨by positivity,?_⟩
  rw [div_le_one hm'];exact_mod_cast hj

omit [InnerProductSpace ℝ E] in
lemma grid_variation_le (k : ℝ → E) (C : ℝ) (hC : 0 ≤ C)
    (hk : eVariationOn k (Icc (0:ℝ) 1) ≤ ENNReal.ofReal C) (m : ℕ) (hm : 0 < m) :
    variation (fun j => k ((j:ℝ)/m)) m ≤ C := by
  have hcomp := eVariationOn.comp_le_of_monotoneOn k (fun j : ℕ => (j:ℝ)/m)
    (s:=Icc (0:ℝ) 1) (t:=Iic m)
    (by intro i hi j hj hij;exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg _))
    (by intro j hj;exact uniform_grid_mem m j hm hj)
  have hh := hcomp.trans hk
  change eVariationOn (fun j : ℕ => k ((j:ℝ)/m)) (Iic m) ≤ ENNReal.ofReal C at hh
  rw [eVariation_discrete] at hh
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hh

lemma normal_cutoff (u v k : ℝ → E) (m N : ℕ) (hNm : N ≤ m) :
    normalPartition u k (fun j => if j < N then v ((j:ℝ)/m) else u ((j:ℝ)/m)) m =
      ∑ j ∈ Finset.range N,⟪u ((j:ℝ)/m)-v ((j:ℝ)/m),k ((j+1:ℕ)/(m:ℝ))-k ((j:ℝ)/m)⟫ := by
  classical
  rw [normalPartition,←Finset.sum_subset (Finset.range_mono hNm)]
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [ite_eq_left (Finset.mem_range.mp hj)]
  · intro j hj hjN
    simp only [Finset.mem_range] at hjN
    simp only [ite_eq_right hjN,sub_self,inner_zero_left]

lemma discrete_left_energy (d : ℕ → E) (N : ℕ) :
    ‖d N‖^2=‖d 0‖^2+2*(∑j∈Finset.range N,⟪d j,d (j+1)-d j⟫)+
      ∑j∈Finset.range N,‖d (j+1)-d j‖^2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have hh := norm_add_sq_real (d N) (d (N+1)-d N)
    have he : d N+(d (N+1)-d N)=d (N+1) := by abel
    rw [he] at hh
    linarith

lemma discrete_normal_contraction (d k l : ℕ → E) (N : ℕ) (ε δ : ℝ)
    (hδ : 0 ≤ δ)
    (hinc : ∀j < N,d (j+1)-d j=(k (j+1)-k j)-(l (j+1)-l j))
    (hsmall : ∀j < N,‖d (j+1)-d j‖ ≤ δ)
    (hk : (∑j∈Finset.range N,⟪d j,k (j+1)-k j⟫) ≤ ε)
    (hl : (∑j∈Finset.range N,⟪-d j,l (j+1)-l j⟫) ≤ ε) :
    ‖d N‖^2 ≤ ‖d 0‖^2+4*ε+δ*(variation k N+variation l N) := by
  have hp : (∑j∈Finset.range N,⟪d j,d (j+1)-d j⟫) =
      (∑j∈Finset.range N,⟪d j,k (j+1)-k j⟫)+(∑j∈Finset.range N,⟪-d j,l (j+1)-l j⟫) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hinc j (Finset.mem_range.mp hj),inner_sub_right,inner_neg_left,sub_eq_add_neg]
  have hs : (∑j∈Finset.range N,‖d (j+1)-d j‖^2) ≤ δ*(variation k N+variation l N) := by
    calc
      _ ≤ ∑j∈Finset.range N,δ*(‖k (j+1)-k j‖+‖l (j+1)-l j‖) := by
        apply Finset.sum_le_sum
        intro j hj
        have h₁ := hsmall j (Finset.mem_range.mp hj)
        have h₂ : ‖d (j+1)-d j‖ ≤ ‖k (j+1)-k j‖+‖l (j+1)-l j‖ := by
          rw [hinc j (Finset.mem_range.mp hj)];exact norm_sub_le _ _
        calc
          _ ≤ δ*‖d (j+1)-d j‖ := by nlinarith [norm_nonneg (d (j+1)-d j)]
          _ ≤ _ := mul_le_mul_of_nonneg_left h₂ hδ
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib];rfl
  have he := discrete_left_energy d N
  rw [hp] at he
  linarith

end ConvexSkorokhod

end OAI
