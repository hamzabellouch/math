import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open Set Filter Real
open scoped Topology

def intervalMeshPoint (k : ℕ) (i : Fin (4^k+1)) : ℝ := (i:ℝ)/(4:ℝ)^k

lemma intervalMeshPoint_mem (k : ℕ) (i : Fin (4^k+1)) :
    intervalMeshPoint k i ∈ Icc (0:ℝ) 1 := by
  constructor
  · unfold intervalMeshPoint;positivity
  · unfold intervalMeshPoint
    apply (div_le_one (by positivity : (0:ℝ)<4^k)).mpr
    exact_mod_cast (Nat.le_of_lt_succ i.isLt)

def intervalMeshIndex (t : Icc (0:ℝ) 1) (k : ℕ) : Fin (4^k+1) :=
  ⟨⌊(t:ℝ)*(4:ℝ)^k⌋₊,Nat.lt_succ_of_le (Nat.floor_le_of_le (by
    have hh := mul_le_mul_of_nonneg_right t.property.2 (show (0:ℝ) ≤ 4^k by positivity)
    simpa only [one_mul,Nat.cast_pow,Nat.cast_ofNat] using hh))⟩

lemma intervalMeshIndex_bounds (t : Icc (0:ℝ) 1) (k : ℕ) :
    intervalMeshPoint k (intervalMeshIndex t k) ≤ (t:ℝ) ∧
    (t:ℝ)-intervalMeshPoint k (intervalMeshIndex t k) ≤ (1/4:ℝ)^k := by
  have hq : (0:ℝ) < 4^k := by positivity
  have hl := Nat.floor_le (mul_nonneg t.property.1 (show (0:ℝ) ≤ 4^k by positivity))
  have hu := Nat.lt_floor_add_one ((t:ℝ)*(4:ℝ)^k)
  change (⌊(t:ℝ)*(4:ℝ)^k⌋₊:ℝ)/(4:ℝ)^k ≤ (t:ℝ) ∧ _
  constructor
  · exact (div_le_iff₀ hq).mpr hl
  · change (t:ℝ)-(⌊(t:ℝ)*(4:ℝ)^k⌋₊:ℝ)/(4:ℝ)^k ≤ _
    rw [one_div_pow]
    apply (le_div_iff₀ hq).mpr
    have he : ((t:ℝ)-(⌊(t:ℝ)*(4:ℝ)^k⌋₊:ℝ)/(4:ℝ)^k)*(4:ℝ)^k =
        (t:ℝ)*(4:ℝ)^k-(⌊(t:ℝ)*(4:ℝ)^k⌋₊:ℝ) := by field_simp
    rw [he]
    linarith only [hu]

lemma intervalMeshIndex_tendsto (t : Icc (0:ℝ) 1) :
    Tendsto (fun k=>intervalMeshPoint k (intervalMeshIndex t k)) atTop (𝓝 (t:ℝ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _=>dist_nonneg) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num))
  intro k
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (intervalMeshIndex_bounds t k).1)]
  linarith only [(intervalMeshIndex_bounds t k).2]

lemma intervalMeshIndex_increment (t : Icc (0:ℝ) 1) (k : ℕ) :
    |intervalMeshPoint (k+1) (intervalMeshIndex t (k+1))-
      intervalMeshPoint k (intervalMeshIndex t k)| ≤ 2*(1/4:ℝ)^k := by
  have h₁ := intervalMeshIndex_bounds t k
  have h₂ := intervalMeshIndex_bounds t (k+1)
  have hq : (0:ℝ) ≤ (1/4:ℝ)^k := by positivity
  rw [pow_succ] at h₂
  apply abs_le.mpr
  constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,hq]

lemma intervalMesh_edges_card (k : ℕ)
    (s : Finset (Fin (4^k+1)×Fin (4^(k+1)+1))) :
    s.card ≤ 16^(k+1) := by
  have hc := Finset.card_le_univ s
  simp only [Fintype.card_prod,Fintype.card_fin] at hc
  apply hc.trans
  have hq : 1 ≤ 4^k := one_le_pow₀ (by omega)
  have hq' : 4^(k+1)=4^k*4 := pow_succ _ _
  have he : 16^(k+1)=16*(4^k)^2 := by
    have h : (16:ℕ)=4^2 := by norm_num
    rw [pow_succ,h,← pow_mul,← pow_mul]
    ring_nf
  rw [hq',he]
  nlinarith
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Set Filter Real
open scoped Topology BigOperators
variable {α : Type*}

def boxMeshPoint (k : ℕ) (v : α→Fin (4^k+1)) : α→Icc (0:ℝ) 1 :=
  fun i=>⟨intervalMeshPoint k (v i),intervalMeshPoint_mem k (v i)⟩
def boxMeshIndex (θ : α→Icc (0:ℝ) 1) (k : ℕ) : α→Fin (4^k+1) := fun i=>intervalMeshIndex (θ i) k

lemma boxMeshIndex_tendsto (θ : α→Icc (0:ℝ) 1) :
    Tendsto (fun k=>boxMeshPoint k (boxMeshIndex θ k)) atTop (𝓝 θ) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact tendsto_subtype_rng.mpr (intervalMeshIndex_tendsto (θ i))

variable [Fintype α]
lemma boxMeshIndex_increment (θ : α→Icc (0:ℝ) 1) (k : ℕ) :
    dist (boxMeshPoint (k+1) (boxMeshIndex θ (k+1))) (boxMeshPoint k (boxMeshIndex θ k))≤2*(1/4:ℝ)^k := by
  apply (dist_pi_le_iff (by positivity : (0:ℝ)≤2*(1/4:ℝ)^k)).mpr
  intro i
  exact intervalMeshIndex_increment (θ i) k

variable [DecidableEq α]
lemma boxMesh_card (k : ℕ) : Fintype.card (α→Fin (4^k+1))≤(2*4^k)^(Fintype.card α) := by
  simp only [Fintype.card_fun,Fintype.card_fin]
  apply Nat.pow_le_pow_left
  have hh : 1≤4^k := one_le_pow₀ (by omega)
  omega

lemma boxMesh_edges_card (k : ℕ)
    (s : Finset ((α→Fin (4^k+1))×(α→Fin (4^(k+1)+1)))) :
    s.card≤16^((k+1)*Fintype.card α) := by
  apply (Finset.card_le_univ s).trans
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,←mul_pow]
  have hh := intervalMesh_edges_card k (Finset.univ : Finset (Fin (4^k+1)×Fin (4^(k+1)+1)))
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] at hh
  simpa only [pow_mul] using Nat.pow_le_pow_left hh (Fintype.card α)

lemma boxMesh_edges_exp (k : ℕ)
    (s : Finset ((α→Fin (4^k+1))×(α→Fin (4^(k+1)+1)))) :
    (s.card:ℝ)≤exp (log 16*((k:ℝ)+1)*(Fintype.card α:ℝ)) := by
  have hh : (s.card:ℝ)≤(16:ℝ)^((k+1)*Fintype.card α) := by exact_mod_cast boxMesh_edges_card k s
  apply hh.trans_eq
  rw [←exp_log (by norm_num : (0:ℝ)<16),←exp_nat_mul]
  congr 1
  push_cast
  simp only [log_exp]
  ring
end SKGap
end
end

end OAI
