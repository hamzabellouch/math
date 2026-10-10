import Mathlib
import OAI.Combinatorics.KMedian.Expanders.L2

namespace OAI

section Inline_PCPGraphMix

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

lemma l2_scale {V : Type} [Fintype V] [Nonempty V] (f : V → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    l2 (fun v => c*f v)=c*l2 f := by
  have hh : energy (fun v => c*f v)=c^2*energy f := by
    unfold energy
    simp_rw [mul_pow]
    exact (mul_expect univ _ _).symm
  have h₁ := l2_sq (fun v => c*f v)
  have h₂ := l2_sq f
  have hn := l2_nonneg (fun v => c*f v)
  have hp := mul_nonneg hc (l2_nonneg f)
  rw [hh,← h₂,← mul_pow] at h₁
  nlinarith

namespace PortGraph
variable {V D S : Type}
variable (G : PortGraph V D) (H : PortGraph V S)
abbrev BlendPort := Fin 3 × (D × S)

def blendRotate (p : V × BlendPort (D := D) (S := S)) : V × BlendPort (D := D) (S := S) :=
  if p.2.1=0 then
    (G.step p.1 p.2.2.1,(p.2.1,(G.back p.1 p.2.2.1,p.2.2.2))) else
    (H.step p.1 p.2.2.2,(p.2.1,(p.2.2.1,H.back p.1 p.2.2.2)))

lemma blendRotate_involutive : Function.Involutive (blendRotate G H) := by
  rintro ⟨v,i,d,s⟩
  by_cases hi : i=0 <;> simp [blendRotate,hi,step_back,back_back]

def blend : PortGraph V (BlendPort (D := D) (S := S)) where
  rotate := { toFun := blendRotate G H
              invFun := blendRotate G H
              left_inv := blendRotate_involutive G H
              right_inv := blendRotate_involutive G H }
  involutive := blendRotate_involutive G H

@[simp] lemma blend_step (v : V) (i : Fin 3) (d : D) (s : S) :
    (G.blend H).step v (i,d,s)=if i=0 then G.step v d else H.step v s := by
  change (blendRotate G H (v,i,d,s)).1 = _
  by_cases h : i=0 <;> simp [blendRotate,h]

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype S] [Nonempty S]
omit [Fintype V] [Nonempty V] in
lemma blend_adjacency (f : V → ℝ) :
    (G.blend H).adjacency f = fun v => (G.adjacency f v+2*H.adjacency f v)/3 := by
  funext v
  unfold adjacency
  rw [expect_prod]
  simp_rw [expect_prod,blend_step]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fin,Nat.cast_ofNat,Fin.sum_univ_succ]
  simp only [Fin.isValue,ite_true,Fin.succ_zero_eq_one,Fin.reduceEq,
    ite_false,Fintype.expect_const,Finset.sum_empty,Finset.univ_eq_empty,add_zero,Fin.succ_ne_zero]
  ring

theorem blend_contracts {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hG : G.Contracts ρ) (hH : H.Contracts σ) :
    (G.blend H).Contracts ((ρ+2*σ)/3) := by
  intro f hf
  have hg := G.l2_contracts hρ hG f hf
  have hh := H.l2_contracts hσ hH f hf
  have hs := l2_add (G.adjacency f) (fun v => 2*H.adjacency f v)
  rw [l2_scale _ 2 (by norm_num)] at hs
  have he : l2 ((G.blend H).adjacency f) =
      (1/3)*l2 (fun v => G.adjacency f v+2*H.adjacency f v) := by
    rw [blend_adjacency]
    have hr : (fun v => (G.adjacency f v+2*H.adjacency f v)/3)=
        (fun v => (1/3)*(G.adjacency f v+2*H.adjacency f v)) := by funext v; ring
    rw [hr,l2_scale _ (1/3) (by norm_num)]
  have hl : l2 ((G.blend H).adjacency f) ≤ ((ρ+2*σ)/3)*l2 f := by
    rw [he]
    calc
      _ ≤ (1/3)*(l2 (G.adjacency f)+2*l2 (H.adjacency f)) := by linarith
      _ ≤ (1/3)*(ρ*l2 f+2*(σ*l2 f)) := by linarith
      _ = _ := by ring
  have hp : 0 ≤ ((ρ+2*σ)/3)*l2 f := mul_nonneg (by positivity) (l2_nonneg f)
  have hq : 0 ≤ l2 ((G.blend H).adjacency f) := l2_nonneg _
  have hsq := sq_le_sq₀ hq hp
  rw [← l2_sq,← l2_sq,← mul_pow]
  exact hsq.mpr hl

omit [Nonempty V] in
lemma contracts_one : G.Contracts 1 := by
  intro f _
  simpa using G.energy_adjacency_le f

lemma blend_half (hH : H.Contracts (1/16)) : (G.blend H).Contracts (1/2) := by
  have hh := G.blend_contracts H (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1/16)
    G.contracts_one hH
  intro f hf
  have h := hh f hf
  have hn := energy_nonneg f
  norm_num at h ⊢
  nlinarith

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphMix

end OAI
