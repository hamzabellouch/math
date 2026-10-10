import Mathlib
import OAI.Probability.SKValue.GroundState.BlockCoeff
import OAI.Probability.SKValue.GroundState.LogComparison

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

theorem expected_affine_max_le {ι κ ν : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) (b : ι → ν → ℝ) (d : ι → ℝ)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (fun i ↦ linearProcess a z i+d i) ∂gaussianProduct κ) ≤
      ∫ z, finiteMaximum (fun i ↦ linearProcess b z i+d i) ∂gaussianProduct ν := by
  classical
  let A := fun z ↦ finiteMaximum (fun i ↦ linearProcess a z i+d i)
  let B := fun z ↦ finiteMaximum (fun i ↦ linearProcess b z i+d i)
  have hiA : Integrable A (gaussianProduct κ) := affineMaximum_integrable a d
  have hiB : Integrable B (gaussianProduct ν) := affineMaximum_integrable b d
  let C := ∑ i, |d i|
  have hC (i : ι) : 0 ≤ d i+C := by
    have h := Finset.single_le_sum (fun j _ ↦ abs_nonneg (d j)) (Finset.mem_univ i)
    have hh := neg_abs_le (d i)
    dsimp [C]
    linarith
  let L := Real.log (2*(Fintype.card ι : ℝ))
  have hβbound (β : ℝ) (hβ : 0 ≤ β) :
      β*(∫ z, A z ∂gaussianProduct κ) ≤ β*(∫ z, B z ∂gaussianProduct ν)+L := by
    let m : ι → ℕ := fun i ↦ ⌈Real.exp (β*(d i+C))⌉₊
    have hm (i : ι) : 0 < m i := Nat.ceil_pos.mpr (Real.exp_pos _)
    let : Nonempty (Σ i, Fin (m i)) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty ι),⟨0,hm _⟩⟩⟩
    have hl (i : ι) : Real.exp (β*(d i+C)) ≤ (m i : ℝ) := Nat.le_ceil _
    have hu (i : ι) : (m i : ℝ) ≤ 2*Real.exp (β*(d i+C)) := by
      have he : 1 ≤ Real.exp (β*(d i+C)) := Real.one_le_exp_iff.mpr (mul_nonneg hβ (hC i))
      have hh := Nat.ceil_lt_add_one (Real.exp_pos (β*(d i+C))).le
      dsimp [m]
      linarith
    let a' : (Σ i, Fin (m i)) → κ → ℝ := fun i k ↦ β*a i.1 k
    let b' : (Σ i, Fin (m i)) → ν → ℝ := fun i k ↦ β*b i.1 k
    have hcomp := expected_logPartition_le a' b' (fun i j ↦ by
      have heA : (∑ k, (β*a i.1 k-β*a j.1 k)^2) =
          β^2*∑ k, (a i.1 k-a j.1 k)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      have heB : (∑ k, (β*b i.1 k-β*b j.1 k)^2) =
          β^2*∑ k, (b i.1 k-b j.1 k)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      dsimp [a',b']
      rw [heA,heB]
      exact mul_le_mul_of_nonneg_left (hdist i.1 j.1) (sq_nonneg β))
    have hAi := logPartition_integrable a'
    have hBi := logPartition_integrable b'
    have hlow (z : κ → ℝ) : β*(A z+C) ≤ logPartition (linearProcess a' z) := by
      have h := (replicated_partition_bounds (linearProcess a z)
        (fun i ↦ d i+C) β hβ m hl hu).1
      have he : (fun i ↦ linearProcess a z i+(d i+C)) =
          (fun i ↦ (linearProcess a z i+d i)+C) := by funext i; ring
      rw [he,finiteMaximum_add_const] at h
      simpa only [A,a',linearProcess_scaled,linearProcess] using h
    have hupp (z : ν → ℝ) : logPartition (linearProcess b' z) ≤ β*(B z+C)+L := by
      have h := (replicated_partition_bounds (linearProcess b z)
        (fun i ↦ d i+C) β hβ m hl hu).2
      have he : (fun i ↦ linearProcess b z i+(d i+C)) =
          (fun i ↦ (linearProcess b z i+d i)+C) := by funext i; ring
      rw [he,finiteMaximum_add_const] at h
      simpa only [B,b',linearProcess_scaled,linearProcess,L] using h
    have h1 := integral_mono ((hiA.add (integrable_const C)).const_mul β) hAi hlow
    have h2 := integral_mono hBi
      (((hiB.add (integrable_const C)).const_mul β).add (integrable_const L)) hupp
    have h := h1.trans (hcomp.trans h2)
    simp only [Pi.add_apply] at h
    rw [integral_const_mul,integral_add hiA (integrable_const C),integral_const] at h
    have hiB' : Integrable (fun z ↦ β*(B z+C)) (gaussianProduct ν) :=
      (hiB.add (integrable_const C)).const_mul β
    rw [integral_add hiB' (integrable_const L),
      integral_const_mul,integral_add hiB (integrable_const C),integral_const,integral_const] at h
    simp only [probReal_univ,one_smul] at h
    linarith
  by_contra hh
  have hΔ : 0 < (∫ z, A z ∂gaussianProduct κ)-(∫ z, B z ∂gaussianProduct ν) :=
    sub_pos.mpr (lt_of_not_ge hh)
  let Δ := (∫ z, A z ∂gaussianProduct κ)-(∫ z, B z ∂gaussianProduct ν)
  let β := (|L|+1)/Δ
  have hb : 0<β := div_pos (by positivity) hΔ
  have h := hβbound β hb.le
  have he : β*Δ=|L|+1 := div_mul_cancel₀ _ hΔ.ne'
  have hl := le_abs_self L
  dsimp [Δ] at he
  nlinarith

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma product_inner_sum {κ ν : Type*} [Fintype κ] [Fintype ν]
    (x y : κ → ℝ) (u v : ν → ℝ) :
    (∑ k : κ×ν, (x k.1*u k.2)*(y k.1*v k.2)) =
      (∑ k, x k*y k)*(∑ k, u k*v k) := by
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sq_distance_sum {κ : Type*} [Fintype κ] (x y : κ → ℝ) :
    (∑ k, (x k-y k)^2) = (∑ k, x k^2)+(∑ k, y k^2)-2*(∑ k, x k*y k) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

noncomputable def leafFieldCoeff {Λ κ : Type*} (n : ℕ) (v : Λ → κ → ℝ)
    (p : (Fin n → Bool)×Λ) (k : Fin n×κ) : ℝ := spin (p.1 k.1)*v p.2 k.2

noncomputable def leafAuxCoeff {Λ κ : Type*} (n : ℕ) (v : Λ → κ → ℝ)
    (α : Λ) (k : κ×κ) : ℝ := Real.sqrt ((n : ℝ)/2)*v α k.1*v α k.2

noncomputable def guerraCoeff {Λ κ : Type*} (n : ℕ) (v : Λ → κ → ℝ)
    (p : (Fin n → Bool)×Λ) : (Fin n×Fin n) ⊕ (κ×κ) → ℝ :=
  Sum.elim (hamCoeff n p.1) (leafAuxCoeff n v p.2)

lemma leafField_inner {Λ κ : Type*} [Fintype κ] (n : ℕ) (v : Λ → κ → ℝ)
    (p q : (Fin n → Bool)×Λ) :
    (∑ k, leafFieldCoeff n v p k*leafFieldCoeff n v q k) =
      (∑ i, spin (p.1 i)*spin (q.1 i))*(∑ k, v p.2 k*v q.2 k) :=
  product_inner_sum (fun i ↦ spin (p.1 i)) (fun i ↦ spin (q.1 i)) (v p.2) (v q.2)

lemma leafField_sq {Λ κ : Type*} [Fintype κ] (n : ℕ) (v : Λ → κ → ℝ)
    (hv : ∀ α, ∑ k, (v α k)^2=1) (p : (Fin n → Bool)×Λ) :
    (∑ k, (leafFieldCoeff n v p k)^2)=(n : ℝ) := by
  simp_rw [sq]
  rw [leafField_inner]
  simp only [←sq,spin_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,hv]

lemma leafAux_inner {Λ κ : Type*} [Fintype κ] (n : ℕ) (v : Λ → κ → ℝ)
    (α β : Λ) :
    (∑ k, leafAuxCoeff n v α k*leafAuxCoeff n v β k) =
      ((n : ℝ)/2)*(∑ k, v α k*v β k)^2 := by
  have hp := product_inner_sum (v α) (v β) (v α) (v β)
  calc
    _ = (Real.sqrt ((n : ℝ)/2))^2 *
        (∑ k : κ×κ, (v α k.1*v α k.2)*(v β k.1*v β k.2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [leafAuxCoeff]
      ring
    _ = _ := by rw [Real.sq_sqrt (by positivity),hp]; ring

lemma leafAux_sq {Λ κ : Type*} [Fintype κ] (n : ℕ) (v : Λ → κ → ℝ)
    (hv : ∀ α, ∑ k, (v α k)^2=1) (α : Λ) :
    (∑ k, (leafAuxCoeff n v α k)^2)=(n : ℝ)/2 := by
  simp_rw [sq]
  rw [leafAux_inner]
  simp only [←sq,hv,one_pow,mul_one]

theorem guerra_metric_remainder {Λ κ : Type*} [Fintype κ] {n : ℕ}
    (hn : 0<n) (v : Λ → κ → ℝ) (hv : ∀ α, ∑ k, (v α k)^2=1)
    (p q : (Fin n → Bool)×Λ) :
    (∑ k, (leafFieldCoeff n v p k-leafFieldCoeff n v q k)^2)-
      (∑ k, (guerraCoeff n v p k-guerraCoeff n v q k)^2) =
      (n : ℝ)*((∑ i, spin (p.1 i)*spin (q.1 i))/(n : ℝ)-
        (∑ k, v p.2 k*v q.2 k))^2 := by
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  rw [Fintype.sum_sum_type]
  simp only [guerraCoeff,Sum.elim_inl,Sum.elim_inr]
  rw [hamCoeff_distance hn,sq_distance_sum (leafFieldCoeff n v p),
    leafField_sq n v hv,leafField_sq n v hv,leafField_inner,
    sq_distance_sum (leafAuxCoeff n v p.2),leafAux_sq n v hv,
    leafAux_sq n v hv,leafAux_inner]
  field_simp
  ring

lemma guerra_metric_le {Λ κ : Type*} [Fintype κ] {n : ℕ}
    (hn : 0<n) (v : Λ → κ → ℝ) (hv : ∀ α, ∑ k, (v α k)^2=1)
    (p q : (Fin n → Bool)×Λ) :
    (∑ k, (guerraCoeff n v p k-guerraCoeff n v q k)^2) ≤
      ∑ k, (leafFieldCoeff n v p k-leafFieldCoeff n v q k)^2 := by
  have h := guerra_metric_remainder hn v hv p q
  have hs : 0 ≤ (n : ℝ)*((∑ i, spin (p.1 i)*spin (q.1 i))/(n : ℝ)-
      (∑ k, v p.2 k*v q.2 k))^2 := by positivity
  linarith

end SKValueG

end

end OAI
