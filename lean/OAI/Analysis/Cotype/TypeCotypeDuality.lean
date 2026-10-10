import OAI.Analysis.Cotype.KConvexDuality
import OAI.Analysis.Cotype.Moments
import Mathlib.Analysis.Normed.Module.DoubleDual

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def HasType (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (p : ℝ) : Prop :=
  1 < p ∧ p ≤ 2 ∧ ∃ D : ℝ, 0 ≤ D ∧ ∀ (n : ℕ) (x : Fin n → X),
    cubeL2 X (rademacherSum X x) ≤ D * (∑ i, ‖x i‖ ^ p) ^ (1/p)

def NontrivialType (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ p : ℝ, HasType X p

theorem tuple_dual_lq_le {n : ℕ} (φ : Fin n → (X →L[ℝ] ℝ))
    {p q C : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : (q-1)*p = q) (hC : 0 ≤ C)
    (h : ∀ x : Fin n → X, |∑ i, φ i (x i)| ≤ C*(∑ i, ‖x i‖^p)^(1/p)) :
    (∑ i, ‖φ i‖^q)^(1/q) ≤ C := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  let a : Fin n → ℝ := fun i => ‖φ i‖^(q-1)
  let S : ℝ := ∑ i, ‖φ i‖^q
  have ha i : 0 ≤ a i := Real.rpow_nonneg (norm_nonneg _) _
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hap i : (a i)^p = ‖φ i‖^q := by
    dsimp [a]; rw [← Real.rpow_mul (norm_nonneg _), hpq]
  have ham i : a i * ‖φ i‖ = ‖φ i‖^q := by
    by_cases hz : ‖φ i‖ = 0
    · simp [hz, Real.zero_rpow (ne_of_gt hq0)]
    · dsimp [a]
      calc
        _ = ‖φ i‖^(q-1) * ‖φ i‖^(1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))]
          congr 1; ring
  have hb : S ≤ C*S^(1/p) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let A := ∑ i, a i
    have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
    let δ := ε/(A+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    choose x hx he using (fun i => exists_unit_eval_gt (φ i) (by linarith : ‖φ i‖-δ < ‖φ i‖))
    let y : Fin n → X := fun i => a i • x i
    have hy : (∑ i, ‖y i‖^p)^(1/p) ≤ S^(1/p) := by
      apply Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))
      · apply Finset.sum_le_sum
        intro i _
        rw [← hap]
        apply Real.rpow_le_rpow (norm_nonneg _) _ hp0.le
        simpa [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i)] using
          mul_le_of_le_one_right (ha i) (hx i)
      · positivity
    have hval : (∑ i, φ i (y i)) ≤ C*S^(1/p) :=
      (le_abs_self _).trans ((h y).trans (mul_le_mul_of_nonneg_left hy hC))
    have hδA : δ*A ≤ ε := by
      have hh : δ*(A+1)=ε := by dsimp [δ]; field_simp
      nlinarith
    calc
      S = ∑ i, a i * ‖φ i‖ := by simp only [ham, S]
      _ ≤ ∑ i, (a i * φ i (x i) + δ*a i) := Finset.sum_le_sum (fun i _ => by
        nlinarith [mul_le_mul_of_nonneg_left (show ‖φ i‖ ≤ φ i (x i)+δ by linarith [he i]) (ha i)])
      _ = (∑ i, φ i (y i)) + δ*A := by simp [y, A, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by linarith
  change S^(1/q) ≤ C
  by_cases hz : S = 0
  · rw [hz, Real.zero_rpow (by positivity : (1/q : ℝ) ≠ 0)]; exact hC
  have hS0 : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  have he : 1/q+1/p = 1 := by field_simp [ne_of_gt hp0, ne_of_gt hq0]; nlinarith [hpq]
  have hsprod : S^(1/q)*S^(1/p) = S := by rw [← Real.rpow_add hS0, he, Real.rpow_one]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hS0 (1/p))).mp
  rw [hsprod]
  exact hb

theorem dualPairing_rademacherSum {n : ℕ} (x : Fin n → X) (φ : Fin n → (X →L[ℝ] ℝ)) :
    dualPairing (rademacherSum X x) (rademacherSum (X →L[ℝ] ℝ) φ) = ∑ i, φ i (x i) := by
  calc
    _ = ∑ i, φ i (moment X (rademacherSum X x) i) := by
      generalize rademacherSum X x = f
      simp only [dualPairing, rademacherSum, moment, average, map_smul, map_sum,
        sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by simp only [moment_rademacherSum]

theorem hasCotype_dual_of_hasType {p : ℝ} (h : HasType X p) :
    HasCotype (X →L[ℝ] ℝ) (p/(p-1)) := by
  obtain ⟨hp,hp2,D,hD,h⟩ := h
  have hp1 : 0 < p-1 := by linarith
  have hq2 : 2 ≤ p/(p-1) := (le_div_iff₀ hp1).mpr (by linarith)
  refine ⟨hq2,D,hD,fun n φ => ?_⟩
  apply tuple_dual_lq_le φ hp (by linarith : 1 < p/(p-1))
    (by field_simp [ne_of_gt hp1]; ring) (mul_nonneg hD (cubeL2_nonneg _))
  intro x
  rw [← dualPairing_rademacherSum x φ]
  exact (dualPairing_bound _ _).trans (by
    have hh := mul_le_mul_of_nonneg_right (h n x) (cubeL2_nonneg (rademacherSum (X →L[ℝ] ℝ) φ))
    simpa [mul_assoc, mul_comm, mul_left_comm] using hh)

theorem hasCotype_of_linearIsometry {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (j : X →ₗᵢ[ℝ] Y) {q : ℝ} (h : HasCotype Y q) : HasCotype X q := by
  obtain ⟨hq,C,hC,h⟩ := h
  refine ⟨hq,C,hC,fun n x => ?_⟩
  have he (u : Cube n) : rademacherSum Y (fun i => j (x i)) u = j (rademacherSum X x u) := by
    simp [rademacherSum]
  simpa only [j.norm_map, cubeL2, he] using h n (fun i => j (x i))

theorem hasCotype_of_bidual {q : ℝ}
    (h : HasCotype ((X →L[ℝ] ℝ) →L[ℝ] ℝ) q) : HasCotype X q :=
  hasCotype_of_linearIsometry (NormedSpace.inclusionInDoubleDualLi (E := X) ℝ) h

theorem finiteCotype_pair_of_nontrivialType (hX : NontrivialType X)
    (hY : NontrivialType (X →L[ℝ] ℝ)) :
    FiniteCotype X ∧ FiniteCotype (X →L[ℝ] ℝ) := by
  obtain ⟨p,hp⟩ := hX
  obtain ⟨q,hq⟩ := hY
  exact ⟨⟨q/(q-1),hasCotype_of_bidual (hasCotype_dual_of_hasType hq)⟩,
    ⟨p/(p-1),hasCotype_dual_of_hasType hp⟩⟩

end Cotype

end

end OAI
