import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.L2MultiplierContinuity

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate BigOperators
noncomputable section
namespace Coulomb
lemma pairEnergy_eq_sum {n:ℕ} (u:H1Vector n) :
    pairEnergy u=∑ s,∑ i,∑ j,if i<j then (∫ x,coulombKernel (position x i-position x j)*‖u.value s x‖^2) else 0 := by
  unfold pairEnergy
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  have hi(i j:Fin n) : Integrable (fun x => if i<j then coulombKernel (position x i-position x j)*‖u.value s x‖^2 else 0) := by
    split_ifs with h
    · exact (u.pair_coulomb_integrable_bound s i j (ne_of_lt h) (by norm_num : (0:ℝ)<1)).1
    · simp
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all

lemma nuclearEnergy_strong_tendsto {M n:ℕ} (S:Nuclei M) (u:ℕ → H1Vector n) (v:H1Vector n)
    (hv:∀ s,Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s)))
    (K:ℝ) (hK:∀ k,kinetic (u k)≤K) :
    Tendsto (fun k => nuclearEnergy S (u k)) atTop (𝓝 (nuclearEnergy S v)) := by
  simp only [nuclearEnergy_eq_sum]
  apply tendsto_finsetSum
  intro s _
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply Tendsto.const_mul
  simpa only [hardyCoulomb_nuclear] using hardy_form_strong_tendsto u v s i (nuclearHardyCoordinates i (S.position j)) (hv s) K hK

lemma pairEnergy_strong_tendsto {n:ℕ} (u:ℕ → H1Vector n) (v:H1Vector n)
    (hv:∀ s,Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s)))
    (K:ℝ) (hK:∀ k,kinetic (u k)≤K) :
    Tendsto (fun k => pairEnergy (u k)) atTop (𝓝 (pairEnergy v)) := by
  simp only [pairEnergy_eq_sum]
  apply tendsto_finsetSum
  intro s _
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  by_cases h:i<j
  · simp only [ite_eq_left h]
    simpa only [hardyCoulomb_pair] using hardy_form_strong_tendsto u v s i (pairHardyCoordinates i j (ne_of_lt h)) (hv s) K hK
  · simp only [ite_eq_right h]; exact tendsto_const_nhds

lemma finite_weak_norm_sq_le_of_tendsto {ι H:Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u:ℕ → ι → H) (v:ι → H) (L:ℝ)
    (hw:∀ i w,Tendsto (fun k => inner ℂ w (u k i)) atTop (𝓝 (inner ℂ w (v i))))
    (hL:Tendsto (fun k => ∑ i,‖u k i‖^2) atTop (𝓝 L)) : ∑ i,‖v i‖^2≤L := by
  let U:ℕ → PiLp 2 (fun _:ι => H):=fun k => WithLp.toLp 2 (u k)
  let V:PiLp 2 (fun _:ι => H):=WithLp.toLp 2 v
  have hL0:0≤L := ge_of_tendsto hL (Eventually.of_forall fun k => Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hW:∀ W:PiLp 2 (fun _:ι => H),Tendsto (fun k => inner ℂ W (U k)) atTop (𝓝 (inner ℂ W V)) := by
    intro W
    simp only [PiLp.inner_apply,U,V]
    exact tendsto_finsetSum _ (fun i _ => hw i (W i))
  apply le_of_forall_pos_le_add
  intro ε hε
  have hU:∀ᶠ k in atTop,‖U k‖≤Real.sqrt (L+ε) := by
    filter_upwards [hL.eventually (gt_mem_nhds (show L<L+ε by linarith))] with k hk
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2,Real.sq_sqrt (by positivity)]
    exact hk.le
  have hV:=weak_tendsto_norm_le (Real.sqrt_nonneg (L+ε)) hW hU
  have H:=pow_le_pow_left₀ (norm_nonneg _) hV 2
  rw [Real.sq_sqrt (by positivity),PiLp.norm_sq_eq_of_L2] at H
  exact H

lemma form_strong_weak_limit_le {M n:ℕ} (S:Nuclei M) (u:ℕ → H1Vector n) (v:H1Vector n)
    (hv:∀ s,Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s)))
    (hw:∀ s a w,Tendsto (fun k => inner ℂ w ((u k).gradientL2 s a)) atTop
      (𝓝 (inner ℂ w (v.gradientL2 s a))))
    (K:ℝ) (hK:∀ k,kinetic (u k)≤K) (E:ℝ)
    (hE:Tendsto (fun k => form S (u k)) atTop (𝓝 E)) : form S v≤E := by
  let : Fact ((2:ℝ≥0∞)≠(⊤:ℝ≥0∞)) := ⟨by norm_num⟩
  have hkin:Tendsto (fun k => kinetic (u k)) atTop (𝓝 (E+nuclearEnergy S v-pairEnergy v)) := by
    convert (hE.add (nuclearEnergy_strong_tendsto S u v hv K hK)).sub (pairEnergy_strong_tendsto u v hv K hK) using 1
    ext k; unfold form; ring
  have H:=finite_weak_norm_sq_le_of_tendsto
    (fun k (sa:Spins n × (Fin n × Fin 3)) => (u k).gradientL2 sa.1 sa.2)
    (fun sa => v.gradientL2 sa.1 sa.2) (2*(E+nuclearEnergy S v-pairEnergy v))
    (fun sa => hw sa.1 sa.2) (by
      convert hkin.const_mul 2 using 1
      ext k
      rw [H1Vector.kinetic_eq_norm,Fintype.sum_prod_type]
      ring)
  rw [Fintype.sum_prod_type] at H
  rw [form,H1Vector.kinetic_eq_norm]
  linarith
end Coulomb
end

end

end OAI
