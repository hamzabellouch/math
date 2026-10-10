import OAI.Probability.EntangledGames.Refinement

namespace OAI

universe u_I u_Z u_X u_Y u_R u_m u_n

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {I : Type u_I} {Z : Type u_Z} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]
omit [DecidableEq Z] in
lemma coord_entropy_nonneg (q : I → Law Z) (f : (I → Z) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : I) :
    0 ≤ (q i).avg (fun z => coordDensity q f i z*Real.log (coordDensity q f i z)) := by
  rw [← kl_tilt (q i) _ (coordDensity_nonneg q f hf i) (coordDensity_total q f ht i)]
  exact kl_nonneg _ _ (tilt_supports _ _ _ _)

lemma list_coord_entropy_sum_le (q : I → Law Z) (f : (I → Z) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (l : List I) (hN : l.Nodup) :
    (∑ j : Fin l.length, (q l[j.val]).avg (fun z => coordDensity q f l[j.val] z*Real.log (coordDensity q f l[j.val] z))) ≤
      (pi q).avg (fun z => f z*Real.log (f z)) := by
  let g : I → ℝ := fun i => (q i).avg (fun z => coordDensity q f i z*Real.log (coordDensity q f i z))
  have hi : Function.Injective (fun j : Fin l.length => l[j.val]) := by
    intro i j h
    apply hN.get_inj_iff.mp
    simpa only [List.get_eq_getElem] using h
  have hs : (∑ j : Fin l.length, g l[j.val]) ≤ ∑ i, g i := by
    rw [← Finset.sum_image (f := g) (s := Finset.univ) (Set.injOn_of_injective hi)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => coord_entropy_nonneg q f hf ht i)
  exact hs.trans (coord_entropy_sum_le q f hf ht)
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
namespace EventSystem
variable (S : EventSystem X Y I R m n)

lemma rawA_error_eq (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1)) =
    (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      (S.U (j+1) r z*S.C*(S.V j r z-S.V (j+1) r z)ᵀ)) := by
  simp only [S.rawA_eq, D, stateAt_distance_right S.μ S.θ S.hθ S.hp]
  change S.μ.avg (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      (S.U (j+1) r (Function.update z S.l[j.val] q)*S.C*
        (S.V j r (Function.update z S.l[j.val] q)-S.V (j+1) r (Function.update z S.l[j.val] q))ᵀ))) = _
  rw [avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ _ S.θ
    (fun r => S.localθL r _ (List.getElem_mem j.isLt)) (fun r => S.localθR r _ (List.getElem_mem j.isLt))
    (fun r z => hsSq (S.U (j+1) r z*S.C*(S.V j r z-S.V (j+1) r z)ᵀ))
lemma rawB_error_eq (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.D j q-S.rawB j q.2)) =
    (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      ((S.U (j+1) r z-S.U j r z)*S.C*(S.V j r z)ᵀ)) := by
  simp only [S.rawB_eq, D, stateAt_distance_left S.μ S.θ S.hθ S.hp]
  change S.μ.avg (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      ((S.U (j+1) r (Function.update z S.l[j.val] q)-S.U j r (Function.update z S.l[j.val] q))*S.C*
        (S.V j r (Function.update z S.l[j.val] q))ᵀ))) = _
  rw [avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ _ S.θ
    (fun r => S.localθL r _ (List.getElem_mem j.isLt)) (fun r => S.localθR r _ (List.getElem_mem j.isLt))
    (fun r z => hsSq ((S.U (j+1) r z-S.U j r z)*S.C*(S.V j r z)ᵀ))

lemma raw_error_bounds :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1))) ≤ Real.log ((Fintype.card R : ℝ)/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawB j q.2))) ≤ Real.log ((Fintype.card R : ℝ)/S.p) := by
  have hh := chain_error_bounds S.μ S.x₀ S.y₀ S.l S.nodup S.C S.hC.le S.F S.H
    S.hF S.hF1 S.hH S.hH1 S.localF S.localH S.θ S.hθ S.hθ1 S.localθL S.localθR S.hp S.mass
  dsimp only at hh
  simp only [S.rawA_error_eq, S.rawB_error_eq, ← Finset.mul_sum]
  constructor
  · have h := mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ 1/S.p from div_nonneg zero_le_one S.hp.le)
    simpa only [U, V, ← mul_assoc, one_div, inv_mul_cancel₀ S.hp.ne', one_mul] using h
  · have h := mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ 1/S.p from div_nonneg zero_le_one S.hp.le)
    simpa only [U, V, ← mul_assoc, one_div, inv_mul_cancel₀ S.hp.ne', one_mul] using h

def M (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ) (x : X) :=
  unitize (S.rawA j x) E
def N (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ) (y : Y) :=
  unitize (S.rawB j y) E
lemma M_unit (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) (x : X) : hsSq (S.M j E x) = 1 := hsSq_unitize _ _ hE
lemma N_unit (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) (y : Y) : hsSq (S.N j E y) = 1 := hsSq_unitize _ _ hE

lemma norm_cost_bounds (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawA j q.1-S.M j E q.1))) ≤ Real.log (1/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawB j q.2-S.N j E q.2))) ≤ Real.log (1/S.p) := by
  have he := list_coord_entropy_sum_le (fun _ : I => S.μ) S.density S.density_nonneg S.density_total S.l S.nodup
  have hlog := kl_tilt_le (pi (fun _ : I => S.μ)) S.density S.density_nonneg S.density_total
    (one_div_pos.mpr S.hp) S.density_le
  rw [kl_tilt] at hlog
  have hb := he.trans hlog
  have hA (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.rawA j q.1-S.M j E q.1)) ≤
      S.μ.avg (fun z => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z *
        Real.log (coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z)) := by
    exact first_unitize_cost S.μ S.y₀
      (coordDensity (fun _ : I => S.μ) S.density S.l[j.val])
      (coordDensity_nonneg _ _ S.density_nonneg S.l[j.val])
      (coordDensity_total _ _ S.density_total S.l[j.val]) (S.rawA j) (S.rawA_norm j) E hE
  have hB (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.rawB j q.2-S.N j E q.2)) ≤
      S.μ.avg (fun z => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z *
        Real.log (coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z)) := by
    exact second_unitize_cost S.μ S.x₀
      (coordDensity (fun _ : I => S.μ) S.density S.l[j.val])
      (coordDensity_nonneg _ _ S.density_nonneg S.l[j.val])
      (coordDensity_total _ _ S.density_total S.l[j.val]) (S.rawB j) (S.rawB_norm j) E hE
  exact ⟨(Finset.sum_le_sum fun j _ => hA j).trans hb, (Finset.sum_le_sum fun j _ => hB j).trans hb⟩

lemma normalized_error_bounds (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.M j E q.1))) ≤ 4*Real.log ((Fintype.card R : ℝ)/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.N j E q.2))) ≤ 4*Real.log ((Fintype.card R : ℝ)/S.p) := by
  have hcard : (1:ℝ) ≤ Fintype.card R := by exact_mod_cast Fintype.card_pos (α := R)
  have hl : Real.log (1/S.p) ≤ Real.log ((Fintype.card R : ℝ)/S.p) :=
    Real.log_le_log (one_div_pos.mpr S.hp) (div_le_div_of_nonneg_right hcard S.hp.le)
  have ha := S.raw_error_bounds
  have hb := S.norm_cost_bounds E hE
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      avg_unitize_triangle S.μ (S.D j) (fun q => S.rawA j q.1) E)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    change (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.M j E q.1))) ≤
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1)))+
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawA j q.1-S.M j E q.1))) at hh
    linarith
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      avg_unitize_triangle S.μ (S.D j) (fun q => S.rawB j q.2) E)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    change (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.N j E q.2))) ≤
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawB j q.2)))+
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawB j q.2-S.N j E q.2))) at hh
    linarith
end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI
