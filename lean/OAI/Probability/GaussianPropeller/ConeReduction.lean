import OAI.Probability.GaussianPropeller.ConeConcavity

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace GaussianPropeller.Reduction
open Set GaussianPropeller.Quantile
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
lemma difference_cone_eq [NeZero k] (z : Fin k → Space d) (i : Fin k) :
    EhrhardCone.cone (fun j : {j : Fin k // j ≠ i} => z i-z j) = closedCell z i := by
  ext x
  constructor
  · intro hx j
    by_cases hji : j = i
    · subst j; rfl
    · have hh := hx ⟨j,hji⟩
      simp only [inner_sub_left] at hh
      linarith only [hh]
  · intro hx j
    change 0 ≤ ⟪z i-z j,x⟫
    rw [inner_sub_left]
    exact sub_nonneg.mpr (hx j)

omit [NeZero k] in
lemma gap_event_eq [NeZero k] (hk : 2 ≤ k) (z : Fin k → Space d) (i : Fin k)
    (h : Space d) (hh : ∀ j, j ≠ i → ⟪h,z i-z j⟫ = 1) {u : ℝ} (hu : 0 < u) :
    {x | u ≤ max (⟪z i,x⟫ - omittedMax hk z i x) 0} =
      EhrhardCone.shifted (fun j : {j : Fin k // j ≠ i} => z i-z j) (-u•h) := by
  classical
  ext x
  have hpair (j : {j : Fin k // j ≠ i}) : ⟪z i-z j,-u•h+x⟫ = -u+(⟪z i,x⟫-⟪z j,x⟫) := by
    have hcomm : ⟪z i-z j,h⟫=1 := (real_inner_comm _ _).trans (hh j j.property)
    rw [inner_add_right, inner_smul_right, hcomm, mul_one, inner_sub_left]
  change (u ≤ max (⟪z i,x⟫ - omittedMax hk z i x) 0) ↔
    ∀ j : {j : Fin k // j ≠ i}, 0 ≤ ⟪z i-z j,-u•h+x⟫
  simp only [le_max_iff, not_le.mpr hu, or_false, hpair]
  constructor
  · intro hx j
    have hm := Finset.le_sup' (fun j => ⟪z j,x⟫)
      (Finset.mem_erase.mpr ⟨j.property,Finset.mem_univ _⟩)
    change ⟪z j,x⟫ ≤ omittedMax hk z i x at hm
    linarith only [hx,hm]
  · intro hx
    have hm : omittedMax hk z i x ≤ ⟪z i,x⟫-u := by
      apply Finset.sup'_le
      intro j hj
      have hj' := hx ⟨j, Finset.ne_of_mem_erase hj⟩
      linarith only [hj']
    linarith only [hm]

lemma minimal_loss_upper (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    (∫ x, max (⟪centroid (A i),x⟫ -
      omittedMax hk (fun j => centroid (A j)) i x) 0 ∂gaussian d) ≤
      ((k:ℝ)/((k:ℝ)-1)) * φ (q ((gaussian d).real (A i))) *
      (q ((gaussian d).real (A i)) * (gaussian d).real (A i)+φ (q ((gaussian d).real (A i)))) := by
  classical
  let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian (Space d)))
  let z : Fin k → Space d := fun j => centroid (A j)
  let v : {j : Fin k // j ≠ i} → Space d := fun j => z i-z j
  have : Nonempty {j : Fin k // j ≠ i} := by
    obtain ⟨j,hj⟩ := erase_univ_nonempty hk i
    exact ⟨j,Finset.ne_of_mem_erase hj⟩
  have hneg : Pairwise (fun j l => ⟪z j,z l⟫ < 0) := fun j l hjl =>
    negative_inner_of_minimal hA hjl (hall j) (hall l)
  have hz : ∑ j, z j = 0 := sum_centroid_eq_zero hA.1.1
  obtain ⟨h,_,hh,hpair⟩ := Gram.exists_translation z hneg hz i
  simp only [Fintype.card_fin] at hpair
  have hcone : EhrhardCone.cone v = closedCell z i := difference_cone_eq z i
  have hae : A i =ᵐ[gaussian d] EhrhardCone.cone v := by
    rw [hcone]; exact active_eq_closedCell_ae hA hpos (hall i)
  have hcentroid : (∫ x in EhrhardCone.cone v, x ∂gaussian d) = z i :=
    setIntegral_congr_set hae.symm
  have hp : EhrhardCone.prob v 0 = (gaussian d).real (A i) := by
    rw [EhrhardCone.prob_zero]
    exact congrArg ENNReal.toReal (measure_congr hae.symm)
  have he (j : {j : Fin k // j ≠ i}) : 0 < ⟪v j,z i⟫ := by
    dsimp [v]
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have hn := hneg j.property
    nlinarith only [hn, sq_nonneg ‖z i‖]
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hβ : 0 < ⟪h, ∫ x in EhrhardCone.cone v, x ∂stdGaussian (Space d)⟫ := by
    change 0 < ⟪h, ∫ x in EhrhardCone.cone v, x ∂gaussian d⟫
    rw [hcentroid,hpair]
    exact div_pos (by linarith) hk0
  have hup := EhrhardCone.integral_prob_upper v (z i) he h hβ
  change (∫ u in Ioi (0:ℝ), EhrhardCone.prob v (-u•h)) ≤ _ at hup
  change _ ≤ φ (q (EhrhardCone.prob v 0)) *
    (q (EhrhardCone.prob v 0)*EhrhardCone.prob v 0+φ (q (EhrhardCone.prob v 0))) /
      ⟪h, ∫ x in EhrhardCone.cone v, x ∂gaussian d⟫ at hup
  rw [hp,hcentroid,hpair] at hup
  have hfi : Integrable (fun x => max (⟪z i,x⟫-omittedMax hk z i x) 0) (gaussian d) :=
    ((Integrable.const_inner _ (integrable_id_gaussian d)).sub
      (omittedMax_integrable hk z hz i)).sup (integrable_const 0)
  rw [hfi.integral_eq_integral_meas_le (ae_of_all _ (fun x => le_max_right _ _))]
  have heq : (∫ u in Ioi (0:ℝ), (gaussian d).real {x | u ≤ max (⟪z i,x⟫-omittedMax hk z i x) 0}) =
      ∫ u in Ioi (0:ℝ), EhrhardCone.prob v (-u•h) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change (gaussian d).real {x | u ≤ max (⟪z i,x⟫-omittedMax hk z i x) 0} = _
    rw [gap_event_eq hk z i h hh hu]
    rfl
  change (∫ u in Ioi (0:ℝ), (gaussian d).real {x | u ≤ max (⟪z i,x⟫-omittedMax hk z i x) 0}) ≤ _
  rw [heq]
  convert hup using 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end GaussianPropeller.Reduction

end OAI
