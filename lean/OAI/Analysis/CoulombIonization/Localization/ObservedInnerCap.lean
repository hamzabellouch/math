import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.PricedCoulombTail
import OAI.Analysis.CoulombIonization.FieldAnalysis.ObservedFieldScale

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Set

lemma annular_cut_cost_innerScale {D h u : ℝ} (hD : 0 ≤ D) (hh : 0 < h) (hu : h ≤ u) :
    (annularOffsetMass D u)^2/u/h ≤ 3*innerScale D h := by
  have hup : 0 < u := hh.trans_le hu
  calc
    _ ≤ (3*(1/u^6+1+D*u))/u/h :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (annularOffsetMass_sq_le hD hup) hup.le) hh.le
    _ = 3*((1/u^7)/h+(1/u)/h+D/h) := by field_simp
    _ ≤ 3*((1/h^7)/h+(1/h)/h+D/h) := by gcongr
    _ = _ := by unfold innerScale; field_simp

lemma finite_annular_excess_at_innerScale {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevFermion psi) (hm : formMass psi = 1) {Z lam alpha beta u D h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (ha : 0 < alpha) (hD : 0 ≤ D) (hh : 0 < h) (hu : h ≤ u)
    (he : max (corePriceExcess Z lam psi) 0 ≤ D) (ys : List Space)
    (hys : ∀ y ∈ ys, alpha*u ≤ ‖y‖ ∧ ‖y‖ ≤ beta*u) :
    max (((CoreObservationEnsemble.initial psi hpsi).observeCells ys).excess Z lam) 0/h ≤
      ((radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
        (1+3*annularCellCostConstant alpha beta))*innerScale D h := by
  have hbase := actual_finite_annular_cut_excess hpsi hm hZ hlam ha (hh.trans_le hu) hD he ys hys
  have hcost := annular_cut_cost_innerScale hD hh hu
  have hC := (annularCellCostConstant_pos (beta := beta) ha).le
  have hK : 0 ≤ (radialCutExcessConstant actualCellMomentConstant+1)^ys.length := by
    have := radialCutExcessConstant_one_le actualCellMomentConstant_one_le
    positivity
  have hD' : D/h ≤ innerScale D h := by
    unfold innerScale
    have h1 : 0 ≤ 1/h^8 := by positivity
    have h2 : 0 ≤ 1/h^2 := by positivity
    linarith
  calc
    _ ≤ ((radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
      (D+annularCellCostConstant alpha beta*(annularOffsetMass D u)^2/u))/h :=
        div_le_div_of_nonneg_right hbase hh.le
    _ = (radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
      (D/h+annularCellCostConstant alpha beta*((annularOffsetMass D u)^2/u/h)) := by ring
    _ ≤ (radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
      (innerScale D h+annularCellCostConstant alpha beta*(3*innerScale D h)) :=
        mul_le_mul_of_nonneg_left (add_le_add hD' (mul_le_mul_of_nonneg_left hcost hC)) hK
    _ = _ := by ring

lemma actual_observed_local_count {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevFermion psi) (hm : formMass psi = 1) {Z lam D : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (he : max (corePriceExcess Z lam psi) 0 ≤ D)
    (ys : List Space) {z : Space} (hz : z ≠ 0) :
    ((CoreObservationEnsemble.initial psi hpsi).observeCells ys).countMoment z (8*localCellRadius z) ≤
      actualCellMomentConstant*(localOffsetMass D z)^2 := by
  let E := CoreObservationEnsemble.initial psi hpsi
  have hr := localCellRadius_pos hz
  calc
    _ ≤ E.countMoment z (8*localCellRadius z) := E.observeCells_countMoment ys _ _
    _ ≤ E.countMoment z (32*localCellRadius z) := E.countMoment_le_of_radius z z
      (by simp only [sub_self,norm_zero,zero_add]; linarith)
    _ = rawCountMoment psi z (32*localCellRadius z) := CoreObservationEnsemble.initial_countMoment ..
    _ ≤ actualCellMomentConstant*(localOffsetMass (max (corePriceExcess Z lam psi) 0) z)^2 :=
      priced_enlarged_cell_count hpsi hm hZ hlam hz
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (zero_le_one.trans (localOffsetMass_one_le _ z)) (localOffsetMass_mono he z) 2)
      (zero_le_one.trans actualCellMomentConstant_one_le)

 theorem exists_actual_observed_innerCap_constant {alpha beta : ℝ} (ha : 0 < alpha) (L : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z lam : ℝ) (N : ℕ) (psi : FormVector N) (hpsi : SobolevFermion psi),
      formMass psi = 1 → 0 ≤ Z → 0 < lam → ∀ (D h u : ℝ), 0 ≤ D → 0 < h → h ≤ u →
      max (corePriceExcess Z lam psi) 0 ≤ D → ∀ ys : List Space, ys.length = L →
      (∀ y ∈ ys, alpha*u ≤ ‖y‖ ∧ ‖y‖ ≤ beta*u) →
      ((CoreObservationEnsemble.initial psi hpsi).observeCells ys).innerCapAverage Z lam h ≤
        C*(innerScale D h+lam^2) := by
  obtain ⟨T,hT,hTail⟩ := exists_priced_coulomb_tail_constant
  let A := (radialCutExcessConstant actualCellMomentConstant+1)^L*(1+3*annularCellCostConstant alpha beta)
  let F := localFieldUniversalConstant*(100000*A+(5+actualCellMomentConstant)*3*(annularCellScaleConstant 1 3*100000)^2)
  let K := 3*(packetDensityConstant*64*(36*Real.pi))^2*F+3*(16*packetPotentialConstant)^2*T
  let C := max K 3
  have hA : 0 ≤ A := by
    have := radialCutExcessConstant_one_le actualCellMomentConstant_one_le
    have := annularCellCostConstant_pos (beta := beta) ha
    dsimp [A]; positivity
  have hF : 0 ≤ F := by
    have := localFieldUniversalConstant_pos
    have := actualCellMomentConstant_one_le
    dsimp [F]; positivity
  refine ⟨C,(by dsimp [C]; exact (by norm_num : (1:ℝ) ≤ 3).trans (le_max_right _ _)),?_⟩
  intro Z lam N psi hpsi hm hZ hlam D h u hD hh hu he ys hlen hys
  let E := (CoreObservationEnsemble.initial psi hpsi).observeCells ys
  have hmE : E.mass = 1 := (CoreObservationEnsemble.observeCells_mass ..).trans ((CoreObservationEnsemble.initial_mass ..).trans hm)
  have hEx : max (E.excess Z lam) 0/h ≤ A*innerScale D h := by
    simpa only [E,A,hlen] using finite_annular_excess_at_innerScale hpsi hm hZ hlam ha hD hh hu he ys hys
  have hf : ∀ z ∈ innerFieldTestAnnulus h, E.fieldMoment Z lam z ≤ F*innerScale D h := by
    intro z hz
    exact ensemble_field_annular_bound E hZ hlam hD hh hmE hEx
      (fun z hz => actual_observed_local_count hpsi hm hZ hlam he ys (norm_pos_iff.mp (hh.trans_le hz.1))) hz
  have ht : E.weightedMoment (coulombTailWeight h) ≤ T*innerScale D h := by
    calc
      _ ≤ (CoreObservationEnsemble.initial psi hpsi).weightedMoment (coulombTailWeight h) :=
        CoreObservationEnsemble.observeCells_weightedMoment _ ys (coulombTailWeight_measurable h)
          (coulombTailWeight_nonneg h) (coulombTailWeight_le hh)
      _ = rawWeightedMoment psi (coulombTailWeight h) := CoreObservationEnsemble.initial_weightedMoment ..
      _ ≤ _ := hTail Z lam N psi hpsi hm hZ hlam D h hD hh he
  have hb := innerCapAverage_scale E hZ hlam.le hD hh hmE hF hf ht
  calc
    _ ≤ K*innerScale D h+3*lam^2 := hb
    _ ≤ C*innerScale D h+C*lam^2 := add_le_add
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (innerScale_nonneg hD hh))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
    _ = _ := by ring

end
open MeasureTheory Filter
open scoped BigOperators

structure FullStatistic where
  value : ∀ N, Configuration N → ℝ
  measurable : ∀ N, Measurable (value N)
  bounded : ∀ N, ∃ B : ℝ, ∀ x, ‖value N x‖ ≤ B
  reindex : ∀ {M N} (e : Fin M ≃ Fin N) (x : Configuration M),
    value N (x ∘ e.symm) = value M x

lemma rawFormPair_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (psi : FormVector N)
    (F : FullStatistic) : rawFormPair (reindexForm e psi) (F.value M) = rawFormPair psi (F.value N) := by
  have he (s : Spins M) :
      (∫ x, F.value M x*‖(reindexForm e psi).value s x‖^2) =
      ∫ x, F.value N x*‖psi.value (s ∘ e.symm) x‖^2 := by
    simpa only [reindexForm,F.reindex] using
      integral_reindex e (fun x => F.value N x*‖psi.value (s ∘ e.symm) x‖^2)
  unfold rawFormPair
  simp_rw [he]
  exact sum_spin_reindex e (fun s : Spins N => ∫ x, F.value N x*‖psi.value s x‖^2)

lemma rawFormPair_nextCoreObservation {N M : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (psi : FormVector (N+M)) (c : Fin N → Fin 2) (F : FullStatistic) :
    rawFormPair (nextCoreObservation p hp psi c) (F.value _) =
      rawFormPair (multiplyForm (coreLiftMultiplier M (spatialProduct p hp c)) psi) (F.value _) := by
  unfold nextCoreObservation repeatedCutForm
  rw [rawFormPair_reindex,rawFormPair_reindex]

lemma sum_rawFormPair_nextCoreObservation {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2=1) (F : FullStatistic) :
    (∑ c : Fin N → Fin 2, rawFormPair (nextCoreObservation p hp psi c) (F.value _)) =
      rawFormPair psi (F.value _) := by
  simp_rw [rawFormPair_nextCoreObservation]
  obtain ⟨B,hB⟩ := F.bounded (N+M)
  unfold rawFormPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hi (c : Fin N → Fin 2) : Integrable (fun x => F.value (N+M) x*
      ‖(multiplyForm (coreLiftMultiplier M (spatialProduct p hp c)) psi).value s x‖^2) :=
    (((hpsi.multiply _).1 s).norm.integrable_sq).bdd_mul (F.measurable _).aestronglyMeasurable
      (ae_of_all _ hB)
  rw [←integral_finsetSum _ (fun c _ => hi c)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hs : ∑ c : Fin N → Fin 2, (coreLiftMultiplier M (spatialProduct p hp c)).value x^2 = 1 := by
    exact spatial_square_partition p hp (leftList x)
  simp only [multiplyForm,Complex.norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [←Finset.mul_sum,←Finset.sum_mul,hs]
  ring

namespace CoreObservationGraph
 def fullAverage (G : CoreObservationGraph) (F : FullStatistic) : ℝ :=
    rawFormPair G.vector (F.value _)
 lemma observe_fullAverage (G : CoreObservationGraph)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (F : FullStatistic) :
    (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).fullAverage F) = G.fullAverage F :=
    sum_rawFormPair_nextCoreObservation G.sobolev p hp F
end CoreObservationGraph
namespace CoreObservationEnsemble
 def fullAverage (E : CoreObservationEnsemble) (F : FullStatistic) : ℝ :=
    ∑ i, (E.graph i).fullAverage F
 lemma initial_fullAverage {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi) (F : FullStatistic) :
    (initial psi hpsi).fullAverage F = rawFormPair psi (F.value N) := by
    change (∑ _i : Unit, rawFormPair psi (F.value N)) = _
    simp
 lemma observe_fullAverage (E : CoreObservationEnsemble)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (F : FullStatistic) : (E.observe p hp).fullAverage F = E.fullAverage F := by
    change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
      ((E.graph ic.1).observe p hp ic.2).fullAverage F) = _
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => (E.graph i).observe_fullAverage p hp F)
 lemma observeCells_fullAverage (E : CoreObservationEnsemble) (ys : List Space) (F : FullStatistic) :
    (E.observeCells ys).fullAverage F = E.fullAverage F := by
    induction ys generalizing E with
    | nil => rfl
    | cons y ys ih =>
      rw [observeCells,ih]
      unfold observeCell
      split_ifs
      · rfl
      · exact observe_fullAverage E _ _ F
end CoreObservationEnsemble

end CoulombAtom

end

end OAI
