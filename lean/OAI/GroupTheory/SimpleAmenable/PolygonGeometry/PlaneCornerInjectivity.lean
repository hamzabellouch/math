import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PlaneStepFunctions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PlaneCornerInjectivity
open Classical

@[simp] theorem cutForm_zero (a : ℕ) (j : Fin 4) : cutForm a j (0,0)=0 := by
  fin_cases j <;> simp [cutForm]

@[simp] theorem cutForm_neg (a : ℕ) (j : Fin 4) (v : ℝ × ℝ) :
    cutForm a j (-v) = -cutForm a j v := by
  fin_cases j <;> simp [cutForm] <;> ring

theorem TransverseDirection.neg {a : ℕ} {v : ℝ × ℝ} (hv : TransverseDirection a v) :
    TransverseDirection a (-v) := by
  intro j
  simpa only [cutForm_neg,neg_ne_zero] using hv j

theorem genericPlane_transverse {a : ℕ} (p : GenericPlane a) :
    TransverseDirection a p.val := by
  intro j hj
  exact p.property j 0 (by simpa using hj)

theorem planeGerm_evaluate_incident {a : ℕ} (f : PlaneStep a) {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    {z v : ℝ × ℝ} (hv : TransverseDirection a v) {p : GenericPlane a}
    (hp : p.val∈arrangementNeighborhood a S z)
    (hpv : ∀ l∈S, cutForm a l.1 z=ordinary l.2 →
      (cutForm a l.1 p.val<ordinary l.2 ↔ cutForm a l.1 v<0)) :
    f.val p=planeGerm f z v := by
  obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
  obtain ⟨q,hq,hqv⟩ := planeSector_generic hv
    ((arrangementNeighborhood_open a S z).inter hN)
    ⟨self_mem_arrangementNeighborhood a S z,hz⟩
  have hpq : f.val p=f.val q := hS p q (by
    intro l hl
    rw [planeSign_neighborhood hq.1 hqv hl]
    unfold planeSign
    apply decide_eq_decide.mpr
    by_cases he : cutForm a l.1 z=ordinary l.2
    · rw [ite_eq_left he]
      exact hpv l hl he
    · rw [ite_eq_right he]
      have hh := Set.mem_iInter₂.mp hp l hl
      rw [ite_eq_right he] at hh
      by_cases ht : cutForm a l.1 z<ordinary l.2
      · rw [ite_eq_left ht] at hh
        exact iff_of_true hh ht
      · rw [ite_eq_right ht] at hh
        exact iff_of_false (not_lt_of_gt hh) ht)
  exact hpq.trans (hf q hq.2 hqv)

theorem exists_incident_direction {a : ℕ} (S : Finset PlaneCut) (z : ℝ × ℝ)
    (p : GenericPlane a) : ∃ v : ℝ × ℝ, TransverseDirection a v ∧
      ∀ l∈S, cutForm a l.1 z=ordinary l.2 →
        (cutForm a l.1 p.val<ordinary l.2 ↔ cutForm a l.1 v<0) := by
  let U : Set (ℝ × ℝ) := ⋂ l∈S, if cutForm a l.1 z=ordinary l.2 then
    if cutForm a l.1 p.val<ordinary l.2 then {v | cutForm a l.1 v<0}
      else {v | 0<cutForm a l.1 v} else Set.univ
  have hU : IsOpen U := by
    apply isOpen_biInter_finset
    intro l hl
    split_ifs
    · exact isOpen_lt (cutForm_continuous a l.1) continuous_const
    · exact isOpen_lt continuous_const (cutForm_continuous a l.1)
    · exact isOpen_univ
  have hpU : p.val-z∈U := by
    apply Set.mem_iInter₂.mpr
    intro l hl
    split_ifs with he ht
    · change cutForm a l.1 (p.val-z)<0
      rw [cutForm_sub,he]
      linarith
    · change 0<cutForm a l.1 (p.val-z)
      rw [cutForm_sub,he]
      have hh := p.property l.1 l.2
      exact sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm hh))
    · trivial
  obtain ⟨v,hv,hvg⟩ := (avoidsCuts_dense a).inter_open_nonempty U hU ⟨p.val-z,hpU⟩
  refine ⟨v,genericPlane_transverse ⟨v,hvg⟩,fun l hl he => ?_⟩
  have hh := Set.mem_iInter₂.mp hv l hl
  rw [ite_eq_left he] at hh
  by_cases ht : cutForm a l.1 p.val<ordinary l.2
  · rw [ite_eq_left ht] at hh
    exact iff_of_true ht hh
  · rw [ite_eq_right ht] at hh
    exact iff_of_false ht (not_lt_of_gt hh)

theorem planeGerm_zero_neighborhood {a : ℕ} (f : PlaneStep a) (z : ℝ × ℝ)
    (h : ∀ v, TransverseDirection a v → planeGerm f z v=0) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z∈N ∧
      ∀ p : GenericPlane a, p.val∈N → f.val p=0 := by
  obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
  refine ⟨arrangementNeighborhood a S z,arrangementNeighborhood_open a S z,
    self_mem_arrangementNeighborhood a S z,fun p hp => ?_⟩
  obtain ⟨v,hv,hpv⟩ := exists_incident_direction S z p
  exact (planeGerm_evaluate_incident f hS hv hp hpv).trans (h v hv)

noncomputable def planeHeight (p : ℝ × ℝ) : ℝ := p.1+p.2

theorem planeHeight_continuous : Continuous planeHeight := continuous_fst.add continuous_snd

theorem planeSector_generic_descending {a : ℕ} {z v : ℝ × ℝ}
    (hv : TransverseDirection a v) (hdesc : planeHeight v<0)
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hz : z∈N) :
    ∃ p : GenericPlane a, p.val∈N ∧ p.val∈planeSector a z v ∧
      planeHeight p.val<planeHeight z := by
  let ray : ℝ → ℝ × ℝ := fun t => z+t • v
  have hray : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
  have he : ray ⁻¹' N∈nhds (0:ℝ) := by
    apply hray.continuousAt.preimage_mem_nhds
    simpa [ray] using hN.mem_nhds hz
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp he
  let t := ε/2
  have ht : 0<t := by dsimp [t]; positivity
  have htN : ray t∈N := hεN (by
    change dist t 0<ε
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    dsimp [t]; linarith)
  have hsector : ray t∈planeSector a z v := by
    intro j
    simp only [ray,cutForm_add,cutForm_smul]
    split_ifs with hj
    · nlinarith
    · have hh := lt_of_le_of_ne (le_of_not_gt hj) (hv j).symm
      nlinarith
  have hdown : planeHeight (ray t)<planeHeight z := by
    change z.1+t*v.1+(z.2+t*v.2)<z.1+z.2
    change v.1+v.2<0 at hdesc
    nlinarith
  obtain ⟨p,hp,hpg⟩ := (avoidsCuts_dense a).inter_open_nonempty
    (N∩planeSector a z v∩{q | planeHeight q<planeHeight z})
    ((hN.inter (planeSector_open a z v)).inter
      (isOpen_lt planeHeight_continuous continuous_const))
    ⟨ray t,⟨htN,hsector⟩,hdown⟩
  exact ⟨⟨p,hpg⟩,hp.1.1,hp.1.2,hp.2⟩

theorem plane_antidiagonal_transverse (a : ℕ) : TransverseDirection a (-1,1) := by
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  intro j
  fin_cases j <;> simp [cutForm] <;> linarith

theorem transverse_negative_perturbation {a : ℕ} {v : ℝ × ℝ}
    (hv : TransverseDirection a v) (hh : planeHeight v≤0) :
    ∃ w : ℝ × ℝ, TransverseDirection a w ∧ planeHeight w<0 ∧
      ∀ j, (cutForm a j v<0 ↔ cutForm a j w<0) := by
  let U := planeSector a (0,0) v
  have hvU : v∈U := by
    intro j
    simp only [cutForm_zero]
    split_ifs with hj
    · exact hj
    · exact lt_of_le_of_ne (le_of_not_gt hj) (hv j).symm
  let ray : ℝ → ℝ × ℝ := fun t => v-t • (1,1)
  have hray : Continuous ray := continuous_const.sub (continuous_id.smul continuous_const)
  have he : ray ⁻¹' U∈nhds (0:ℝ) := by
    apply hray.continuousAt.preimage_mem_nhds
    have hz : ray 0=v := by ext <;> simp [ray]
    rw [hz]
    exact (planeSector_open a (0,0) v).mem_nhds hvU
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp he
  let t := ε/2
  have ht : 0<t := by dsimp [t]; positivity
  have htU : ray t∈U := hεU (by
    change dist t 0<ε
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    dsimp [t]; linarith)
  have hs (j : Fin 4) : (cutForm a j v<0 ↔ cutForm a j (ray t)<0) ∧
      cutForm a j (ray t)≠0 := by
    have hj := htU j
    simp only [cutForm_zero] at hj
    by_cases h : cutForm a j v<0
    · rw [ite_eq_left h] at hj
      exact ⟨iff_of_true h hj,ne_of_lt hj⟩
    · rw [ite_eq_right h] at hj
      exact ⟨iff_of_false h (not_lt_of_gt hj),ne_of_gt hj⟩
  refine ⟨ray t,fun j => (hs j).2,?_,fun j => (hs j).1⟩
  change (v.1-t*1)+(v.2-t*1)<0
  change v.1+v.2≤0 at hh
  linarith

end PlaneCornerInjectivity

end SimpleAmenable
end
end

end OAI
