import Mathlib
import OAI.Analysis.HardSphere.Geometry.GroundPositionLaw

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

def centeredCell (L : Length) (c : Torus L) : Set (Torus L) :=
  {x | ∀ j, ((AddCircle.equivIco L.val (-L.val/2)) (x j-c j)).val ∈ Ico (-1/2:ℝ) (1/2)}

lemma centeredCell_measurable (L : Length) (c : Torus L) : MeasurableSet (centeredCell L c) := by
  simp only [centeredCell,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_Ico.preimage (measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco L.val (-L.val/2)).measurable.comp
      ((measurable_pi_apply j).sub measurable_const)))

lemma centered_rep_abs (L : Length) (x : AddCircle L.val) :
    |((AddCircle.equivIco L.val (-L.val/2)) x).val|=‖x‖ := by
  let t := (AddCircle.equivIco L.val (-L.val/2)) x
  have ht : |t.val| ≤ |L.val|/2 := by
    rw [abs_of_pos L.property,abs_le]
    constructor <;> linarith [t.property.1,t.property.2]
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr ht
  rw [AddCircle.coe_equivIco] at he
  exact he.symm

lemma chi_support_centeredCell (L : Length) (c x : Torus L) (hx : chi L (1/100) c x≠0) :
    x∈centeredCell L c := by
  have hnb : bump L (8*(1/100)) c x≠0 := by
    intro he
    apply hx
    simp only [chi,he,zero_pow (by norm_num : (2:ℕ)≠0)]
  have hb := bump_support (by norm_num : (0:ℝ)<8*(1/100)) c (subset_closure hnb)
  have hb' := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<8*(1/100)) c hb
  intro j
  have hj : dist (x j) (c j) ≤ 2*(8*(1/100)) := Set.mem_univ_pi.mp hb' j
  have ht : |((AddCircle.equivIco L.val (-L.val/2)) (x j-c j)).val| ≤ 2*(8*(1/100)) := by
    rw [centered_rep_abs,← dist_eq_norm]
    exact hj
  obtain ⟨hl,hu⟩ := abs_le.mp ht
  constructor <;> linarith

noncomputable def centeredCount {n : ℕ} (L : Length) (c : Torus L) (X : Configuration n L) : ℕ :=
  by classical exact (Finset.univ.filter (fun i ↦ X i∈centeredCell L c)).card

lemma centeredCount_measurable {n : ℕ} (L : Length) (c : Torus L) :
    Measurable (centeredCount (n:=n) L c) := by
  classical
  unfold centeredCount
  simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite ((centeredCell_measurable L c).preimage (measurable_pi_apply i))
    measurable_const measurable_const

lemma count_le_centeredCount {n : ℕ} (L : Length) (c : Torus L) (X : Configuration n L) :
    count L (1/100) c X ≤ (centeredCount L c X:ℝ) := by
  classical
  change (∑ i, chi L (1/100) c (X i)) ≤ ((Finset.univ.filter (fun i ↦ X i∈centeredCell L c)).card:ℝ)
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : X i∈centeredCell L c
  · simpa only [ite_eq_left hi] using (chi_bounds L (1/100) c (X i)).2
  · rw [ite_eq_right hi]
    have hz : chi L (1/100) c (X i)=0 := by
      by_contra hh
      exact hi (chi_support_centeredCell L c (X i) hh)
    exact hz.le

theorem scaled_centered_low_counts : ∃ α₀ ell D₀ Q : ℝ,
    0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (D α : ℝ),
      2≤n → 1 ≤ L.val → D=(n:ℝ)/L.val^3 → D₀ ≤ D →
      α₀/2 ≤ α → α ≤ 2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ A : Finset S,
      groundPositionLaw n L g {X | ∀ s∈A, (centeredCount L (c s) X:ℝ) < ell*D} ≤
        ENNReal.ofReal ((Q/D^2)^A.card) := by
  obtain ⟨α₀,ell,D₀,Q,hα,hell,hD₀,hQ,hs⟩ := scaled_low_count_probability
  refine ⟨α₀,ell,D₀,Q,hα,hell,hD₀,hQ,?_⟩
  intro S _ n L D α hn hL hDN hDD hαl hαu g hg c hc A
  apply (measure_mono (show {X : Configuration n L | ∀ s∈A, (centeredCount L (c s) X:ℝ)<ell*D} ⊆
      {X | ∀ s∈A, count L (1/100) (c s) X<ell*D} from ?_)).trans
      (hs S n L D α hn hL hDN hDD hαl hαu g hg c hc A)
  intro X hX s hs
  exact (count_le_centeredCount L (c s) X).trans_lt (hX s hs)

end
end HardSphere.CellOrbital

namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

lemma centeredCell_image {L : Length} (hL : 1 ≤ L.val) (c x : Torus L) :
    x∈centeredCell L c ↔ ∀ j, ∃ t∈Ico (-1/2:ℝ) (1/2), (t : AddCircle L.val)=x j-c j := by
  constructor
  · intro hx j
    exact ⟨_,hx j,AddCircle.coe_equivIco⟩
  · intro hx j
    obtain ⟨t,ht,he⟩ := hx j
    have ht' : t∈Ico (-L.val/2) (-L.val/2+L.val) := by constructor <;> linarith [ht.1,ht.2]
    rw [← he,AddCircle.equivIco_coe_eq ht']
    exact ht

def gridCenter {K : ℕ} (L : Length) (v : Fin 3 → Fin K) : Torus L :=
  fun j ↦ ((v j:ℝ) : AddCircle L.val)

lemma fin_circle_dist {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) {v w : Fin K} (hvw : v≠w) :
    1 ≤ dist ((v:ℝ) : AddCircle L.val) ((w:ℝ) : AddCircle L.val) := by
  have hi (v : Fin K) : (v:ℝ)∈Ico (0:ℝ) (0+L.val) := by
    constructor
    · positivity
    · simpa only [zero_add,hL] using (show (v:ℝ)<(K:ℝ) by exact_mod_cast v.isLt)
  have hne : ((v:ℝ):AddCircle L.val)≠((w:ℝ):AddCircle L.val) := by
    intro he
    have he' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hi v) (hi w)).mp he
    exact hvw (Fin.ext (by exact_mod_cast he'))
  let z : ℤ := (v.val:ℤ)-(w.val:ℤ)-round (L.val⁻¹*((v:ℝ)-(w:ℝ)))*(K:ℤ)
  have hd : dist ((v:ℝ):AddCircle L.val) ((w:ℝ):AddCircle L.val)=|(z:ℝ)| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    dsimp [z]
    push_cast
    rw [hL]
  have hz : z≠0 := by
    intro hz
    apply hne
    apply dist_eq_zero.mp
    rw [hd,hz,Int.cast_zero,abs_zero]
  have ha : (1:ℤ)≤|z| := by
    have hh : 0 < |z| := abs_pos.mpr hz
    omega
  rw [hd,← Int.cast_abs]
  exact_mod_cast ha

lemma gridCenter_separated {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) :
    ∀ z v : Fin 3 → Fin K, z≠v → 1 ≤ dist (gridCenter L z) (gridCenter L v) := by
  intro z v hzv
  obtain ⟨j,hj⟩ : ∃ j, z j≠v j := by
    by_contra hh
    push Not at hh
    exact hzv (funext hh)
  exact (fin_circle_dist hL hj).trans (dist_le_pi_dist (gridCenter L z) (gridCenter L v) j)

theorem grid_low_count_probability : ∃ α₀ ell D₀ Q : ℝ,
    0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (K n : ℕ) (L : Length) (D α : ℝ),
      1≤K → L.val=(K:ℝ) → D=(n:ℝ)/L.val^3 → D₀ ≤ D →
      α₀/2 ≤ α → α ≤ 2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ A : Finset (Fin 3 → Fin K),
      groundPositionLaw n L g {X | ∀ s∈A, (centeredCount L (gridCenter L s) X:ℝ) < ell*D} ≤
        ENNReal.ofReal ((Q/D^2)^A.card) := by
  obtain ⟨α₀,ell,D₀,Q,hα,hell,hD₀,hQ,hs⟩ := scaled_centered_low_counts
  refine ⟨α₀,ell,max D₀ 2,Q,hα,hell,lt_of_lt_of_le hD₀ (le_max_left _ _),hQ,?_⟩
  intro K n L D α hK hLK hDN hDD hαl hαu g hg A
  have hL : 1 ≤ L.val := by rw [hLK]; exact_mod_cast hK
  have hD : 2 ≤ D := (le_max_right D₀ 2).trans hDD
  have hn : 2≤n := by
    have hp : 1 ≤ L.val^3 := one_le_pow₀ hL
    have hmul : 2*L.val^3 ≤ (n:ℝ) := by
      rw [hDN] at hD
      exact (le_div_iff₀ (by positivity)).mp hD
    have hn' : (2:ℝ)≤(n:ℝ) := by linarith
    exact_mod_cast hn'
  exact hs (Fin 3 → Fin K) n L D α hn hL hDN ((le_max_left D₀ 2).trans hDD) hαl hαu
    g hg (gridCenter L) (gridCenter_separated hLK) A

end
end HardSphere.CellOrbital

end
end
end
end
end
end
end
end

end OAI
