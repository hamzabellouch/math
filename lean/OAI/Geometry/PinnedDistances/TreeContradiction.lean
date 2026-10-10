import OAI.Geometry.PinnedDistances.FiberTransport

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section

namespace WeakPinned.Cuts
open MeasureTheory Hierarchy Variance
open scoped BigOperators
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

omit [Fintype P] [DecidableEq P] in
lemma cost_mixture (s : Finset (Finset P)) (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0≤l C)
    (w : I → ℝ) (p : I → P → ℝ) (a : P → ℝ) (hw : ∀ i, 0≤w i) (hW : ∑ i, w i=1) :
    cost s l (fun y => ∑ i, w i*p i y) a≤∑ i, w i*cost s l (p i) a := by
  have hm (C : Finset P) : mass (fun y => ∑ i, w i*p i y) C-mass a C=
      ∑ i, w i*(mass (p i) C-mass a C) := by
    simp only [mass,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hW,one_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  unfold cost
  simp only [hm]
  calc
    _ ≤ ∑ C ∈ s, l C*∑ i, w i*|mass (p i) C-mass a C| := by
      apply Finset.sum_le_sum
      intro C hC
      apply mul_le_mul_of_nonneg_left _ (hl C hC)
      convert Finset.abs_sum_le_sum_abs (s:=Finset.univ) (fun i => w i*(mass (p i) C-mass a C)) using 1
      simp only [abs_mul,abs_of_nonneg (hw _)]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun C _ => by ring))

omit [DecidableEq P] in
lemma mass_upper (p : P → ℝ) (hp0 : ∀ x, 0≤p x) (hp : ∑ x, p x=1) (C : Finset P) : mass p C≤1 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hp0 x)).trans_eq hp

omit [DecidableEq P] in
lemma cost_bound (s : Finset (Finset P)) (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0≤l C)
    (p a : P → ℝ) (hp0 : ∀ x, 0≤p x) (ha0 : ∀ x, 0≤a x)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) : cost s l p a≤∑ C ∈ s, l C := by
  apply Finset.sum_le_sum
  intro C hC
  have hh : |mass p C-mass a C|≤1 := abs_le.mpr ⟨by linarith [mass_nonneg p hp0 C,mass_upper a ha0 ha C],
    by linarith [mass_nonneg a ha0 C,mass_upper p hp0 hp C]⟩
  simpa using mul_le_mul_of_nonneg_left hh (hl C hC)

lemma projection_replacement (d d' : Depth P) (δ : ℝ) (hδ : 0≤δ) (p a : P → ℝ)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) (x y : P) :
    |distance d.allCuts (d.cutLength (fun C => tent δ (mass a C))) x y-
        rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass a C))) y|≤
      |distance d.allCuts (d.cutLength (fun C => tent δ (mass p C))) x y-
        rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass p C))) y|+
      charge d δ p a+charge d' δ p a := by
  have h1 := distance_change_charge d δ hδ p a hp ha hps has x y
  have h2 := root_change_charge d' δ hδ p a hp ha hps has y
  let A := distance d.allCuts (d.cutLength (fun C => tent δ (mass a C))) x y
  let B := rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass a C))) y
  let C := distance d.allCuts (d.cutLength (fun C => tent δ (mass p C))) x y
  let D := rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass p C))) y
  change |C-A|≤charge d δ p a at h1
  change |D-B|≤charge d' δ p a at h2
  change |A-B|≤|C-D|+charge d δ p a+charge d' δ p a
  have hh1 : |A-B|≤|A-C|+|C-B| := abs_sub_le A C B
  have hh2 : |C-B|≤|C-D|+|D-B| := abs_sub_le C D B
  have hh3 : |A-C|=|C-A| := abs_sub_comm A C
  rw [hh3] at hh1
  linarith only [hh1,hh2,h1,h2]

lemma family_charge_occurrence (d : Depth P) (hn : 2≤Fintype.card P) (w : I → ℝ)
    (B : I → Finset P) (hB : ∀ i, (B i).Nonempty) (δ : ℝ) (hδ : 0≤δ)
    (hp : ∀ i x, prob (B i) x≤δ) (ha : ∀ x, prob (Finset.univ : Finset P) x≤δ) :
    (∑ i, w i*charge d δ (prob (B i)) (prob Finset.univ))=
      weightedIntegral d.mass (familyCutError w B δ) := by
  have ha1 : ∑ x, prob (Finset.univ : Finset P) x=1 := sum_prob _ (by
    apply Finset.univ_nonempty_iff.mpr
    exact Fintype.card_pos_iff.mp (by omega))
  simp only [charge_occurrence d hn δ hδ _ _ (sum_prob _ (hB _)) ha1 (hp _) ha]
  simp only [weightedIntegral,Finset.mul_sum,familyCutError]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro i _
  simp only [mass,sum_prob_cell]
  ring

/-- One coordinate of the finite tree contradiction, before arithmetic
averaging. The incoming laws are arbitrary probabilities representing the
actual conditional source law, not an independence hypothesis. -/
lemma length_upper (d d' : Depth P) (δ : ℝ) (hδ : 0≤δ)
    (a t : P → ℝ) (ρ : P → P → ℝ) (w : I → ℝ) (p : I → P → ℝ) (src : I → P)
    (ha0 : ∀ x, 0≤a x) (ht0 : ∀ y, 0≤t y) (hρ0 : ∀ y x, 0≤ρ y x) (hw : ∀ i, 0≤w i)
    (ha : ∑ x, a x=1) (ht : ∑ y, t y=1) (hρ : ∀ y, ∑ x, ρ y x=1) (hW : ∑ i, w i=1)
    (hp : ∀ i, ∑ y, p i y=1) (hp0 : ∀ i y, 0≤p i y)
    (has : ∀ x, a x≤δ) (hps : ∀ i x, p i x≤δ)
    (htm : t=fun y => ∑ i, w i*p i y)
    (hedge : ∀ F : P → P → ℝ, (∑ y, t y*∑ x, ρ y x*F x y)=∑ i, w i*∑ y, p i y*F (src i) y) :
    δ^3*(∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass a B)) C)≤
      2*Global.fiberCutDiscrepancy w p src δ d d'+
      4*(∑ i, w i*charge d δ (p i) a)+2*(∑ i, w i*charge d' δ (p i) a)+
      2*(∑ y, t y*cost d.allCuts (d.cutLength (fun B => tent δ (mass a B))) (ρ y) a) := by
  let l := d.cutLength (fun B => tent δ (mass a B))
  have hl (C) (_ : C∈d.allCuts) : 0≤l C := d.cutLength_nonneg _ (fun C => tent_nonneg _ _) C
  have hlow := d.actual_cut_fluctuation a ha0 ha (tent δ) (tent_nonneg δ) δ hδ (fun u hn => by
    apply le_antisymm _ (tent_nonneg δ u)
    by_contra hh
    have hu := tent_positive (lt_of_not_ge hh)
    exact hn ⟨hu.1.le,by linarith [hu.2]⟩)
  have hupper := iid_transfer d.allCuts d.allCuts_laminar l hl a t ρ ha0 ht0 hρ0 ha ht hρ
    (rootDistance d'.allCuts (d'.cutLength (fun B => tent δ (mass a B))))
  rw [hedge] at hupper
  have hproj : (∑ i, w i*∑ y, p i y*
      |distance d.allCuts l (src i) y-rootDistance d'.allCuts (d'.cutLength (fun B => tent δ (mass a B))) y|)≤
      Global.fiberCutDiscrepancy w p src δ d d'+∑ i, w i*charge d δ (p i) a+∑ i, w i*charge d' δ (p i) a := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s:=Finset.univ) (fun y _ => mul_le_mul_of_nonneg_left
        (projection_replacement d d' δ hδ (p i) a (hp i) ha (hps i) has (src i) y) (hp0 i y))) (hw i))
    simpa only [Global.fiberCutDiscrepancy,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul,l] using hh
  have hcost : cost d.allCuts l t a≤∑ i, w i*charge d δ (p i) a := by
    rw [htm]
    exact (cost_mixture d.allCuts l hl w p a hw hW).trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (cost_le_charge d δ hδ (p i) a (hp i) ha (hps i) has) (hw i)))
  dsimp only [l] at hupper hproj hcost
  linarith
end WeakPinned.Cuts
noncomputable section
namespace WeakPinned.Core.Fibers
open MeasureTheory Hierarchy Variance Cuts
open scoped BigOperators
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype V] in
lemma prob_nn (B : Finset V) (x : V) : 0≤prob B x := by
  unfold prob
  split_ifs <;> positivity

def conditionalSource (y : V) : V → ℝ :=
  if (G.incoming y).Nonempty then prob (G.incoming y) else prob Finset.univ

omit [Fintype I] in
lemma conditionalSource_nonneg (y x : V) : 0≤G.conditionalSource y x := by
  unfold conditionalSource
  split_ifs <;> exact prob_nn _ _

omit [Fintype I] in
lemma conditionalSource_sum (hn : 2≤Fintype.card V) (y : V) : ∑ x, G.conditionalSource y x=1 := by
  unfold conditionalSource
  split_ifs with h
  · exact sum_prob _ h
  · exact sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))

omit [Fintype I] in
lemma incomingWeight_nonneg (y : V) : 0≤G.incomingWeight y := by unfold incomingWeight edgeCount; positivity

omit [Fintype I] in
lemma sampling_conditional (y x : V) : G.incomingWeight y*G.conditionalSource y x=G.edgeLaw x y := by
  by_cases h : (G.incoming y).Nonempty
  · simpa only [conditionalSource,ite_eq_left h] using G.sampling_incoming x y
  · have he : G.incoming y=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hh := G.sampling_incoming x y
    have hw : G.incomingWeight y=0 := by simp [incomingWeight,he]
    simp only [hw,zero_mul] at hh ⊢
    exact hh

lemma incoming_eval (F : V → V → ℝ) :
    (∑ y, G.incomingWeight y*∑ x, G.conditionalSource y x*F x y)=
      ∑ e, G.fiberWeight e*∑ y, prob (G.targets e) y*F (G.source e) y := by
  simp only [Finset.mul_sum,← mul_assoc,G.sampling_conditional,← G.sampling_fiber,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext y
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro y _
  simp only [ite_mul,zero_mul]
  simp

lemma incoming_repr : G.incomingWeight=fun y => ∑ e, G.fiberWeight e*prob (G.targets e) y := by
  funext y
  rw [G.fiber_marginal,G.incoming_marginal]

def omittedMass (T : ℝ) : ℝ := ∑ y, if ((G.incoming y).card:ℝ)<T then G.incomingWeight y else 0

omit [Fintype I] in
lemma omittedMass_nonneg (T : ℝ) : 0≤G.omittedMass T := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact G.incomingWeight_nonneg y
  · rfl

omit [Fintype I] in
lemma retained_cost (d : Depth V) (δ T : ℝ) (hδ : 0≤δ) (hT : 0<T)
    (has : ∀ x, prob (Finset.univ : Finset V) x≤δ)
    (hrs : ∀ y x, prob (G.retainedSet T y) x≤δ)
    (hrn : ∀ y, (G.retainedSet T y).Nonempty) (hn : 2≤Fintype.card V) :
    (∑ y, G.incomingWeight y*cost d.allCuts (d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)))
      (G.conditionalSource y) (prob Finset.univ))≤
      (∑ y, G.retainedWeight T y*charge d δ (prob (G.retainedSet T y)) (prob Finset.univ))+
      G.omittedMass T*(∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)) C) := by
  have ha : ∑ x, prob (Finset.univ : Finset V) x=1 :=
    sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
  unfold omittedMass
  rw [Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  by_cases hs : T≤((G.incoming y).card:ℝ)
  · have hy : (G.incoming y).Nonempty := Finset.card_pos.mp (by exact_mod_cast hT.trans_le hs)
    have he : G.retainedSet T y=G.incoming y := by simp only [retainedSet,ite_eq_left hs]
    have hh := cost_le_charge d δ hδ (prob (G.retainedSet T y)) (prob Finset.univ)
      (sum_prob _ (hrn y)) ha (hrs y) has
    simp only [he] at hh
    simpa only [retainedWeight,ite_eq_left hs,conditionalSource,ite_eq_left hy,not_lt_of_ge hs,ite_false,zero_mul,add_zero,he]
      using mul_le_mul_of_nonneg_left hh (G.incomingWeight_nonneg y)
  · have hh := cost_bound d.allCuts (d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)))
      (fun C _ => d.cutLength_nonneg _ (fun B => tent_nonneg _ _) C)
      (G.conditionalSource y) (prob Finset.univ) (G.conditionalSource_nonneg y) (prob_nn _)
      (G.conditionalSource_sum hn y) ha
    simpa only [retainedWeight,ite_eq_right hs,lt_of_not_ge hs,ite_true,zero_mul,zero_add] using
      mul_le_mul_of_nonneg_left hh (G.incomingWeight_nonneg y)

lemma graph_length_upper (d d' : Depth V) (δ T : ℝ) (hδ : 0≤δ) (hT : 0<T)
    (hn : 2≤Fintype.card V) (hG : 0<G.edgeCount)
    (has : ∀ x, prob (Finset.univ : Finset V) x≤δ)
    (hps : ∀ e x, prob (G.targets e) x≤δ) (hpn : ∀ e, (G.targets e).Nonempty)
    (hrs : ∀ y x, prob (G.retainedSet T y) x≤δ) (hrn : ∀ y, (G.retainedSet T y).Nonempty) :
    δ^3*(∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)) C)≤
      2*Global.fiberCutDiscrepancy G.fiberWeight (fun e => prob (G.targets e)) G.source δ d d'+
      4*(∑ e, G.fiberWeight e*charge d δ (prob (G.targets e)) (prob Finset.univ))+
      2*(∑ e, G.fiberWeight e*charge d' δ (prob (G.targets e)) (prob Finset.univ))+
      2*(∑ y, G.retainedWeight T y*charge d δ (prob (G.retainedSet T y)) (prob Finset.univ))+
      2*G.omittedMass T*(∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)) C) := by
  have ha : ∑ x, prob (Finset.univ : Finset V) x=1 :=
    sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
  have hh := length_upper d d' δ hδ (prob Finset.univ) G.incomingWeight G.conditionalSource G.fiberWeight
    (fun e => prob (G.targets e)) G.source (prob_nn _) G.incomingWeight_nonneg G.conditionalSource_nonneg
    G.fiberWeight_nonneg ha (G.sum_incomingWeight hG) (G.conditionalSource_sum hn) (G.sum_fiberWeight hG)
    (fun e => sum_prob _ (hpn e)) (fun e => prob_nn _) has hps G.incoming_repr G.incoming_eval
  have hc := G.retained_cost d δ T hδ hT has hrs hrn hn
  linarith
end WeakPinned.Core.Fibers

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
