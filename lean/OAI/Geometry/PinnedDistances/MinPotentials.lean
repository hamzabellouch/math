import OAI.Geometry.PinnedDistances.OverlapRates

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

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

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

/-- The giant-complement second moment estimate needed to compare W and W₂.
The linear error, unlike an absolute singleton error, can be integrated. -/
lemma cell_second_moment (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) (C : Finset P) :
    (∑ i, w i*(cellProb (B i) C)^2) ≤
      2*varianceCell w B T C + 4*pairCell Finset.univ C + κ*M*cellProb Finset.univ C := by
  have hmean := mean_cell_bound w B C M hdom
  have hm : 0≤M*cellProb Finset.univ C := (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (cellProb_nonneg _ _))).trans hmean
  unfold varianceCell
  split_ifs with hlarge
  · have hmC : 2≤C.card := by have : (1:ℝ)<C.card := hT.trans_lt hlarge; exact_mod_cast this
    have hcomp := (uniform_pair_comparison C hmC).1
    have hb : (∑ i, w i*(cellProb Finset.univ C)^2) ≤ (cellProb Finset.univ C)^2 := by
      rw [← Finset.sum_mul]
      nlinarith [sq_nonneg (cellProb Finset.univ C)]
    have hh : (∑ i, w i*(cellProb (B i) C)^2) ≤
        2*(∑ i, w i*(cellProb (B i) C-cellProb Finset.univ C)^2) +
        2*(∑ i, w i*(cellProb Finset.univ C)^2) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (show (cellProb (B i) C)^2 ≤
        2*(cellProb (B i) C-cellProb Finset.univ C)^2+2*(cellProb Finset.univ C)^2 by
          nlinarith [sq_nonneg (cellProb (B i) C-2*cellProb Finset.univ C)]) (hw i)
      nlinarith
    nlinarith [mul_nonneg hκ hm]
  · have hh : (∑ i, w i*(cellProb (B i) C)^2) ≤
        (∑ i, w i*(if 2/((B i).card:ℝ)≤cellProb (B i) C then (cellProb (B i) C)^2 else 0)) +
        κ*(∑ i, w i*cellProb (B i) C) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · nlinarith [mul_nonneg hκ (mul_nonneg (hw i) (cellProb_nonneg (B i) C))]
      · have hp : cellProb (B i) C≤κ := (le_of_lt (lt_of_not_ge hi)).trans (hk i)
        have h := mul_le_mul_of_nonneg_left hp (mul_nonneg (hw i) (cellProb_nonneg (B i) C))
        nlinarith
    have hκmean := mul_le_mul_of_nonneg_left hmean hκ
    nlinarith [pairCell_nonneg Finset.univ C]

/-- Small positive-mass cut contributions are slice contributions or variance. -/
lemma small_mass_qCell {w : I → ℝ} {B : I → Finset P} (src : I → P) (T δ : ℝ)
    (hw : ∀ i, 0≤w i) (hδ : 0<δ) (hk : ∀ i, 2/((B i).card:ℝ)≤2*δ)
    (C : Finset P) (hC : cellProb Finset.univ C≤δ) :
    (∑ i, w i*(if src i ∈ C then cellProb (B i) C else 0)) ≤
      (∑ i, w i*(if src i ∈ C ∧ cellProb (B i) C<2*δ then cellProb (B i) C else 0)) +
      (2/δ)*varianceCell w B T C := by
  let err := fun i => if T<C.card then (cellProb (B i) C-cellProb Finset.univ C)^2
    else (1/2)*(if 2/((B i).card:ℝ)≤cellProb (B i) C then (cellProb (B i) C)^2 else 0)
  have he : varianceCell w B T C=∑ i, w i*err i := by
    unfold varianceCell err
    split_ifs <;> simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hnon (i) : 0≤err i := by dsimp [err]; split_ifs <;> positivity
  have hpoint (i) : (if src i ∈ C then cellProb (B i) C else 0) ≤
      (if src i ∈ C ∧ cellProb (B i) C<2*δ then cellProb (B i) C else 0)+(2/δ)*err i := by
    by_cases hs : src i ∈ C
    · by_cases hsmall : cellProb (B i) C<2*δ
      · simp only [hs,hsmall,true_and,ite_true]
        exact le_add_of_nonneg_right (mul_nonneg (by positivity) (hnon i))
      · have hp2 : 2*δ≤cellProb (B i) C := le_of_not_gt hsmall
        simp only [hs,hsmall,true_and,ite_true,ite_false,zero_add]
        rw [show (2/δ)*err i=2*err i/δ by ring]
        apply (le_div_iff₀ hδ).mpr
        dsimp [err]
        split_ifs with hl hp
        · have hd : δ≤cellProb (B i) C-cellProb Finset.univ C := by linarith
          have hp := cellProb_nonneg (B i) C
          nlinarith [mul_nonneg (by linarith : 0≤cellProb (B i) C-2*cellProb Finset.univ C)
            (by linarith : 0≤cellProb (B i) C-cellProb Finset.univ C),
            mul_nonneg hp (sub_nonneg.mpr hd)]
        · nlinarith [mul_nonneg (cellProb_nonneg (B i) C)
            (by linarith : 0≤cellProb (B i) C-δ)]
        · exact False.elim (hp ((hk i).trans hp2))
    · simp only [hs,false_and,ite_false,zero_add]
      exact mul_nonneg (by positivity) (hnon i)
  rw [he,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hh := mul_le_mul_of_nonneg_left (hpoint i) (hw i)
  convert hh using 1; ring

end WeakPinned.Variance

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
open scoped BigOperators
variable {P : Type u3} [Fintype P] [DecidableEq P] (d : Depth P)

lemma mem_giant_iff_cell (r : ℝ) (x : P) :
    x ∈ d.giant r ↔ Fintype.card P < 2*(d.cell r x).card := by
  constructor
  · intro hx
    obtain ⟨C,hC,hx⟩ := Finset.mem_biUnion.mp hx
    have hc := (d.mem_giants r C).mp hC
    simpa only [d.cell_of_mem hc.1 hx] using hc.2
  · intro hx
    have hc : d.cell r x ∈ d.giants r := (d.mem_giants r _).mpr ⟨d.cell_mem_cells _ _,hx⟩
    rw [d.giant_eq hc]
    exact d.self_mem_cell r x

lemma mem_giant_exists (r : ℝ) (x : P) :
    x ∈ d.giant r ↔ ∃ C : Finset P, Fintype.card P < 2*C.card ∧ ∀ y ∈ C, d.share r x y := by
  rw [d.mem_giant_iff_cell]
  constructor
  · intro hc
    exact ⟨d.cell r x,hc,fun y hy => (d.mem_cell r x y).mp hy⟩
  · rintro ⟨C,hc,hs⟩
    have hsub : C ⊆ d.cell r x := fun y hy => (d.mem_cell r x y).mpr (hs y hy)
    have := Finset.card_le_card hsub
    omega

lemma mem_giant_mono {r t : ℝ} (htr : t ≤ r) {x : P} (hx : x ∈ d.giant r) : x ∈ d.giant t := by
  rw [d.mem_giant_iff_cell] at hx ⊢
  have := Finset.card_le_card (d.cell_mono htr x)
  omega

lemma isClosed_mem_giant (x : P) : IsClosed {r : ℝ | x ∈ d.giant r} := by
  simp_rw [d.mem_giant_exists,Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h : Fintype.card P < 2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy : x=y
    · simp [share,hxy]
    · simp only [share,hxy,false_or]
      exact isClosed_le continuous_id continuous_const

lemma mem_giant_low (hn : 2 ≤ Fintype.card P) (x : P) : x ∈ d.giant (-d.radius) := by
  rw [d.mem_giant_iff_cell,d.cell_of_low le_rfl,Finset.card_univ]
  omega

lemma mem_giant_le_M (hn : 2 ≤ Fintype.card P) {r : ℝ} {x : P} (hx : x ∈ d.giant r) : r ≤ d.M := by
  obtain ⟨C,hC,_⟩ := Finset.mem_biUnion.mp hx
  exact (d.giants_cutoff hn r).mp ⟨C,hC⟩

/-- The last level at which the vertex belongs to the nested giant. -/
def departure (x : P) : ℝ := sSup {r : ℝ | x ∈ d.giant r}

lemma departure_cutoff (hn : 2 ≤ Fintype.card P) (x : P) (r : ℝ) :
    x ∈ d.giant r ↔ r ≤ d.departure x := by
  have hne : Set.Nonempty {t : ℝ | x ∈ d.giant t} := ⟨-d.radius,d.mem_giant_low hn x⟩
  have hbd : BddAbove {t : ℝ | x ∈ d.giant t} := ⟨d.M,fun t ht => d.mem_giant_le_M hn ht⟩
  exact ⟨fun hx => le_csSup hbd hx,fun hr => d.mem_giant_mono hr ((d.isClosed_mem_giant x).csSup_mem hne hbd)⟩

lemma departure_le_M (hn : 2 ≤ Fintype.card P) (x : P) : d.departure x ≤ d.M :=
  d.mem_giant_le_M hn ((d.departure_cutoff hn x _).mpr le_rfl)

lemma outside_departure (hn : 2 ≤ Fintype.card P) (x : P) :
    (fun r => d.outsideIndicator r x) = (Set.Ioc (d.departure x) d.M).indicator (fun _ => (1:ℝ)) := by
  funext r
  simp only [outsideIndicator,d.giants_cutoff hn,d.departure_cutoff hn,not_le,Set.indicator,Set.mem_Ioc]
  congr 1
  exact propext and_comm

lemma integral_one_Ioc {a b : ℝ} (hab : a ≤ b) :
    (∫ r : ℝ, (Set.Ioc a b).indicator (fun _ => (1:ℝ)) r)=b-a := by
  rw [integral_indicator measurableSet_Ioc,integral_const]
  simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma potential_departure (hn : 2 ≤ Fintype.card P) (x : P) : d.potential x = d.M-d.departure x := by
  unfold potential
  rw [d.outside_departure hn x,integral_one_Ioc (d.departure_le_M hn x)]

lemma outside_product (hn : 2 ≤ Fintype.card P) (x y : P) :
    (fun r => d.outsideIndicator r x*d.outsideIndicator r y) =
      (Set.Ioc (max (d.departure x) (d.departure y)) d.M).indicator (fun _ => (1:ℝ)) := by
  funext r
  rw [congrFun (d.outside_departure hn x) r,congrFun (d.outside_departure hn y) r]
  simp only [Set.indicator,Set.mem_Ioc,max_lt_iff]
  split_ifs <;> simp_all

/-- Exact layer-cake identity, including the finite set of threshold ties. -/
lemma min_potential (hn : 2 ≤ Fintype.card P) (x y : P) :
    min (d.potential x) (d.potential y) = ∫ r, d.outsideIndicator r x*d.outsideIndicator r y := by
  rw [d.outside_product hn x y,integral_one_Ioc (max_le (d.departure_le_M hn x) (d.departure_le_M hn y)),
    d.potential_departure hn x,d.potential_departure hn y]
  exact min_sub_sub_left d.M (d.departure x) (d.departure y)

end WeakPinned.Hierarchy.Depth

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace WeakPinned.MinKernel
variable {P : Type u4} [Fintype P]

def step (a : ℝ) : ℝ → ℝ := (Set.Ioc 0 a).indicator (fun _ => 1)

lemma integrable_step (a : ℝ) : Integrable (step a) := by
  rw [step,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma step_mul (a b : ℝ) : (fun r => step a r*step b r)=step (min a b) := by
  funext r
  simp only [step,Set.indicator,Set.mem_Ioc,le_min_iff]
  split_ifs <;> simp_all

lemma integral_step (a : ℝ) (ha : 0≤a) : (∫ r, step a r)=a := by
  rw [step,integral_indicator measurableSet_Ioc]
  simp [integral_const,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal ha]

def tail (p a : P → ℝ) (r : ℝ) : ℝ := ∑ x, p x*step (a x) r

def energy (p a b : P → ℝ) : ℝ := ∑ x, ∑ y, p x*p y*min (a x) (b y)

lemma tail_product (p a b : P → ℝ) :
    (fun r => tail p a r*tail p b r) = fun r => ∑ x, ∑ y, (p x*p y)*step (min (a x) (b y)) r := by
  funext r
  simp only [tail]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [← congrFun (step_mul (a x) (b y)) r]
  ring

lemma integrable_tail_product (p a b : P → ℝ) : Integrable (fun r => tail p a r*tail p b r) := by
  rw [tail_product]
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (integrable_step _).const_mul _

lemma energy_integral (p a b : P → ℝ) (ha : ∀ x, 0≤a x) (hb : ∀ x, 0≤b x) :
    energy p a b = ∫ r, tail p a r*tail p b r := by
  rw [tail_product,integral_finsetSum _ (fun x _ => integrable_finsetSum _ fun y _ => (integrable_step _).const_mul _)]
  simp_rw [integral_finsetSum _ (fun y _ => (integrable_step _).const_mul _),integral_const_mul]
  simp only [integral_step _ (le_min (ha _) (hb _)),energy]

lemma energy_cross (p a b : P → ℝ) (ha : ∀ x, 0≤a x) (hb : ∀ x, 0≤b x) :
    2*energy p a b ≤ energy p a a+energy p b b := by
  rw [energy_integral p a b ha hb,energy_integral p a a ha ha,energy_integral p b b hb hb]
  rw [← integral_const_mul,← integral_add (integrable_tail_product p a a) (integrable_tail_product p b b)]
  apply integral_mono ((integrable_tail_product p a b).const_mul 2)
    ((integrable_tail_product p a a).add (integrable_tail_product p b b))
  intro r
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (tail p a r-tail p b r)]

lemma min_add_four (a b c d : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
    min (a+b) (c+d) ≤ min a c+min a d+min b c+min b d := by
  simp only [min_def]
  split_ifs <;> linarith

lemma energy_sum (p a b : P → ℝ) (hp : ∀ x, 0≤p x) (ha : ∀ x, 0≤a x) (hb : ∀ x, 0≤b x) :
    energy p (a+b) (a+b) ≤ 2*(energy p a a+energy p b b) := by
  have hh : energy p (a+b) (a+b) ≤ energy p a a+energy p a b+energy p b a+energy p b b := by
    unfold energy
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    have h := mul_le_mul_of_nonneg_left (min_add_four (a x) (b x) (a y) (b y) (ha x) (hb x) (ha y) (hb y))
      (mul_nonneg (hp x) (hp y))
    simpa only [Pi.add_apply,mul_add] using h
  nlinarith [energy_cross p a b ha hb,energy_cross p b a hb ha]
end WeakPinned.MinKernel

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
open scoped BigOperators
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def outsideMass (p : P → ℝ) (r : ℝ) : ℝ := ∑ x, p x*d.outsideIndicator r x

lemma integrable_outside_product (hn : 2 ≤ Fintype.card P) (x y : P) :
    Integrable (fun r => d.outsideIndicator r x*d.outsideIndicator r y) := by
  rw [d.outside_product hn x y,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma outsideMass_square (p : P → ℝ) (r : ℝ) :
    (d.outsideMass p r)^2 = ∑ x, ∑ y, p x*p y*(d.outsideIndicator r x*d.outsideIndicator r y) := by
  unfold outsideMass
  rw [pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma iid_min_potential (hn : 2 ≤ Fintype.card P) (p : P → ℝ) :
    MinKernel.energy p d.potential d.potential = ∫ r, (d.outsideMass p r)^2 := by
  simp only [d.outsideMass_square]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ fun y _ => (d.integrable_outside_product hn x y).const_mul _)]
  simp_rw [integral_finsetSum _ (fun y _ => (d.integrable_outside_product hn _ y).const_mul _),integral_const_mul]
  simp only [MinKernel.energy,d.min_potential hn]

/-- The source min-potential upper bound before averaging places and grids. -/

theorem iid_min_two_potentials (d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ x, 0≤p x) :
    (∑ x, ∑ y, p x*p y*min (d.potential x+d'.potential x) (d.potential y+d'.potential y)) ≤
      2*((∫ r, (d.outsideMass p r)^2)+(∫ r, (d'.outsideMass p r)^2)) := by
  rw [← d.iid_min_potential hn p,← d'.iid_min_potential hn p]
  exact MinKernel.energy_sum p d.potential d'.potential hp d.potential_nonneg d'.potential_nonneg
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory Variance
open scoped BigOperators
variable {P : Type u6} {I : Type u7} [Fintype P] [DecidableEq P] [Fintype I]
variable (d : Depth P)

lemma outsideMass_prob (B : Finset P) {r : ℝ} {G : Finset P} (hG : G∈d.giants r) :
    d.outsideMass (prob B) r=cellProb B Gᶜ := by
  have hne : (d.giants r).Nonempty := ⟨G,hG⟩
  have he (x) : prob B x*d.outsideIndicator r x=if x∈Gᶜ then prob B x else 0 := by
    simp only [outsideIndicator,hne,d.giant_eq hG,true_and]
    by_cases hx : x∈G <;> simp [hx]
  simp only [outsideMass,he,Finset.sum_ite_mem,Finset.univ_inter,sum_prob_cell]

lemma outsideMass_zero (p : P → ℝ) {r : ℝ} (hG : ¬(d.giants r).Nonempty) : d.outsideMass p r=0 := by
  simp [outsideMass,outsideIndicator,hG]

lemma sumCells_nonneg (f : Finset P → ℝ) (hf : ∀ C, 0≤f C) (r : ℝ) : 0≤d.sumCells f r := by
  rw [d.sumCells_count]
  exact Finset.sum_nonneg (fun C _ => mul_nonneg (by unfold count; positivity) (hf C))

lemma complement_le_sumCells (f : Finset P → ℝ) (hf : ∀ C, 0≤f C) {r : ℝ} {G : Finset P}
    (hG : G∈d.giants r) : f Gᶜ≤d.sumCells f r := by
  have hs : d.giants r={G} := Finset.ext fun C => by
    simp only [Finset.mem_singleton]
    exact ⟨fun hC => d.giants_unique hC hG,fun h => h ▸ hG⟩
  rw [d.sumCells_split,hs,Finset.sum_singleton]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun C _ => by split_ifs <;> simp_all only [le_refl]))

lemma outside_square_bound (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) (r : ℝ) :
    (∑ i, w i*(d.outsideMass (prob (B i)) r)^2) ≤
      d.sumCells (fun C => 2*varianceCell w B T C+4*pairCell Finset.univ C) r +
      κ*M*d.outsideMass (prob Finset.univ) r := by
  have hf (C : Finset P) : 0≤2*varianceCell w B T C+4*pairCell Finset.univ C :=
    add_nonneg (mul_nonneg (by norm_num) (varianceCell_nonneg w B T hw C))
      (mul_nonneg (by norm_num) (pairCell_nonneg _ _))
  by_cases hg : (d.giants r).Nonempty
  · obtain ⟨G,hG⟩ := hg
    simp_rw [d.outsideMass_prob _ hG]
    exact (cell_second_moment w B T M κ hw hW hT hκ hk hdom Gᶜ).trans
      (add_le_add (d.complement_le_sumCells _ hf hG) le_rfl)
  · simp only [d.outsideMass_zero _ hg,zero_pow (by norm_num : 2≠0),mul_zero,Finset.sum_const_zero,add_zero]
    exact d.sumCells_nonneg _ hf r

lemma integrable_outsideMass_square (hn : 2≤Fintype.card P) (p : P → ℝ) :
    Integrable (fun r => (d.outsideMass p r)^2) := by
  simp only [d.outsideMass_square]
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (d.integrable_outside_product hn x y).const_mul _

lemma integral_outsideMass (hn : 2≤Fintype.card P) (p : P → ℝ) :
    (∫ r, d.outsideMass p r)=∑ x, p x*d.potential x := by
  simp only [outsideMass]
  rw [integral_finsetSum _ (fun x _ => (d.integrable_outsideIndicator hn x).const_mul _)]
  simp only [integral_const_mul,potential]

/-- The integrable complement second moment estimate. All singleton terms
are charged to the finite potential, not integrated as constant errors. -/
theorem integrated_outside_square (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) :
    (∑ i, w i*(∫ r, (d.outsideMass (prob (B i)) r)^2)) ≤
      2*weightedIntegral d.mass (varianceCell w B T) +
      4*weightedIntegral d.mass (pairCell Finset.univ) +
      κ*M*(∑ x, prob Finset.univ x*d.potential x) := by
  let f := fun C => 2*varianceCell w B T C+4*pairCell Finset.univ C
  have hf : ∀ C, C.card≤1 → f C=0 := by
    intro C hC
    simp [f,varianceCell_singleton w B T hT hB C hC,singleton_pairCell Finset.univ C hC]
  have hi₁ : Integrable (fun r => ∑ i, w i*(d.outsideMass (prob (B i)) r)^2) :=
    integrable_finsetSum _ (fun i _ => (d.integrable_outsideMass_square hn _).const_mul _)
  have hi₂ : Integrable (fun r => d.sumCells f r) := d.integrable_sumCells hn f hf
  have hi₃ : Integrable (fun r => κ*M*d.outsideMass (prob Finset.univ) r) :=
    (integrable_finsetSum _ (fun x _ => (d.integrable_outsideIndicator hn x).const_mul _)).const_mul _
  have hh := integral_mono hi₁ (hi₂.add hi₃) (d.outside_square_bound w B T M κ hw hW hT hκ hk hdom)
  simp only [Pi.add_apply] at hh
  rw [integral_finsetSum _ (fun i _ => (d.integrable_outsideMass_square hn _).const_mul _),
    integral_add hi₂ hi₃,integral_const_mul,d.integral_outsideMass hn _,d.integral_sumCells hn f hf] at hh
  try simp only [integral_const_mul] at hh
  have he : (∑ C, d.mass C*f C)=
      2*weightedIntegral d.mass (varianceCell w B T)+4*weightedIntegral d.mass (pairCell Finset.univ) := by
    simp only [weightedIntegral,f,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl; intro C _; ring
    · apply Finset.sum_congr rfl; intro C _; ring
  rwa [he] at hh

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.MinKernel
open scoped BigOperators
variable {P : Type u8} [Fintype P]

/-- A fiber whose potential is a constant plus nonnegative overlap and a
small signed grid error has a large iid minimum. This preserves self-pairs
in the sampling, exactly as in the unbounded-scale argument. -/
lemma energy_lower (p S L E : P → ℝ) (c : ℝ)
    (hp : ∀ x, 0≤p x) (hsum : (∑ x, p x)=1)
    (hL : ∀ x, 0≤L x)
    (hS : ∀ x, p x≠0 → S x=c+L x-E x) :
    (∑ x, p x*S x)-(∑ x, p x*L x)-(∑ x, p x*|E x|)≤energy p S S := by
  have hpair (x y : P) :
      p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2) ≤
        p x*p y*min (S x) (S y) := by
    by_cases hx : p x=0
    · simp [hx]
    by_cases hy : p y=0
    · simp [hy]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hp x) (hp y))
    have hxS := hS x hx
    have hyS := hS y hy
    apply le_min <;> linarith [hL x,hL y,le_abs_self (E x),le_abs_self (E y),neg_abs_le (E x),neg_abs_le (E y)]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hpair x y))
  change _≤energy p S S at hh
  have he : (∑ x, ∑ y, p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2))=
      (∑ x, p x*S x)-(∑ x, p x*L x)-(∑ x, p x*|E x|) := by
    have hform (x y : P) : p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2)=
        (p x*S x)*p y/2+p x*(p y*S y)/2-
        ((p x*L x)*p y/2+p x*(p y*L y)/2+(p x*|E x|)*p y/2+p x*(p y*|E y|)/2) := by ring
    simp_rw [hform,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_div,
      ← Finset.mul_sum,← Finset.sum_mul,hsum,mul_one,one_mul]
    ring
  rwa [he] at hh
end WeakPinned.MinKernel

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory Variance
open scoped BigOperators
variable {P : Type u9} {I : Type u10} [Fintype P] [DecidableEq P] [Fintype I]

lemma min_upper_family (d d' : Depth P) (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) :
    (∑ i, w i*MinKernel.energy (prob (B i)) (d.potential+d'.potential) (d.potential+d'.potential)) ≤
      4*(weightedIntegral d.mass (varianceCell w B T)+weightedIntegral d'.mass (varianceCell w B T))+
      8*(weightedIntegral d.mass (pairCell Finset.univ)+weightedIntegral d'.mass (pairCell Finset.univ))+
      2*κ*M*(∑ x, prob Finset.univ x*(d.potential x+d'.potential x)) := by
  have hm (i) := d.iid_min_two_potentials d' hn (prob (B i))
    (fun x => by unfold prob; split_ifs <;> positivity)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (hm i) (hw i))
  change (∑ i, w i*MinKernel.energy (prob (B i)) (d.potential+d'.potential) (d.potential+d'.potential))≤_ at hsum
  have h₁ := d.integrated_outside_square hn w B T M κ hw hW hT hκ hB hk hdom
  have h₂ := d'.integrated_outside_square hn w B T M κ hw hW hT hκ hB hk hdom
  have hr : (∑ i, w i*(2*((∫ r, (d.outsideMass (prob (B i)) r)^2)+
      (∫ r, (d'.outsideMass (prob (B i)) r)^2))))=
      2*((∑ i, w i*(∫ r, (d.outsideMass (prob (B i)) r)^2))+
      (∑ i, w i*(∫ r, (d'.outsideMass (prob (B i)) r)^2))) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hr] at hsum
  simp only [mul_add,Finset.sum_add_distrib]
  linarith

lemma local_potential_fiber_bound (d d' : Depth P) (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (src : I → P) (t : I → ℝ) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hsrc : ∀ i, src i∉B i)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) :
    (∑ i, w i*∑ y, prob (B i) y*(d.potential y+d'.potential y)) ≤
      4*(weightedIntegral d.mass (varianceCell w B T)+weightedIntegral d'.mass (varianceCell w B T))+
      8*(weightedIntegral d.mass (pairCell Finset.univ)+weightedIntegral d'.mass (pairCell Finset.univ))+
      2*κ*M*(∑ x, prob Finset.univ x*(d.potential x+d'.potential x))+
      (∑ i, w i*∑ y, prob (B i) y*(weightedOverlap d.mass (src i) y+weightedOverlap d'.mass (src i) y))+
      (∑ i, w i*∑ y, prob (B i) y*|d.value (src i) y+d'.value (src i) y-t i|) := by
  have hp (i : I) (y : P) : 0≤prob (B i) y := by unfold prob; split_ifs <;> positivity
  have hL (dd : Depth P) (x y : P) : 0≤weightedOverlap dd.mass x y := by
    apply Finset.sum_nonneg; intro C _
    exact mul_nonneg (dd.mass_nonneg C) (by dsimp; split_ifs <;> norm_num)
  have hs (i : I) (y : P) (hy : prob (B i) y≠0) : y∈B i := by
    by_contra hh; exact hy (by simp [prob,hh])
  have hv (dd : Depth P) (i : I) (y : P) (hy : prob (B i) y≠0) :
      weightedOverlap dd.mass (src i) y=dd.overlapLength (src i) y (fun he => hsrc i (he ▸ hs i y hy)) :=
    dd.mass_overlap hn _ _ _
  have he (i : I) := MinKernel.energy_lower (prob (B i))
    (d.potential+d'.potential)
    (fun y => weightedOverlap d.mass (src i) y+weightedOverlap d'.mass (src i) y)
    (fun y => d.value (src i) y+d'.value (src i) y-t i)
    (d.M+d'.M-d.potential (src i)-d'.potential (src i)-t i)
    (hp i) (sum_prob (B i) (Finset.card_pos.mp (by have := hB i; omega)))
    (fun y => add_nonneg (hL d _ _) (hL d' _ _)) (by
      intro y hy
      have hxy : src i≠y := fun h => hsrc i (h ▸ hs i y hy)
      have hx := d.depth_identity hn (src i) y hxy
      have hx' := d'.depth_identity hn (src i) y hxy
      rw [hv d i y hy,hv d' i y hy]
      simp only [Pi.add_apply]
      linarith)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (he i) (hw i))
  have hu := min_upper_family d d' hn w B T M κ hw hW hT hκ hB hk hdom
  simp only [Pi.add_apply,mul_sub,Finset.sum_sub_distrib] at hh
  linarith

end WeakPinned.Hierarchy.Depth
noncomputable section

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
