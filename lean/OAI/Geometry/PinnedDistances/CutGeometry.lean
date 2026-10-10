import OAI.Geometry.PinnedDistances.TreeTransport

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

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

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def allCuts : Finset (Finset P) := by
  classical
  exact Finset.univ.filter (fun C => ∃ r : ℝ, C ∈ d.cells r)

lemma mem_allCuts (C : Finset P) : C ∈ d.allCuts ↔ ∃ r : ℝ, C ∈ d.cells r := by
  classical
  simp [allCuts]

lemma cells_subset_allCuts (r : ℝ) : d.cells r ⊆ d.allCuts :=
  fun C hC => (d.mem_allCuts C).mpr ⟨r,hC⟩

lemma allCuts_laminar : Cuts.Laminar d.allCuts := by
  intro C hC B hB
  obtain ⟨r,hr⟩ := (d.mem_allCuts C).mp hC
  obtain ⟨t,ht⟩ := (d.mem_allCuts B).mp hB
  by_cases hi : Disjoint C B
  · exact Or.inr (Or.inr hi)
  · obtain ⟨x,hxC,hxB⟩ := Finset.not_disjoint_iff.mp hi
    rw [d.cell_of_mem hr hxC,d.cell_of_mem ht hxB]
    rcases le_total t r with h | h
    · exact Or.inl (d.cell_mono h x)
    · exact Or.inr (Or.inl (d.cell_mono h x))

def cutAt (f : Finset P → ℝ) (C : Finset P) (r : ℝ) : ℝ :=
  if C ∈ d.cells r then f C else 0

def cutLength (f : Finset P → ℝ) (C : Finset P) : ℝ := ∫ r, d.cutAt f C r

lemma measurable_cutAt (f : Finset P → ℝ) (C : Finset P) : Measurable (d.cutAt f C) :=
  (measurable_of_finite (fun s : Finset (Finset P) => if C ∈ s then f C else 0)).comp d.measurable_cells

lemma cutAt_bound (f : Finset P → ℝ) (C : Finset P) (r : ℝ) : ‖d.cutAt f C r‖ ≤ |f C| := by
  unfold cutAt
  split_ifs <;> simp [Real.norm_eq_abs,abs_nonneg]

lemma cutAt_vanish (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (C : Finset P) (r : ℝ) (hr : r ∉ Set.Icc (-d.radius) d.radius) :
    d.cutAt f C r=0 := by
  unfold cutAt
  split_ifs with hc
  · obtain ⟨x,rfl⟩ := (d.mem_cells r C).mp hc
    rcases not_and_or.mp hr with hlo | hhi
    · rw [d.cell_of_low (le_of_lt (lt_of_not_ge hlo)),hfu]
    · rw [d.cell_of_high (lt_of_not_ge hhi),hfs]
  · rfl

lemma integrable_cutAt (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (C : Finset P) : Integrable (d.cutAt f C) := by
  exact integrable_supported_Icc (d.measurable_cutAt f C) (d.cutAt_bound f C)
    (d.cutAt_vanish f hfu hfs C)

lemma cutLength_nonneg (f : Finset P → ℝ) (hf : ∀ C, 0 ≤ f C) (C : Finset P) :
    0 ≤ d.cutLength f C := by
  apply integral_nonneg
  intro r
  unfold cutAt
  split_ifs
  · exact hf C
  · exact le_rfl

lemma cutLength_eq_zero (f : Finset P → ℝ) (C : Finset P) (hC : f C=0) :
    d.cutLength f C=0 := by simp [cutLength,cutAt,hC]

lemma cutLength_outside (f : Finset P → ℝ) (C : Finset P) (hC : C ∉ d.allCuts) :
    d.cutLength f C=0 := by
  have hh (r : ℝ) : C ∉ d.cells r := fun hc => hC ((d.mem_allCuts C).mpr ⟨r,hc⟩)
  simp [cutLength,cutAt,hh]

lemma integral_cut_sum (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (g : Finset P → ℝ) :
    (∫ r, ∑ C ∈ d.cells r, f C*g C) = ∑ C ∈ d.allCuts, d.cutLength f C*g C := by
  have he (r : ℝ) : (∑ C ∈ d.cells r, f C*g C) =
      ∑ C ∈ d.allCuts, d.cutAt f C r*g C := by
    simp only [cutAt,ite_mul,zero_mul,← Finset.sum_filter]
    congr 1
    ext C
    simp only [Finset.mem_filter]
    exact ⟨fun hc => ⟨d.cells_subset_allCuts r hc,hc⟩,fun hc => hc.2⟩
  simp only [he]
  rw [integral_finsetSum _ (fun C _ => (d.integrable_cutAt f hfu hfs C).mul_const (g C))]
  exact Finset.sum_congr rfl (fun C _ => by rw [integral_mul_const]; rfl)

lemma symmetric_integral_cut_sum (hn : 2 ≤ Fintype.card P) (f : Finset P → ℝ)
    (hfs : ∀ C, C.card ≤ 1 → f C=0) (hsym : ∀ C, f Cᶜ=f C) :
    (∑ C, d.mass C*f C) = ∑ C ∈ d.allCuts, d.cutLength f C := by
  have hu : f Finset.univ=0 := by simpa using (hsym ∅).trans (hfs ∅ (by simp))
  rw [← d.integral_sumCells hn f hfs]
  have he (r : ℝ) : d.sumCells f r=∑ C ∈ d.cells r, f C := by
    simp only [d.sumCells_formula,hsym,sub_self,Finset.sum_const_zero,add_zero]
  simp only [he]
  simpa using d.integral_cut_sum f hu (fun x => hfs {x} (by simp)) (fun _ => 1)

lemma cutLength_balanced (p : P → ℝ) (w : ℝ → ℝ) (η : ℝ)
    (hws : ∀ u, ¬(η ≤ u ∧ η ≤ 1-u) → w u=0) (C : Finset P)
    (hC : 0 < d.cutLength (fun B => w (Cuts.mass p B)) C) :
    η ≤ Cuts.mass p C ∧ η ≤ 1-Cuts.mass p C := by
  by_contra hn
  have hz := d.cutLength_eq_zero (fun B => w (Cuts.mass p B)) C (hws _ hn)
  linarith

lemma actual_cut_fluctuation (p : P → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x=1)
    (w : ℝ → ℝ) (hw : ∀ u, 0 ≤ w u) (η : ℝ) (hη : 0 ≤ η)
    (hws : ∀ u, ¬(η ≤ u ∧ η ≤ 1-u) → w u=0) :
    η^3*(∑ C ∈ d.allCuts, d.cutLength (fun B => w (Cuts.mass p B)) C) ≤
      ∑ y, p y*Cuts.doubleMean d.allCuts (d.cutLength (fun B => w (Cuts.mass p B))) p y := by
  exact Cuts.fluctuation_lower d.allCuts d.allCuts_laminar _
    (fun C _ => d.cutLength_nonneg _ (fun C => hw _) C) p hp0 hp η hη
    (fun C _ hC => d.cutLength_balanced p w η hws C hC)

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u2} [Fintype P] [DecidableEq P]
variable (d : Depth P)

omit [Fintype P] [DecidableEq P] in
lemma value_eq_of_lt (x y z : P) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hlt : d.value x y < d.value y z) : d.value x z=d.value x y := by
  have h1 := d.ultra x y z hxy hyz hxz
  rw [min_eq_left (le_of_lt hlt)] at h1
  apply le_antisymm _ h1
  by_contra! hn
  have h2 := d.ultra x z y hxz hyz.symm hxy
  rw [d.symm z y] at h2
  exact (lt_min hn hlt).not_ge h2

def differenceTail (x y : P) (u : ℝ) : Finset P :=
  Finset.univ.filter (fun z => z=y ∨ (z ≠ x ∧ u ≤ d.value y z-d.value x z))

lemma differenceTail_pos (x y : P) (hxy : x ≠ y) (u : ℝ) (hu : 0 < u) :
    d.differenceTail x y u=d.cell (d.value x y+u) y := by
  ext z
  simp only [differenceTail,Finset.mem_filter,Finset.mem_univ,true_and,mem_cell,share]
  by_cases hzy : z=y
  · simp [hzy]
  by_cases hzx : z=x
  · subst z
    have hlt : ¬d.value x y+u ≤ d.value y x := by rw [d.symm y x]; linarith
    simp [hxy,hxy.symm,hlt]
  · simp only [hzx,ne_eq,false_or,not_false_eq_true,true_and,eq_comm (a:=y) (b:=z),hzy]
    constructor
    · intro h
      have hlt : d.value x z < d.value z y := by rw [d.symm z y]; linarith
      have he := d.value_eq_of_lt x z y (Ne.symm hzx) hzy hxy hlt
      linarith
    · intro h
      have hlt : d.value x y < d.value y z := by linarith
      rw [d.value_eq_of_lt x y z hxy (Ne.symm hzy) (Ne.symm hzx) hlt]
      linarith

lemma differenceTail_neg_compl (x y : P) (hxy : x ≠ y) (u : ℝ) (hu : u < 0)
    (hne : ∀ z, u ≠ d.value x y-d.value x z) :
    (d.differenceTail x y u)ᶜ=d.cell (d.value x y-u) x := by
  ext z
  simp only [Finset.mem_compl,differenceTail,Finset.mem_filter,Finset.mem_univ,true_and,mem_cell,share]
  by_cases hzx : z=x
  · subst z
    simp [hxy]
  by_cases hzy : z=y
  · subst z
    have hlt : ¬d.value x y-u ≤ d.value x y := by linarith
    simp [hxy,hxy.symm,hlt]
  · simp only [hzy,false_or,ne_eq,not_false_eq_true,true_and,eq_comm (a:=x) (b:=z),hzx,not_le]
    constructor
    · intro h
      have hlt : d.value y z < d.value z x := by rw [d.symm z x]; linarith
      have he := d.value_eq_of_lt y z x (Ne.symm hzy) hzx hxy.symm hlt
      rw [d.symm y x] at he
      linarith
    · intro h
      have hlt : d.value y x < d.value x z := by rw [d.symm y x]; linarith
      have he := d.value_eq_of_lt y x z hxy.symm (Ne.symm hzx) (Ne.symm hzy) hlt
      rw [d.symm y x] at he
      have hn := hne z
      rw [he]
      rcases lt_or_eq_of_le h with h | h
      · linarith
      · exfalso
        apply hn
        linarith

lemma mass_compl (p : P → ℝ) (hp : ∑ x, p x=1) (C : Finset P) :
    Cuts.mass p Cᶜ=1-Cuts.mass p C := by
  have hh := Finset.sum_add_sum_compl C p
  simp only [Cuts.mass]
  rw [hp] at hh
  linarith

lemma ae_differenceTail_formula (p : P → ℝ) (hp : ∑ x, p x=1) (w : ℝ → ℝ)
    (hw : ∀ u, w (1-u)=w u) (x y : P) (hxy : x ≠ y) :
    ∀ᵐ u : ℝ, w (Cuts.mass p (d.differenceTail x y u)) =
      (if d.value x y < d.value x y+u then w (Cuts.mass p (d.cell (d.value x y+u) y)) else 0)+
      (if d.value x y < d.value x y-u then w (Cuts.mass p (d.cell (d.value x y-u) x)) else 0) := by
  have hn : ∀ᵐ u : ℝ, ∀ z : P, u ≠ d.value x y-d.value x z :=
    ae_all_iff.mpr (fun z => volume.ae_ne _)
  filter_upwards [hn,volume.ae_ne (0 : ℝ)] with u hne hu
  rcases lt_or_gt_of_ne hu with hu | hu
  · have he := d.differenceTail_neg_compl x y hxy u hu hne
    have hm := mass_compl p hp (d.differenceTail x y u)
    rw [he] at hm
    rw [ite_eq_right (by linarith),ite_eq_left (by linarith),zero_add,hm,hw]
  · rw [d.differenceTail_pos x y hxy u hu,ite_eq_left (by linarith),ite_eq_right (by linarith),add_zero]

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def aboveCell (f : Finset P → ℝ) (a : ℝ) (x : P) (r : ℝ) : ℝ :=
  if a < r then f (d.cell r x) else 0

omit [DecidableEq P] in
lemma measurable_aboveCell (f : Finset P → ℝ) (a : ℝ) (x : P) :
    Measurable (d.aboveCell f a x) := by
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · exact (measurable_of_finite f).comp (d.measurable_cell x)
  · exact measurable_const

omit [DecidableEq P] in
lemma integrable_aboveCell (f : Finset P → ℝ) (hfs : ∀ x, f {x}=0)
    (a : ℝ) (ha : -d.radius ≤ a) (x : P) : Integrable (d.aboveCell f a x) := by
  apply integrable_supported_Icc (d.measurable_aboveCell f a x)
      (C:=∑ C : Finset P, |f C|) (a:= -d.radius) (b:=d.radius)
  · intro r
    unfold aboveCell
    split_ifs
    · simpa only [Real.norm_eq_abs] using (Finset.single_le_sum (s:=Finset.univ) (f:=fun C : Finset P => |f C|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ (d.cell r x)))
    · simpa using Finset.sum_nonneg (fun C (_ : C ∈ (Finset.univ : Finset (Finset P))) => abs_nonneg (f C))
  · intro r hr
    rcases not_and_or.mp hr with hlo | hhi
    · have hh : ¬a < r := by have := lt_of_not_ge hlo; linarith
      simp [aboveCell,hh]
    · simp [aboveCell,d.cell_of_high (lt_of_not_ge hhi) x,hfs]

lemma sum_cut_separation (f : Finset P → ℝ) (r : ℝ) (x y : P) (hxy : x ≠ y) :
    (∑ C ∈ d.cells r, f C*|Cuts.ind C x-Cuts.ind C y|) =
      d.aboveCell f (d.value x y) x r+d.aboveCell f (d.value x y) y r := by
  have hmem (z : P) (C : Finset P) (hC : C ∈ d.cells r) : z ∈ C ↔ C=d.cell r z :=
    ⟨fun hz => d.cell_of_mem hC hz,fun he => by rw [he]; exact d.self_mem_cell r z⟩
  by_cases hr : r ≤ d.value x y
  · have hce : d.cell r x=d.cell r y := d.cell_eq_of_share (Or.inr hr)
    have hz : ∑ C ∈ d.cells r, f C*|Cuts.ind C x-Cuts.ind C y|=0 := by
      apply Finset.sum_eq_zero
      intro C hC
      have hm : x ∈ C ↔ y ∈ C := by rw [hmem x C hC,hmem y C hC,hce]
      simp only [Cuts.ind,hm,sub_self,abs_zero,mul_zero]
    simp [hz,aboveCell,not_lt.mpr hr]
  · have hlt : d.value x y < r := lt_of_not_ge hr
    have hns : ¬d.share r x y := by simpa [share,hxy] using hr
    have he (C : Finset P) (hC : C ∈ d.cells r) :
        f C*|Cuts.ind C x-Cuts.ind C y| =
          (if C=d.cell r x then f (d.cell r x) else 0)+
          (if C=d.cell r y then f (d.cell r y) else 0) := by
      by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
      · have hc := d.cell_of_mem hC hx
        have hh : d.share r x y := by rwa [hc,d.mem_cell] at hy
        exact (hns hh).elim
      · have hc := (hmem x C hC).mp hx
        have hn : C ≠ d.cell r y := fun h => hy ((hmem y C hC).mpr h)
        simp only [Cuts.ind,ite_eq_left hx,ite_eq_right hy,sub_zero,abs_one,mul_one,ite_eq_left hc,ite_eq_right hn,add_zero]
        rw [hc]
      · have hc := (hmem y C hC).mp hy
        have hn : C ≠ d.cell r x := fun h => hx ((hmem x C hC).mpr h)
        simp only [Cuts.ind,ite_eq_right hx,ite_eq_left hy,zero_sub,abs_neg,abs_one,mul_one,ite_eq_left hc,ite_eq_right hn,zero_add]
        rw [hc]
      · have hn1 : C ≠ d.cell r x := fun h => hx ((hmem x C hC).mpr h)
        have hn2 : C ≠ d.cell r y := fun h => hy ((hmem y C hC).mpr h)
        simp [Cuts.ind,hx,hy,hn1,hn2]
    rw [Finset.sum_congr rfl he,Finset.sum_add_distrib]
    simp [d.cell_mem_cells,aboveCell,hlt]

lemma cut_distance_two_integrals (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (x y : P) (hxy : x ≠ y) :
    Cuts.distance d.allCuts (d.cutLength f) x y =
      (∫ r, d.aboveCell f (d.value x y) x r)+(∫ r, d.aboveCell f (d.value x y) y r) := by
  rw [Cuts.distance,← d.integral_cut_sum f hfu hfs (fun C => |Cuts.ind C x-Cuts.ind C y|)]
  simp only [d.sum_cut_separation f _ x y hxy]
  exact integral_add (d.integrable_aboveCell f hfs _ (abs_le.mp (d.abs_value_le_radius x y)).1 x)
    (d.integrable_aboveCell f hfs _ (abs_le.mp (d.abs_value_le_radius x y)).1 y)

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable (d : Depth P)

/-- Exact projection identity, including the formal infinite values at the
    two endpoints, represented by their tail-set membership. -/
lemma cut_projection (p : P → ℝ) (hp : ∑ x, p x=1) (w : ℝ → ℝ)
    (hwu : w 1=0) (hws : ∀ x, w (p x)=0) (hwsym : ∀ u, w (1-u)=w u)
    (x y : P) (hxy : x ≠ y) :
    Cuts.distance d.allCuts (d.cutLength (fun C => w (Cuts.mass p C))) x y =
      ∫ u, w (Cuts.mass p (d.differenceTail x y u)) := by
  let f : Finset P → ℝ := fun C => w (Cuts.mass p C)
  have hfu : f Finset.univ=0 := by simpa [f,Cuts.mass,hp] using hwu
  have hfs : ∀ z, f {z}=0 := by intro z; simpa [f,Cuts.mass] using hws z
  have hi (z : P) := d.integrable_aboveCell f hfs (d.value x y)
    (abs_le.mp (d.abs_value_le_radius x y)).1 z
  have hiY : Integrable (fun u => d.aboveCell f (d.value x y) y (d.value x y+u)) := by
    exact ((measurePreserving_add_left volume (d.value x y)).integrable_comp (hi y).aestronglyMeasurable).mpr (hi y)
  have hiX : Integrable (fun u => d.aboveCell f (d.value x y) x (d.value x y-u)) :=
    (integrable_comp_sub_left _ _).mpr (hi x)
  rw [d.cut_distance_two_integrals f hfu hfs x y hxy]
  have he := integral_congr_ae (d.ae_differenceTail_formula p hp w hwsym x y hxy)
  change (∫ u, w (Cuts.mass p (d.differenceTail x y u))) =
    ∫ u, d.aboveCell f (d.value x y) y (d.value x y+u)+d.aboveCell f (d.value x y) x (d.value x y-u) at he
  rw [he,integral_add hiY hiX,integral_add_left_eq_self,integral_sub_left_eq_self]
  exact add_comm _ _

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Tail
open MeasureTheory
open scoped NNReal
variable {P : Type u5} [Fintype P]

def step (a u : ℝ) : ℝ := if u ≤ a then 1 else 0

def law (b : ℝ) (p : P → ℝ) (f : P → ℝ) (u : ℝ) : ℝ := b+∑ z, p z*step (f z) u

lemma measurable_step (a : ℝ) : Measurable (step a) := by
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const

lemma measurable_law (b : ℝ) (p f : P → ℝ) : Measurable (law b p f) :=
  measurable_const.add (Finset.measurable_sum _ (fun _z _ => measurable_const.mul (measurable_step _)))

lemma step_difference (a b u : ℝ) : |step a u-step b u| =
    if min a b < u ∧ u ≤ max a b then 1 else 0 := by
  unfold step
  rcases le_total a b with h | h
  · rw [min_eq_left h,max_eq_right h]
    by_cases hua : u ≤ a
    · have hub : u ≤ b := hua.trans h
      simp [hua,hub,not_lt.mpr hua]
    · have hau : a < u := lt_of_not_ge hua
      by_cases hub : u ≤ b <;> simp [hua,hub,hau]
  · rw [min_eq_right h,max_eq_left h]
    by_cases hub : u ≤ b
    · have hua : u ≤ a := hub.trans h
      simp [hua,hub,not_lt.mpr hub]
    · have hbu : b < u := lt_of_not_ge hub
      by_cases hua : u ≤ a <;> simp [hua,hub,hbu]

lemma step_difference_indicator (a b : ℝ) : (fun u => |step a u-step b u|) =
    (Set.Ioc (min a b) (max a b)).indicator (fun _ : ℝ => 1) := by
  funext u
  simp [step_difference,Set.indicator_apply]

lemma integrable_step_difference (a b : ℝ) : Integrable (fun u => |step a u-step b u|) := by
  rw [step_difference_indicator,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma integral_step_difference (a b : ℝ) : (∫ u, |step a u-step b u|) = |a-b| := by
  rw [step_difference_indicator,integral_indicator measurableSet_Ioc]
  simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,measureReal_def,Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max (a:=a) (b:=b)))]
  rcases le_total a b with hh | hh
  · simp [max_eq_right hh,min_eq_left hh,abs_of_nonpos (sub_nonpos.mpr hh)]
  · simp [max_eq_left hh,min_eq_right hh,abs_of_nonneg (sub_nonneg.mpr hh)]

lemma law_difference_bound (b : ℝ) (p f g : P → ℝ) (hp : ∀ z, 0 ≤ p z) (u : ℝ) :
    |law b p f u-law b p g u| ≤ ∑ z, p z*|step (f z) u-step (g z) u| := by
  have he : law b p f u-law b p g u=∑ z, p z*(step (f z) u-step (g z) u) := by
    simp only [law,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ∑ z, |p z*(step (f z) u-step (g z) u)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul,abs_of_nonneg (hp _)]

lemma lipschitz_tail_bound (b : ℝ) (p f g : P → ℝ) (hp : ∀ z, 0 ≤ p z)
    (w : ℝ → ℝ) (Λ : ℝ≥0) (hw : LipschitzWith Λ w) :
    (∫ u, |w (law b p f u)-w (law b p g u)|) ≤ (Λ:ℝ)*∑ z, p z*|f z-g z| := by
  let h : ℝ → ℝ := fun u => (Λ:ℝ)*∑ z, p z*|step (f z) u-step (g z) u|
  have hi : Integrable h := (integrable_finsetSum (s:=Finset.univ)
    (fun z _ => (integrable_step_difference (f z) (g z)).const_mul (p z))).const_mul _
  have hb (u : ℝ) : |w (law b p f u)-w (law b p g u)| ≤ h u := by
    have hh := hw.norm_sub_le (law b p f u) (law b p g u)
    simp only [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (law_difference_bound b p f g hp u) Λ.coe_nonneg)
  have hm : Measurable (fun u => |w (law b p f u)-w (law b p g u)|) :=
    ((hw.continuous.measurable.comp (measurable_law b p f)).sub
      (hw.continuous.measurable.comp (measurable_law b p g))).abs
  have hi' := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun u => by
    simpa only [Real.norm_eq_abs,abs_abs] using hb u))
  calc
    _ ≤ ∫ u, h u := integral_mono hi' hi hb
    _ = _ := by
      simp only [h,integral_const_mul]
      rw [integral_finsetSum _ (fun z _ => (integrable_step_difference (f z) (g z)).const_mul (p z))]
      simp only [integral_const_mul,integral_step_difference]

end WeakPinned.Tail

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u6} [Fintype P] [DecidableEq P]
variable (d : Depth P)

omit [DecidableEq P] in
lemma integrable_cellWeight (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (x : P) : Integrable (fun r => f (d.cell r x)) := by
  apply integrable_supported_Icc ((measurable_of_finite f).comp (d.measurable_cell x))
    (C:=∑ C : Finset P, |f C|) (a:= -d.radius) (b:=d.radius)
  · intro r
    simpa only [Function.comp_def,Real.norm_eq_abs] using (Finset.single_le_sum (s:=Finset.univ) (f:=fun C : Finset P => |f C|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (d.cell r x)))
  · intro r hr
    change f (d.cell r x)=0
    rcases not_and_or.mp hr with hlo | hhi
    · rw [d.cell_of_low (le_of_lt (lt_of_not_ge hlo)),hfu]
    · rw [d.cell_of_high (lt_of_not_ge hhi),hfs]

lemma cut_root_projection (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (y : P) :
    Cuts.rootDistance d.allCuts (d.cutLength f) y = ∫ r, f (d.cell r y) := by
  rw [Cuts.rootDistance,← d.integral_cut_sum f hfu hfs (fun C => Cuts.ind C y)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  have he (C : Finset P) (hC : C ∈ d.cells r) : f C*Cuts.ind C y =
      if C=d.cell r y then f (d.cell r y) else 0 := by
    by_cases hy : y ∈ C
    · have hc := d.cell_of_mem hC hy
      subst C
      simp [Cuts.ind,d.self_mem_cell]
    · have hn : C ≠ d.cell r y := fun h => hy (h ▸ d.self_mem_cell r y)
      simp [Cuts.ind,hy,hn]
  change (∑ C ∈ d.cells r, f C*Cuts.ind C y)=f (d.cell r y)
  rw [Finset.sum_congr rfl he]
  simp [d.cell_mem_cells]

lemma integrable_differenceTail (p : P → ℝ) (hp : ∑ x, p x=1) (w : ℝ → ℝ)
    (hws : ∀ x, w (p x)=0) (hwsym : ∀ u, w (1-u)=w u)
    (x y : P) (hxy : x ≠ y) : Integrable (fun u => w (Cuts.mass p (d.differenceTail x y u))) := by
  let f : Finset P → ℝ := fun C => w (Cuts.mass p C)
  have hfs : ∀ z, f {z}=0 := by intro z; simpa [f,Cuts.mass] using hws z
  have hi (z : P) := d.integrable_aboveCell f hfs (d.value x y)
    (abs_le.mp (d.abs_value_le_radius x y)).1 z
  have hiY : Integrable (fun u => d.aboveCell f (d.value x y) y (d.value x y+u)) :=
    ((measurePreserving_add_left volume (d.value x y)).integrable_comp (hi y).aestronglyMeasurable).mpr (hi y)
  have hiX : Integrable (fun u => d.aboveCell f (d.value x y) x (d.value x y-u)) :=
    (integrable_comp_sub_left _ _).mpr (hi x)
  apply (hiY.add hiX).congr
  filter_upwards [d.ae_differenceTail_formula p hp w hwsym x y hxy] with u hu
  exact hu.symm

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Tail
open MeasureTheory Hierarchy
open scoped NNReal
variable {P : Type u7} [Fintype P] [DecidableEq P]

def offTwo (p : P → ℝ) (x y z : P) : ℝ := if z=x ∨ z=y then 0 else p z

omit [Fintype P] in
lemma offTwo_nonneg (p : P → ℝ) (hp : ∀ z, 0 ≤ p z) (x y z : P) : 0 ≤ offTwo p x y z := by
  unfold offTwo
  split_ifs <;> simp [hp]

lemma mass_as_sum (p : P → ℝ) (C : Finset P) : Cuts.mass p C=∑ z, if z ∈ C then p z else 0 := by
  simp [Cuts.mass]

lemma differenceTail_law (d : Depth P) (p : P → ℝ) (x y : P) (hxy : x ≠ y) (u : ℝ) :
    Cuts.mass p (d.differenceTail x y u)=
      law (p y) (offTwo p x y) (fun z => d.value y z-d.value x z) u := by
  rw [mass_as_sum]
  have he (z : P) : (if z ∈ d.differenceTail x y u then p z else 0)=
      (if z=y then p y else 0)+offTwo p x y z*step (d.value y z-d.value x z) u := by
    by_cases hy : z=y
    · subst z; simp [Depth.differenceTail,offTwo]
    by_cases hx : z=x
    · subst z; simp [Depth.differenceTail,offTwo,hxy]
    · simp [Depth.differenceTail,offTwo,step,hx,hy,mul_ite]
  simp only [he,Finset.sum_add_distrib]
  simp [law]

lemma rootTail_law (d : Depth P) (p : P → ℝ) (x y : P) (hx : p x=0) (hxy : x ≠ y) (c u : ℝ) :
    Cuts.mass p (d.cell (u-c) y)=law (p y) (offTwo p x y) (fun z => d.value y z+c) u := by
  rw [mass_as_sum]
  have he (z : P) : (if z ∈ d.cell (u-c) y then p z else 0)=
      (if z=y then p y else 0)+offTwo p x y z*step (d.value y z+c) u := by
    by_cases hy : z=y
    · subst z; simp [offTwo,d.self_mem_cell]
    by_cases hz : z=x
    · subst z; simp [offTwo,hx,hxy]
    · have hh : u-c ≤ d.value y z ↔ u ≤ d.value y z+c := by constructor <;> intro hh <;> linarith
      simp [Depth.mem_cell,Depth.share,offTwo,step,hz,hy,Ne.symm hy,hh,mul_ite]
  simp only [he,Finset.sum_add_distrib]
  simp [law]

/-- Quantitative fiber-tree comparison, before inserting the arithmetic
    raw-depth equation. The y endpoint is included; x has zero fiber mass. -/
lemma fiber_cut_error (d d' : Depth P) (p : P → ℝ) (hp0 : ∀ z, 0 ≤ p z) (hp : ∑ z, p z=1)
    (w : ℝ → ℝ) (Λ : ℝ≥0) (hw : LipschitzWith Λ w)
    (hwu : w 1=0) (hws : ∀ z, w (p z)=0) (hwsym : ∀ u, w (1-u)=w u)
    (x y : P) (hpx : p x=0) (hxy : x ≠ y) (c : ℝ) :
    |Cuts.distance d.allCuts (d.cutLength (fun C => w (Cuts.mass p C))) x y-
      Cuts.rootDistance d'.allCuts (d'.cutLength (fun C => w (Cuts.mass p C))) y| ≤
      (Λ:ℝ)*∑ z, offTwo p x y z*|d.value y z-d.value x z-(d'.value y z+c)| := by
  let f : Finset P → ℝ := fun C => w (Cuts.mass p C)
  have hfu : f Finset.univ=0 := by simpa [f,Cuts.mass,hp] using hwu
  have hfs : ∀ z, f {z}=0 := by intro z; simpa [f,Cuts.mass] using hws z
  let a := law (p y) (offTwo p x y) (fun z => d.value y z-d.value x z)
  let b := law (p y) (offTwo p x y) (fun z => d'.value y z+c)
  have hia : Integrable (fun u => w (a u)) := by
    simpa only [differenceTail_law d p x y hxy] using
      d.integrable_differenceTail p hp w hws hwsym x y hxy
  have hib0 := d'.integrable_cellWeight f hfu hfs y
  have hib : Integrable (fun u => w (b u)) := by
    have hh := ((measurePreserving_add_right volume (-c)).integrable_comp hib0.aestronglyMeasurable).mpr hib0
    simpa only [Function.comp_def,f,← sub_eq_add_neg,rootTail_law d' p x y hpx hxy c] using hh
  have he : (∫ u, w (b u))=Cuts.rootDistance d'.allCuts (d'.cutLength f) y := by
    rw [d'.cut_root_projection f hfu hfs y]
    have hh := integral_add_right_eq_self (μ:=volume) (fun r => f (d'.cell r y)) (-c)
    simpa only [f,← sub_eq_add_neg,rootTail_law d' p x y hpx hxy c] using hh
  rw [d.cut_projection p hp w hwu hws hwsym x y hxy,← he]
  simp only [differenceTail_law d p x y hxy]
  change |(∫ u, w (a u))-(∫ u, w (b u))| ≤ _
  rw [← integral_sub hia hib]
  calc
    _ ≤ ∫ u, |w (a u)-w (b u)| := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun u => w (a u)-w (b u))
    _ ≤ _ := lipschitz_tail_bound (p y) (offTwo p x y) _ _ (offTwo_nonneg p hp0 x y) w Λ hw

end WeakPinned.Tail

namespace WeakPinned.Arithmetic
variable {K : Type u8} [Field K]

lemma paired_log (v : AbsoluteValue K ℝ) (a b c d z w t : K)
    (hc : c ≠ a) (hz : z ≠ a) (hcz : c ≠ z) (ht : t ≠ 0)
    (hcd : (c-a)*(d-b)=t) (hzw : (z-a)*(w-b)=t) :
    -Real.log (v (w-d)) = -Real.log (v (c-z))+Real.log (v (z-a))-
      Real.log (v t)+Real.log (v (c-a)) := by
  rw [paired_difference a b c d z w t hc hz hcd hzw,
    map_div₀,map_mul,map_mul,
    Real.log_div (mul_ne_zero (v.pos ht).ne' (v.pos (sub_ne_zero.mpr hcz)).ne')
      (mul_ne_zero (v.pos (sub_ne_zero.mpr hz)).ne' (v.pos (sub_ne_zero.mpr hc)).ne'),
    Real.log_mul (v.pos ht).ne' (v.pos (sub_ne_zero.mpr hcz)).ne',
    Real.log_mul (v.pos (sub_ne_zero.mpr hz)).ne' (v.pos (sub_ne_zero.mpr hc)).ne']
  ring

lemma absval_sub_symm (v : AbsoluteValue K ℝ) (a b : K) : v (a-b)=v (b-a) := by
  rw [← neg_sub b a,map_neg_eq_map]

/-- The raw cross-fiber identity at every place. The three points are distinct
    and the source is outside its fiber. -/
lemma raw_cross_fiber {P : Type u9} (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁)
    (h₂ : Function.Injective Z₂) (v : AbsoluteValue K ℝ) (x y z : P)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (t : K)
    (hy : (Z₁ x-Z₁ y)*(Z₂ x-Z₂ y)=t)
    (hz : (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t) :
    -Real.log (v (Z₂ y-Z₂ z)) = -Real.log (v (Z₁ y-Z₁ z))-
      (-Real.log (v (Z₁ x-Z₁ z)))-Real.log (v t)-(-Real.log (v (Z₁ x-Z₁ y))) := by
  have ht : t ≠ 0 := by rw [← hy]; exact mul_ne_zero (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
  have hh := paired_log v (Z₁ x) (Z₂ x) (Z₁ y) (Z₂ y) (Z₁ z) (Z₂ z) t
    (h₁.ne hxy.symm) (h₁.ne hxz.symm) (h₁.ne hyz) ht
    (by convert hy using 1; ring) (by convert hz using 1; ring)
  rw [absval_sub_symm v (Z₂ z) (Z₂ y),absval_sub_symm v (Z₁ z) (Z₁ x),
    absval_sub_symm v (Z₁ y) (Z₁ x)] at hh
  linarith
end WeakPinned.Arithmetic

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
