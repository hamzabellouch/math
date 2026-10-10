import OAI.Geometry.PinnedDistances.CutApproximation

namespace OAI

universe u1

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

/- Finite tree transport by laminar-cut telescoping, without optimal-coupling selection. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Cuts
variable {P : Type u1} [Fintype P] [DecidableEq P]

def Laminar (s : Finset (Finset P)) : Prop :=
  ∀ A ∈ s, ∀ B ∈ s, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

def value (s : Finset (Finset P)) (d : Finset P → ℝ) (a : ℝ) (x : P) : ℝ :=
  a + ∑ C ∈ s, if x ∈ C then d C else 0

def mass (b : P → ℝ) (C : Finset P) : ℝ := ∑ x ∈ C, b x

omit [Fintype P] in
lemma laminar_erase {s : Finset (Finset P)} (hs : Laminar s) (C : Finset P) : Laminar (s.erase C) :=
  fun _ hA _ hB => hs _ (Finset.mem_of_mem_erase hA) _ (Finset.mem_of_mem_erase hB)

omit [Fintype P] in
lemma minimal_constant {s : Finset (Finset P)} (hs : Laminar s)
    (C : Finset P) (hC : C ∈ s) (hmin : ∀ D ∈ s, C.card ≤ D.card)
    (d : Finset P → ℝ) (a : ℝ) :
    ∀ x ∈ C, value (s.erase C) d a x = a+∑ D ∈ s.erase C, if C ⊆ D then d D else 0 := by
  intro x hx
  unfold value
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  have hDs := Finset.mem_of_mem_erase hD
  have hDC : D ≠ C := (Finset.mem_erase.mp hD).1
  have hnot : ¬D ⊆ C := by
    intro hh
    exact hDC (Finset.eq_of_subset_of_card_le hh (hmin D hDs))
  by_cases hCD : C ⊆ D
  · simp [hCD,hCD hx]
  · have hd : Disjoint C D := (hs C hC D hDs).resolve_left hCD |>.resolve_left hnot
    have hxD : x ∉ D := fun hxD => Finset.disjoint_left.mp hd hx hxD
    simp [hCD,hxD]

omit [Fintype P] in
lemma value_erase {s : Finset (Finset P)} (C : Finset P) (hC : C ∈ s)
    (d : Finset P → ℝ) (a : ℝ) (x : P) :
    value s d a x = value (s.erase C) d a x + (if x ∈ C then d C else 0) := by
  unfold value
  rw [← Finset.add_sum_erase _ _ hC]
  ring

/-- Dual tree transport with completely explicit cut cost. The signed measure
    b has total mass zero. Neither nonnegativity nor coupling existence is needed. -/
lemma signed_lipschitz_bound (s : Finset (Finset P)) (hs : Laminar s)
    (b : P → ℝ) (hb : ∑ x, b x=0) (d : Finset P → ℝ) (a : ℝ)
    (g : ℝ → ℝ) (hg : ∀ u v, |g u-g v| ≤ |u-v|) :
    |∑ x, b x*g (value s d a x)| ≤ ∑ C ∈ s, |d C| * |mass b C| := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hsn : s.Nonempty
    · obtain ⟨C,hC,hmin⟩ := Finset.exists_min_image s Finset.card hsn
      let q := a+∑ D ∈ s.erase C, if C ⊆ D then d D else 0
      let Δ := g (q+d C)-g q
      have hΔ : |Δ| ≤ |d C| := by
        simpa only [Δ,add_sub_cancel_left] using hg (q+d C) q
      have he (x : P) : g (value s d a x) =
          g (value (s.erase C) d a x)+(if x ∈ C then Δ else 0) := by
        rw [value_erase C hC]
        by_cases hx : x ∈ C
        · rw [ite_eq_left hx,ite_eq_left hx,minimal_constant hs C hC hmin d a x hx]
          dsimp only [Δ,q]
          ring
        · simp [hx]
      have hi := ih (s.erase C) (Finset.erase_ssubset hC) (laminar_erase hs C)
      have he' : (∑ x, b x*g (value s d a x)) =
          (∑ x, b x*g (value (s.erase C) d a x))+Δ*mass b C := by
        simp_rw [he,mul_add,Finset.sum_add_distrib]
        congr 1
        simp only [mul_ite,mul_zero,mass,Finset.mul_sum]
        simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      rw [he',← Finset.add_sum_erase _ _ hC]
      calc
        _ ≤ |∑ x, b x*g (value (s.erase C) d a x)|+|Δ*mass b C| := abs_add_le _ _
        _ ≤ (∑ D ∈ s.erase C, |d D| * |mass b D|)+|d C| * |mass b C| := by
          apply add_le_add hi
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)
        _ = _ := by ring
    · have hs0 := Finset.not_nonempty_iff_eq_empty.mp hsn
      simp only [hs0,value,Finset.sum_empty,add_zero,← Finset.sum_mul,hb,zero_mul,abs_zero,le_refl]

def ind (C : Finset P) (x : P) : ℝ := if x ∈ C then 1 else 0

def distance (s : Finset (Finset P)) (l : Finset P → ℝ) (x y : P) : ℝ :=
  ∑ C ∈ s, l C*|ind C x-ind C y|

def rootDistance (s : Finset (Finset P)) (l : Finset P → ℝ) (y : P) : ℝ :=
  ∑ C ∈ s, l C*ind C y

def coeff (l : Finset P → ℝ) (y : P) (C : Finset P) : ℝ :=
  if y ∈ C then -l C else l C

def cost (s : Finset (Finset P)) (l : Finset P → ℝ) (p q : P → ℝ) : ℝ :=
  ∑ C ∈ s, l C*|mass p C-mass q C|

omit [Fintype P] in
lemma distance_symm (s : Finset (Finset P)) (l : Finset P → ℝ) (x y : P) :
    distance s l x y=distance s l y x := by
  simp only [distance,abs_sub_comm]

omit [Fintype P] in
lemma distance_nonneg (s : Finset (Finset P)) (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C)
    (x y : P) : 0 ≤ distance s l x y :=
  Finset.sum_nonneg (fun C hC => mul_nonneg (hl C hC) (abs_nonneg _))

omit [Fintype P] in
lemma distance_as_value (s : Finset (Finset P)) (l : Finset P → ℝ) (x y : P) :
    distance s l x y=value s (coeff l y) (rootDistance s l y) x := by
  simp only [distance,value,rootDistance,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> simp [ind,coeff,hx,hy]

omit [Fintype P] in
lemma abs_coeff (l : Finset P → ℝ) (y : P) (C : Finset P) (hC : 0 ≤ l C) :
    |coeff l y C|=l C := by
  unfold coeff
  split_ifs <;> simp [abs_of_nonneg hC]

lemma function_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p q : P → ℝ)
    (hpq : ∑ x, p x=∑ x, q x) (y : P) (g : ℝ → ℝ)
    (hg : ∀ u v, |g u-g v| ≤ |u-v|) :
    |(∑ x, p x*g (distance s l x y))-(∑ x, q x*g (distance s l x y))| ≤ cost s l p q := by
  have hb : (∑ x, (p x-q x))=0 := by rw [Finset.sum_sub_distrib,hpq,sub_self]
  have hh := signed_lipschitz_bound s hs (fun x => p x-q x) hb (coeff l y) (rootDistance s l y) g hg
  simp only [← distance_as_value,sub_mul,Finset.sum_sub_distrib,mass] at hh
  simp only [cost,mass]
  convert hh using 1
  exact Finset.sum_congr rfl (fun C hC => by rw [abs_coeff l y C (hl C hC)])

lemma first_fluctuation_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p q : P → ℝ)
    (hpq : ∑ x, p x=∑ x, q x) (x' y : P) :
    |(∑ x, p x*|distance s l x y-distance s l x' y|)-
      (∑ x, q x*|distance s l x y-distance s l x' y|)| ≤ cost s l p q := by
  apply function_transfer s hs l hl p q hpq y (fun u => |u-distance s l x' y|)
  intro u v
  simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le_abs_sub (u-distance s l x' y) (v-distance s l x' y)

omit [Fintype P] in
lemma value_sub (s : Finset (Finset P)) (d e : Finset P → ℝ) (a b : ℝ) (x : P) :
    value s d a x-value s e b x=value s (fun C => d C-e C) (a-b) x := by
  simp only [value]
  have he : (∑ C ∈ s, if x ∈ C then d C-e C else 0) =
      (∑ C ∈ s, if x ∈ C then d C else 0)-(∑ C ∈ s, if x ∈ C then e C else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun C _ => by split_ifs <;> ring)
  rw [he]
  ring

lemma last_fluctuation_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p q : P → ℝ)
    (hpq : ∑ x, p x=∑ x, q x) (x x' : P) :
    |(∑ y, p y*|distance s l x y-distance s l x' y|)-
      (∑ y, q y*|distance s l x y-distance s l x' y|)| ≤ 2*cost s l p q := by
  have hb : (∑ y, (p y-q y))=0 := by rw [Finset.sum_sub_distrib,hpq,sub_self]
  have hh := signed_lipschitz_bound s hs (fun y => p y-q y) hb
    (fun C => coeff l x C-coeff l x' C) (rootDistance s l x-rootDistance s l x') abs abs_abs_sub_abs_le_abs_sub
  have he (y : P) : value s (fun C => coeff l x C-coeff l x' C) (rootDistance s l x-rootDistance s l x') y =
      distance s l x y-distance s l x' y := by
    rw [← value_sub,← distance_as_value,← distance_as_value,distance_symm s l y x,distance_symm s l y x']
  simp only [he,sub_mul,Finset.sum_sub_distrib,mass] at hh
  refine hh.trans ?_
  simp only [cost,mass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C hC
  have hc : |coeff l x C-coeff l x' C| ≤ 2*l C := by
    calc
      _ ≤ |coeff l x C|+|coeff l x' C| := abs_sub _ _
      _ = _ := by rw [abs_coeff l x C (hl C hC),abs_coeff l x' C (hl C hC)]; ring
  calc
    _ ≤ (2*l C)*|∑ y ∈ C, p y-∑ y ∈ C, q y| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ = _ := by ring

omit [Fintype P] [DecidableEq P] in
lemma mass_nonneg (p : P → ℝ) (hp : ∀ x, 0 ≤ p x) (C : Finset P) : 0 ≤ mass p C :=
  Finset.sum_nonneg (fun x _ => hp x)

lemma expected_cut (p : P → ℝ) (hp : ∑ x, p x=1) (C : Finset P) (y : P) :
    (∑ x, p x*|ind C x-ind C y|) = if y ∈ C then 1-mass p C else mass p C := by
  by_cases hy : y ∈ C
  · have he (x : P) : p x*|ind C x-ind C y|=p x-(if x ∈ C then p x else 0) := by
      by_cases hx : x ∈ C <;> simp [ind,hx,hy]
    simp_rw [he]
    simp only [Finset.sum_sub_distrib,hp,← Finset.sum_filter,
      Finset.filter_mem_eq_inter,Finset.univ_inter,ite_eq_left hy,mass]
  · have he (x : P) : p x*|ind C x-ind C y|=if x ∈ C then p x else 0 := by
      by_cases hx : x ∈ C <;> simp [ind,hx,hy]
    simp_rw [he]
    simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,ite_eq_right hy,mass]

lemma expected_distance_ge (s : Finset (Finset P)) (l : Finset P → ℝ)
    (hl : ∀ C ∈ s, 0 ≤ l C) (p : P → ℝ) (hp : ∑ x, p x=1) (η : ℝ)
    (hbal : ∀ C ∈ s, 0 < l C → η ≤ mass p C ∧ η ≤ 1-mass p C) (y : P) :
    η*(∑ C ∈ s, l C) ≤ ∑ x, p x*distance s l x y := by
  simp only [distance,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro C hC
  have he : (∑ x, p x*(l C*|ind C x-ind C y|)) =
      l C*(∑ x, p x*|ind C x-ind C y|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [he,expected_cut p hp]
  by_cases hpos : 0 < l C
  · rcases hbal C hC hpos with ⟨h1,h2⟩
    have hh : η ≤ if y ∈ C then 1-mass p C else mass p C := by split_ifs <;> assumption
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh (hl C hC)
  · have hz : l C=0 := le_antisymm (le_of_not_gt hpos) (hl C hC)
    simp [hz]

omit [Fintype P] in
lemma exists_zero_cell (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C)
    (hn : (s.filter (fun C => 0 < l C)).Nonempty) :
    ∃ C ∈ s, 0 < l C ∧ ∀ x ∈ C, ∀ y ∈ C, distance s l x y=0 := by
  obtain ⟨C,hC,hmin⟩ := Finset.exists_min_image (s.filter (fun C => 0 < l C)) Finset.card hn
  rcases Finset.mem_filter.mp hC with ⟨hCs,hCl⟩
  refine ⟨C,hCs,hCl,?_⟩
  intro x hx y hy
  unfold distance
  apply Finset.sum_eq_zero
  intro D hD
  by_cases hd : 0 < l D
  · have hcD : C.card ≤ D.card := hmin D (Finset.mem_filter.mpr ⟨hD,hd⟩)
    rcases hs C hCs D hD with hCD | hDC | hdis
    · simp [ind,hCD hx,hCD hy]
    · have he : C=D := (Finset.eq_of_subset_of_card_le hDC hcD).symm
      simp [ind,← he,hx,hy]
    · have hxD : x ∉ D := fun h => Finset.disjoint_left.mp hdis hx h
      have hyD : y ∉ D := fun h => Finset.disjoint_left.mp hdis hy h
      simp [ind,hxD,hyD]
  · have hz : l D=0 := le_antisymm (le_of_not_gt hd) (hl D hD)
    simp [hz]

/-- A minimal positive cut collapses a set of mass at least η to a single
    pseudometric point. This gives a direct fluctuation bound without
    constructing a tree graph. -/
lemma fluctuation_lower (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p : P → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x=1) (η : ℝ) (hη : 0 ≤ η)
    (hbal : ∀ C ∈ s, 0 < l C → η ≤ mass p C ∧ η ≤ 1-mass p C) :
    η^3*(∑ C ∈ s, l C) ≤
      ∑ y, p y*∑ x', p x'*∑ x, p x*|distance s l x y-distance s l x' y| := by
  let L := ∑ C ∈ s, l C
  have hL : 0 ≤ L := Finset.sum_nonneg hl
  have hf0 (y x' : P) : 0 ≤ ∑ x, p x*|distance s l x y-distance s l x' y| :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hp0 x) (abs_nonneg _))
  by_cases hn : (s.filter (fun C => 0 < l C)).Nonempty
  · obtain ⟨C,hC,hCl,hzero⟩ := exists_zero_cell s hs l hl hn
    have hm : η ≤ mass p C := (hbal C hC hCl).1
    have hc0 := mass_nonneg p hp0 C
    have hy (y : P) (hy : y ∈ C) : mass p C*(η*L) ≤
        ∑ x', p x'*∑ x, p x*|distance s l x y-distance s l x' y| := by
      calc
        _ = ∑ x' ∈ C, p x'*(η*L) := by simp only [mass,Finset.sum_mul]
        _ ≤ ∑ x' ∈ C, p x'*∑ x, p x*|distance s l x y-distance s l x' y| := by
          apply Finset.sum_le_sum
          intro x' hx'
          apply mul_le_mul_of_nonneg_left _ (hp0 x')
          simp only [hzero x' hx' y hy,sub_zero,abs_of_nonneg (distance_nonneg s l hl _ _)]
          exact expected_distance_ge s l hl p hp η hbal y
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
          (fun x' _ _ => mul_nonneg (hp0 x') (hf0 y x'))
    calc
      _ ≤ mass p C*(mass p C*(η*L)) := by
        have hsq : η*η ≤ mass p C*mass p C := mul_le_mul hm hm hη hc0
        have hmL := mul_le_mul_of_nonneg_right hsq (mul_nonneg hη hL)
        dsimp only [L] at hmL
        nlinarith only [hmL]
      _ = ∑ y ∈ C, p y*(mass p C*(η*L)) := by simp only [mass,Finset.sum_mul]
      _ ≤ ∑ y ∈ C, p y*∑ x', p x'*∑ x, p x*|distance s l x y-distance s l x' y| :=
        Finset.sum_le_sum (fun y hyC => mul_le_mul_of_nonneg_left (hy y hyC) (hp0 y))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        (fun y _ _ => mul_nonneg (hp0 y) (Finset.sum_nonneg (fun x' _ => mul_nonneg (hp0 x') (hf0 y x'))))
  · have hz : ∑ C ∈ s, l C=0 := by
      apply Finset.sum_eq_zero
      intro C hC
      have hnot : ¬0 < l C := fun hc => hn ⟨C,Finset.mem_filter.mpr ⟨hC,hc⟩⟩
      exact le_antisymm (le_of_not_gt hnot) (hl C hC)
    rw [hz,mul_zero]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hp0 y)
      (Finset.sum_nonneg (fun x' _ => mul_nonneg (hp0 x') (hf0 y x'))))

omit [Fintype P] [DecidableEq P] in
lemma cost_symm (s : Finset (Finset P)) (l : Finset P → ℝ) (p q : P → ℝ) :
    cost s l p q=cost s l q p := by simp only [cost,abs_sub_comm]

def fluctuation (s : Finset (Finset P)) (l : Finset P → ℝ) (x x' y : P) : ℝ :=
  |distance s l x y-distance s l x' y|

def doubleMean (s : Finset (Finset P)) (l : Finset P → ℝ) (p : P → ℝ) (y : P) : ℝ :=
  ∑ x', p x'*∑ x, p x*fluctuation s l x x' y

omit [Fintype P] in
lemma fluctuation_symm (s : Finset (Finset P)) (l : Finset P → ℝ) (x x' y : P) :
    fluctuation s l x x' y=fluctuation s l x' x y := abs_sub_comm _ _

lemma sum_le_add_of_abs {a b c : ℝ} (h : |a-b| ≤ c) : a ≤ b+c :=
  by have := (abs_le.mp h).2; linarith

lemma doubleMean_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p q : P → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp : ∑ x, p x=1) (hq : ∑ x, q x=1) (y : P) :
    doubleMean s l p y ≤ doubleMean s l q y+2*cost s l p q := by
  have h1 (x' : P) : (∑ x, p x*fluctuation s l x x' y) ≤
      (∑ x, q x*fluctuation s l x x' y)+cost s l p q :=
    sum_le_add_of_abs (first_fluctuation_transfer s hs l hl p q (hp.trans hq.symm) x' y)
  have h2 (x : P) : (∑ x', p x'*fluctuation s l x x' y) ≤
      (∑ x', q x'*fluctuation s l x x' y)+cost s l p q := by
    simpa only [fluctuation,abs_sub_comm] using
      sum_le_add_of_abs (first_fluctuation_transfer s hs l hl p q (hp.trans hq.symm) x y)
  calc
    _ ≤ ∑ x', p x'*((∑ x, q x*fluctuation s l x x' y)+cost s l p q) :=
      Finset.sum_le_sum (fun x' _ => mul_le_mul_of_nonneg_left (h1 x') (hp0 x'))
    _ = (∑ x, q x*∑ x', p x'*fluctuation s l x x' y)+cost s l p q := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul]
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => by ring))
    _ ≤ (∑ x, q x*((∑ x', q x'*fluctuation s l x x' y)+cost s l p q))+cost s l p q := by
      exact add_le_add (Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h2 x) (hq0 x))) le_rfl
    _ = doubleMean s l q y+2*cost s l p q := by
      simp only [doubleMean,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hq,one_mul]
      rw [show (∑ x, q x*∑ x', q x'*fluctuation s l x x' y) =
          ∑ x, q x*∑ x', q x'*fluctuation s l x' x y from by simp_rw [fluctuation_symm s l _ _ y]]
      ring

lemma doubleMean_fiber (s : Finset (Finset P)) (l : Finset P → ℝ) (p : P → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x=1) (y : P) (R : ℝ) :
    doubleMean s l p y ≤ 2*∑ x, p x*|distance s l x y-R| := by
  have ht (x x' : P) : fluctuation s l x x' y ≤
      |distance s l x y-R|+|distance s l x' y-R| := by
    simpa only [fluctuation,abs_sub_comm (R : ℝ)] using abs_sub_le (distance s l x y) R (distance s l x' y)
  calc
    _ ≤ ∑ x', p x'*∑ x, p x*(|distance s l x y-R|+|distance s l x' y-R|) := by
      apply Finset.sum_le_sum
      intro x' _
      apply mul_le_mul_of_nonneg_left _ (hp0 x')
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (ht x x') (hp0 x))
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul]
      ring

lemma last_doubleMean_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (a p q : P → ℝ)
    (ha0 : ∀ x, 0 ≤ a x) (ha : ∑ x, a x=1) (hpq : ∑ x, p x=∑ x, q x) :
    (∑ y, p y*doubleMean s l a y) ≤
      (∑ y, q y*doubleMean s l a y)+2*cost s l p q := by
  have ht (x x' : P) : (∑ y, p y*fluctuation s l x x' y) ≤
      (∑ y, q y*fluctuation s l x x' y)+2*cost s l p q :=
    sum_le_add_of_abs (last_fluctuation_transfer s hs l hl p q hpq x x')
  have he (b : P → ℝ) : (∑ y, b y*doubleMean s l a y) =
      ∑ x', a x'*∑ x, a x*∑ y, b y*fluctuation s l x x' y := by
    simp only [doubleMean,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [he p,he q]
  calc
    _ ≤ ∑ x', a x'*∑ x, a x*((∑ y, q y*fluctuation s l x x' y)+2*cost s l p q) := by
      apply Finset.sum_le_sum
      intro x' _
      apply mul_le_mul_of_nonneg_left _ (ha0 x')
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (ht x x') (ha0 x))
    _ = _ := by simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,ha,one_mul]

/-- Finite transport to independent sampling with explicit cut costs. -/

lemma iid_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (a t : P → ℝ) (ρ : P → P → ℝ)
    (ha0 : ∀ x, 0 ≤ a x) (ht0 : ∀ y, 0 ≤ t y) (hρ0 : ∀ y x, 0 ≤ ρ y x)
    (ha : ∑ x, a x=1) (ht : ∑ y, t y=1) (hρ : ∀ y, ∑ x, ρ y x=1) (R : P → ℝ) :
    (∑ y, a y*doubleMean s l a y) ≤
      2*(∑ y, t y*∑ x, ρ y x*|distance s l x y-R y|)+
      2*(∑ y, t y*cost s l (ρ y) a)+2*cost s l t a := by
  have hlast := last_doubleMean_transfer s hs l hl a a t ha0 ha (ha.trans ht.symm)
  rw [cost_symm s l a t] at hlast
  have hy (y : P) : doubleMean s l a y ≤
      2*(∑ x, ρ y x*|distance s l x y-R y|)+2*cost s l (ρ y) a := by
    have h1 := doubleMean_transfer s hs l hl a (ρ y) ha0 (hρ0 y) ha (hρ y) y
    rw [cost_symm s l a (ρ y)] at h1
    exact h1.trans (add_le_add (doubleMean_fiber s l (ρ y) (hρ0 y) (hρ y) y (R y)) le_rfl)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ => mul_le_mul_of_nonneg_left (hy y) (ht0 y))
  have he : (∑ y, t y*(2*(∑ x, ρ y x*|distance s l x y-R y|)+2*cost s l (ρ y) a)) =
      2*(∑ y, t y*∑ x, ρ y x*|distance s l x y-R y|)+2*(∑ y, t y*cost s l (ρ y) a) := by
    simp only [mul_add,Finset.sum_add_distrib]
    rw [Finset.mul_sum,Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [he] at hsum
  linarith

end WeakPinned.Cuts

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
