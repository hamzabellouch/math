import OAI.Geometry.PeriodicTiling.FiniteMasks
import OAI.Geometry.PeriodicTiling.TilesRegion
import OAI.Geometry.PeriodicTiling.PlaneLattices
import OAI.Geometry.PeriodicTiling.ConfigurationDifferenceReduction
import OAI.Geometry.PeriodicTiling.BoundedDifferences
import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega

namespace OAI

universe uG uι

noncomputable section

open scoped BigOperators Classical

namespace PeriodicTilingThree

def componentTarget {G : Type uG} [AddCommGroup G]
    (F : Finset G) (D : Set G) : Set G :=
  {x | tileCount F D x = 1}

private theorem unique_of_nat_sum_one {ι : Type uι} [Fintype ι]
    (c : ι → ℕ) (hc : (∑ i, c i) = 1) : ∃! i, c i = 1 := by
  classical
  have hle (i : ι) : c i ≤ 1 := by
    calc
      c i ≤ ∑ j, c j := Finset.single_le_sum (fun j _ => Nat.zero_le (c j))
        (Finset.mem_univ i)
      _ = 1 := hc
  have hcard : (Finset.univ.filter fun i => c i = 1).card = 1 := by
    calc
      (Finset.univ.filter fun i => c i = 1).card =
          ∑ i, if c i = 1 then (1 : ℕ) else 0 := by simp
      _ = ∑ i, c i := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := hle i
        split_ifs <;> omega
      _ = 1 := hc
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hmem : i ∈ Finset.univ.filter (fun i => c i = 1) := by
    rw [hi]
    exact Finset.mem_singleton_self i
  refine ⟨i, (Finset.mem_filter.mp hmem).2, ?_⟩
  intro j hj
  have hjmem : j ∈ Finset.univ.filter (fun i => c i = 1) := by simp [hj]
  simpa only [hi, Finset.mem_singleton] using hjmem

theorem component_tileCount_sum {G : Type uG} [AddCommGroup G]
    {ι : Type uι} [Fintype ι] {F : Finset G} {A : Set G}
    (parts : ι → Set G) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (x : G) : (∑ j, tileCount F (parts j) x) = 1 := by
  have hreal : ((∑ j, tileCount F (parts j) x : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sum]
    simp_rw [tileCount_cast]
    rw [Finset.sum_comm]
    simp_rw [hpartition]
    exact hTile.sum_tileIndicator_eq_one ℝ x
  exact_mod_cast hreal

theorem component_tileCount_le_one {G : Type uG} [AddCommGroup G]
    {ι : Type uι} [Fintype ι] {F : Finset G} {A : Set G}
    (parts : ι → Set G) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (j : ι) (x : G) : tileCount F (parts j) x ≤ 1 := by
  calc
    tileCount F (parts j) x ≤ ∑ i, tileCount F (parts i) x :=
      Finset.single_le_sum (f := fun i => tileCount F (parts i) x)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = 1 := component_tileCount_sum parts hTile hpartition x

theorem tilesRegion_componentTarget {G : Type uG} [AddCommGroup G]
    (F : Finset G) (D : Set G) (hcount : ∀ x, tileCount F D x ≤ 1) :
    TilesRegion F D (componentTarget F D) := by
  classical
  constructor
  · intro f hf d hd
    change tileCount F D (f + d) = 1
    apply Nat.le_antisymm (hcount (f + d))
    have hterm : tileIndicator ℕ D (f + d - f) = 1 := by
      simp [tileIndicator, hd]
    calc
      1 = tileIndicator ℕ D (f + d - f) := hterm.symm
      _ ≤ tileCount F D (f + d) :=
        Finset.single_le_sum (f := fun g => tileIndicator ℕ D (f + d - g))
          (fun g _ => Nat.zero_le _) hf
  · intro x hx
    change tileCount F D x = 1 at hx
    have hcard : (F.filter fun f => x - f ∈ D).card = 1 := by
      rw [← tileCount_eq_card_filter]
      exact hx
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    have hm : f ∈ F ∧ x - f ∈ D := by
      apply Finset.mem_filter.mp
      rw [hf]
      exact Finset.mem_singleton_self f
    refine ⟨⟨f, hm.1⟩, hm.2, ?_⟩
    intro g hg
    apply Subtype.ext
    have hg' : g.val ∈ F.filter (fun f => x - f ∈ D) :=
      Finset.mem_filter.mpr ⟨g.property, hg⟩
    simpa only [hf, Finset.mem_singleton] using hg'

theorem component_targets_partition {G : Type uG} [AddCommGroup G]
    {ι : Type uι} [Fintype ι] {F : Finset G} {A : Set G}
    (parts : ι → Set G) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (x : G) : ∃! j, x ∈ componentTarget F (parts j) :=
  unique_of_nat_sum_one (fun j => tileCount F (parts j) x)
    (component_tileCount_sum parts hTile hpartition x)

private theorem real_tileCount_periodic {G : Type uG} [AddCommGroup G]
    (F : Finset G) (D : Set G) (v : G) (hD : Period D v) :
    Function.Periodic (fun x => (tileCount F D x : ℝ)) v := by
  intro x
  change (tileCount F D (x + v) : ℝ) = (tileCount F D x : ℝ)
  rw [tileCount_cast, tileCount_cast]
  apply Finset.sum_congr rfl
  intro f _
  have he : x + v - f = (x - f) + v := by abel
  simp only [tileIndicator, he, hD (x - f)]

private theorem componentTarget_period_of_count {G : Type uG} [AddCommGroup G]
    (F : Finset G) (D : Set G) (v : G)
    (h : Function.Periodic (fun x => (tileCount F D x : ℝ)) v) :
    Period (componentTarget F D) v := by
  intro x
  have he : tileCount F D (x + v) = tileCount F D x := by
    have hreal : (tileCount F D (x + v) : ℝ) = (tileCount F D x : ℝ) := h x
    exact_mod_cast hreal
  change tileCount F D (x + v) = 1 ↔ tileCount F D x = 1
  rw [he]

private theorem bounded_component_periodic {ι : Type uι} [Fintype ι]
    (g : ι → Plane → ℝ) (w : ι → Plane) (j : ι) (e : Plane)
    (hperiod : ∀ i, Function.Periodic (g i) (w i))
    (hsum : (∑ i, g i) = fun _ => (1 : ℝ))
    (hbound : ∃ B : ℝ, ∀ x, |g j x| ≤ B)
    (hother : ∃ i, i ≠ j)
    (hspan : ∀ i, i ≠ j → ∃ a b : ℤ, e = a • w i + b • w j) :
    Function.Periodic (g j) e := by
  classical
  have hchoice : ∀ i, ∃ a b : ℤ, i ≠ j → e = a • w i + b • w j := by
    intro i
    by_cases hij : i = j
    · exact ⟨0, 0, fun h => (h hij).elim⟩
    · obtain ⟨a, b, h⟩ := hspan i hij
      exact ⟨a, b, fun _ => h⟩
  choose a b hab using hchoice
  let vs : List Plane := (Finset.univ.erase j).toList.map (fun i => a i • w i)
  have hmem (i : ι) (hij : i ≠ j) : a i • w i ∈ vs := by
    apply List.mem_map.mpr
    refine ⟨i, ?_, rfl⟩
    simpa only [Finset.mem_toList, Finset.mem_erase, Finset.mem_univ, and_true] using hij
  have hvs : vs ≠ [] := by
    obtain ⟨i, hij⟩ := hother
    intro he
    have h := hmem i hij
    rw [he] at h
    exact List.not_mem_nil h
  have hkill : ∀ i, i ≠ j → ∃ v ∈ vs, Function.Periodic (g i) v := by
    intro i hij
    exact ⟨a i • w i, hmem i hij, (hperiod i).zsmul (a i)⟩
  have hmods : ∀ u ∈ vs, ∃ k : ℤ, u = e + k • w j := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    have hij : i ≠ j := (Finset.mem_erase.mp (Finset.mem_toList.mp hi)).1
    refine ⟨-b i, ?_⟩
    rw [hab i hij, neg_smul]
    abel
  have hzero := configDiffs_component_zero j vs hvs g 1 hsum hkill
  rw [configDiffs_eq_iterate_of_period vs e (w j) (g j) (hperiod j) hmods] at hzero
  exact periodic_of_bounded_configDiff_iterate e vs.length (g j) hbound
    (List.length_pos_iff.mpr hvs) hzero

theorem componentTarget_fullyPeriodic {m : ℕ} {F : Finset Plane} {A : Set Plane}
    (parts : Fin m → Set Plane) (w : Fin m → Plane) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (hw : ∀ j, w j ≠ 0) (hperiod : ∀ j, Period (parts j) (w j))
    (htrans : ∀ i j, i ≠ j → planeDet (w i) (w j) ≠ 0)
    (j : Fin m) : FullyPeriodic (componentTarget F (parts j)) := by
  classical
  let g : Fin m → Plane → ℝ := fun i x => tileCount F (parts i) x
  have hgperiod : ∀ i, Function.Periodic (g i) (w i) :=
    fun i => real_tileCount_periodic F (parts i) (w i) (hperiod i)
  have hsum : (∑ i, g i) = fun _ => (1 : ℝ) := by
    ext x
    simp only [Finset.sum_apply, g, ← Nat.cast_sum]
    rw [component_tileCount_sum parts hTile hpartition x]
    simp
  have hbound : ∃ B : ℝ, ∀ x, |g j x| ≤ B := by
    refine ⟨1, fun x => ?_⟩
    have hn := component_tileCount_le_one parts hTile hpartition j x
    have hr : (tileCount F (parts j) x : ℝ) ≤ 1 := by exact_mod_cast hn
    change |(tileCount F (parts j) x : ℝ)| ≤ 1
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact hr
  by_cases hother : ∃ i, i ≠ j
  · obtain ⟨e, _he, hdet, hspan⟩ := exists_common_transverse w hw htrans
    have hge : Function.Periodic (g j) e := bounded_component_periodic g w j e
      hgperiod hsum hbound hother (fun i hij => hspan i j hij)
    exact fullyPeriodic_of_independent_periods
      (componentTarget_period_of_count F (parts j) e hge)
      (componentTarget_period_of_count F (parts j) (w j) (hgperiod j)) (hdet j)
  · have hall : ∀ i : Fin m, i = j := by
      intro i
      by_contra hij
      exact hother ⟨i, hij⟩
    have hone : ∀ x, tileCount F (parts j) x = 1 := by
      intro x
      have he := component_tileCount_sum parts hTile hpartition x
      have hs : (∑ i, tileCount F (parts i) x) = tileCount F (parts j) x := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          exact (hij (hall i)).elim
        · intro hj
          exact (hj (Finset.mem_univ j)).elim
      rwa [hs] at he
    have hE : componentTarget F (parts j) = Set.univ := by
      ext x
      simp only [componentTarget, Set.mem_ofPred_eq, hone x, Set.mem_univ]
    rw [hE]
    refine ⟨⊤, ?_, fun v _ x => ?_⟩
    · exact ⟨by simp⟩
    · simp

theorem component_targets {m : ℕ} {F : Finset Plane} {A : Set Plane}
    (parts : Fin m → Set Plane) (w : Fin m → Plane) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (hw : ∀ j, w j ≠ 0) (hperiod : ∀ j, Period (parts j) (w j))
    (htrans : ∀ i j, i ≠ j → planeDet (w i) (w j) ≠ 0) :
    (∀ j, TilesRegion F (parts j) (componentTarget F (parts j))) ∧
      (∀ x, ∃! j, x ∈ componentTarget F (parts j)) ∧
      ∀ j, FullyPeriodic (componentTarget F (parts j)) := by
  refine ⟨?_, component_targets_partition parts hTile hpartition, ?_⟩
  · intro j
    exact tilesRegion_componentTarget F (parts j)
      (component_tileCount_le_one parts hTile hpartition j)
  · exact componentTarget_fullyPeriodic parts w hTile hpartition hw hperiod htrans

end PeriodicTilingThree

end

end OAI
