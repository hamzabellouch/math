import OAI.Geometry.PeriodicTiling.Dependence
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

namespace OAI

universe uι uM uN uA uB uH uC

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

section CycleCombinatorics

variable {ι : Type uι} [Fintype ι]
variable {M : ι → Type uM} {N : ι → Type uN}
variable [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
variable {t : ℕ} [NeZero t]

def cycleExtend (cycle : ZMod t ↪ ι) (v : ∀ j, M (cycle j)) : ∀ i, M i := by
  classical
  exact ∑ j : ZMod t, Pi.single (cycle j) (v j)

@[simp] theorem cycleExtend_apply
    {ι : Type uι} [Fintype ι]
    {M : ι → Type uM} [∀ i, AddCommGroup (M i)] {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ ι)
    (v : ∀ j, M (cycle j)) (j : ZMod t) :
    cycleExtend cycle v (cycle j) = v j := by
  classical
  rw [cycleExtend, Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro l _ hlj
    have hne : cycle l ≠ cycle j := fun h => hlj (cycle.injective h)
    simp [Ne.symm hne]
  · simp

theorem cycleExtend_eq_zero
    {ι : Type uι} [Fintype ι]
    {M : ι → Type uM} [∀ i, AddCommGroup (M i)] {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ ι)
    (v : ∀ j, M (cycle j)) {i : ι} (hi : ∀ j, cycle j ≠ i) :
    cycleExtend cycle v i = 0 := by
  classical
  rw [cycleExtend, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  simp [Ne.symm (hi j)]

def cycleShift (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j) (e : ∀ i, N i) : ∀ i, M i :=
  cycleExtend cycle (fun j => (d j (e (cycle (j - 1))) : M (cycle j)))

@[simp] theorem cycleShift_apply
    {ι : Type uι} [Fintype ι]
    {M : ι → Type uM} {N : ι → Type uN}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j) (e : ∀ i, N i) (j : ZMod t) :
    cycleShift cycle U d e (cycle j) = (d j (e (cycle (j - 1))) : M (cycle j)) :=
  cycleExtend_apply cycle _ j

theorem cycleShift_eq_zero
    {ι : Type uι} [Fintype ι]
    {M : ι → Type uM} {N : ι → Type uN}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j) (e : ∀ i, N i)
    {i : ι} (hi : ∀ j, cycle j ≠ i) : cycleShift cycle U d e i = 0 :=
  cycleExtend_eq_zero cycle _ hi

def cycleMap (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j)
    (g : ∀ i, M i → N i) (k : ∀ i, M i) (e : ∀ i, N i) : ∀ i, N i :=
  fun i => e i + g i (k i - cycleShift cycle U d e i)

@[simp] theorem cycleMap_apply_cycle (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j)
    (g : ∀ i, M i → N i) (k : ∀ i, M i) (e : ∀ i, N i) (j : ZMod t) :
    cycleMap cycle U d g k e (cycle j) =
      e (cycle j) + g (cycle j) (k (cycle j) - d j (e (cycle (j - 1)))) := by
  simp only [cycleMap, cycleShift_apply]

theorem forall_of_cyclic_step {Q : ZMod t → Prop} (j₀ : ZMod t) (h₀ : Q j₀)
    (hstep : ∀ j, Q j → Q (j + 1)) : ∀ j, Q j := by
  have hnat : ∀ n : ℕ, Q (j₀ + (n : ZMod t)) := by
    intro n
    induction n with
    | zero => simpa using h₀
    | succ n ih => simpa only [Nat.cast_succ, add_assoc] using hstep _ ih
  intro j
  have h := hnat (j - j₀).val
  simpa only [ZMod.natCast_zmod_val, add_sub_cancel] using h

theorem cycleMap_injective_of_inactive (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j)
    (g : ∀ i, M i → N i) (k : ∀ i, M i)
    (j₀ : ZMod t) (hinactive : ¬ DigitActive (g (cycle j₀)) (U j₀)) :
    Function.Injective (cycleMap cycle U d g k) := by
  classical
  have hagree {w w' : M (cycle j₀)} (hw : w - w' ∈ U j₀) :
      g (cycle j₀) w = g (cycle j₀) w' := by
    by_contra hne
    exact hinactive ⟨w, w', hw, hne⟩
  have hconstant (e : ∀ i, N i) :
      g (cycle j₀) (k (cycle j₀) - d j₀ (e (cycle (j₀ - 1)))) =
        g (cycle j₀) (k (cycle j₀)) := by
    apply hagree
    have heq : (k (cycle j₀) - (d j₀ (e (cycle (j₀ - 1))) : M (cycle j₀))) -
        k (cycle j₀) = -((d j₀ (e (cycle (j₀ - 1)))) : M (cycle j₀)) := by abel
    rw [heq]
    exact (U j₀).neg_mem (d j₀ (e (cycle (j₀ - 1)))).property
  intro e e' he
  have hstart : e (cycle j₀) = e' (cycle j₀) := by
    have h := congrFun he (cycle j₀)
    rw [cycleMap_apply_cycle, cycleMap_apply_cycle, hconstant, hconstant] at h
    exact add_right_cancel h
  have hstep (j : ZMod t) (hj : e (cycle j) = e' (cycle j)) :
      e (cycle (j + 1)) = e' (cycle (j + 1)) := by
    have h := congrFun he (cycle (j + 1))
    simp only [cycleMap_apply_cycle] at h
    have hprev : e (cycle (j + 1 - 1)) = e' (cycle (j + 1 - 1)) := by
      exact Eq.mpr (congrArg (fun l : ZMod t => e (cycle l) = e' (cycle l))
        (add_sub_cancel_right j 1)) hj
    rw [hprev] at h
    exact add_right_cancel h
  have hon := forall_of_cyclic_step j₀ hstart hstep
  funext i
  by_cases hi : ∃ j, cycle j = i
  · obtain ⟨j, rfl⟩ := hi
    exact hon j
  · have hoff : ∀ j, cycle j ≠ i := by simpa only [not_exists] using hi
    have h := congrFun he i
    simp only [cycleMap, cycleShift_eq_zero cycle U d e hoff,
      cycleShift_eq_zero cycle U d e' hoff, sub_zero] at h
    exact add_right_cancel h

theorem cycleMap_bijective_of_inactive [∀ i, Fintype (N i)]
    (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j)
    (g : ∀ i, M i → N i) (k : ∀ i, M i)
    (j₀ : ZMod t) (hinactive : ¬ DigitActive (g (cycle j₀)) (U j₀)) :
    Function.Bijective (cycleMap cycle U d g k) :=
  (cycleMap_injective_of_inactive cycle U d g k j₀ hinactive).bijective_of_finite

theorem cycleMap_collision_of_all_active (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j))) (g : ∀ i, M i → N i)
    (hactive : ∀ j, DigitActive (g (cycle j)) (U j)) :
    ∃ (k : ∀ i, M i) (d : ∀ j, N (cycle (j - 1)) → U j)
      (ε : ∀ i, N i), ε ≠ 0 ∧
      cycleMap cycle U d g k 0 = cycleMap cycle U d g k ε := by
  classical
  choose w w' hmem hne using hactive
  let ε₀ : ∀ j, N (cycle j) := fun j => g (cycle j) (w j) - g (cycle j) (w' j)
  have hε₀ (j : ZMod t) : ε₀ j ≠ 0 := sub_ne_zero.mpr (hne j)
  let ε : ∀ i, N i := cycleExtend cycle ε₀
  let k : ∀ i, M i := cycleExtend cycle w
  let d : ∀ j, N (cycle (j - 1)) → U j := fun j v =>
    if v = ε₀ (j - 1) then ⟨w j - w' j, hmem j⟩ else 0
  have hd₀ (j : ZMod t) : d j 0 = 0 := by
    simp only [d, ite_eq_right (Ne.symm (hε₀ (j - 1)))]
  have hdε (j : ZMod t) : d j (ε (cycle (j - 1))) = ⟨w j - w' j, hmem j⟩ := by
    simp only [d, ε, cycleExtend_apply, ite_eq_left rfl]
  refine ⟨k, d, ε, ?_, ?_⟩
  · intro hz
    have h := congrFun hz (cycle 0)
    apply hε₀ 0
    simpa only [ε, cycleExtend_apply, Pi.zero_apply] using h
  · funext i
    by_cases hi : ∃ j, cycle j = i
    · obtain ⟨j, rfl⟩ := hi
      calc
        cycleMap cycle U d g k 0 (cycle j) = g (cycle j) (w j) := by
          simp only [cycleMap_apply_cycle, Pi.zero_apply, hd₀, ZeroMemClass.coe_zero,
            sub_zero, zero_add, k, cycleExtend_apply]
        _ = ε₀ j + g (cycle j) (w' j) := (sub_add_cancel _ _).symm
        _ = cycleMap cycle U d g k ε (cycle j) := by
          rw [cycleMap_apply_cycle, hdε]
          simp only [k, ε, cycleExtend_apply, sub_sub_cancel]
    · have hoff : ∀ j, cycle j ≠ i := by simpa only [not_exists] using hi
      simp only [cycleMap, Pi.zero_apply, ε, cycleExtend_eq_zero cycle ε₀ hoff,
        cycleShift_eq_zero cycle U d 0 hoff,
        cycleShift_eq_zero cycle U d (cycleExtend cycle ε₀) hoff]

theorem forall_cycleMap_bijective_iff [∀ i, Fintype (N i)]
    (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (g : ∀ i, M i → N i) :
    (∀ (d : ∀ j, N (cycle (j - 1)) → U j) (k : ∀ i, M i),
      Function.Bijective (cycleMap cycle U d g k)) ↔
      ∃ j, ¬ DigitActive (g (cycle j)) (U j) := by
  constructor
  · intro hall
    by_contra hnone
    have hactive : ∀ j, DigitActive (g (cycle j)) (U j) := by
      simpa only [not_exists, not_not] using hnone
    obtain ⟨k, d, ε, hε, hcollision⟩ :=
      cycleMap_collision_of_all_active cycle U g hactive
    exact hε ((hall d k).1 hcollision).symm
  · rintro ⟨j, hj⟩ d k
    exact cycleMap_bijective_of_inactive cycle U d g k j hj

end CycleCombinatorics

theorem existsUnique_fixed_comp_iff {A : Type uA} {B : Type uB} (f : A → B) (g : B → A) :
    (∃! a, g (f a) = a) ↔ ∃! b, f (g b) = b := by
  constructor
  · rintro ⟨a, ha, hu⟩
    refine ⟨f a, ?_, ?_⟩
    · exact congrArg f ha
    · intro b hb
      have hg : g b = a := hu _ (congrArg g hb)
      calc
        b = f (g b) := hb.symm
        _ = f a := congrArg f hg
  · rintro ⟨b, hb, hu⟩
    refine ⟨g b, ?_, ?_⟩
    · exact congrArg g hb
    · intro a ha
      have hf : f a = b := hu _ (congrArg f ha)
      calc
        a = g (f a) := ha.symm
        _ = g b := congrArg g hf

theorem tiles_offset_iff_permutation
    {H : Type uH} {B : Type uB} {C : Type uC} [AddCommGroup H] [AddCommGroup B] [AddCommGroup C]
    (q : H →+ B) (ψ : H →+ C) (s : B → H) (hs : ∀ b, q (s b) = b)
    (hjoint : Function.Surjective (fun y => (q y, ψ y)))
    (Δ : C → B) (F : Finset H)
    (hF : ∀ y, y ∈ F ↔ q y = Δ (ψ y)) :
    Tiles F (Set.range s) ↔
      ∀ b, Function.Bijective (fun e => e + ψ (s (b - Δ e))) := by
  have hinj : Function.Injective s := by
    intro b b' h
    simpa only [hs] using congrArg q h
  have hmem (y : H) (b : B) : y - s b ∈ F ↔
      q y - Δ (ψ y - ψ (s b)) = b := by
    rw [hF, map_sub, hs, map_sub]
    simp only [sub_eq_iff_eq_add]
    exact ⟨fun h => h.trans (add_comm _ _), fun h => h.trans (add_comm _ _)⟩
  have hfibre (y : H) : (∃! b, y - s b ∈ F) ↔
      ∃! e, e + ψ (s (q y - Δ e)) = ψ y := by
    calc
      _ ↔ ∃! b, q y - Δ (ψ y - ψ (s b)) = b := existsUnique_congr (hmem y)
      _ ↔ ∃! e, ψ y - ψ (s (q y - Δ e)) = e :=
        existsUnique_fixed_comp_iff (fun b => ψ y - ψ (s b)) (fun e => q y - Δ e)
      _ ↔ _ := existsUnique_congr (fun e => by rw [sub_eq_iff_eq_add]; exact eq_comm)
  rw [tiles_range_iff_unique_base s hinj F]
  constructor
  · intro h b
    apply (Function.bijective_iff_existsUnique _).mpr
    intro c
    obtain ⟨y, hy⟩ := hjoint (b, c)
    have hq : q y = b := congrArg Prod.fst hy
    have hψ : ψ y = c := congrArg Prod.snd hy
    simpa only [hq, hψ] using (hfibre y).mp (h y)
  · intro h y
    exact (hfibre y).mpr ((h (q y)).existsUnique (ψ y))

section ConcreteTiles

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def usefulProjection : Ambient E →+ Useful E where
  toFun v := fun i => (v.2.2 i).2
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem usefulProjection_apply (v : Ambient E) (i : Channel p) :
    usefulProjection E v i = (v.2.2 i).2 := rfl

@[simp] theorem usefulProjection_point (o : GraphOutputs E) (b : Base E) :
    usefulProjection E (point o b) = o.c b := rfl

theorem q0_usefulProjection_surjective :
    Function.Surjective (fun y : Ambient E => (q0 E y, usefulProjection E y)) := by
  rintro ⟨b, c⟩
  let o : GraphOutputs E := ⟨fun _ => c, fun _ => 0, fun _ => 0⟩
  refine ⟨point o b, ?_⟩
  exact Prod.ext (q0_point o b) rfl

private theorem offset_horizontal_zero (D : Useful E → Low E)
    (v : {v : Ambient E // q0 E v = (0, D (usefulProjection E v))}) :
    (v : Ambient E).1 = 0 := congrArg Prod.fst v.property

noncomputable instance offsetFintype (D : Useful E → Low E) :
    Fintype {v : Ambient E // q0 E v = (0, D (usefulProjection E v))} :=
  Fintype.ofInjective (fun v => (v : Ambient E).2) (by
    intro v w h
    apply Subtype.ext
    exact Prod.ext ((offset_horizontal_zero E D v).trans
      (offset_horizontal_zero E D w).symm) h)

def offsetTile (D : Useful E → Low E) : Finset (Ambient E) :=
  (Finset.univ : Finset {v : Ambient E // q0 E v = (0, D (usefulProjection E v))}).map
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_offsetTile (D : Useful E → Low E) (v : Ambient E) :
    v ∈ offsetTile E D ↔ q0 E v = (0, D (usefulProjection E v)) := by
  constructor
  · intro h
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp h
    exact w.property
  · intro h
    exact Finset.mem_map.mpr ⟨⟨v, h⟩, Finset.mem_univ _, rfl⟩

theorem offsetTile_nonempty (D : Useful E → Low E) : (offsetTile E D).Nonempty := by
  let o : GraphOutputs E := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩
  refine ⟨point o (0, D 0), (mem_offsetTile E D _).mpr ?_⟩
  exact q0_point o (0, D 0)

theorem offsetTile_iff (D : Useful E → Low E) (o : GraphOutputs E) :
    Tiles (offsetTile E D) (graph o) ↔
      ∀ x k, Function.Bijective (fun e : Useful E => e + o.c (x, k - D e)) := by
  have h := tiles_offset_iff_permutation (q0 E) (usefulProjection E) (point o)
    (q0_point o) (q0_usefulProjection_surjective E) (fun e => (0, D e))
    (offsetTile E D) (mem_offsetTile E D)
  change Tiles (offsetTile E D) (graph o) ↔ _ at h
  constructor
  · intro htile x k
    have hb := h.mp htile (x, k)
    change Function.Bijective (fun e : Useful E => e + o.c (x - 0, k - D e)) at hb
    simpa only [sub_zero] using hb
  · intro hmap
    apply h.mpr
    rintro ⟨x, k⟩
    change Function.Bijective (fun e : Useful E => e + o.c (x - 0, k - D e))
    simpa only [sub_zero] using hmap x k

variable {t : ℕ} [NeZero t]

def cycleTile (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j))
    (d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j)) :
    Finset (Ambient E) :=
  offsetTile E (cycleShift cycle (fun j => digitSubgroup E (cycle j) (labels j)) d)

theorem cycleTile_nonempty (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j))
    (d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j)) :
    (cycleTile E cycle labels d).Nonempty := offsetTile_nonempty E _

theorem cycleTile_iff (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j))
    (d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j))
    (o : GraphOutputs E) (g : ∀ i, Plane → K E i → P E i)
    (hfactor : ∀ x k i, o.c (x, k) i = g i x (k i)) :
    Tiles (cycleTile E cycle labels d) (graph o) ↔
      ∀ x k, Function.Bijective
        (cycleMap cycle (fun j => digitSubgroup E (cycle j) (labels j)) d
          (fun i => g i x) k) := by
  let U := fun j => digitSubgroup E (cycle j) (labels j)
  have hm (x : Plane) (k : Low E) :
      (fun e : Useful E => e + o.c (x, k - cycleShift cycle U d e)) =
        cycleMap cycle U d (fun i => g i x) k := by
    funext e i
    change e i + o.c (x, k - cycleShift cycle U d e) i =
      e i + g i x (k i - cycleShift cycle U d e i)
    exact congrArg (fun v => e i + v) (hfactor x (k - cycleShift cycle U d e) i)
  simpa only [cycleTile, hm] using offsetTile_iff E (cycleShift cycle U d) o

theorem all_cycleTile_iff (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j))
    (o : GraphOutputs E) (g : ∀ i, Plane → K E i → P E i)
    (hfactor : ∀ x k i, o.c (x, k) i = g i x (k i)) :
    (∀ d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j),
      Tiles (cycleTile E cycle labels d) (graph o)) ↔
      ∀ x, ∃ j, ¬ DigitActive (g (cycle j) x) (digitSubgroup E (cycle j) (labels j)) := by
  constructor
  · intro h x
    apply (forall_cycleMap_bijective_iff cycle
      (fun j => digitSubgroup E (cycle j) (labels j)) (fun i => g i x)).mp
    intro d k
    exact (cycleTile_iff E cycle labels d o g hfactor).mp (h d) x k
  · intro h d
    apply (cycleTile_iff E cycle labels d o g hfactor).mpr
    intro x k
    obtain ⟨j, hj⟩ := h x
    exact cycleMap_bijective_of_inactive cycle
      (fun j => digitSubgroup E (cycle j) (labels j)) d (fun i => g i x) k j hj

def cycleTiles (cycle : ZMod t ↪ Channel p) (labels : ∀ j, Label p (cycle j)) :
    Finset (Finset (Ambient E)) := by
  classical
  exact Finset.univ.image (cycleTile E cycle labels)

theorem cycleTiles_nonempty (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j)) : (cycleTiles E cycle labels).Nonempty := by
  classical
  exact ⟨cycleTile E cycle labels (fun _ _ => 0),
    Finset.mem_image.mpr ⟨(fun _ _ => 0), Finset.mem_univ _, rfl⟩⟩

theorem nonempty_of_mem_cycleTiles (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j)) {F : Finset (Ambient E)}
    (hF : F ∈ cycleTiles E cycle labels) : F.Nonempty := by
  classical
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hF
  exact cycleTile_nonempty E cycle labels d

theorem forall_mem_cycleTiles_iff (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j)) (A : Set (Ambient E)) :
    (∀ F ∈ cycleTiles E cycle labels, Tiles F A) ↔
      ∀ d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j),
        Tiles (cycleTile E cycle labels d) A := by
  classical
  simp only [cycleTiles, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h d
    exact h _ ⟨d, rfl⟩
  · intro h F hF
    obtain ⟨d, rfl⟩ := hF
    exact h d

theorem cycle_exclusion_iff (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j)) (o : GraphOutputs E)
    (hdep : HasDependence E o) :
    (∀ F ∈ cycleTiles E cycle labels, Tiles F (graph o)) ↔
      ∀ x, ∃ j, ¬ Active E o (cycle j) x (labels j) := by
  rw [forall_mem_cycleTiles_iff]
  exact all_cycleTile_iff E cycle labels o (usefulAt E o) (usefulAt_factor E hdep)

end ConcreteTiles

end PeriodicTilingThree

end

end OAI
