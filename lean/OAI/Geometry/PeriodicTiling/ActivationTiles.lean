import OAI.Geometry.PeriodicTiling.ActivationOffsets
import OAI.Geometry.PeriodicTiling.GraphTests
import Mathlib.Tactic.Abel

namespace OAI

universe uJ uB

namespace PeriodicTilingThree

noncomputable section

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def activationBatch (i : Channel p) (h : Plane) (e : P E i)
    (freeZ : Bool) : Finset (Ambient E) := by
  classical
  exact (Finset.univ.filter fun v : V E =>
    (v.2 i).1 = (h.1 : ZMod ((E.r i) ^ 2)) ∧ (v.2 i).2 = e ∧
    (∀ j, j ≠ i → low E j (v.2 j).1 = 0) ∧ (freeZ = true ∨ v.1 = 0)).image
      (fun v => (h, v))

theorem mem_activationBatch (i : Channel p) (h : Plane) (e : P E i)
    (freeZ : Bool) (g : Ambient E) :
    g ∈ activationBatch E i h e freeZ ↔
      g.1 = h ∧ (g.2.2 i).1 = (h.1 : ZMod ((E.r i) ^ 2)) ∧
      (g.2.2 i).2 = e ∧ (∀ j, j ≠ i → low E j (g.2.2 j).1 = 0) ∧
      (freeZ = true ∨ g.2.1 = 0) := by
  classical
  simp only [activationBatch, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨rfl, hv⟩
  · rintro ⟨hh, hv⟩
    exact ⟨g.2, hv, Prod.ext hh.symm rfl⟩

theorem activationBatch_nonempty (i : Channel p) (h : Plane) (e : P E i)
    (freeZ : Bool) : (activationBatch E i h e freeZ).Nonempty := by
  classical
  refine ⟨(h, 0, Function.update 0 i ((h.1 : ZMod ((E.r i) ^ 2)), e)), ?_⟩
  apply (mem_activationBatch E i h e freeZ _).mpr
  refine ⟨rfl, ?_, ?_, ?_, Or.inr rfl⟩
  · simp
  · simp
  · intro j hji
    simp [hji]

theorem activationBatch_q0 (i : Channel p) (h : Plane) (e : P E i)
    (freeZ : Bool) {g : Ambient E} (hg : g ∈ activationBatch E i h e freeZ) :
    q0 E g = (h, Function.update (0 : Input E) i (h.1 : K E i)) := by
  classical
  obtain ⟨hh, hv, _hc, hother, _hz⟩ := (mem_activationBatch E i h e freeZ g).mp hg
  apply Prod.ext hh
  funext j
  by_cases hji : j = i
  · subst j
    change low E i (g.2.2 i).1 = _
    rw [hv]
    simp [low]
  · simpa [hji] using hother j hji

theorem activationBatch_disjoint (i : Channel p) {h h' : Plane}
    (e e' : P E i) (z z' : Bool) (hh : h ≠ h') :
    Disjoint (activationBatch E i h e z) (activationBatch E i h' e' z') := by
  classical
  apply Finset.disjoint_left.mpr
  intro g hg hg'
  exact hh (((mem_activationBatch E i h e z g).mp hg).1.symm.trans
    ((mem_activationBatch E i h' e' z' g).mp hg').1)

def activationSource (i : Channel p) (b : Base E) (h : Plane) (l : K E i) : Base E :=
  (b.1 - h, Function.update b.2 i (b.2 i - l))

theorem activationSource_eq_sub (i : Channel p) (b : Base E) (h : Plane) (l : K E i) :
    activationSource E i b h l = b - (h, Function.update (0 : Input E) i l) := by
  classical
  refine Prod.ext rfl ?_
  funext j
  by_cases hji : j = i
  · subst j
    simp [activationSource]
  · simp [activationSource, hji]

theorem activationSource_shear (i : Channel p) (b : Base E) (h : Plane) (l β : K E i)
    (hl : (h.1 : K E i) = l) :
    shear E i (activationSource E i b h l).1.1
        ((activationSource E i b h l).2 i) β + (h.1 : ZMod ((E.r i) ^ 2)) =
      shear E i b.1.1 (b.2 i) β := by
  simpa [activationSource] using shear_source_add E i b.1.1 h.1 (b.2 i) l β hl

def targetBeta (y : Ambient E) (i : Channel p) : K E i :=
  (shearEquiv E i y.1.1 ((q0 E y).2 i)).symm ⟨(y.2.2 i).1, rfl⟩

@[simp] theorem shear_targetBeta (y : Ambient E) (i : Channel p) :
    shear E i y.1.1 ((q0 E y).2 i) (targetBeta E y i) = (y.2.2 i).1 :=
  congrArg Subtype.val ((shearEquiv E i y.1.1 ((q0 E y).2 i)).apply_symm_apply
    ⟨(y.2.2 i).1, rfl⟩)

@[simp] theorem targetBeta_point (o : GraphOutputs E) (b : Base E) (i : Channel p) :
    targetBeta E (point o b) i = o.beta b i := by
  apply shear_injective E i b.1.1 (b.2 i)
  simpa only [q0_point, point_horizontal, point_v] using shear_targetBeta E (point o b) i

theorem difference_mem_activationBatch (o : GraphOutputs E) (i : Channel p)
    (h : Plane) (l : K E i) (hl : (h.1 : K E i) = l) (e : P E i)
    (freeZ : Bool) (y : Ambient E) (b : Base E) :
    y - point o b ∈ activationBatch E i h e freeZ ↔
      activationSource E i (q0 E y) h l = b ∧
      o.c b i + e = (y.2.2 i).2 ∧ o.beta b i = targetBeta E y i ∧
      (freeZ = true ∨ o.z b = y.2.1) := by
  constructor
  · intro hm
    have hq := activationBatch_q0 E i h e freeZ hm
    have hq' : q0 E y - b = (h, Function.update (0 : Input E) i l) := by
      simpa only [map_sub, q0_point, hl] using hq
    have hb : activationSource E i (q0 E y) h l = b := by
      rw [activationSource_eq_sub]
      have he := congrArg (fun z : Base E => q0 E y - z) hq'
      simpa using he.symm
    obtain ⟨_hh, hv, hc, _hother, hz⟩ :=
      (mem_activationBatch E i h e freeZ (y - point o b)).mp hm
    refine ⟨hb, ?_, ?_, ?_⟩
    · change (y.2.2 i).2 - o.c b i = e at hc
      rw [← hc]
      abel
    · apply shear_injective E i y.1.1 ((q0 E y).2 i)
      rw [shear_targetBeta]
      have hs := activationSource_shear E i (q0 E y) h l (o.beta b i) hl
      rw [hb] at hs
      change (y.2.2 i).1 - shear E i b.1.1 (b.2 i) (o.beta b i) =
        (h.1 : ZMod ((E.r i) ^ 2)) at hv
      change shear E i b.1.1 (b.2 i) (o.beta b i) +
        (h.1 : ZMod ((E.r i) ^ 2)) =
        shear E i y.1.1 ((q0 E y).2 i) (o.beta b i) at hs
      rw [← hs, ← hv]
      abel
    · rcases hz with hz | hz
      · exact Or.inl hz
      · right
        change y.2.1 - o.z b = 0 at hz
        exact (sub_eq_zero.mp hz).symm
  · rintro ⟨hb, hc, hβ, hz⟩
    apply (mem_activationBatch E i h e freeZ (y - point o b)).mpr
    have hs := activationSource_shear E i (q0 E y) h l (o.beta b i) hl
    rw [hb, hβ] at hs
    change shear E i b.1.1 (b.2 i) (targetBeta E y i) +
      (h.1 : ZMod ((E.r i) ^ 2)) =
      shear E i y.1.1 ((q0 E y).2 i) (targetBeta E y i) at hs
    rw [shear_targetBeta] at hs
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change y.1 - b.1 = h
      rw [← hb]
      change y.1 - (y.1 - h) = h
      abel
    · change (y.2.2 i).1 - shear E i b.1.1 (b.2 i) (o.beta b i) =
        (h.1 : ZMod ((E.r i) ^ 2))
      rw [hβ]
      rw [← hs]
      abel
    · change (y.2.2 i).2 - o.c b i = e
      rw [← hc]
      abel
    · intro j hji
      change low E j ((y.2.2 j).1 - shear E j b.1.1 (b.2 j) (o.beta b j)) = 0
      rw [map_sub, low_shear, ← hb]
      simp [activationSource, hji, q0]
    · rcases hz with hz | hz
      · exact Or.inl hz
      · right
        change y.2.1 - o.z b = 0
        rw [hz, sub_self]

def ordinaryActivationTile (n : Column p) : Finset (Ambient E) := by
  classical
  exact Finset.univ.biUnion fun j : ActivationIndex E (.inl n) =>
    activationBatch E (.inl n) (ordinaryOffset E n j)
      (shift (E.a (.inl n)) (E.b (.inl n)) j.2) true

def seedActivationTile (t : Fin 2) : Finset (Ambient E) := by
  classical
  exact Finset.univ.biUnion fun j : SeedActivationIndex E t =>
    activationBatch E (.inr t) (seedOffset E t j)
      (shift (E.a (.inr t)) (E.b (.inr t)) j.1.2) false

def ordinarySource (n : Column p) (b : Base E) (j : ActivationIndex E (.inl n)) : Base E :=
  activationSource E (.inl n) b (ordinaryOffset E n j) j.1

def seedSource (t : Fin 2) (b : Base E) (j : SeedActivationIndex E t) : Base E :=
  activationSource E (.inr t) b (seedOffset E t j) j.1.1

@[simp] theorem ordinarySource_horizontal (n : Column p) (b : Base E)
    (j : ActivationIndex E (.inl n)) :
    (ordinarySource E n b j).1 = b.1 - ordinaryOffset E n j := rfl

@[simp] theorem ordinarySource_own (n : Column p) (b : Base E)
    (j : ActivationIndex E (.inl n)) :
    (ordinarySource E n b j).2 (.inl n) = b.2 (.inl n) - j.1 := by
  simp [ordinarySource, activationSource]

@[simp] theorem seedSource_horizontal (t : Fin 2) (b : Base E)
    (j : SeedActivationIndex E t) :
    (seedSource E t b j).1 = b.1 - seedOffset E t j := rfl

@[simp] theorem seedSource_own (t : Fin 2) (b : Base E)
    (j : SeedActivationIndex E t) :
    (seedSource E t b j).2 (.inr t) = b.2 (.inr t) - j.1.1 := by
  simp [seedSource, activationSource]

@[simp] theorem ordinarySource_lineValue (n : Column p) (b : Base E)
    (j : ActivationIndex E (.inl n)) :
    lineValue n (ordinarySource E n b j).1 = lineValue n b.1 := by
  simp only [ordinarySource_horizontal, lineValue, ordinaryOffset,
    Prod.fst_sub, Prod.snd_sub]
  ring

theorem seedSource_residue (t : Fin 2) (b : Base E) (j : SeedActivationIndex E t) :
    ((((seedSource E t b j).1.1 : ℤ) : ZMod (p ^ 2)),
      (((seedSource E t b j).1.2 : ℤ) : ZMod (p ^ 2))) =
      ((b.1.1 : ZMod (p ^ 2)), (b.1.2 : ZMod (p ^ 2))) - j.2 := by
  rw [seedSource_horizontal]
  simpa only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Prod.mk_sub_mk] using
    congrArg (fun z : Residues p =>
      ((b.1.1 : ZMod (p ^ 2)), (b.1.2 : ZMod (p ^ 2))) - z)
      (seedOffset_residue E t j)

def ordinaryActivationMap (n : Column p) (o : GraphOutputs E) (b : Base E)
    (j : ActivationIndex E (.inl n)) : P E (.inl n) × K E (.inl n) :=
  (o.c (ordinarySource E n b j) (.inl n) + shift (E.a (.inl n)) (E.b (.inl n)) j.2,
    o.beta (ordinarySource E n b j) (.inl n))

def seedActivationMap (t : Fin 2) (o : GraphOutputs E) (b : Base E)
    (j : SeedActivationIndex E t) : (P E (.inr t) × K E (.inr t)) × ZMod (D p) :=
  ((o.c (seedSource E t b j) (.inr t) + shift (E.a (.inr t)) (E.b (.inr t)) j.1.2,
    o.beta (seedSource E t b j) (.inr t)), o.z (seedSource E t b j))

def ordinaryTarget (n : Column p) (y : Ambient E) : P E (.inl n) × K E (.inl n) :=
  ((y.2.2 (.inl n)).2, targetBeta E y (.inl n))

def seedTarget (t : Fin 2) (y : Ambient E) :
    (P E (.inr t) × K E (.inr t)) × ZMod (D p) :=
  (((y.2.2 (.inr t)).2, targetBeta E y (.inr t)), y.2.1)

theorem ordinarySource_injective (n : Column p) (b : Base E) :
    Function.Injective (ordinarySource E n b) := by
  intro j j' hj
  apply ordinaryOffset_injective E n
  have hh := congrArg (fun d : Base E => b.1 - d.1) hj
  simpa [ordinarySource, activationSource] using hh

theorem seedSource_injective (t : Fin 2) (b : Base E) :
    Function.Injective (seedSource E t b) := by
  intro j j' hj
  apply seedOffset_injective E t
  have hh := congrArg (fun d : Base E => b.1 - d.1) hj
  simpa [seedSource, activationSource] using hh

theorem difference_mem_ordinaryActivationTile (n : Column p) (o : GraphOutputs E)
    (y : Ambient E) (b : Base E) :
    y - point o b ∈ ordinaryActivationTile E n ↔
      ∃ j, ordinarySource E n (q0 E y) j = b ∧
        ordinaryActivationMap E n o (q0 E y) j = ordinaryTarget E n y := by
  classical
  simp only [ordinaryActivationTile, Finset.mem_biUnion, Finset.mem_univ, true_and]
  apply exists_congr
  intro j
  rw [difference_mem_activationBatch E o (.inl n) (ordinaryOffset E n j) j.1
    (ordinaryOffset_low E n j)]
  simp only [true_or, and_true]
  constructor
  · rintro ⟨hb, hc, hβ⟩
    change ordinarySource E n (q0 E y) j = b at hb
    refine ⟨hb, ?_⟩
    unfold ordinaryActivationMap ordinaryTarget
    rw [hb]
    exact Prod.ext hc hβ
  · rintro ⟨hb, hmap⟩
    unfold ordinaryActivationMap ordinaryTarget at hmap
    rw [hb] at hmap
    exact ⟨hb, congrArg Prod.fst hmap, congrArg Prod.snd hmap⟩

theorem difference_mem_seedActivationTile (t : Fin 2) (o : GraphOutputs E)
    (y : Ambient E) (b : Base E) :
    y - point o b ∈ seedActivationTile E t ↔
      ∃ j, seedSource E t (q0 E y) j = b ∧
        seedActivationMap E t o (q0 E y) j = seedTarget E t y := by
  classical
  simp only [seedActivationTile, Finset.mem_biUnion, Finset.mem_univ, true_and]
  apply exists_congr
  intro j
  rw [difference_mem_activationBatch E o (.inr t) (seedOffset E t j) j.1.1
    (seedOffset_low E t j)]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨hb, hc, hβ, hz⟩
    change seedSource E t (q0 E y) j = b at hb
    refine ⟨hb, ?_⟩
    unfold seedActivationMap seedTarget
    rw [hb]
    exact Prod.ext (Prod.ext hc hβ) hz
  · rintro ⟨hb, hmap⟩
    unfold seedActivationMap seedTarget at hmap
    rw [hb] at hmap
    exact ⟨hb, congrArg (fun z => z.1.1) hmap,
      congrArg (fun z => z.1.2) hmap, congrArg Prod.snd hmap⟩

private theorem existsUnique_source_iff {J : Type uJ} {B : Type uB} (s : J → B)
    (hs : Function.Injective s) (Q : J → Prop) :
    (∃! b, ∃ j, s j = b ∧ Q j) ↔ ∃! j, Q j := by
  constructor
  · rintro ⟨b, ⟨j, hj, hQ⟩, huniq⟩
    refine ⟨j, hQ, ?_⟩
    intro j' hQ'
    apply hs
    exact (huniq (s j') ⟨j', rfl, hQ'⟩).trans hj.symm
  · rintro ⟨j, hj, huniq⟩
    refine ⟨s j, ⟨j, rfl, hj⟩, ?_⟩
    rintro b ⟨j', hj', hQ'⟩
    rw [← hj', huniq j' hQ']

theorem ordinaryTarget_surjective (n : Column p) (b : Base E)
    (q : P E (.inl n) × K E (.inl n)) :
    ∃ y : Ambient E, q0 E y = b ∧ ordinaryTarget E n y = q := by
  classical
  let o : GraphOutputs E :=
    ⟨fun _ => Function.update 0 (.inl n) q.1,
      fun _ => Function.update 0 (.inl n) q.2, fun _ => 0⟩
  refine ⟨point o b, q0_point o b, ?_⟩
  simp [ordinaryTarget, o]

theorem seedTarget_surjective (t : Fin 2) (b : Base E)
    (q : (P E (.inr t) × K E (.inr t)) × ZMod (D p)) :
    ∃ y : Ambient E, q0 E y = b ∧ seedTarget E t y = q := by
  classical
  let o : GraphOutputs E :=
    ⟨fun _ => Function.update 0 (.inr t) q.1.1,
      fun _ => Function.update 0 (.inr t) q.1.2, fun _ => q.2⟩
  refine ⟨point o b, q0_point o b, ?_⟩
  simp [seedTarget, o]

theorem ordinaryActivationTile_iff (n : Column p) (o : GraphOutputs E) :
    Tiles (ordinaryActivationTile E n) (graph o) ↔
      ∀ b : Base E, Function.Bijective (ordinaryActivationMap E n o b) := by
  rw [graph, tiles_range_iff_unique_base (point o) (point_injective o)]
  simp_rw [difference_mem_ordinaryActivationTile,
    existsUnique_source_iff _ (ordinarySource_injective E n _)]
  constructor
  · intro h b
    apply (Function.bijective_iff_existsUnique _).mpr
    intro q
    obtain ⟨y, hy, hq⟩ := ordinaryTarget_surjective E n b q
    simpa only [hy, hq] using h y
  · intro h y
    exact (h (q0 E y)).existsUnique (ordinaryTarget E n y)

theorem seedActivationTile_iff (t : Fin 2) (o : GraphOutputs E) :
    Tiles (seedActivationTile E t) (graph o) ↔
      ∀ b : Base E, Function.Bijective (seedActivationMap E t o b) := by
  rw [graph, tiles_range_iff_unique_base (point o) (point_injective o)]
  simp_rw [difference_mem_seedActivationTile,
    existsUnique_source_iff _ (seedSource_injective E t _)]
  constructor
  · intro h b
    apply (Function.bijective_iff_existsUnique _).mpr
    intro q
    obtain ⟨y, hy, hq⟩ := seedTarget_surjective E t b q
    simpa only [hy, hq] using h y
  · intro h y
    exact (h (q0 E y)).existsUnique (seedTarget E t y)

theorem ordinaryActivationTile_nonempty (n : Column p) :
    (ordinaryActivationTile E n).Nonempty := by
  classical
  let δ : ShiftIndex (E.a (.inl n)) (E.b (.inl n)) :=
    ⟨(0, 0), ⟨0, by simp [shiftMultiplicity]⟩⟩
  let j : ActivationIndex E (.inl n) := (0, δ)
  obtain ⟨g, hg⟩ := activationBatch_nonempty E (.inl n) (ordinaryOffset E n j)
    (shift (E.a (.inl n)) (E.b (.inl n)) j.2) true
  refine ⟨g, ?_⟩
  simp only [ordinaryActivationTile, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨j, hg⟩

theorem seedActivationTile_nonempty (t : Fin 2) :
    (seedActivationTile E t).Nonempty := by
  classical
  let δ : ShiftIndex (E.a (.inr t)) (E.b (.inr t)) := ⟨(0, 0), ⟨0, by simp [shiftMultiplicity]⟩⟩
  let j : SeedActivationIndex E t := ((0, δ), 0)
  obtain ⟨g, hg⟩ := activationBatch_nonempty E (.inr t) (seedOffset E t j)
    (shift (E.a (.inr t)) (E.b (.inr t)) j.1.2) false
  refine ⟨g, ?_⟩
  simp only [seedActivationTile, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨j, hg⟩

end

end PeriodicTilingThree

end OAI
