import OAI.Analysis.Nonexpansive.GeneratedMaps

namespace OAI

/-!
# Resolvent tail families

The outer resolvent in every tail map gives a uniform approximate fixed
point bound. Convex hulls are taken in the ambient vector space of maps.
Precomposition is linear on that vector space; only this linear operation
is distributed over convex combinations.
-/

noncomputable section

open Set

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [CompleteSpace X] {K : Set X}
variable (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
variable (T : K → K) (hT : LipschitzWith 1 T)

/-- Tail maps retain their actual outer resolvent and generated inner map. -/
def tailFamily (m : ℕ) : Set (K → K) :=
  {h | ∃ (n : ℕ) (hn : 1 ≤ n), m ≤ n ∧
    ∃ g : K → K, Generated hKclosed hKconvex T hT g ∧
      h = resolvent hKclosed hKconvex T hT n hn ∘ g}

theorem tailFamily_nonempty (m : ℕ) (hm : 1 ≤ m) :
    (tailFamily hKclosed hKconvex T hT m).Nonempty := by
  refine ⟨resolvent hKclosed hKconvex T hT m hm ∘ id, m, hm, le_rfl,
    id, Generated.id, rfl⟩

theorem tailFamily_generated {m : ℕ} {h : K → K}
    (hh : h ∈ tailFamily hKclosed hKconvex T hT m) :
    Generated hKclosed hKconvex T hT h := by
  rcases hh with ⟨n, hn, _, g, hg, rfl⟩
  exact Generated.comp (Generated.resolvent n hn) hg

theorem tailFamily_antitone : Antitone (tailFamily hKclosed hKconvex T hT) := by
  intro m n hmn h hh
  rcases hh with ⟨k, hk, hnk, g, hg, rfl⟩
  exact ⟨k, hk, hmn.trans hnk, g, hg, rfl⟩

theorem tailFamily_nonexpansive {m : ℕ} {h : K → K}
    (hh : h ∈ tailFamily hKclosed hKconvex T hT m) :
    LipschitzWith 1 h :=
  generated_nonexpansive
    (tailFamily_generated hKclosed hKconvex T hT hh)

theorem tailFamily_defect_le
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) {h : K → K}
    (hh : h ∈ tailFamily hKclosed hKconvex T hT m) (a : K) :
    ‖(T (h a) : X) - (h a : X)‖ ≤ 1 / (m : ℝ) := by
  rcases hh with ⟨n, hn, hmn, g, hg, rfl⟩
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  exact (resolvent_defect_le hKclosed hKconvex T hT hdiam n hn (g a)).trans
    (one_div_le_one_div_of_le hm0 hmn')

/-- Appending any generated map on the input side retains the same tail. -/
theorem tailFamily_precomp {m : ℕ} {h g : K → K}
    (hh : h ∈ tailFamily hKclosed hKconvex T hT m)
    (hg : Generated hKclosed hKconvex T hT g) :
    h ∘ g ∈ tailFamily hKclosed hKconvex T hT m := by
  rcases hh with ⟨n, hn, hmn, f, hf, rfl⟩
  exact ⟨n, hn, hmn, f ∘ g, Generated.comp hf hg, rfl⟩

/-- Tail maps represented in the actual vector space of ambient-valued maps. -/
def ambientTailFamily (m : ℕ) : Set (K → X) :=
  ambientMap '' tailFamily hKclosed hKconvex T hT m

/-- The algebraic convex hull, before pointwise weak closure is taken. -/
def ambientTailConvexHull (m : ℕ) : Set (K → X) :=
  convexHull ℝ (ambientTailFamily hKclosed hKconvex T hT m)

theorem ambientTailFamily_nonempty (m : ℕ) (hm : 1 ≤ m) :
    (ambientTailFamily hKclosed hKconvex T hT m).Nonempty :=
  (tailFamily_nonempty hKclosed hKconvex T hT m hm).image ambientMap

theorem ambientTailFamily_antitone :
    Antitone (ambientTailFamily hKclosed hKconvex T hT) := by
  intro m n hmn
  exact image_mono (tailFamily_antitone hKclosed hKconvex T hT hmn)

theorem ambientTailConvexHull_nonempty (m : ℕ) (hm : 1 ≤ m) :
    (ambientTailConvexHull hKclosed hKconvex T hT m).Nonempty :=
  (ambientTailFamily_nonempty hKclosed hKconvex T hT m hm).convexHull

theorem ambientTailConvexHull_antitone :
    Antitone (ambientTailConvexHull hKclosed hKconvex T hT) := by
  intro m n hmn
  exact convexHull_mono (ambientTailFamily_antitone hKclosed hKconvex T hT hmn)

theorem convex_ambientTailConvexHull (m : ℕ) :
    Convex ℝ (ambientTailConvexHull hKclosed hKconvex T hT m) :=
  convex_convexHull ℝ _

theorem ambientTailFamily_subset_generated (m : ℕ) :
    ambientTailFamily hKclosed hKconvex T hT m ⊆
      ambientGenerated hKclosed hKconvex T hT := by
  rintro f ⟨g, hg, rfl⟩
  exact ⟨g, tailFamily_generated hKclosed hKconvex T hT hg, rfl⟩

theorem ambientTailConvexHull_subset_generated (m : ℕ) :
    ambientTailConvexHull hKclosed hKconvex T hT m ⊆
      ambientGenerated hKclosed hKconvex T hT :=
  convexHull_subset_ambientGenerated
    (ambientTailFamily_subset_generated hKclosed hKconvex T hT m)

/-- Every element of the ambient convex hull is a genuine generated selfmap. -/
theorem ambientTailConvexHull_representative {m : ℕ} {f : K → X}
    (hf : f ∈ ambientTailConvexHull hKclosed hKconvex T hT m) :
    ∃ g : K → K, Generated hKclosed hKconvex T hT g ∧ ambientMap g = f :=
  ambientTailConvexHull_subset_generated hKclosed hKconvex T hT m hf

theorem ambientTailConvexHull_mapsTo {m : ℕ} {f : K → X}
    (hf : f ∈ ambientTailConvexHull hKclosed hKconvex T hT m) (a : K) :
    f a ∈ K := by
  rcases ambientTailConvexHull_representative hKclosed hKconvex T hT hf with
    ⟨g, _, rfl⟩
  exact (g a).property

theorem ambientTailConvexHull_nonexpansive {m : ℕ} {f : K → X}
    (hf : f ∈ ambientTailConvexHull hKclosed hKconvex T hT m) :
    LipschitzWith 1 f := by
  rcases ambientTailConvexHull_representative hKclosed hKconvex T hT hf with
    ⟨g, hg, rfl⟩
  apply LipschitzWith.of_dist_le_mul
  intro a b
  exact (generated_nonexpansive hg).dist_le_mul a b

/-- Precomposition by a fixed selfmap is a linear map on ambient-valued maps. -/
def precompLinear (g : K → K) : (K → X) →ₗ[ℝ] (K → X) where
  toFun f := f ∘ g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ambientTailConvexHull_precomp {m : ℕ} {f : K → X}
    (hf : f ∈ ambientTailConvexHull hKclosed hKconvex T hT m)
    {g : K → K} (hg : Generated hKclosed hKconvex T hT g) :
    f ∘ g ∈ ambientTailConvexHull hKclosed hKconvex T hT m := by
  have hImage : precompLinear g '' ambientTailFamily hKclosed hKconvex T hT m ⊆
      ambientTailFamily hKclosed hKconvex T hT m := by
    rintro k ⟨f', ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h ∘ g, tailFamily_precomp hKclosed hKconvex T hT hh hg, rfl⟩
  have hMem : precompLinear g f ∈ precompLinear g ''
      convexHull ℝ (ambientTailFamily hKclosed hKconvex T hT m) := ⟨f, hf, rfl⟩
  rw [(precompLinear g).image_convexHull] at hMem
  exact convexHull_mono hImage hMem

/-- Composition closure follows from linear precomposition, without a
continuity or affinity assumption on the nonlinear maps. -/
theorem ambientTailConvexHull_comp {m : ℕ} {f g : K → K}
    (hf : ambientMap f ∈ ambientTailConvexHull hKclosed hKconvex T hT m)
    (hg : ambientMap g ∈ ambientTailConvexHull hKclosed hKconvex T hT m) :
    ambientMap (f ∘ g) ∈ ambientTailConvexHull hKclosed hKconvex T hT m := by
  exact ambientTailConvexHull_precomp hKclosed hKconvex T hT hf
    (generated_of_ambient_mem
      (ambientTailConvexHull_subset_generated hKclosed hKconvex T hT m hg))

end ReflexiveFixedPoints

end

end OAI
