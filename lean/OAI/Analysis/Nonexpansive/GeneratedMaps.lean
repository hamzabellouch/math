import OAI.Analysis.Nonexpansive.Resolvents

namespace OAI

/-!
# The finitely generated family of nonexpansive selfmaps

The family consists of actual maps of the norm subtype. Its constructors
are identity, resolvents, composition, and binary convex combinations.
Its image in the ambient module of maps to `X` is convex, and the finite
convex-combination theorem below proves closure under every finite family.
Thus the binary presentation also gives closure under finite convex combinations. All displacement constants are proved from the derivation.
-/

noncomputable section

open Set
open scoped BigOperators

namespace ReflexiveFixedPoints

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}

/-- The ambient representative of an actual selfmap. -/
def ambientMap (g : K → K) : K → X := fun a => g a

@[simp] theorem ambientMap_apply {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Set X} (g : K → K) (a : K) :
    ambientMap g a = (g a : X) := rfl

theorem ambientMap_injective {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Set X} : Function.Injective (ambientMap (K := K)) := by
  intro f g h
  funext a
  apply Subtype.ext
  exact congrFun h a

/-- A binary convex combination, with membership proved in the ambient space. -/
def convexMix (hKconvex : Convex ℝ K) (f g : K → K)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : K → K :=
  fun x => ⟨a • (f x : X) + b • (g x : X),
    hKconvex (f x).property (g x).property ha hb hab⟩

@[simp] theorem convexMix_val (hKconvex : Convex ℝ K) (f g : K → K)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (x : K) :
    (convexMix hKconvex f g a b ha hb hab x : X) =
      a • (f x : X) + b • (g x : X) := rfl

theorem convexMix_nonexpansive (hKconvex : Convex ℝ K) (f g : K → K)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g) :
    LipschitzWith 1 (convexMix hKconvex f g a b ha hb hab) := by
  apply LipschitzWith.mk_one
  intro x y
  have hfx : ‖(f x : X) - (f y : X)‖ ≤ ‖(x : X) - (y : X)‖ := by
    simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      using hf.dist_le_mul x y
  have hgx : ‖(g x : X) - (g y : X)‖ ≤ ‖(x : X) - (y : X)‖ := by
    simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      using hg.dist_le_mul x y
  change dist (a • (f x : X) + b • (g x : X))
      (a • (f y : X) + b • (g y : X)) ≤ dist (x : X) (y : X)
  simp only [dist_eq_norm]
  calc
    ‖(a • (f x : X) + b • (g x : X)) -
        (a • (f y : X) + b • (g y : X))‖ =
        ‖a • ((f x : X) - (f y : X)) +
          b • ((g x : X) - (g y : X))‖ := by
      rw [smul_sub, smul_sub, add_sub_add_comm]
    _ ≤ ‖a • ((f x : X) - (f y : X))‖ +
        ‖b • ((g x : X) - (g y : X))‖ := norm_add_le _ _
    _ = a * ‖(f x : X) - (f y : X)‖ +
        b * ‖(g x : X) - (g y : X)‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * ‖(x : X) - (y : X)‖ + b * ‖(x : X) - (y : X)‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hfx ha)
        (mul_le_mul_of_nonneg_left hgx hb)
    _ = ‖(x : X) - (y : X)‖ := by rw [← add_mul, hab, one_mul]

theorem convexMix_displacement (hKconvex : Convex ℝ K) (T f g : K → K)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (cf cg : ℝ)
    (hf : ∀ x : K, ‖(f x : X) - (x : X)‖ ≤ cf * ‖(T x : X) - (x : X)‖)
    (hg : ∀ x : K, ‖(g x : X) - (x : X)‖ ≤ cg * ‖(T x : X) - (x : X)‖)
    (x : K) :
    ‖(convexMix hKconvex f g a b ha hb hab x : X) - (x : X)‖ ≤
      (a * cf + b * cg) * ‖(T x : X) - (x : X)‖ := by
  change ‖a • (f x : X) + b • (g x : X) - (x : X)‖ ≤
    (a * cf + b * cg) * ‖(T x : X) - (x : X)‖
  have hsplit : a • (f x : X) + b • (g x : X) - (x : X) =
      a • ((f x : X) - (x : X)) + b • ((g x : X) - (x : X)) := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
  rw [hsplit]
  calc
    ‖a • ((f x : X) - (x : X)) + b • ((g x : X) - (x : X))‖ ≤
        ‖a • ((f x : X) - (x : X))‖ + ‖b • ((g x : X) - (x : X))‖ :=
      norm_add_le _ _
    _ = a * ‖(f x : X) - (x : X)‖ + b * ‖(g x : X) - (x : X)‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * (cf * ‖(T x : X) - (x : X)‖) +
        b * (cg * ‖(T x : X) - (x : X)‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (hf x) ha)
        (mul_le_mul_of_nonneg_left (hg x) hb)
    _ = (a * cf + b * cg) * ‖(T x : X) - (x : X)‖ := by
      rw [add_mul, mul_assoc, mul_assoc]

/-- Right composition is precomposition of the pointwise combination. -/
theorem convexMix_comp_right (hKconvex : Convex ℝ K) (f g k : K → K)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    convexMix hKconvex f g a b ha hb hab ∘ k =
      convexMix hKconvex (f ∘ k) (g ∘ k) a b ha hb hab := rfl

/-- An actual finite pointwise convex combination, for arbitrary finite index universes. -/
def convexCombination (hKconvex : Convex ℝ K) {ι : Type v} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (g : ι → K → K) : K → K :=
  fun a => ⟨∑ i, w i • (g i a : X),
    hKconvex.sum_mem (fun i _ => hw i) hsum (fun i _ => (g i a).property)⟩

@[simp] theorem convexCombination_val (hKconvex : Convex ℝ K)
    {ι : Type v} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (g : ι → K → K) (a : K) :
    (convexCombination hKconvex w hw hsum g a : X) =
      ∑ i, w i • (g i a : X) := rfl

theorem ambientMap_convexCombination (hKconvex : Convex ℝ K)
    {ι : Type v} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (g : ι → K → K) :
    ambientMap (convexCombination hKconvex w hw hsum g) =
      ∑ i, w i • ambientMap (g i) := by
  funext a
  simp only [ambientMap_apply, convexCombination_val, Finset.sum_apply, Pi.smul_apply]

theorem convexCombination_comp_right (hKconvex : Convex ℝ K)
    {ι : Type v} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (g : ι → K → K) (k : K → K) :
    convexCombination hKconvex w hw hsum g ∘ k =
      convexCombination hKconvex w hw hsum (fun i => g i ∘ k) := rfl

variable [CompleteSpace X]

/-- The actual family generated using finitely many constructors. -/
inductive Generated (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) : (K → K) → Prop where
  | id : Generated hKclosed hKconvex T hT id
  | resolvent (n : ℕ) (hn : 1 ≤ n) :
      Generated hKclosed hKconvex T hT
        (ReflexiveFixedPoints.resolvent hKclosed hKconvex T hT n hn)
  | comp {f g : K → K} (hf : Generated hKclosed hKconvex T hT f)
      (hg : Generated hKclosed hKconvex T hT g) :
      Generated hKclosed hKconvex T hT (f ∘ g)
  | mix {f g : K → K} (hf : Generated hKclosed hKconvex T hT f)
      (hg : Generated hKclosed hKconvex T hT g)
      (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
      Generated hKclosed hKconvex T hT (convexMix hKconvex f g a b ha hb hab)

variable {hKclosed : IsClosed K} {hKconvex : Convex ℝ K}
variable {T : K → K} {hT : LipschitzWith 1 T}

theorem generated_nonexpansive {g : K → K}
    (hg : Generated hKclosed hKconvex T hT g) : LipschitzWith 1 g := by
  induction hg with
  | id => exact LipschitzWith.id
  | resolvent n hn => exact resolvent_nonexpansive hKclosed hKconvex T hT n hn
  | comp hf hg ihf ihg => simpa only [one_mul] using ihf.comp ihg
  | @mix f g hf hg a b ha hb hab ihf ihg =>
      exact convexMix_nonexpansive hKconvex f g a b ha hb hab ihf ihg

/-- Every generated map has a finite nonnegative displacement constant. -/
theorem generated_displacement {g : K → K}
    (hg : Generated hKclosed hKconvex T hT g) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : K,
      ‖(g a : X) - (a : X)‖ ≤ c * ‖(T a : X) - (a : X)‖ := by
  induction hg with
  | id => exact ⟨0, le_rfl, fun a => by simp⟩
  | resolvent n hn =>
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact ⟨(n : ℝ) - 1, sub_nonneg.mpr hn',
        resolvent_displacement_le hKclosed hKconvex T hT n hn⟩
  | @comp f g hf hg ihf ihg =>
      obtain ⟨cf, hcf, hdf⟩ := ihf
      obtain ⟨cg, hcg, hdg⟩ := ihg
      refine ⟨cg + cf, add_nonneg hcg hcf, ?_⟩
      intro a
      have hfg : ‖(f (g a) : X) - (f a : X)‖ ≤ ‖(g a : X) - (a : X)‖ := by
        simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
          using (generated_nonexpansive hf).dist_le_mul (g a) a
      change ‖(f (g a) : X) - (a : X)‖ ≤ (cg + cf) * ‖(T a : X) - (a : X)‖
      calc
        ‖(f (g a) : X) - (a : X)‖ ≤
            ‖(f (g a) : X) - (f a : X)‖ + ‖(f a : X) - (a : X)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖(g a : X) - (a : X)‖ + ‖(f a : X) - (a : X)‖ :=
          add_le_add_left hfg _
        _ ≤ cg * ‖(T a : X) - (a : X)‖ + cf * ‖(T a : X) - (a : X)‖ :=
          add_le_add (hdg a) (hdf a)
        _ = (cg + cf) * ‖(T a : X) - (a : X)‖ := (add_mul _ _ _).symm
  | @mix f g hf hg a b ha hb hab ihf ihg =>
      obtain ⟨cf, hcf, hdf⟩ := ihf
      obtain ⟨cg, hcg, hdg⟩ := ihg
      exact ⟨a * cf + b * cg, add_nonneg (mul_nonneg ha hcf) (mul_nonneg hb hcg),
        convexMix_displacement hKconvex T f g a b ha hb hab cf cg hdf hdg⟩

/-- The ambient function-space image of the generated actual selfmaps. -/
def ambientGenerated (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) : Set (K → X) :=
  ambientMap '' {g | Generated hKclosed hKconvex T hT g}

theorem ambientMap_mem_ambientGenerated {g : K → K}
    (hg : Generated hKclosed hKconvex T hT g) :
    ambientMap g ∈ ambientGenerated hKclosed hKconvex T hT := ⟨g, hg, rfl⟩

theorem generated_of_ambient_mem {g : K → K}
    (hg : ambientMap g ∈ ambientGenerated hKclosed hKconvex T hT) :
    Generated hKclosed hKconvex T hT g := by
  obtain ⟨f, hf, hfg⟩ := hg
  have h : f = g := ambientMap_injective hfg
  exact h ▸ hf

theorem ambientMap_mem_ambientGenerated_iff {g : K → K} :
    ambientMap g ∈ ambientGenerated hKclosed hKconvex T hT ↔
      Generated hKclosed hKconvex T hT g :=
  ⟨generated_of_ambient_mem, ambientMap_mem_ambientGenerated⟩

theorem convex_ambientGenerated (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) :
    Convex ℝ (ambientGenerated hKclosed hKconvex T hT) := by
  rintro f ⟨f', hf, rfl⟩ g ⟨g', hg, rfl⟩ a b ha hb hab
  exact ⟨convexMix hKconvex f' g' a b ha hb hab,
    Generated.mix hf hg a b ha hb hab, rfl⟩

theorem convexHull_subset_ambientGenerated {S : Set (K → X)}
    (hS : S ⊆ ambientGenerated hKclosed hKconvex T hT) :
    convexHull ℝ S ⊆ ambientGenerated hKclosed hKconvex T hT :=
  convexHull_min hS (convex_ambientGenerated hKclosed hKconvex T hT)

/-- Binary generation is closed under every finite pointwise convex combination. -/
theorem generated_convexCombination {ι : Type v} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (g : ι → K → K) (hg : ∀ i, Generated hKclosed hKconvex T hT (g i)) :
    Generated hKclosed hKconvex T hT (convexCombination hKconvex w hw hsum g) := by
  apply generated_of_ambient_mem
  rw [ambientMap_convexCombination]
  exact (convex_ambientGenerated hKclosed hKconvex T hT).sum_mem
    (fun i _ => hw i) hsum (fun i _ => ambientMap_mem_ambientGenerated (hg i))

end ReflexiveFixedPoints

end

end OAI
