import OAI.MeasureTheory.Falconer.Estimates.PathDifferenceBound

namespace OAI

/-! Five-edge sum labels give the two-sided small-sumset refinement used
to pass from projection collisions to a Cartesian product. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

abbrev IntegerFivePath := Σ _b : ℤ, IntegerPath

noncomputable def integerFivePaths (A B G : Finset ℤ) (e : ℤ → ℤ → Prop)
    (a c : ℤ) : Finset IntegerFivePath :=
  (G.filter fun b => e a b).sigma fun b => integerFourPaths A B e b c

def integerFiveSums (a c : ℤ) (p : IntegerFivePath) : ℤ × ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (a+p.1,integerPathSums p.1 c p.2)

theorem integerFiveSums_alternating (a c : ℤ) (p : IntegerFivePath) :
    (integerFiveSums a c p).1-(integerFiveSums a c p).2.1.1+
      (integerFiveSums a c p).2.1.2-(integerFiveSums a c p).2.2.1+
      (integerFiveSums a c p).2.2.2 = a+c := by
  dsimp [integerFiveSums,integerPathSums]
  ring

theorem integerFiveSums_injective (a c : ℤ) : Function.Injective (integerFiveSums a c) := by
  rintro ⟨b,p⟩ ⟨d,q⟩ he
  have hb := congrArg Prod.fst he
  change a+b = a+d at hb
  have hbd : b = d := add_left_cancel hb
  subst d
  have hp := congrArg Prod.snd he
  have hpq : p = q := integerPathSums_injective b c hp
  subst q
  rfl

theorem integerFiveSums_mem (A B C G : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hGB : G ⊆ B) (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C)
    {a c : ℤ} (ha : a ∈ A) (hc : c ∈ B) {p : IntegerFivePath}
    (hp : p ∈ integerFivePaths A B G e a c) :
    integerFiveSums a c p ∈ C ×ˢ ((C ×ˢ C) ×ˢ (C ×ˢ C)) := by
  obtain ⟨hb,hpath⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hbG,he⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_product.mpr ⟨hlabels a ha _ (hGB hbG) he,
    integerPathSums_mem A B C e hlabels (hGB hbG) hc hpath⟩

theorem integerFivePaths_lower (A B G : Finset ℤ) (e : ℤ → ℤ → Prop)
    {a c : ℤ} {m k : ℝ} (hk : 0 ≤ k)
    (hdegree : m ≤ ((G.filter fun b => e a b).card : ℝ))
    (hfour : ∀ b ∈ G, k ≤ ((integerFourPaths A B e b c).card : ℝ)) :
    m*k ≤ ((integerFivePaths A B G e a c).card : ℝ) := by
  calc
    _ ≤ ((G.filter fun b => e a b).card : ℝ)*k := mul_le_mul_of_nonneg_right hdegree hk
    _ = ∑ _b ∈ G.filter (fun b => e a b), k := by simp
    _ ≤ ∑ b ∈ G.filter (fun b => e a b), ((integerFourPaths A B e b c).card : ℝ) :=
      Finset.sum_le_sum fun b hb => hfour b (Finset.mem_filter.mp hb).1
    _ = _ := by simp only [integerFivePaths,Finset.card_sigma,Nat.cast_sum]

theorem five_path_sum_bound (A B C X G : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hXA : X ⊆ A) (hGB : G ⊆ B)
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C)
    {k : ℝ} (hpaths : ∀ a ∈ X, ∀ c ∈ G, k ≤ (integerFivePaths A B G e a c).card) :
    ((X+G).card : ℝ)*k ≤ (C.card : ℝ)^5 := by
  have hex (z : ℤ) : ∃ a c : ℤ, z ∈ X+G → a ∈ X ∧ c ∈ G ∧ a+c = z := by
    by_cases hz : z ∈ X+G
    · obtain ⟨a,ha,c,hc,he⟩ := Finset.mem_add.mp hz
      exact ⟨a,c,fun _ => ⟨ha,hc,he⟩⟩
    · exact ⟨0,0,fun h => False.elim (hz h)⟩
  choose a c hac using hex
  let W := (X+G).sigma fun z => integerFivePaths A B G e (a z) (c z)
  let code : (Σ _z : ℤ, IntegerFivePath) → ℤ × ((ℤ × ℤ) × (ℤ × ℤ)) :=
    fun p => integerFiveSums (a p.1) (c p.1) p.2
  let V : Finset (ℤ × ((ℤ × ℤ) × (ℤ × ℤ))) := C ×ˢ ((C ×ˢ C) ×ˢ (C ×ˢ C))
  have hlower : ((X+G).card : ℝ)*k ≤ (W.card : ℝ) := by
    calc
      _ = ∑ _z ∈ X+G, k := by simp
      _ ≤ ∑ z ∈ X+G, ((integerFivePaths A B G e (a z) (c z)).card : ℝ) :=
        Finset.sum_le_sum fun z hz => hpaths _ (hac z hz).1 _ (hac z hz).2.1
      _ = _ := by simp only [W,Finset.card_sigma,Nat.cast_sum]
  have hmap : Set.MapsTo code (W : Set (Σ _z : ℤ, IntegerFivePath))
      (V : Set (ℤ × ((ℤ × ℤ) × (ℤ × ℤ)))) := by
    intro p hp
    obtain ⟨hz,hp⟩ := Finset.mem_sigma.mp hp
    exact integerFiveSums_mem A B C G e hGB hlabels (hXA (hac p.1 hz).1)
      (hGB (hac p.1 hz).2.1) hp
  have hinj : Set.InjOn code (W : Set (Σ _z : ℤ, IntegerFivePath)) := by
    rintro ⟨z,p⟩ hp ⟨w,q⟩ hq he
    have hz := (Finset.mem_sigma.mp hp).1
    have hw := (Finset.mem_sigma.mp hq).1
    have hd := congrArg (fun t : ℤ × ((ℤ × ℤ) × (ℤ × ℤ)) =>
      t.1-t.2.1.1+t.2.1.2-t.2.2.1+t.2.2.2) he
    change (integerFiveSums (a z) (c z) p).1-(integerFiveSums (a z) (c z) p).2.1.1+
        (integerFiveSums (a z) (c z) p).2.1.2-(integerFiveSums (a z) (c z) p).2.2.1+
        (integerFiveSums (a z) (c z) p).2.2.2 =
      (integerFiveSums (a w) (c w) q).1-(integerFiveSums (a w) (c w) q).2.1.1+
        (integerFiveSums (a w) (c w) q).2.1.2-(integerFiveSums (a w) (c w) q).2.2.1+
        (integerFiveSums (a w) (c w) q).2.2.2 at hd
    rw [integerFiveSums_alternating,integerFiveSums_alternating,
      (hac z hz).2.2,(hac w hw).2.2] at hd
    subst w
    have hpq : p = q := integerFiveSums_injective (a z) (c z) he
    subst q
    rfl
  have hc := Finset.card_le_card_of_injOn code hmap hinj
  dsimp [V] at hc
  simp only [Finset.card_product] at hc
  have hu : (W.card : ℝ) ≤ (C.card : ℝ)^5 := by
    have hc' : (W.card : ℝ) ≤ (C.card : ℝ)*
        (((C.card : ℝ)*(C.card : ℝ))*((C.card : ℝ)*(C.card : ℝ))) := by exact_mod_cast hc
    exact hc'.trans_eq (by ring)
  exact hlower.trans hu

end Falconer

end OAI
