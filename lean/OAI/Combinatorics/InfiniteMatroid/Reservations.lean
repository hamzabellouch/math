import OAI.Combinatorics.InfiniteMatroid.DensityIdeal

namespace OAI

section
open Set Filter Finset
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

def liftD (X : Set D) : Set E0 := Prod.fst ⁻¹' X

lemma density_liftD (X : Set D) (m : ℕ) : density (liftD X) m = dDensity X m := by
  classical
  have he : traceFinset (wBlock m) (liftD X) = (traceFinset (dBlock m) X).product univ := by
    ext x
    simp [wBlock, liftD]
  rw [density, finiteDensity, he]
  simp [dDensity, finiteDensity, wBlock]
  ring

lemma small_liftD_iff (X : Set D) : Small (liftD X) ↔ DSmall X := by
  have he : density (liftD X) = dDensity X := funext (density_liftD X)
  rw [Small, DSmall, he]

def DCell (t : CIndex) (k : Bool) : Set D :=
  {x | x.2 (prefixString (columnString (tagA t)) x.1) = false ∧
    x.2 (prefixString (columnString (tagB t)) x.1) = k}
def HCell (t : CIndex) (k : Bool) : Set E0 := liftD (DCell t k)

lemma dCell_subset_Acompl (t : CIndex) (k : Bool) : DCell t k ⊆ (AColumn t)ᶜ := by
  intro x hx ha
  exact Bool.false_ne_true (hx.1.symm.trans ha)

lemma hCell_disjoint (t : CIndex) : Disjoint (HCell t false) (HCell t true) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Bool.false_ne_true (hx.2.symm.trans hy.2)

lemma card_avoid_cells {A : Type} [Fintype A] (k : A → Bool) :
    Nat.card {v : A × Bool → Bool // ∀ t, ¬ (v (t,false) = false ∧ v (t,true) = k t)} =
      3 ^ Fintype.card A := by
  classical
  let e := ((Equiv.curry A Bool Bool).subtypeEquiv
    (p := fun v ↦ ∀ t, ¬(v (t,false) = false ∧ v (t,true) = k t))
    (q := fun v ↦ ∀ t, ¬(v t false = false ∧ v t true = k t)) (fun _ ↦ Iff.rfl)).trans
      (Equiv.subtypePiEquivPi (α := A) (β := fun _ ↦ Bool → Bool)
        (p := fun t v ↦ ¬(v false = false ∧ v true = k t)))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi]
  have hc (b : Bool) : Fintype.card {v : Bool → Bool // ¬(v false = false ∧ v true = b)} = 3 := by
    cases b <;> decide
  simp only [hc, Finset.prod_const, Finset.card_univ]

def avoidCells (F : Finset CIndex) (k : F → Bool) : Set D :=
  {x | ∀ t : F, x ∉ DCell t (k t)}

lemma eventually_avoidCells (F : Finset CIndex) (k : F → Bool) :
    ∀ᶠ m in atTop, dDensity (avoidCells F k) m = (3/4 : ℝ)^F.card := by
  classical
  let e : F × Bool ↪ ColumnTag := ⟨fun p ↦ if p.2 then tagB p.1 else tagA p.1, by
    rintro ⟨t,b⟩ ⟨s,c⟩ he
    have ht : t = s := by
      apply Subtype.ext
      cases b <;> cases c <;> exact congrArg Prod.fst he
    subst s
    congr 1
    cases b <;> cases c <;> simp_all [tagA,tagB]⟩
  have h := columns_uniform e (fun v ↦ ∀ t : F, ¬(v (t,false) = false ∧ v (t,true) = k t))
  rw [card_avoid_cells] at h
  filter_upwards [h] with m hm
  have he : {x : D | ∀ t : F, ¬(x.2 (prefixString (columnString (e (t,false))) x.1) = false ∧
      x.2 (prefixString (columnString (e (t,true))) x.1) = k t)} = avoidCells F k := rfl
  rw [he] at hm
  rw [hm]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_comm F.card 2, pow_mul, div_pow]
  norm_num

lemma eventually_avoidHCells (F : Finset CIndex) (k : F → Bool) :
    ∀ᶠ m in atTop, density {x | ∀ t : F, x ∉ HCell t (k t)} m = (3/4 : ℝ)^F.card := by
  have h := eventually_avoidCells F k
  filter_upwards [h] with m hm
  change density (liftD (avoidCells F k)) m = _
  rwa [density_liftD]

lemma small_biUnion {ι : Type} (F : Finset ι) (X : ι → Set E0) (hX : ∀ t ∈ F, Small (X t)) :
    Small (⋃ t ∈ F, X t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using small_empty
  | @insert t F ht ih =>
    simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using
      small_union (hX t (Finset.mem_insert_self _ _))
        (ih (fun s hs ↦ hX s (Finset.mem_insert_of_mem hs)))

lemma bad_cells_finite {S : Set E0} (hS : ¬ Small S) :
    {t | ∃ k : Bool, Small (S ∩ HCell t k)}.Finite := by
  classical
  by_contra hinf
  apply hS
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun m ↦ ha.trans_le (finiteDensity_nonneg _ _)
  · intro ε hε
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4)
      (by norm_num : (3/4:ℝ) < 1)).eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨q,hq⟩ := hp.exists
    obtain ⟨F,hF,hFfin,hFcard⟩ := Set.Infinite.exists_subset_ncard_eq hinf q
    let Q := hFfin.toFinset
    have hchoose : ∀ t : Q, ∃ k : Bool, Small (S ∩ HCell t k) := by
      intro t
      exact hF (hFfin.mem_toFinset.mp t.property)
    choose k hk using hchoose
    let N := ⋃ t : Q, S ∩ HCell t (k t)
    have hN : Small N := by
      have := small_biUnion (Finset.univ : Finset Q) (fun t ↦ S ∩ HCell t (k t)) (fun t _ ↦ hk t)
      simpa only [Finset.mem_univ, iUnion_true] using this
    have hsub : S ⊆ N ∪ {x | ∀ t : Q, x ∉ HCell t (k t)} := by
      intro x hx
      by_cases hn : x ∈ N
      · exact Or.inl hn
      · right
        intro t ht
        exact hn (mem_iUnion.mpr ⟨t,hx,ht⟩)
    have hQ : Q.card = q := (Set.ncard_eq_toFinset_card F hFfin).symm.trans hFcard
    filter_upwards [eventually_avoidHCells Q k, hN.eventually (gt_mem_nhds (half_pos hε))] with m hm hn
    have hle := (finiteDensity_mono (wBlock m) hsub).trans
      (finiteDensity_union_le (wBlock m) N {x | ∀ t : Q, x ∉ HCell t (k t)})
    change density S m ≤ density N m + density _ m at hle
    rw [hm, hQ] at hle
    linarith

lemma simultaneous_reservations {ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum)
    (S : ι → Set E0) (hS : ∀ i, ¬ Small (S i)) :
    ∃ t : CIndex, ∀ i k, ¬ Small (S i ∩ HCell t k) := by
  obtain ⟨t,ht⟩ := exists_avoid_finite_family hι
    (fun i ↦ {t | ∃ k : Bool, Small (S i ∩ HCell t k)}) (fun i ↦ bad_cells_finite (hS i))
  exact ⟨t,fun i k h ↦ ht i ⟨k,h⟩⟩

end InfiniteMatroidCounterexample
end

end OAI
