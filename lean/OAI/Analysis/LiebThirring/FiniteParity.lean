import OAI.Analysis.LiebThirring.FlagGeometry

namespace OAI

universe u40 u41 u42 u43 u44 u45 u46 u47 u48 u49 u50 u51 u52 u53 u54 u55 u56 u57 u58 u59 u60 u61 u62 u63 u64 u65 u66 u67

noncomputable section
open Finset


/-! Finite parity for the PL continuation argument.
The argument constructs continuation without assuming a topological degree theorem. -/
noncomputable section
open Finset
namespace SharpLiebThirring.PLParity

/-- Endpoints of a line meeting a simplex: in general position either no facet,
or exactly two facets, are met. The roots `r` are the facet crossing parameters. -/
lemma affine_constraints_endpoints {ι : Type u40} [Fintype ι] [DecidableEq ι]
    (b r : ι → ℝ) (hb : ∀ i, b i ≠ 0) (hr : Function.Injective r)
    (hpos : ∃ i, 0 < b i) (hneg : ∃ i, b i < 0) :
    ∃ i j : ι, i ≠ j ∧
      ({k | ∀ l, 0 ≤ b l * (r k - r l)} : Finset ι) =
        if r i < r j then {i, j} else ∅ := by
  classical
  have hp : (univ.filter (fun i ↦ 0 < b i)).Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, by simp [hi]⟩
  have hn : (univ.filter (fun i ↦ b i < 0)).Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, by simp [hi]⟩
  obtain ⟨i, hi, hmax⟩ := exists_max_image (univ.filter (fun i ↦ 0 < b i)) r hp
  obtain ⟨j, hj, hmin⟩ := exists_min_image (univ.filter (fun i ↦ b i < 0)) r hn
  simp only [mem_filter, mem_univ, true_and] at hi hj hmax hmin
  have hij : i ≠ j := by rintro rfl; linarith
  have hrij : r i ≠ r j := fun h ↦ hij (hr h)
  refine ⟨i, j, hij, ?_⟩
  ext k
  simp only [mem_filter, mem_univ, true_and]
  by_cases hlt : r i < r j
  · rw [ite_eq_left hlt]
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hk
      have hleft : r i ≤ r k := by
        have hh := (mul_nonneg_iff_of_pos_left hi).mp (hk i)
        linarith
      have hright : r k ≤ r j := by
        have hh := nonpos_of_mul_nonneg_right (hk j) hj
        linarith
      rcases lt_or_gt_of_ne (hb k) with hkn | hkp
      · right
        have hh := hmin k hkn
        exact hr (le_antisymm hright hh)
      · left
        have hh := hmax k hkp
        exact hr (le_antisymm hh hleft)
    · rintro (rfl | rfl) l
      · rcases lt_or_gt_of_ne (hb l) with hln | hlp
        · apply mul_nonneg_of_nonpos_of_nonpos hln.le
          have hh := hmin l hln
          linarith
        · exact mul_nonneg hlp.le (sub_nonneg.mpr (hmax l hlp))
      · rcases lt_or_gt_of_ne (hb l) with hln | hlp
        · exact mul_nonneg_of_nonpos_of_nonpos hln.le (sub_nonpos.mpr (hmin l hln))
        · apply mul_nonneg hlp.le
          have hh := hmax l hlp
          linarith
  · rw [ite_eq_right hlt]
    simp only [Finset.notMem_empty, iff_false]
    intro hk
    have hleft : r i ≤ r k := by
      have hh := (mul_nonneg_iff_of_pos_left hi).mp (hk i)
      linarith
    have hright : r k ≤ r j := by
      have hh := nonpos_of_mul_nonneg_right (hk j) hj
      linarith
    exact hrij (le_antisymm (hleft.trans hright) (le_of_not_gt hlt))

lemma even_affine_constraints_endpoints {ι : Type u41} [Fintype ι] [DecidableEq ι]
    (b r : ι → ℝ) (hb : ∀ i, b i ≠ 0) (hr : Function.Injective r)
    (hpos : ∃ i, 0 < b i) (hneg : ∃ i, b i < 0) :
    Even ({k | ∀ l, 0 ≤ b l * (r k - r l)} : Finset ι).card := by
  obtain ⟨i, j, hij, he⟩ := affine_constraints_endpoints b r hb hr hpos hneg
  rw [he]
  split_ifs <;> simp [hij]


section AffineFiber
attribute [local instance] Classical.propDecidable
variable {ι : Type u42} {V : Type u43} [Fintype ι]
  [AddCommGroup V] [Module ℝ V]

/-- Total affine weights and their vector sum. -/
def augmentedMap (v : ι → V) : (ι → ℝ) →ₗ[ℝ] ℝ × V where
  toFun w := (∑ i, w i, ∑ i, w i • v i)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, Finset.smul_sum, smul_smul]

@[simp] lemma augmentedMap_apply (v : ι → V) (w : ι → ℝ) :
    augmentedMap v w = (∑ i, w i, ∑ i, w i • v i) := rfl

/-- A facet is selected when its affine image contains zero. -/
def facetHit (v : ι → V) (i : ι) : Prop :=
  ∃ w : ι → ℝ, augmentedMap v w = (1, 0) ∧ w i = 0 ∧ ∀ j, 0 ≤ w j

lemma facetHit_congr (v u : ι → V) (i : ι) (he : ∀ j, j ≠ i → v j = u j) :
    facetHit v i ↔ facetHit u i := by
  have hs (w : ι → ℝ) (hw : w i = 0) : ∑ j, w j • v j = ∑ j, w j • u j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · simp only [hji, hw, zero_smul]
    · rw [he j hji]
  constructor <;> rintro ⟨w, hw, hi, hn⟩ <;> refine ⟨w, ?_, hi, hn⟩
  · apply Prod.ext
    · simpa only [augmentedMap_apply] using congrArg Prod.fst hw
    · change ∑ j, w j • u j = 0
      rw [← hs w hi]
      exact congrArg Prod.snd hw
  · apply Prod.ext
    · simpa only [augmentedMap_apply] using congrArg Prod.fst hw
    · change ∑ j, w j • v j = 0
      rw [hs w hi]
      exact congrArg Prod.snd hw

lemma facetHit_linearEquiv (v : ι → V) (A : V ≃ₗ[ℝ] V) (i : ι) :
    facetHit (fun j ↦ A (v j)) i ↔ facetHit v i := by
  constructor <;> rintro ⟨w, hw, hi, hn⟩ <;> refine ⟨w, ?_, hi, hn⟩
  · apply Prod.ext
    · simpa only [augmentedMap_apply] using congrArg Prod.fst hw
    · change ∑ j, w j • v j = 0
      apply A.injective
      simpa only [augmentedMap_apply, map_sum, map_smul, map_zero] using congrArg Prod.snd hw
  · apply Prod.ext
    · simpa only [augmentedMap_apply] using congrArg Prod.fst hw
    · change ∑ j, w j • A (v j) = 0
      have hh := congrArg A (congrArg Prod.snd hw)
      simpa only [augmentedMap_apply, map_sum, map_smul, map_zero] using hh

lemma kernel_line_parameterization (v : ι → V)
    (hdim : Module.finrank ℝ (LinearMap.ker (augmentedMap v)) = 1)
    {b : ι → ℝ} (hb : b ∈ LinearMap.ker (augmentedMap v)) (hb0 : b ≠ 0)
    {a w : ι → ℝ} (ha : augmentedMap v a = (1, 0))
    (hw : augmentedMap v w = (1, 0)) :
    ∃ t : ℝ, w = a + t • b := by
  have hwb : w - a ∈ LinearMap.ker (augmentedMap v) := by
    rw [LinearMap.mem_ker, map_sub, hw, ha, sub_self]
  obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hdim
    (x := (⟨b, hb⟩ : LinearMap.ker (augmentedMap v)))
    (by simpa using hb0) (⟨w - a, hwb⟩ : LinearMap.ker (augmentedMap v))
  refine ⟨t, ?_⟩
  have h := congrArg Subtype.val ht
  change t • b = w - a at h
  rw [h, add_sub_cancel]

/-- Parity of facet hits for a generic affine map from a (d+1)-simplex to
R^d. The algebraic general-position conditions are separated from the
finite counting argument so they can be supplied by generic vertex choices. -/
lemma even_facetHit_of_kernel_line (v : ι → V)
    (hsur : Function.Surjective (augmentedMap v))
    (hdim : Module.finrank ℝ (LinearMap.ker (augmentedMap v)) = 1)
    (hcoord : ∀ b : ι → ℝ, augmentedMap v b = 0 → b ≠ 0 → ∀ i, b i ≠ 0)
    (hpair : ∀ w : ι → ℝ, augmentedMap v w = (1, 0) →
      ∀ i j, w i = 0 → w j = 0 → i = j) :
    Even ({i | facetHit v i} : Finset ι).card := by
  classical
  obtain ⟨a, ha⟩ := hsur (1, 0)
  have hkne : LinearMap.ker (augmentedMap v) ≠ ⊥ := by
    intro h
    rw [h] at hdim
    simp at hdim
  obtain ⟨b, hb, hb0⟩ := (LinearMap.ker (augmentedMap v)).ne_bot_iff.mp hkne
  have hbA : augmentedMap v b = 0 := hb
  have hbi := hcoord b hbA hb0
  have hbSum : ∑ i, b i = 0 := congrArg Prod.fst hbA
  have hpos : ∃ i, 0 < b i := by
    by_contra! h
    have hh := (Finset.sum_eq_zero_iff_of_nonpos (by simpa using h)).mp hbSum
    apply hb0
    ext i
    exact hh i (mem_univ i)
  have hneg : ∃ i, b i < 0 := by
    by_contra! h
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (by simpa using h)).mp hbSum
    apply hb0
    ext i
    exact hh i (mem_univ i)
  let r : ι → ℝ := fun i ↦ -a i / b i
  have hroot (i : ι) : a i + r i * b i = 0 := by
    dsimp [r]
    rw [div_mul_cancel₀ _ (hbi i)]
    ring
  have hr : Function.Injective r := by
    intro i j hij
    apply hpair (a + r i • b)
    · rw [map_add, map_smul, hbA, smul_zero, add_zero, ha]
    · exact hroot i
    · change a j + r i * b j = 0
      rw [hij]
      exact hroot j
  have heq : ({i | facetHit v i} : Finset ι) =
      ({i | ∀ j, 0 ≤ b j * (r i - r j)} : Finset ι) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, hwi, hwj⟩
      obtain ⟨t, rfl⟩ := kernel_line_parameterization v hdim hb hb0 ha hw
      have ht : t = r i := by
        change a i + t * b i = 0 at hwi
        apply (mul_right_cancel₀ (hbi i))
        linarith [hroot i]
      subst t
      intro j
      have hj := hwj j
      change 0 ≤ a j + r i * b j at hj
      nlinarith [hroot j]
    · intro hi
      refine ⟨a + r i • b, ?_, hroot i, ?_⟩
      · rw [map_add, map_smul, hbA, smul_zero, add_zero, ha]
      · intro j
        change 0 ≤ a j + r i * b j
        nlinarith [hi j, hroot j]
  rw [heq]
  exact even_affine_constraints_endpoints b r hbi hr hpos hneg


lemma sum_subtype_eq_of_zero {M : Type u44} [AddCommMonoid M]
    (P : ι → Prop) [DecidablePred P] (f : ι → M) (h : ∀ i, ¬ P i → f i = 0) :
    (∑ i : {i // P i}, f i) = ∑ i, f i := by
  have h0 : (∑ i : {i // ¬ P i}, f i) = 0 :=
    Finset.sum_eq_zero (fun i _ ↦ h i i.prop)
  simpa only [h0, add_zero] using Fintype.sum_subtype_add_sum_subtype P f

lemma augmentedMap_single (v : ι → V) (i : ι) :
    augmentedMap v (Pi.single i 1) = (1, v i) := by
  classical
  simp [augmentedMap, Pi.single_apply, ite_smul]

lemma augmented_kernel_nonzero_coordinates (v : ι → V)
    (hgen : ∀ i : ι, LinearIndependent ℝ (fun j : {j // j ≠ i} ↦ ((1 : ℝ), v j)))
    (b : ι → ℝ) (hb : augmentedMap v b = 0) (hb0 : b ≠ 0) :
    ∀ i, b i ≠ 0 := by
  intro i hi
  have hs : (∑ j : {j // j ≠ i}, b j • ((1 : ℝ), v j)) = 0 := by
    calc
      _ = ∑ j, b j • ((1 : ℝ), v j) := sum_subtype_eq_of_zero (fun j ↦ j ≠ i) (fun j ↦ b j • ((1 : ℝ), v j)) (by
      intro j hj
      have : j = i := by simpa using hj
      simp [this, hi])
      _ = 0 := by
        simpa only [augmentedMap_apply, Prod.smul_mk, smul_eq_mul, mul_one, ← prod_mk_sum] using hb
  have hz := Fintype.linearIndependent_iff.mp (hgen i) (fun j ↦ b j) hs
  apply hb0
  ext j
  by_cases hj : j = i
  · simpa [hj] using hi
  · exact hz ⟨j, hj⟩

lemma augmented_nonzero_two_coordinates (v : ι → V)
    (hgen : ∀ i j : ι, i ≠ j →
      LinearIndependent ℝ (fun k : {k // k ≠ i ∧ k ≠ j} ↦ v k))
    (w : ι → ℝ) (hw : augmentedMap v w = (1, 0))
    (i j : ι) (hi : w i = 0) (hj : w j = 0) : i = j := by
  by_contra hij
  have hs : (∑ k : {k // k ≠ i ∧ k ≠ j}, w k • v k) = 0 := by
    calc
      _ = ∑ k, w k • v k := sum_subtype_eq_of_zero (fun k ↦ k ≠ i ∧ k ≠ j) (fun k ↦ w k • v k) (by
      intro k hk
      by_cases hki : k = i
      · simp [hki, hi]
      · have hkj : k = j := by aesop
        simp [hkj, hj])
      _ = 0 := congrArg Prod.snd hw
  have hz := Fintype.linearIndependent_iff.mp (hgen i j hij) (fun k ↦ w k) hs
  have hw0 : w = 0 := by
    ext k
    by_cases hki : k = i
    · simpa [hki] using hi
    by_cases hkj : k = j
    · simpa [hkj] using hj
    exact hz ⟨k, hki, hkj⟩
  simpa [hw0] using congrArg Prod.fst hw

lemma facetHit_positive (v : ι → V)
    (hgen : ∀ i j : ι, i ≠ j →
      LinearIndependent ℝ (fun k : {k // k ≠ i ∧ k ≠ j} ↦ v k))
    (i : ι) (hi : facetHit v i) :
    ∃ w : ι → ℝ, augmentedMap v w = (1, 0) ∧ w i = 0 ∧
      (∀ j, 0 ≤ w j) ∧ ∀ j, j ≠ i → 0 < w j := by
  obtain ⟨w, hw, hwi, hn⟩ := hi
  refine ⟨w, hw, hwi, hn, ?_⟩
  intro j hji
  refine lt_of_le_of_ne (hn j) ?_
  intro h
  exact hji ((augmented_nonzero_two_coordinates v hgen w hw i j hwi h.symm).symm)

lemma augmentedMap_surjective [FiniteDimensional ℝ V] (v : ι → V)
    (hcard : Fintype.card ι = Module.finrank ℝ V + 2)
    (hgen : ∀ i : ι, LinearIndependent ℝ (fun j : {j // j ≠ i} ↦ ((1 : ℝ), v j))) :
    Function.Surjective (augmentedMap v) := by
  classical
  have hcpos : 0 < Fintype.card ι := by omega
  let : Nonempty ι := Fintype.card_pos_iff.mp hcpos
  let i : ι := Classical.arbitrary ι
  have hc : Fintype.card {j : ι // j ≠ i} = Module.finrank ℝ (ℝ × V) := by
    rw [Fintype.card_subtype_compl (fun j ↦ j = i)]
    simp [hcard, Module.finrank_prod, Nat.add_comm]
  have hspan : Submodule.span ℝ (Set.range (fun j : {j // j ≠ i} ↦ ((1 : ℝ), v j)))
      ≤ LinearMap.range (augmentedMap v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single j.val 1, augmentedMap_single v j.val⟩
  apply LinearMap.range_eq_top.mp
  apply top_unique
  have hs := (hgen i).span_eq_top_of_card_eq_finrank' hc
  rwa [hs] at hspan

lemma even_facetHit [FiniteDimensional ℝ V] (v : ι → V)
    (hcard : Fintype.card ι = Module.finrank ℝ V + 2)
    (haug : ∀ i : ι, LinearIndependent ℝ (fun j : {j // j ≠ i} ↦ ((1 : ℝ), v j)))
    (hvec : ∀ i j : ι, i ≠ j →
      LinearIndependent ℝ (fun k : {k // k ≠ i ∧ k ≠ j} ↦ v k)) :
    Even ({i | facetHit v i} : Finset ι).card := by
  have hsur := augmentedMap_surjective v hcard haug
  apply even_facetHit_of_kernel_line v hsur
  · have hd := LinearMap.finrank_range_add_finrank_ker (augmentedMap v)
    rw [LinearMap.range_eq_top.mpr hsur] at hd
    simp only [finrank_top, Module.finrank_prod, Module.finrank_self, Module.finrank_pi] at hd
    omega
  · exact augmented_kernel_nonzero_coordinates v haug
  · exact augmented_nonzero_two_coordinates v hvec

end AffineFiber
end SharpLiebThirring.PLParity


/-! Free-action double counting for continuation modulo two. -/
noncomputable section
open Finset
namespace SharpLiebThirring.PLParity
attribute [local instance] Classical.propDecidable

section OrbitSum
variable {G : Type u45} {X : Type u46} [Group G] [MulAction G X] [IsCancelSMul G X]

omit [IsCancelSMul G X] in
lemma orbit_mk_smul (g : G) (x : X) :
    (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel G X)) = Quotient.mk'' x :=
  Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩))

/-- Reconstruct a point in a free orbit from its representative and a group element. -/
def orbitProductEquiv : (Quotient (MulAction.orbitRel G X) × G) ≃ X :=
  Equiv.ofBijective (fun z ↦ z.2 • z.1.out) (by
    constructor
    · rintro ⟨q, g⟩ ⟨r, h⟩ he
      have hq : q = r := by
        have hh := congrArg (fun x : X ↦ (Quotient.mk'' x : Quotient (MulAction.orbitRel G X))) he
        simpa only [orbit_mk_smul, Quotient.out_eq'] using hh
      subst r
      have hg : g = h := IsCancelSMul.right_cancel g h q.out he
      subst h
      rfl
    · intro x
      let q : Quotient (MulAction.orbitRel G X) := Quotient.mk'' x
      have hr : (MulAction.orbitRel G X) x q.out :=
        Quotient.exact' (by rw [Quotient.out_eq'])
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hr)
      exact ⟨(q, g), hg⟩)

lemma sum_eq_card_mul_orbit_sum [Fintype G] [Fintype X]
    (f : X → ℕ) (hf : ∀ g : G, ∀ x, f (g • x) = f x) :
    ∑ x, f x = Fintype.card G * ∑ q : Quotient (MulAction.orbitRel G X), f q.out := by
  classical
  have h := Fintype.sum_equiv (orbitProductEquiv (G := G) (X := X))
    (fun z ↦ f (z.2 • z.1.out)) f (fun _ ↦ rfl)
  rw [← h, Fintype.sum_prod_type]
  simp only [hf, sum_const, card_univ, smul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm
end OrbitSum

section Incidence
variable {G : Type u47} {T : Type u48} {F : Type u49} [Group G] [Fintype G] [Fintype T] [Fintype F]
  [MulAction G T] [MulAction G F] [IsCancelSMul G T] [IsCancelSMul G F]

def rowDegree (R : T → F → Prop) (t : T) : ℕ := Fintype.card {f // R t f}
def colDegree (R : T → F → Prop) (f : F) : ℕ := Fintype.card {t // R t f}

omit [Fintype G] [Fintype T] [IsCancelSMul G T] [IsCancelSMul G F] in
lemma rowDegree_invariant {R : T → F → Prop}
    (hR : ∀ g : G, ∀ t f, R (g • t) (g • f) ↔ R t f) (g : G) (t : T) :
    rowDegree R (g • t) = rowDegree R t := by
  symm
  exact Fintype.card_congr ((MulAction.toPerm g).subtypeEquiv (fun f ↦ (hR g t f).symm))

omit [Fintype G] [Fintype F] [IsCancelSMul G T] [IsCancelSMul G F] in
lemma colDegree_invariant {R : T → F → Prop}
    (hR : ∀ g : G, ∀ t f, R (g • t) (g • f) ↔ R t f) (g : G) (f : F) :
    colDegree R (g • f) = colDegree R f := by
  symm
  exact Fintype.card_congr ((MulAction.toPerm g).subtypeEquiv (fun t ↦ (hR g t f).symm))

lemma sum_rowDegree_eq_sum_colDegree (R : T → F → Prop) :
    ∑ t, rowDegree R t = ∑ f, colDegree R f := by
  classical
  simp only [rowDegree, colDegree, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  exact Finset.sum_comm

/-- The number of odd-degree facet orbits is even whenever every top-cell
has even degree. This is the equivariant handshaking lemma: the action must
be free, but neither the base nor the target needs an orientation. -/
lemma even_odd_degree_orbits (R : T → F → Prop)
    (hR : ∀ g : G, ∀ t f, R (g • t) (g • f) ↔ R t f)
    (hEven : ∀ t, Even (rowDegree R t)) :
    Even ({q : Quotient (MulAction.orbitRel G F) | Odd (colDegree R q.out)} :
      Finset (Quotient (MulAction.orbitRel G F))).card := by
  classical
  have hsum := sum_rowDegree_eq_sum_colDegree R
  rw [sum_eq_card_mul_orbit_sum (rowDegree R) (rowDegree_invariant hR),
    sum_eq_card_mul_orbit_sum (colDegree R) (colDegree_invariant hR)] at hsum
  have heq := Nat.mul_left_cancel (Fintype.card_pos (α := G)) hsum
  have heven : Even (∑ q : Quotient (MulAction.orbitRel G F), colDegree R q.out) := by
    rw [← heq]
    exact Finset.even_sum _ (fun q _ ↦ hEven q.out)
  exact (Finset.even_sum_iff_even_card_odd _).mp heven

end Incidence
section HalfEdges
variable {G : Type u50} {T : Type u51} {H : Type u52} [Group G] [Fintype G] [Fintype T] [Fintype H]
  [MulAction G T] [MulAction G H] [IsCancelSMul G T] [IsCancelSMul G H]

lemma even_orbit_card_of_even_fibers (p : H → T)
    (hp : ∀ g : G, ∀ h, p (g • h) = g • p h)
    (hEven : ∀ t, Even (Nat.card {h // p h = t})) :
    Even (Fintype.card (Quotient (MulAction.orbitRel G H))) := by
  classical
  have hc (h : H) : colDegree (fun t h ↦ p h = t) h = 1 := by
    simp [colDegree, eq_comm]
  have he := even_odd_degree_orbits (fun t h ↦ p h = t)
    (by intro g t h; rw [hp]; exact smul_left_cancel_iff g)
    (fun t ↦ by simpa only [Nat.card_eq_fintype_card, rowDegree] using hEven t)
  simpa [hc] using he

omit [Fintype G] [Fintype T] [Fintype H] [MulAction G T]
  [IsCancelSMul G T] [IsCancelSMul G H] in
lemma orbit_map_respects (f : H → H) (hf : ∀ g : G, ∀ h, f (g • h) = g • f h)
    {a b : H} (hab : (MulAction.orbitRel G H) a b) :
    (MulAction.orbitRel G H) (f a) (f b) := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
  apply MulAction.orbitRel_apply.mpr
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨g, ?_⟩
  rw [← hf, hg]

/-- An equivariant involution descends to orbit classes. -/
def orbitMap (f : H → H) (hf : ∀ g : G, ∀ h, f (g • h) = g • f h) :
    Quotient (MulAction.orbitRel G H) → Quotient (MulAction.orbitRel G H) :=
  Quotient.map f (by intro a b hab; exact orbit_map_respects f hf hab)

omit [Fintype G] [Fintype T] [Fintype H] [MulAction G T]
  [IsCancelSMul G T] [IsCancelSMul G H] in
lemma orbitMap_involutive (f : H → H) (hf : ∀ g : G, ∀ h, f (g • h) = g • f h)
    (hi : Function.Involutive f) : Function.Involutive (orbitMap f hf) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
      change Quotient.mk'' (f (f x)) = Quotient.mk'' x
      rw [hi]

lemma even_fixedPoints_of_even_card {X : Type u53} [Fintype X]
    (f : X → X) (hi : Function.Involutive f) (he : Even (Fintype.card X)) :
    Even (Nat.card (Function.fixedPoints f)) := by
  classical
  rw [Nat.card_eq_fintype_card]
  let F : Function.End X := f
  have hf : F ^ (2 : ℕ) ^ (1 : ℕ) = 1 := by
    funext x
    exact hi x
  have hm := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Nat.ModEq] at hm
  exact Nat.even_iff.mpr (hm.symm.trans (Nat.even_iff.mp he))

/-- One initial crossing orbit cannot be the only fixed orbit of an equivariant
half-edge pairing; a second boundary crossing orbit must exist. -/
lemma exists_other_fixed_orbit (p : H → T)
    (hp : ∀ g : G, ∀ h, p (g • h) = g • p h)
    (hEven : ∀ t, Even (Nat.card {h // p h = t}))
    (f : H → H) (hf : ∀ g : G, ∀ h, f (g • h) = g • f h)
    (hi : Function.Involutive f)
    (q₀ : Quotient (MulAction.orbitRel G H)) (hq₀ : orbitMap f hf q₀ = q₀) :
    ∃ q : Quotient (MulAction.orbitRel G H), orbitMap f hf q = q ∧ q ≠ q₀ := by
  classical
  have he := even_fixedPoints_of_even_card (orbitMap f hf) (orbitMap_involutive f hf hi)
    (even_orbit_card_of_even_fibers p hp hEven)
  by_contra! h
  have hsingle : Function.fixedPoints (orbitMap f hf) = {q₀} := by
    ext q
    constructor
    · exact fun hq ↦ h q hq
    · intro hq
      change orbitMap f hf q = q
      simpa [Set.mem_singleton_iff.mp hq] using hq₀
  have hcard : Nat.card (Function.fixedPoints (orbitMap f hf)) = 1 :=
    (Nat.card_congr (Set.equivOfEq hsingle)).trans Nat.card_unique
  rw [hcard] at he
  norm_num at he


end HalfEdges
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.PLParity
namespace FinitePairing
attribute [local instance] Classical.propDecidable

@[ext] structure CellFacet (X : Type u54) (J : Type u55) where
  cell : X
  facet : J

instance {X : Type u56} {J : Type u57} [Fintype X] [Fintype J] : Fintype (CellFacet X J) :=
  Fintype.ofEquiv (X × J) ⟨fun p ↦ ⟨p.1, p.2⟩, fun p ↦ (p.cell, p.facet),
    fun _ ↦ rfl, fun _ ↦ rfl⟩

instance {G : Type u58} {X : Type u59} {J : Type u60} [Group G] [MulAction G X] : MulAction G (CellFacet X J) where
  smul g p := ⟨g • p.cell, p.facet⟩
  one_smul p := by
    apply CellFacet.ext
    · exact one_smul _ _
    · rfl
  mul_smul g h p := by
    apply CellFacet.ext
    · exact mul_smul g h p.cell
    · rfl

instance {G : Type u61} {X : Type u62} {J : Type u63} [Group G] [MulAction G X] [IsCancelSMul G X] :
    IsCancelSMul G (CellFacet X J) where
  right_cancel' g h p he := IsCancelSMul.right_cancel g h p.cell
    (congrArg CellFacet.cell he)

variable {G : Type u64} {X : Type u65} {J : Type u66} [Group G] [MulAction G X]
variable (D : SubMulAction G X)
variable (hit : X → J → Prop) (hHit : ∀ g : G, ∀ x j, hit (g • x) j ↔ hit x j)
variable (nbr : X → J → X)
variable (hInv : ∀ x j, nbr (nbr x j) j = x)
variable (hNbr : ∀ g : G, ∀ x j, nbr (g • x) j = g • nbr x j)
variable (hAdj : ∀ x j, hit x j → hit (nbr x j) j)

/-- Selected simplex-facet incidences in a finite invariant domain. -/
def selected : SubMulAction G (CellFacet D J) where
  carrier := {p | hit p.cell.val p.facet}
  smul_mem' g p hp := (hHit g p.cell.val p.facet).mpr hp

instance selectedFintype [Fintype D] [Fintype J] : Fintype (selected D hit hHit) :=
  Fintype.ofFinite _

/-- Pair an interior selected facet with its neighbor, and keep boundary facets fixed. -/
def pairing (p : selected D hit hHit) : selected D hit hHit :=
  if hn : nbr p.val.cell.val p.val.facet ∈ D then
    ⟨⟨⟨nbr p.val.cell.val p.val.facet, hn⟩, p.val.facet⟩,
      hAdj p.val.cell.val p.val.facet p.property⟩
  else p

lemma pairing_boundary (p : selected D hit hHit)
    (hn : nbr p.val.cell.val p.val.facet ∉ D) :
    pairing D hit hHit nbr hAdj p = p := by
  simp only [pairing, dite_eq_right hn]

include hInv in
lemma pairing_involutive : Function.Involutive (pairing D hit hHit nbr hAdj) := by
  intro p
  by_cases hn : nbr p.val.cell.val p.val.facet ∈ D
  · have hnn : nbr (nbr p.val.cell.val p.val.facet) p.val.facet ∈ D := by
      rw [hInv]; exact p.val.cell.property
    simp only [pairing, dite_eq_left hn, hnn, ↓reduceDIte]
    apply Subtype.ext
    apply CellFacet.ext
    · exact Subtype.ext (hInv _ _)
    · rfl
  · simp only [pairing, dite_eq_right hn]

include hNbr in
lemma pairing_equivariant (g : G) (p : selected D hit hHit) :
    pairing D hit hHit nbr hAdj (g • p) = g • pairing D hit hHit nbr hAdj p := by
  have hg : nbr (g • p.val.cell.val) p.val.facet ∈ D ↔
      nbr p.val.cell.val p.val.facet ∈ D := by
    rw [hNbr]
    exact D.smul_mem_iff' g
  by_cases hn : nbr p.val.cell.val p.val.facet ∈ D
  · have hn' : nbr (g • p).val.cell.val (g • p).val.facet ∈ D := hg.mpr hn
    simp only [pairing, dite_eq_left hn, dite_eq_left hn']
    apply Subtype.ext
    apply CellFacet.ext
    · exact Subtype.ext (hNbr _ _ _)
    · rfl
  · have hn' : nbr (g • p).val.cell.val (g • p).val.facet ∉ D := fun h ↦ hn (hg.mp h)
    simp only [pairing, dite_eq_right hn, dite_eq_right hn']

lemma selected_projection_equivariant (g : G) (p : selected D hit hHit) :
    (g • p).val.cell = g • p.val.cell := rfl

lemma even_projection_fiber [Fintype D] [Fintype J]
    (hEven : ∀ x : D, Even (Nat.card {j // hit x.val j})) (x : D) :
    Even (Nat.card {p : selected D hit hHit // p.val.cell = x}) := by
  let e : {p : selected D hit hHit // p.val.cell = x} ≃ {j // hit x.val j} :=
    { toFun := fun p ↦ ⟨p.val.val.facet, by
        exact (congrArg (fun y : D ↦ hit y.val p.val.val.facet) p.property).mp p.val.property⟩
      invFun := fun j ↦ ⟨⟨⟨x, j.val⟩, j.property⟩, rfl⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        apply CellFacet.ext
        · exact p.property.symm
        · rfl
      right_inv := fun _ ↦ rfl }
  simpa only [Nat.card_congr e] using hEven x

include hInv hNbr hAdj in
/-- In a free finite equivariant complex with even selected facet counts, a
boundary crossing orbit forces another boundary crossing orbit. -/
lemma exists_other_boundary [Fintype D] [Fintype J] [Fintype G] [IsCancelSMul G X]
    (hEven : ∀ x : D, Even (Nat.card {j // hit x.val j}))
    (hNoOrbit : ∀ x : D, ∀ j, nbr x.val j ∈ D → ∀ g : G, nbr x.val j ≠ g • x.val)
    (p₀ : selected D hit hHit) (hp₀ : nbr p₀.val.cell.val p₀.val.facet ∉ D) :
    ∃ p : selected D hit hHit, nbr p.val.cell.val p.val.facet ∉ D ∧
      ¬ (MulAction.orbitRel G (selected D hit hHit)) p p₀ := by
  let f := pairing D hit hHit nbr hAdj
  have hf := pairing_equivariant D hit hHit nbr hNbr hAdj
  have hi := pairing_involutive D hit hHit nbr hInv hAdj
  let q₀ : Quotient (MulAction.orbitRel G (selected D hit hHit)) := Quotient.mk'' p₀
  have hq₀ : orbitMap f hf q₀ = q₀ := by
    change Quotient.mk'' (f p₀) = Quotient.mk'' p₀
    exact congrArg Quotient.mk'' (pairing_boundary D hit hHit nbr hAdj p₀ hp₀)
  obtain ⟨q, hq, hne⟩ := exists_other_fixed_orbit (fun p : selected D hit hHit ↦ p.val.cell)
    (selected_projection_equivariant D hit hHit)
    (even_projection_fiber D hit hHit hEven) f hf hi q₀ hq₀
  refine ⟨q.out, ?_, ?_⟩
  · intro hin
    have hre : (MulAction.orbitRel G (selected D hit hHit)) (f q.out) q.out := by
      apply Quotient.exact'
      change orbitMap f hf (Quotient.mk'' q.out) = Quotient.mk'' q.out
      simpa only [Quotient.out_eq'] using hq
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hre)
    have he := congrArg (fun p : selected D hit hHit ↦ p.val.cell.val) hg
    have hp : (f q.out).val.cell.val = nbr q.out.val.cell.val q.out.val.facet := by
      simp only [f, pairing, dite_eq_left hin]
    rw [hp] at he
    exact hNoOrbit q.out.val.cell q.out.val.facet hin g he.symm
  · intro hr
    apply hne
    exact (Quotient.out_eq' q).symm.trans (Quotient.sound' hr)

end FinitePairing
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open SharpLiebThirring.PLParity
section PLComplex
variable {n : ℕ} [NeZero n] (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
variable {V : Type u67} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V))
attribute [local instance] Classical.propDecidable

/-- Extend finite equivariant vertex data by zero outside the invariant complex. -/
def extendValues (a : vertices H D → V) (z : Fin n → ℤ) : V :=
  if hz : z ∈ vertices H D then a ⟨z, hz⟩ else 0

omit [NeZero n] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
lemma extendValues_at (a : vertices H D → V) (F : D) (k : Fin (n + 1)) :
    extendValues H D a (F.val.vertex k) = a (flagVertex H D F k) := by
  simp only [extendValues, dite_eq_left (show F.val.vertex k ∈ vertices H D from ⟨F, k, rfl⟩)]
  rfl

omit [NeZero n] [FiniteDimensional ℝ V] in
lemma extendValues_equivariant (a : vertices H D → V)
    (ha : ∀ s : H, ∀ z, a (s • z) = ρ s (a z)) (s : H) (z : Fin n → ℤ) :
    extendValues H D a (s • z) = ρ s (extendValues H D a z) := by
  by_cases hz : z ∈ vertices H D
  · have hsz : s • z ∈ vertices H D := (vertices H D).smul_mem s hz
    simp only [extendValues, dite_eq_left hz, dite_eq_left hsz]
    exact ha s ⟨z, hz⟩
  · have hsz : s • z ∉ vertices H D := fun h ↦ hz (((vertices H D).smul_mem_iff' s).mp h)
    simp only [extendValues, dite_eq_right hz, dite_eq_right hsz, map_zero]

def cellHit (a : vertices H D → V) (F : Flag n) (j : Fin (n + 1)) : Prop :=
  facetHit (fun k ↦ extendValues H D a (F.vertex k)) j

omit [NeZero n] [FiniteDimensional ℝ V] in
lemma cellHit_equivariant (a : vertices H D → V)
    (ha : ∀ s : H, ∀ z, a (s • z) = ρ s (a z)) (s : H) (F : Flag n) (j : Fin (n + 1)) :
    cellHit H D a (s • F) j ↔ cellHit H D a F j := by
  unfold cellHit
  have he (k : Fin (n + 1)) : extendValues H D a ((s • F).vertex k) =
      ρ s (extendValues H D a (F.vertex k)) := by
    rw [show (s • F).vertex k = s • F.vertex k from F.vertex_smul s.val k]
    exact extendValues_equivariant H D ρ a ha s _
  simp only [he]
  exact facetHit_linearEquiv _ (ρ s) _

omit [FiniteDimensional ℝ V] in
lemma cellHit_neighbor (a : vertices H D → V) (F : Flag n) (j : Fin (n + 1)) :
    cellHit H D a (F.neighbor j) j ↔ cellHit H D a F j := by
  apply facetHit_congr
  intro k hk
  rw [F.neighbor_vertex j k hk]

omit [NeZero n] in
lemma cellHit_even (a : vertices H D → V) (F : D)
    (hc : n = Module.finrank ℝ V + 1)
    (haug : ∀ j : Fin (n + 1), LinearIndependent ℝ
      (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k))))
    (hvec : ∀ i j : Fin (n + 1), i ≠ j → LinearIndependent ℝ
      (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k))) :
    Even (Nat.card {j // cellHit H D a F.val j}) := by
  have he := even_facetHit (fun k ↦ a (flagVertex H D F k)) (by simpa using hc)
    haug hvec
  simpa only [cellHit, extendValues_at, Nat.card_eq_fintype_card, Fintype.card_subtype] using he

lemma neighbor_not_orbit (h : ℝ) (F : D)
    (hfree : ∀ z : vertices H D, ∀ s : H, s • gridPoint h z.val = gridPoint h z.val → s = 1)
    (j : Fin (n + 1)) (s : H) : F.val.neighbor j ≠ s • F.val := by
  apply F.val.neighbor_ne_reflect_of_free j s.val
  intro k hk
  have hz : s • (flagVertex H D F k) = flagVertex H D F k := by
    apply Subtype.ext
    exact funext hk
  have hp : s • gridPoint h (F.val.vertex k) = gridPoint h (F.val.vertex k) := by
    calc
      _ = gridPoint h (s • F.val.vertex k) := (gridPoint_smul h s.val _).symm
      _ = _ := congrArg (gridPoint h) (congrArg Subtype.val hz)
  exact congrArg Subtype.val (hfree (flagVertex H D F k) s hp)

/-- The geometric complex now satisfies the abstract mod-two boundary lemma. -/
lemma another_boundary [Fintype D] (a : vertices H D → V)
    (ha : ∀ s : H, ∀ z, a (s • z) = ρ s (a z)) (hc : n = Module.finrank ℝ V + 1)
    (haug : ∀ F : D, ∀ j : Fin (n + 1), LinearIndependent ℝ
      (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k))))
    (hvec : ∀ F : D, ∀ i j : Fin (n + 1), i ≠ j → LinearIndependent ℝ
      (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k)))
    (h : ℝ) (hfree : ∀ z : vertices H D, ∀ s : H,
      s • gridPoint h z.val = gridPoint h z.val → s = 1)
    (p₀ : FinitePairing.selected D (cellHit H D a) (cellHit_equivariant H D ρ a ha))
    (hp₀ : p₀.val.cell.val.neighbor p₀.val.facet ∉ D) :
    ∃ p : FinitePairing.selected D (cellHit H D a) (cellHit_equivariant H D ρ a ha),
      p.val.cell.val.neighbor p.val.facet ∉ D ∧
      ¬ (MulAction.orbitRel H _) p p₀ := by
  exact FinitePairing.exists_other_boundary D (cellHit H D a) (cellHit_equivariant H D ρ a ha)
    Flag.neighbor Flag.neighbor_neighbor (fun s F j ↦ (F.smul_neighbor s.val j).symm)
    (fun F j hh ↦ (cellHit_neighbor H D a F j).mpr hh)
    (fun F ↦ cellHit_even H D a F hc (haug F) (hvec F))
    (fun F j _ s ↦ neighbor_not_orbit H D h F hfree j s) p₀ hp₀

end PLComplex
end SharpLiebThirring.CubeFlags

end
end
end

end OAI
