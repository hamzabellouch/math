import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Chains.SimplexBasisHeight
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Gray.OrderedAtomGrouping

namespace OAI

section

/-! # The positive globe complex represents bounded cells

Evaluation of a positive chain map at the universal top table is an actual
bijection with bounded cells. In particular the chain parameter used by
the right interval remembers every cell entry, not only its endpoints.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

private theorem chainHom_ext {K L : DirectedComplex.{0}} {f g : Hom K L}
    (h : ∀ k x, f.app k x = g.app k x) : f = g := by
  cases f with
  | mk fa fd fe fp =>
    cases g with
    | mk ga gd ge gp =>
      have hfg : fa = ga := funext (fun k => AddMonoidHom.ext (h k))
      cases hfg
      rfl

theorem topTable_eq_single (n k : ℕ) (s : Basis n k) :
    topTable n s.val k = Finsupp.single s 1 := by
  classical
  unfold topTable
  split_ifs with hk he
  · rfl
  · have hs : s.val = false := by
      rcases s.property with h | ⟨_, h⟩
      · exact False.elim (hk h)
      · exact h
    congr 1
    exact Subtype.ext hs.symm
  · rcases s.property with h | ⟨h, _⟩
    · exact False.elim (hk h)
    · exact False.elim (he h)

/-- Reading the top table and extending its entries recovers the original
positive chain map on every degree and basis element. -/
theorem cellMap_top_inverse {K : DirectedComplex.{0}} (n : ℕ) (F : Hom (complex n) K) :
    cellMap n (F.realization.toFun (topCell n)) = F := by
  apply chainHom_ext
  intro k u
  change cellApp n (Cell.map F (topCell n)) k u = F.app k u
  induction u using Finsupp.induction_linear with
  | zero =>
    exact (cellApp n (Cell.map F (topCell n)) k).map_zero.trans
      (F.app k).map_zero.symm
  | add u v hu hv =>
    exact ((cellApp n (Cell.map F (topCell n)) k).map_add u v).trans
      ((congrArg₂ (· + ·) hu hv).trans ((F.app k).map_add u v).symm)
  | single s z =>
    rw [cellApp_single]
    change z • F.app k (topTable n s.val k) = F.app k (Finsupp.single s z)
    rw [topTable_eq_single]
    let Fk : Chains n k →+ K.group k := F.app k
    change z • Fk (Finsupp.single s 1) = Fk (Finsupp.single s z)
    rw [← map_zsmul, Finsupp.smul_single]
    simp

/-- Positive maps from the globe complex are exactly bounded cells in
Steiner's actual strict realization. -/
def homEquiv (n : ℕ) (K : DirectedComplex.{0}) :
    Hom (complex n) K ≃ {x : K.realization // K.realization.DimensionLE n x} where
  toFun F := ⟨F.realization.toFun (topCell n), F.realization.dimensionLE (topCell_dimension n)⟩
  invFun x := cellMap n x.val
  left_inv F := cellMap_top_inverse n F
  right_inv x := Subtype.ext (cellMap_top_of_bounded n x.val x.property)

end

end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # Positive weights in the actual globe complex

The two signed basis coefficients control every positive table. Their
weights decrease with degree and are bounded by augmentation one. These
are the finite chain estimates needed to identify the globe realization.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

abbrev chainTable {n : ℕ} (x : Cell (complex n)) (a : Bool) (k : ℕ) : Chains n k :=
  x.table a k

theorem chain_eq_pair {n k : ℕ} (hk : k < n) (u : Chains n k) :
    u = Finsupp.single ⟨false, Or.inl hk⟩ (u ⟨false, Or.inl hk⟩) +
      Finsupp.single ⟨true, Or.inl hk⟩ (u ⟨true, Or.inl hk⟩) := by
  classical
  ext s
  rcases s with ⟨a, ha⟩
  cases a <;> simp

theorem chain_eq_top (n : ℕ) (u : Chains n n) :
    u = Finsupp.single ⟨false, Or.inr ⟨rfl, rfl⟩⟩
      (u ⟨false, Or.inr ⟨rfl, rfl⟩⟩) := by
  classical
  ext s
  have hs : s = ⟨false, Or.inr ⟨rfl, rfl⟩⟩ := by
    apply Subtype.ext
    rcases s.property with h | ⟨_, h⟩
    · omega
    · exact h
  subst s
  simp

theorem weight_eq_pair {n k : ℕ} (hk : k < n) (u : Chains n k) :
    weight n k u = u ⟨false, Or.inl hk⟩ + u ⟨true, Or.inl hk⟩ := by
  have h := congrArg (weight n k) (chain_eq_pair hk u)
  simpa only [map_add, weight_single] using h

theorem weight_eq_top (n : ℕ) (u : Chains n n) :
    weight n n u = u ⟨false, Or.inr ⟨rfl, rfl⟩⟩ := by
  have h := congrArg (weight n n) (chain_eq_top n u)
  simpa only [weight_single] using h

theorem positive_weight_nonneg {n k : ℕ} {u : Chains n k}
    (hu : u ∈ positive n k) : 0 ≤ weight n k u := by
  rcases lt_trichotomy k n with hk | hk | hk
  · rw [weight_eq_pair hk]
    exact add_nonneg (hu _) (hu _)
  · subst k
    rw [weight_eq_top]
    exact hu _
  · rw [chains_eq_zero_above hk u, map_zero]

theorem positive_eq_zero_of_weight_zero {n k : ℕ} {u : Chains n k}
    (hu : u ∈ positive n k) (hw : weight n k u = 0) : u = 0 := by
  rcases lt_trichotomy k n with hk | hk | hk
  · have hf := hu ⟨false, Or.inl hk⟩
    have ht := hu ⟨true, Or.inl hk⟩
    rw [weight_eq_pair hk] at hw
    have hf0 : u ⟨false, Or.inl hk⟩ = 0 := by omega
    have ht0 : u ⟨true, Or.inl hk⟩ = 0 := by omega
    rw [chain_eq_pair hk u, hf0, ht0]
    simp
  · subst k
    rw [weight_eq_top] at hw
    rw [chain_eq_top n u, hw]
    simp
  · exact chains_eq_zero_above hk u

theorem cell_weight_eq (n : ℕ) (x : Cell (complex n)) (k : ℕ) :
    weight n k (chainTable x true k) = weight n k (chainTable x false k) := by
  have h := congrArg (weight n k) (x.boundary false k)
  change weight n k (differential n k (chainTable x false (k+1))) =
    weight n k (chainTable x true k - chainTable x false k) at h
  rw [weight_differential, map_sub] at h
  omega

theorem cell_weight_succ_le {n k : ℕ} (x : Cell (complex n)) (hk : k < n) :
    weight n (k+1) (chainTable x false (k+1)) ≤ weight n k (chainTable x false k) := by
  have h := congrArg (fun u : Chains n k => u ⟨true, Or.inl hk⟩) (x.boundary false k)
  change differential n k (chainTable x false (k+1)) ⟨true, Or.inl hk⟩ =
    (chainTable x true k - chainTable x false k) ⟨true, Or.inl hk⟩ at h
  rw [differential_eq_weight] at h
  simp [boundary, hk] at h
  have hf := x.positive false k ⟨true, Or.inl hk⟩
  have ht := x.positive true k ⟨false, Or.inl hk⟩
  change 0 ≤ chainTable x false k ⟨true, Or.inl hk⟩ at hf
  change 0 ≤ chainTable x true k ⟨false, Or.inl hk⟩ at ht
  have he := cell_weight_eq n x k
  simp only [weight_eq_pair hk] at he ⊢
  omega

/-- Every cell of the globe chain realization has the expected bound. -/
theorem cell_dimension (n : ℕ) (x : Cell (complex n)) :
    (complex n).realization.DimensionLE n x := by
  apply (Cell.dimensionLE_iff_zero_above x n).mpr
  intro k hk a
  exact chains_eq_zero_above hk (chainTable x a k)

theorem cell_weight_le_one (n : ℕ) (x : Cell (complex n)) (k : ℕ) :
    weight n k (chainTable x false k) ≤ 1 := by
  induction k with
  | zero => exact le_of_eq (x.augmentation false)
  | succ k ih =>
    by_cases hk : k < n
    · exact (cell_weight_succ_le x hk).trans ih
    · have hnk : n < k+1 := by omega
      rw [chains_eq_zero_above hnk (chainTable x false (k+1)), map_zero]
      norm_num

theorem cell_weight_bounds (n : ℕ) (x : Cell (complex n)) (a : Bool) (k : ℕ) :
    0 ≤ weight n k (chainTable x a k) ∧ weight n k (chainTable x a k) ≤ 1 := by
  constructor
  · exact positive_weight_nonneg (x.positive a k)
  · cases a with
    | false => exact cell_weight_le_one n x k
    | true => rw [cell_weight_eq]; exact cell_weight_le_one n x k

end

end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # Classifying the cells of the positive globe complex

Positive weight one selects one basis element. The boundary equations then
force the entire lower table; hence no additional strict cells appear when
the finite globe complex is realized.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

theorem positive_weight_one {n k : ℕ} {u : Chains n k}
    (hu : u ∈ positive n k) (hw : weight n k u = 1) :
    ∃ s : Basis n k, u = Finsupp.single s 1 := by
  rcases lt_trichotomy k n with hk | hk | hk
  · have hf := hu ⟨false, Or.inl hk⟩
    have ht := hu ⟨true, Or.inl hk⟩
    rw [weight_eq_pair hk] at hw
    by_cases hf1 : u ⟨false, Or.inl hk⟩ = 1
    · refine ⟨⟨false, Or.inl hk⟩, ?_⟩
      have ht0 : u ⟨true, Or.inl hk⟩ = 0 := by omega
      rw [chain_eq_pair hk u, hf1, ht0]
      simp
    · refine ⟨⟨true, Or.inl hk⟩, ?_⟩
      have hf0 : u ⟨false, Or.inl hk⟩ = 0 := by omega
      have ht1 : u ⟨true, Or.inl hk⟩ = 1 := by omega
      rw [chain_eq_pair hk u, hf0, ht1]
      simp
  · subst k
    refine ⟨⟨false, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    rw [weight_eq_top] at hw
    rw [chain_eq_top n u, hw]
  · have hz := chains_eq_zero_above hk u
    rw [hz, map_zero] at hw
    norm_num at hw

theorem cell_weight_antitone (n : ℕ) (x : Cell (complex n)) :
    Antitone (fun k => weight n k (chainTable x false k)) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases hk : k < n
  · exact cell_weight_succ_le x hk
  · have hnk : n < k+1 := by omega
    rw [chains_eq_zero_above hnk (chainTable x false (k+1)), map_zero]
    exact (cell_weight_bounds n x false k).1

/-- The least dimension of a cell has positive weight one. -/
theorem minimal_dimension_weight_one {n d : ℕ} (x : Cell (complex n))
    (hd : (complex n).realization.DimensionLE d x)
    (hmin : ∀ k < d, ¬ (complex n).realization.DimensionLE k x) :
    weight n d (chainTable x false d) = 1 := by
  have hb := cell_weight_bounds n x false d
  by_cases hd0 : d = 0
  · subst d
    exact x.augmentation false
  · have hpos : 0 < d := Nat.pos_of_ne_zero hd0
    by_contra hn
    have hw0 : weight n d (chainTable x false d) = 0 := by omega
    have hzero (a : Bool) : chainTable x a d = 0 := by
      apply positive_eq_zero_of_weight_zero (x.positive a d)
      cases a with
      | false => exact hw0
      | true => exact (cell_weight_eq n x d).trans hw0
    apply hmin (d-1) (by omega)
    apply (Cell.dimensionLE_iff_zero_above x (d-1)).mpr
    intro k hk a
    by_cases he : k = d
    · subst k
      exact hzero a
    · exact (Cell.dimensionLE_iff_zero_above x d).mp hd k (by omega) a

/-- Weight one at an upper degree forces the signed lower boundaries. -/
theorem cell_lower_table {n d k : ℕ} (x : Cell (complex n))
    (hdn : d ≤ n) (hkd : k < d)
    (hd : weight n d (chainTable x false d) = 1) (a : Bool) :
    chainTable x a k = topTable n a k := by
  classical
  have hk : k < n := lt_of_lt_of_le hkd hdn
  have hwk := (cell_weight_antitone n x) hkd.le
  change weight n d (chainTable x false d) ≤ weight n k (chainTable x false k) at hwk
  have hwk1 := (cell_weight_bounds n x false k).2
  have hwk_eq : weight n k (chainTable x false k) = 1 := by omega
  have hwk' := (cell_weight_antitone n x) (show k+1 ≤ d by omega)
  change weight n d (chainTable x false d) ≤ weight n (k+1) (chainTable x false (k+1)) at hwk'
  have hwk1' := (cell_weight_bounds n x false (k+1)).2
  have hwk_eq' : weight n (k+1) (chainTable x false (k+1)) = 1 := by omega
  have hb := congrArg (fun u : Chains n k => u ⟨true, Or.inl hk⟩) (x.boundary false k)
  change differential n k (chainTable x false (k+1)) ⟨true, Or.inl hk⟩ =
    (chainTable x true k - chainTable x false k) ⟨true, Or.inl hk⟩ at hb
  rw [differential_eq_weight, hwk_eq'] at hb
  simp [boundary, hk] at hb
  have hwtrue : weight n k (chainTable x true k) = 1 :=
    (cell_weight_eq n x k).trans hwk_eq
  rw [weight_eq_pair hk] at hwk_eq hwtrue
  have hff := x.positive false k ⟨false, Or.inl hk⟩
  have hft := x.positive false k ⟨true, Or.inl hk⟩
  have htf := x.positive true k ⟨false, Or.inl hk⟩
  have htt := x.positive true k ⟨true, Or.inl hk⟩
  change 0 ≤ chainTable x false k ⟨false, Or.inl hk⟩ at hff
  change 0 ≤ chainTable x false k ⟨true, Or.inl hk⟩ at hft
  change 0 ≤ chainTable x true k ⟨false, Or.inl hk⟩ at htf
  change 0 ≤ chainTable x true k ⟨true, Or.inl hk⟩ at htt
  have hff1 : chainTable x false k ⟨false, Or.inl hk⟩ = 1 := by omega
  have hft0 : chainTable x false k ⟨true, Or.inl hk⟩ = 0 := by omega
  have htf0 : chainTable x true k ⟨false, Or.inl hk⟩ = 0 := by omega
  have htt1 : chainTable x true k ⟨true, Or.inl hk⟩ = 1 := by omega
  cases a
  · rw [chain_eq_pair hk (chainTable x false k), hff1, hft0]
    simp [topTable, hk]
  · rw [chain_eq_pair hk (chainTable x true k), htf0, htt1]
    simp [topTable, hk]

/-- Every table is an actual face of the universal top cell. -/
theorem exists_topCell_face (n : ℕ) (x : Cell (complex n)) :
    ∃ (d : ℕ) (s : Basis n d), (topCell n).face s.val d = x := by
  classical
  let hex : ∃ d, (complex n).realization.DimensionLE d x := ⟨n, cell_dimension n x⟩
  let d := Nat.find hex
  have hd : (complex n).realization.DimensionLE d x := Nat.find_spec hex
  have hdn : d ≤ n := Nat.find_min' hex (cell_dimension n x)
  have hmin : ∀ k < d, ¬ (complex n).realization.DimensionLE k x :=
    fun k hk => Nat.find_min hex hk
  have hw := minimal_dimension_weight_one x hd hmin
  obtain ⟨s, hs⟩ := positive_weight_one (x.positive false d) hw
  refine ⟨d, s, ?_⟩
  apply Cell.ext
  funext a k
  change (if k < d then topTable n a k else if k = d then topTable n s.val k else 0) =
    chainTable x a k
  by_cases hk : k < d
  · rw [ite_eq_left hk]
    exact (cell_lower_table x hdn hk hw a).symm
  · by_cases he : k = d
    · subst k
      rw [ite_eq_right (Nat.lt_irrefl d), ite_eq_left rfl]
      rw [topTable_eq_single]
      have ha : chainTable x a d = chainTable x false d := by
        cases a with
        | false => rfl
        | true =>
          have h := congrArg (fun y : Cell (complex n) => chainTable y true d) hd.1
          change (if d < d then chainTable x true d else if d = d then chainTable x false d else 0) =
            chainTable x true d at h
          simpa only [Nat.lt_irrefl, ite_false, ite_true] using h.symm
      exact hs.symm.trans ha.symm
    · have hdk : d < k := by omega
      rw [ite_eq_right hk, ite_eq_right he]
      exact ((Cell.dimensionLE_iff_zero_above x d).mp hd k hdk a).symm

/-- The canonical free globe map is surjective on every strict cell. -/
theorem fromGlobe_surjective (n : ℕ) : Function.Surjective (fromGlobe n).toFun := by
  intro x
  obtain ⟨d, s, hs⟩ := exists_topCell_face n x
  rcases s.property with hd | ⟨hd, _⟩
  · exact ⟨StrictOmegaCategory.Globe.Cell.boundary s.val ⟨d, hd⟩, hs⟩
  · subst d
    refine ⟨StrictOmegaCategory.Globe.Cell.top, ?_⟩
    have hf : (topCell n).face s.val n = topCell n := by
      cases s.val with
      | false => exact (topCell_dimension n).1
      | true => exact (topCell_dimension n).2
    exact hf.symm.trans hs

end

end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # Atomic indecomposability in the actual positive-table category

A unit top coefficient belongs entirely to one of two positive summands.
The disjoint atom boundaries then propagate this choice downwards. Thus an
atom cannot be a composite with two factors of positive relative dimension.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem positive_summand_of_single (p : ℕ) (b : B.Index p)
    (x y : K.group p) (hx : x ∈ K.positive p) (hy : y ∈ K.positive p)
    (he : B.coordinates p (x+y) = Finsupp.single b 1) :
    x = 0 ∨ B.coordinates p x = Finsupp.single b 1 := by
  classical
  have hh (c : B.Index p) :
      B.coordinates p x c + B.coordinates p y c = (Finsupp.single b 1) c := by
    simpa only [map_add, Finsupp.add_apply] using congrArg (fun f => f c) he
  have hx0 := B.coordinate_nonnegative p x hx b
  have hy0 := B.coordinate_nonnegative p y hy b
  have hb := hh b
  rw [Finsupp.single_eq_same] at hb
  have hv : B.coordinates p x b = 0 ∨ B.coordinates p x b = 1 := by omega
  have hc (c : B.Index p) (hcb : c ≠ b) : B.coordinates p x c = 0 := by
    have hp := B.coordinate_nonnegative p x hx c
    have hq := B.coordinate_nonnegative p y hy c
    have hs := hh c
    rw [Finsupp.single_eq_of_ne hcb] at hs
    omega
  rcases hv with hz | ho
  · left
    apply (B.coordinates p).injective
    ext c
    by_cases hcb : c = b
    · subst c
      simpa only [map_zero, Finsupp.zero_apply] using hz
    · simpa only [map_zero, Finsupp.zero_apply] using hc c hcb
  · right
    ext c
    by_cases hcb : c = b
    · subst c
      simpa only [Finsupp.single_eq_same] using ho
    · simpa only [Finsupp.single_eq_of_ne hcb] using hc c hcb

theorem atom_summand_descend {p : ℕ} (b : B.Index p) (r : ℕ) (hrp : r < p)
    (Y Z : Cell K)
    (he : ∀ n, r < n → ∀ side,
      Y.table side n + Z.table side n = (B.atom p b).table side n)
    (htop : Y.table false p = (B.atom p b).table false p) :
    ∀ n, r < n → ∀ side,
      Y.table side n = (B.atom p b).table side n ∧ Z.table side n = 0 := by
  have habove (n : ℕ) (hn : p < n) (side : Bool) :
      Y.table side n = 0 ∧ Z.table side n = 0 := by
    apply B.positive_add_eq_zero n _ _ (Y.positive side n) (Z.positive side n)
    exact (he n (hrp.trans hn) side).trans (B.atom_above p b n hn side)
  have htop' (side : Bool) :
      Y.table side p = (B.atom p b).table side p ∧ Z.table side p = 0 := by
    have hY : Y.table true p = Y.table false p := by
      have hb := Y.boundary false p
      rw [(habove (p+1) (by omega) false).1, map_zero] at hb
      exact sub_eq_zero.mp hb.symm
    have hA : (B.atom p b).table true p = (B.atom p b).table false p := by
      apply (B.coordinates p).injective
      rw [B.atom_top, B.atom_top]
    have hside : Y.table side p = (B.atom p b).table side p := by
      cases side
      · exact htop
      · exact hY.trans (htop.trans hA.symm)
    refine ⟨hside, ?_⟩
    have hh := he p hrp side
    rw [hside] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  have hdown (n : ℕ) (hn : n ≤ p) : r < n → ∀ side,
      Y.table side n = (B.atom p b).table side n ∧ Z.table side n = 0 := by
    induction hn using Nat.decreasingInduction with
    | self => exact fun _ => htop'
    | @of_succ n hn ih =>
      intro hrn side
      have hnext := (ih (by omega) false).1
      have hres := B.residual_positive Y b n hn hnext
      have hsum : (Y.table false n - (B.atom p b).table false n) + Z.table false n = 0 := by
        have hh := he n hrn false
        calc
          _ = (Y.table false n + Z.table false n) - (B.atom p b).table false n := by abel
          _ = 0 := by rw [hh, sub_self]
      have hz := B.positive_add_eq_zero n _ _ hres (Z.positive false n) hsum
      have hyfalse := sub_eq_zero.mp hz.1
      have hytrue : Y.table true n = (B.atom p b).table true n := by
        apply sub_eq_zero.mp
        rw [← residual_sides Y (B.atom p b) n hnext, hz.1]
      have hyside : Y.table side n = (B.atom p b).table side n := by
        cases side <;> assumption
      refine ⟨hyside, ?_⟩
      have hh := he n hrn side
      rw [hyside] at hh
      exact add_left_cancel (hh.trans (add_zero _).symm)
  intro n hn side
  by_cases hnp : n ≤ p
  · exact hdown n hnp hn side
  · have hpn : p < n := by omega
    exact ⟨(habove n hpn side).1.trans (B.atom_above p b n hpn side).symm,
      (habove n hpn side).2⟩

theorem atom_summands {p : ℕ} (b : B.Index p) (r : ℕ) (hrp : r < p)
    (Y Z : Cell K)
    (he : ∀ n, r < n → ∀ side,
      Y.table side n + Z.table side n = (B.atom p b).table side n) :
    ((∀ n, r < n → ∀ side, Y.table side n = (B.atom p b).table side n) ∧
     (∀ n, r < n → ∀ side, Z.table side n = 0)) ∨
    ((∀ n, r < n → ∀ side, Y.table side n = 0) ∧
     (∀ n, r < n → ∀ side, Z.table side n = (B.atom p b).table side n)) := by
  have hh : B.coordinates p (Y.table false p + Z.table false p) = Finsupp.single b 1 :=
    (congrArg (B.coordinates p) (he p hrp false)).trans (B.atom_top p b false)
  rcases B.positive_summand_of_single p b _ _ (Y.positive false p) (Z.positive false p) hh with hz | hy
  · have hZ : Z.table false p = (B.atom p b).table false p := by
      simpa only [hz, zero_add] using he p hrp false
    have hrev := B.atom_summand_descend b r hrp Z Y
      (fun n hn side => (add_comm _ _).trans (he n hn side)) hZ
    exact Or.inr ⟨fun n hn side => (hrev n hn side).2, fun n hn side => (hrev n hn side).1⟩
  · have hY : Y.table false p = (B.atom p b).table false p := by
      apply (B.coordinates p).injective
      exact hy.trans (B.atom_top p b false).symm
    have hdir := B.atom_summand_descend b r hrp Y Z he hY
    exact Or.inl ⟨fun n hn side => (hdir n hn side).1, fun n hn side => (hdir n hn side).2⟩

/-- A binary expression for an atom has an identity factor at its
composition degree. -/
theorem atom_comp_identity_factor (a : B.AtomIndex) (Y Z : Cell K) (r : ℕ)
    (hyz : Y.face true r = Z.face false r)
    (he : Cell.comp Y Z r hyz = B.atomCell a) :
    K.realization.DimensionLE r Y ∨ K.realization.DimensionLE r Z := by
  by_cases hr : r < a.1
  · have hs : ∀ n, r < n → ∀ side,
        Y.table side n + Z.table side n = (B.atom a.1 a.2).table side n := by
      intro n hn side
      have hh := congrArg (fun X : Cell K => X.table side n) he
      simpa only [Cell.comp_table, Cell.pasteTable, Nat.not_lt.mpr hn.le,
        Nat.ne_of_gt hn, ite_false, atomCell] using hh
    rcases B.atom_summands a.2 r hr Y Z hs with ⟨_, hZ⟩ | ⟨hY, _⟩
    · exact Or.inr (Cell.dimensionLE_of_table_zero hZ)
    · exact Or.inl (Cell.dimensionLE_of_table_zero hY)
  · have ha : K.realization.DimensionLE r (B.atomCell a) :=
      Cell.dimensionLE_of_table_zero (fun n hn side =>
        B.atom_above a.1 a.2 n (by omega) side)
    have hc : K.realization.DimensionLE r (Cell.comp Y Z r hyz) := he.symm ▸ ha
    exact Or.inl (Cell.dimensionLE_comp_factors B.positive_add_eq_zero hyz hc).1

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Decomposition levels detect nonidentity composition

At or above its atom-decomposition level a positive cell cannot be the
composite of two nonidentity factors. This bounds the critical composition
degree of every essential generated expression mapping to that cell.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem aboveAtomOrZero_comp_identity_factor (n r : ℕ) (hnr : n ≤ r)
    (Y Z : Cell K) (hyz : Y.face true r = Z.face false r)
    (hX : B.AboveAtomOrZero n (Cell.comp Y Z r hyz)) :
    K.realization.DimensionLE r Y ∨ K.realization.DimensionLE r Z := by
  have hlevel := B.aboveAtomOrZero_mono hnr _ hX
  rcases hlevel with hz | ⟨a, ha, he⟩
  · have hzero (q : ℕ) (hq : r < q) (side : Bool) :
        Y.table side q = 0 ∧ Z.table side q = 0 := by
      apply B.positive_add_eq_zero q _ _ (Y.positive side q) (Z.positive side q)
      have hh := hz q hq side
      simpa only [Cell.comp_table, Cell.pasteTable, Nat.not_lt.mpr hq.le,
        Nat.ne_of_gt hq, ite_false] using hh
    exact Or.inl (Cell.dimensionLE_of_table_zero (fun q hq side => (hzero q hq side).1))
  · have hsum : ∀ q, r < q → ∀ side,
        Y.table side q + Z.table side q = (B.atom a.1 a.2).table side q := by
      intro q hq side
      have hh := he q hq side
      simpa only [Cell.comp_table, Cell.pasteTable, Nat.not_lt.mpr hq.le,
        Nat.ne_of_gt hq, ite_false, atomCell] using hh
    rcases B.atom_summands a.2 r ha Y Z hsum with ⟨_, hZ⟩ | ⟨hY, _⟩
    · exact Or.inr (Cell.dimensionLE_of_table_zero hZ)
    · exact Or.inl (Cell.dimensionLE_of_table_zero hY)

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Unique atom fibres for a generated strict comparison

The source is generated by bounded lifts of the actual atoms. Positivity
reflects the dimensions of all its expressions, and atomic
indecomposability therefore removes every identity factor. No faithfulness
or freeness assumption on the comparison is made.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem atomCell_injective : Function.Injective B.atomCell := by
  rintro ⟨p,a⟩ ⟨q,b⟩ he
  classical
  have hpq : p ≤ q := by
    by_contra hn
    have hh := congrArg (fun X : Cell K => B.coordinates p (X.table false p) a) he
    change B.coordinates p ((B.atom p a).table false p) a =
      B.coordinates p ((B.atom q b).table false p) a at hh
    rw [B.atom_top, B.atom_above q b p (by omega), map_zero,
      Finsupp.single_eq_same, Finsupp.zero_apply] at hh
    omega
  have hqp : q ≤ p := by
    by_contra hn
    have hh := congrArg (fun X : Cell K => B.coordinates q (X.table false q) b) he
    change B.coordinates q ((B.atom p a).table false q) b =
      B.coordinates q ((B.atom q b).table false q) b at hh
    rw [B.atom_top, B.atom_above p a q (by omega), map_zero,
      Finsupp.single_eq_same, Finsupp.zero_apply] at hh
    omega
  have hp : p = q := Nat.le_antisymm hpq hqp
  subst q
  have hab : a = b := by
    by_contra hne
    have hh := congrArg (fun X : Cell K => B.coordinates p (X.table false p) a) he
    simp only [atomCell, B.atom_top, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hne] at hh
    omega
  subst b
  rfl

private theorem comp_eq_left {C : StrictOmegaCategory.{0}} {x y : C} (r : ℕ)
    (hxy : C.target r x = C.source r y) (hy : C.DimensionLE r y) :
    C.comp r x y hxy = x := by
  have he : y = C.target r x := hy.1.symm.trans hxy.symm
  subst y
  exact C.right_unit r x hxy

theorem atom_preimage_of_expression {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    {x : C} (t : CompositionExpression C g x) (a : B.AtomIndex)
    (he : F.toFun x = B.atomCell a) : x = g a := by
  induction t with
  | generator b =>
    have hb : b = a := B.atomCell_injective ((hg b).symm.trans he)
    exact congrArg g hb
  | @comp x y r hxy tx ty ihx ihy =>
    have hf : (F.toFun x).face true r = (F.toFun y).face false r :=
      (F.map_face true r x).symm.trans
        ((congrArg F.toFun hxy).trans (F.map_face false r y))
    have hc : Cell.comp (F.toFun x) (F.toFun y) r hf = B.atomCell a :=
      (F.map_comp r x y hxy hf).symm.trans he
    rcases B.atom_comp_identity_factor a _ _ r hf hc with hx | hy
    · have hdx := B.dimensionLE_of_expression_image g F hg hd tx r hx
      have hunit := C.comp_of_dimensionLE (Nat.le_refl r) hdx hxy
      exact hunit.trans (ihy ((congrArg F.toFun hunit).symm.trans he))
    · have hdy := B.dimensionLE_of_expression_image g F hg hd ty r hy
      have hunit := comp_eq_left r hxy hdy
      exact hunit.trans (ihx ((congrArg F.toFun hunit).symm.trans he))

/-- Every level-zero positive cell has exactly one preimage. This is the
base of the free-gluing induction on upper-table decomposition levels. -/
theorem unique_preimage_level_zero {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    (hgen : ∀ x : C, Nonempty (CompositionExpression C g x))
    (X : Cell K) (hX : B.AboveAtomOrZero 0 X) : ∃! x : C, F.toFun x = X := by
  obtain ⟨p, b, rfl⟩ := (B.aboveAtomOrZero_zero_iff X).mp hX
  refine ⟨g ⟨p,b⟩, hg ⟨p,b⟩, ?_⟩
  intro x hx
  obtain ⟨t⟩ := hgen x
  exact B.atom_preimage_of_expression g F hg hd t ⟨p,b⟩ hx

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Lifting actual ordered composites through a strict comparison

Uniqueness on the lower faces supplies precisely the matching equations
needed to compose chosen lifts. This is the existence step in the
induction proving free gluing.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem lift_composite_of_unique_faces {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) (r : ℕ)
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    {xs : List (Cell K)} {X : Cell K} (hxs : CompositeList K.realization r xs X)
    (hlift : ∀ Y ∈ xs, ∃ y : C, F.toFun y = Y) : ∃ x : C, F.toFun x = X := by
  refine CompositeList.rec
    (motive := fun (xs : List K.realization) (X : K.realization) _ =>
      (∀ Y ∈ xs, ∃ y : C, F.toFun y = Y) → ∃ x : C, F.toFun x = X)
    ?_ ?_ hxs hlift
  · intro X hlift
    exact hlift X (by simp)
  · intro Y ys Z hys hyz ih hlift
    dsimp only [DirectedComplex.realization] at Y ys Z hyz
    obtain ⟨y, hy⟩ := hlift Y (List.mem_cons_self)
    obtain ⟨z, hz⟩ := ih (fun W hW => hlift W (List.mem_cons_of_mem Y hW))
    obtain ⟨_, _, hu⟩ := hunique (Y.face true r) (B.aboveAtomOrZero_face Y true r)
    have hfy : F.toFun (C.target r y) = Y.face true r := by
      rw [F.map_face, hy]
      rfl
    have hfz : F.toFun (C.source r z) = Y.face true r := by
      rw [F.map_face, hz]
      exact hyz.symm
    have hmatch : C.target r y = C.source r z := (hu _ hfy).trans (hu _ hfz).symm
    refine ⟨C.comp r y z hmatch, ?_⟩
    have hf : (F.toFun y).face true r = (F.toFun z).face false r :=
      (F.map_face true r y).symm.trans
        ((congrArg F.toFun hmatch).trans (F.map_face false r z))
    refine (F.map_comp r y z hmatch hf).trans ?_
    congr 1

theorem exists_preimage_successor {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) (r : ℕ)
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    (X : Cell K) (hX : B.AboveAtomOrZero (r+1) X) : ∃ x : C, F.toFun x = X := by
  obtain ⟨as, hd, he⟩ := B.upper_atom_decomposition r X hX
  by_cases has : as = []
  · subst as
    have hz : B.AboveAtomOrZero r X := Or.inl he
    obtain ⟨x, hx, _⟩ := hunique X hz
    exact ⟨x, hx⟩
  let bs := B.sortAtoms as
  have hp : bs.Perm as := B.sortAtoms_perm as
  have hbd : ∀ b ∈ bs, r < b.1 := fun b hb => hd b (hp.mem_iff.mp hb)
  have hbne : bs.map B.atomCell ≠ [] := by
    intro hz
    have hnil : bs = [] := List.map_eq_nil_iff.mp hz
    have hlen := hp.length_eq
    rw [hnil, List.length_nil] at hlen
    exact has (List.length_eq_zero_iff.mp hlen.symm)
  have hsep : (bs.map B.atomCell).Pairwise (fun A D => ∀ e : B.Index r,
      B.coordinates r (A.table false r) e = 0 ∨
      B.coordinates r (D.table true r) e = 0) := by
    rw [List.pairwise_map]
    apply (B.sortAtoms_pairwise as).imp_of_mem
    intro a b ha hb hab e
    exact B.disjoint a.2 b.2 (hbd a ha) (hbd b hb) hab e
  obtain ⟨xs, hxs, hrel⟩ := B.ordered_list_decomposition r (bs.map B.atomCell)
    hbne hsep X (fun n hn side => (he n hn side).trans (B.sortAtoms_table as side n).symm)
  have hlift : ∀ Y ∈ xs, ∃ y : C, F.toFun y = Y := by
    have hr := List.forall₂_map_left_iff.mp hrel
    have aux : ∀ (as : List B.AtomIndex) (ys : List (Cell K)),
        List.Forall₂ (fun a (Y : Cell K) =>
          ∀ n, r < n → ∀ side, Y.table side n = (B.atomCell a).table side n) as ys →
        (∀ a ∈ as, r < a.1) → ∀ Y ∈ ys, ∃ y : C, F.toFun y = Y := by
      intro as ys h
      induction h with
      | nil => simp
      | @cons a Y' as ys hh ht ih =>
        intro hd Y hY
        rcases List.mem_cons.mp hY with rfl | hY
        · obtain ⟨y, hy, _⟩ := hunique Y
            (Or.inr ⟨a, hd a (by simp), hh⟩)
          exact ⟨y, hy⟩
        · exact ih (fun b hb => hd b (by simp [hb])) Y hY
    exact aux bs xs hr hbd
  exact B.lift_composite_of_unique_faces F r hunique hxs hlift

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Equality of lifted ordered factor strings

An equality of total images and of corresponding upper tables determines
all image factors. Uniqueness at the preceding atom level then determines
the actual source factors individually.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem lifted_compositeList_factors_unique {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) (r : ℕ)
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    {xs ys : List C} {x y : C} (hx : CompositeList C r xs x)
    (hy : CompositeList C r ys y) (he : F.toFun x = F.toFun y)
    (hupper : List.Forall₂ (fun a b : C => ∀ n, r < n → ∀ side,
      (F.toFun a).table side n = (F.toFun b).table side n) xs ys)
    (hlevel : ∀ a ∈ xs, B.AboveAtomOrZero r (F.toFun a)) : xs = ys := by
  have hu : List.Forall₂ (fun A D : Cell K => ∀ n, r < n → ∀ side,
      A.table side n = D.table side n) (xs.map F.toFun) (ys.map F.toFun) := by
    exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr hupper)
  have hm := Cell.compositeList_factors_unique (hx.map F) (hy.map F) he hu
  have aux : ∀ (as bs : List C), as.map F.toFun = bs.map F.toFun →
      (∀ a ∈ as, B.AboveAtomOrZero r (F.toFun a)) → as = bs := by
    intro as
    induction as with
    | nil =>
      intro bs he _
      have hb : bs = [] := List.map_eq_nil_iff.mp he.symm
      exact hb.symm
    | cons a as ih =>
      intro bs he hl
      cases bs with
      | nil => simp at he
      | cons b bs =>
        obtain ⟨hab, ht⟩ := List.cons.inj he
        obtain ⟨_, _, hf⟩ := hunique (F.toFun a) (hl a (by simp))
        have hhead : a = b := (hf a rfl).trans (hf b hab.symm).symm
        exact congrArg₂ List.cons hhead (ih bs ht (fun c hc => hl c (by simp [hc])))
  exact aux xs ys hm hlevel

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # The explicit directed path complex for right cylinders

The degree-zero chains record two endpoints and a chain joining them.
In positive degree the third component has the signed differential forced
by tensoring with an interval on the right. All positivity is componentwise.
-/

namespace Thomason.Construction.DirectedComplex.RightPath

open CategoryTheory

noncomputable section

variable (L : DirectedComplex.{0})

abbrev rawGroup (n : ℕ) := L.group n × L.group n × L.group (n+1)

def rawDifferential (n : ℕ) : rawGroup L (n+1) →+ rawGroup L n where
  toFun x := (L.differential n x.1, L.differential n x.2.1,
    L.differential (n+1) x.2.2 - ((-1 : ℤ)^(n+1)) • (x.2.1 - x.1))
  map_zero' := by simp
  map_add' x y := by
    apply Prod.ext
    · exact map_add (L.differential n) x.1 y.1
    · apply Prod.ext
      · exact map_add (L.differential n) x.2.1 y.2.1
      · simp only [Prod.fst_add, Prod.snd_add, map_add, smul_sub, smul_add]
        abel

def zeroGroup : AddSubgroup (rawGroup L 0) where
  carrier := {x | L.differential 0 x.2.2 = x.2.1 - x.1}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change L.differential 0 x.2.2 = x.2.1 - x.1 at hx
    change L.differential 0 y.2.2 = y.2.1 - y.1 at hy
    change L.differential 0 (x.2.2 + y.2.2) = (x.2.1 + y.2.1) - (x.1 + y.1)
    rw [map_add, hx, hy]
    abel
  neg_mem' {x} hx := by
    change L.differential 0 x.2.2 = x.2.1 - x.1 at hx
    change L.differential 0 (-x.2.2) = -x.2.1 - -x.1
    rw [map_neg, hx]
    abel

theorem rawDifferential_zero_mem (x : rawGroup L 1) :
    rawDifferential L 0 x ∈ zeroGroup L := by
  change L.differential 0 (L.differential 1 x.2.2 - ((-1 : ℤ)^1) • (x.2.1 - x.1)) =
    L.differential 0 x.2.1 - L.differential 0 x.1
  simp [L.differential_squared]

theorem rawDifferential_squared (n : ℕ) (x : rawGroup L (n+2)) :
    rawDifferential L n (rawDifferential L (n+1) x) = 0 := by
  ext <;> simp [rawDifferential, L.differential_squared, pow_succ]

abbrev group : ℕ → AddCommGrpCat.{0}
  | 0 => AddCommGrpCat.of (zeroGroup L)
  | n+1 => AddCommGrpCat.of (rawGroup L (n+1))

def differential : (n : ℕ) → group L (n+1) →+ group L n
  | 0 =>
    { toFun := fun x => ⟨rawDifferential L 0 x, rawDifferential_zero_mem L x⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  | n+1 => rawDifferential L (n+1)

theorem differential_squared (n : ℕ) (x : group L (n+2)) :
    differential L n (differential L (n+1) x) = 0 := by
  cases n with
  | zero => exact Subtype.ext (rawDifferential_squared L 0 x)
  | succ n => exact rawDifferential_squared L (n+1) x

def augmentation : group L 0 →+ ℤ where
  toFun x := L.augmentation x.val.1
  map_zero' := map_zero _
  map_add' x y := map_add _ x.val.1 y.val.1

def rawPositive (n : ℕ) : AddSubmonoid (rawGroup L n) :=
  (L.positive n).prod ((L.positive n).prod (L.positive (n+1)))

def positive : (n : ℕ) → AddSubmonoid (group L n)
  | 0 => (rawPositive L 0).comap (zeroGroup L).subtype
  | n+1 => rawPositive L (n+1)

/-- The path complex has the exact signed differential of the right tensor. -/
abbrev complex : DirectedComplex.{0} where
  group := group L
  differential := differential L
  differential_squared := differential_squared L
  augmentation := augmentation L
  augmentation_differential x := L.augmentation_differential x.1
  positive := positive L

variable {L} {K : DirectedComplex.{0}}

/-- The two endpoint restrictions of an arbitrary chain-cylinder map. -/
def endpoint (f : Hom (rightCylinder K) L) (a : Bool) : Hom K L :=
  Hom.comp (RightCylinder.endpoint K a) f

/-- Evaluation on the shifted interval summand. -/
def shifted (f : Hom (rightCylinder K) L) (n : ℕ) : K.group n →+ L.group (n+1) where
  toFun x := f.app (n+1) (0, 0, x)
  map_zero' := map_zero _
  map_add' x y := by
    rw [← map_add]
    congr 1
    ext <;> simp

theorem apply_zero (f : Hom (rightCylinder K) L) (x : (rightCylinder K).group 0) :
    f.app 0 x = (endpoint f false).app 0 x.1 + (endpoint f true).app 0 x.2 := by
  change f.app 0 x = f.app 0 (x.1, 0) + f.app 0 (0, x.2)
  rw [← map_add]
  congr 1
  ext <;> simp

theorem apply_succ (f : Hom (rightCylinder K) L) (n : ℕ)
    (x : (rightCylinder K).group (n+1)) :
    f.app (n+1) x = (endpoint f false).app (n+1) x.1 +
      (endpoint f true).app (n+1) x.2.1 + shifted f n x.2.2 := by
  dsimp only [endpoint, Hom.comp, RightCylinder.endpoint, RightCylinder.endpointMap,
    AddMonoidHom.comp_apply, shifted]
  change f.app (n+1) x = f.app (n+1) (x.1, 0, 0) +
    f.app (n+1) (0, x.2.1, 0) + f.app (n+1) (0, 0, x.2.2)
  rw [← map_add, ← map_add]
  congr 1
  ext <;> simp

theorem shifted_differential_zero (f : Hom (rightCylinder K) L) (x : K.group 0) :
    L.differential 0 (shifted f 0 x) =
      (endpoint f true).app 0 x - (endpoint f false).app 0 x := by
  have h := f.differential 0 (0, 0, x)
  rw [apply_zero] at h
  change (endpoint f false).app 0 (K.differential 0 0 - x) +
    (endpoint f true).app 0 (K.differential 0 0 + x) = _ at h
  simp only [map_zero, zero_sub, zero_add, map_neg] at h
  exact h.symm.trans (by abel)

theorem shifted_differential_succ (f : Hom (rightCylinder K) L) (n : ℕ)
    (x : K.group (n+1)) :
    L.differential (n+1) (shifted f (n+1) x) =
      ((-1 : ℤ)^(n+1)) • ((endpoint f true).app (n+1) x -
        (endpoint f false).app (n+1) x) + shifted f n (K.differential n x) := by
  have h := f.differential (n+1) (0, 0, x)
  rw [apply_succ] at h
  change (endpoint f false).app (n+1) (K.differential (n+1) 0 - (((-1 : ℤ)^(n+1)) • x)) +
    (endpoint f true).app (n+1) (K.differential (n+1) 0 + (((-1 : ℤ)^(n+1)) • x)) +
    shifted f n (K.differential n x) = _ at h
  simp only [map_zero, zero_sub, zero_add, map_neg, map_zsmul] at h
  exact h.symm.trans (by rw [smul_sub]; abel)

def curryRaw (f : Hom (rightCylinder K) L) (n : ℕ) : K.group n →+ rawGroup L n where
  toFun x := ((endpoint f false).app n x, (endpoint f true).app n x, shifted f n x)
  map_zero' := by simp
  map_add' x y := by simp

def curryApp (f : Hom (rightCylinder K) L) : (n : ℕ) → K.group n →+ (complex L).group n
  | 0 =>
    { toFun := fun x => ⟨curryRaw f 0 x, shifted_differential_zero f x⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  | n+1 => curryRaw f (n+1)

/-- Currying is an actual positive augmented chain map into the path complex. -/
def curry (f : Hom (rightCylinder K) L) : Hom K (complex L) where
  app := curryApp f
  differential n x := by
    cases n with
    | zero =>
      apply Subtype.ext
      apply Prod.ext
      · exact (endpoint f false).differential 0 x
      · apply Prod.ext
        · exact (endpoint f true).differential 0 x
        · change shifted f 0 (K.differential 0 x) =
            L.differential 1 (shifted f 1 x) - ((-1 : ℤ)^1) •
              ((endpoint f true).app 1 x - (endpoint f false).app 1 x)
          rw [shifted_differential_succ]
          abel
    | succ n =>
      apply Prod.ext
      · exact (endpoint f false).differential (n+1) x
      · apply Prod.ext
        · exact (endpoint f true).differential (n+1) x
        · change shifted f (n+1) (K.differential (n+1) x) =
            L.differential (n+2) (shifted f (n+2) x) - ((-1 : ℤ)^(n+2)) •
              ((endpoint f true).app (n+2) x - (endpoint f false).app (n+2) x)
          rw [shifted_differential_succ]
          abel
  augmentation x := (endpoint f false).augmentation x
  positive n x hx := by
    have hs := (endpoint f false).positive n hx
    have ht := (endpoint f true).positive n hx
    have he : shifted f n x ∈ L.positive (n+1) := by
      change f.app (n+1) (0, 0, x) ∈ L.positive (n+1)
      exact f.positive (n+1) (x := (0, 0, x)) ⟨(K.positive (n+1)).zero_mem,
        (K.positive (n+1)).zero_mem, hx⟩
    cases n <;> exact ⟨hs, ht, he⟩

end

end Thomason.Construction.DirectedComplex.RightPath

end

end OAI
