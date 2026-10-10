import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TupleChartDomain

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

def SupportedIn {α : Type*} (g : Equiv.Perm α) (U : Set α) : Prop :=
  ∀ p ∉ U, g p = p

theorem supported_disjoint_commute {α : Type*} {f g : Equiv.Perm α}
    {U V : Set α} (hf : SupportedIn f U) (hg : SupportedIn g V)
    (hUV : Disjoint U V) : Commute f g := by
  apply Equiv.Perm.Disjoint.commute
  intro p
  by_cases hp : p ∈ U
  · exact Or.inr (hg p (fun h => Set.disjoint_left.mp hUV hp h))
  · exact Or.inl (hf p hp)

theorem supported_conjugate {α : Type*} (n : Equiv.Perm α)
    {g : Equiv.Perm α} {U : Set α} (hg : SupportedIn g U) :
    SupportedIn (n * g * n⁻¹) (n '' U) := by
  intro p hp
  have hx : n.symm p ∉ U := by
    intro h
    exact hp ⟨n.symm p,h,n.apply_symm_apply p⟩
  change n (g (n.symm p)) = p
  rw [hg _ hx, n.apply_symm_apply]

open scoped commutatorElement in
theorem double_commutator_of_displacement {G : Type*} [Group G] (n a b : G)
    (ha : Commute (n*a*n⁻¹) a) (hb : Commute (n*a*n⁻¹) b) :
    ⁅⁅n,a⁆,b⁆ = ⁅a⁻¹,b⁆ := by
  have hc : Commute (n*a*n⁻¹) ⁅a⁻¹,b⁆ := by
    simpa only [commutatorElement_def, inv_inv] using
      ((ha.inv_right.mul_right hb).mul_right ha).mul_right hb.inv_right
  change ⁅(n*a*n⁻¹)*a⁻¹,b⁆ = _
  rw [commutatorElement_mul_left_eq_conj_mul, hb.commutator_eq, mul_one,
    hc.eq, mul_assoc, mul_inv_cancel, mul_one]

open scoped commutatorElement in

theorem supported_double_commutator {α : Type*} (n a b : Equiv.Perm α)
    (U : Set α) (ha : SupportedIn a U) (hb : SupportedIn b U)
    (hdis : Disjoint U (n '' U)) : ⁅⁅n,a⁆,b⁆ = ⁅a⁻¹,b⁆ := by
  exact double_commutator_of_displacement n a b
    (supported_disjoint_commute (supported_conjugate n ha) ha hdis.symm)
    (supported_disjoint_commute (supported_conjugate n ha) hb hdis.symm)

theorem ordinary_denseRange : DenseRange ordinary := by
  have hd : Dense (AddSubgroup.closure {Real.goldenRatio, (1 : ℝ)} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (by simpa using Real.goldenRatio_irrational)
  apply hd.mono
  change AddSubgroup.closure {Real.goldenRatio, (1 : ℝ)} ≤ ordinary.toAddMonoidHom.range
  apply (AddSubgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact ⟨cutTau, ordinary_cutTau⟩
  · have hx' : x = 1 := by simpa using hx
    subst x
    exact ⟨1,map_one ordinary⟩

theorem exists_cut_between {x y : ℝ} (hxy : x < y) :
    ∃ c : CutRing, x < ordinary c ∧ ordinary c < y :=
  ordinary_denseRange.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hxy)

instance (a : ℕ) : TopologicalSpace (GenericSquare a) := inferInstanceAs
  (TopologicalSpace {p : ℝ × ℝ // p.1 ∈ Set.Ico 0 1 ∧ p.2 ∈ Set.Ico 0 1 ∧ AvoidsCuts a p})

instance (a : ℕ) : MetricSpace (GenericSquare a) := inferInstanceAs
  (MetricSpace {p : ℝ × ℝ // p.1 ∈ Set.Ico 0 1 ∧ p.2 ∈ Set.Ico 0 1 ∧ AvoidsCuts a p})

theorem cutForm_continuous (a : ℕ) (j : Fin 4) : Continuous (cutForm a j) := by
  fin_cases j
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_snd.sub (continuous_const.mul continuous_fst)
  · exact continuous_fst.sub (continuous_const.mul continuous_snd)

theorem halfPlane_isClopen (a : ℕ) (j : Fin 4) (c : CutRing) :
    IsClopen (halfPlane a j c) := by
  have hc : Continuous (fun p : GenericSquare a => cutForm a j p.val) :=
    (cutForm_continuous a j).comp continuous_subtype_val
  have hopen : IsOpen (halfPlane a j c) := isOpen_lt hc continuous_const
  have he : (halfPlane a j c)ᶜ = {p : GenericSquare a | ordinary c < cutForm a j p.val} := by
    ext p
    simp only [Set.mem_compl_iff, halfPlane, Set.mem_ofPred_eq, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (p.property.2.2 j c).symm, le_of_lt⟩
  exact ⟨isOpen_compl_iff.mp (he ▸ isOpen_lt continuous_const hc), hopen⟩

theorem polygon_isClopen {a : ℕ} (U : polygonAlgebra a) : IsClopen U.val := by
  apply polygon_induction (P := IsClopen) (fun j c => halfPlane_isClopen a j c)
    isClopen_empty (fun _ _ h k => h.union k) (fun _ h => h.compl) U.property

theorem generic_coordinates_pos {a : ℕ} (p : GenericSquare a) :
    0 < p.val.1 ∧ 0 < p.val.2 := by
  constructor
  · exact lt_of_le_of_ne p.property.1.1 (by simpa [cutForm] using (p.property.2.2 0 0).symm)
  · exact lt_of_le_of_ne p.property.2.1.1 (by simpa [cutForm] using (p.property.2.2 1 0).symm)

theorem polygon_contains_rectangle {a : ℕ} (U : polygonAlgebra a)
    (hU : U.val.Nonempty) :
    ∃ l r : CutRing × CutRing,
      0 < ordinary l.1 ∧ ordinary l.1 < ordinary r.1 ∧ ordinary r.1 < 1 ∧
      0 < ordinary l.2 ∧ ordinary l.2 < ordinary r.2 ∧ ordinary r.2 < 1 ∧
      ∀ p : GenericSquare a,
        (ordinary l.1 < p.val.1 ∧ p.val.1 < ordinary r.1) →
        (ordinary l.2 < p.val.2 ∧ p.val.2 < ordinary r.2) → p ∈ U.val := by
  obtain ⟨p,hp⟩ := hU
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (polygon_isClopen U).isOpen p hp
  have hp0 := generic_coordinates_pos p
  obtain ⟨l₁,hl₁,hlp⟩ := exists_cut_between
    (show max 0 (p.val.1-ε) < p.val.1 by exact max_lt hp0.1 (sub_lt_self _ hε))
  obtain ⟨l₂,hl₂,hlq⟩ := exists_cut_between
    (show max 0 (p.val.2-ε) < p.val.2 by exact max_lt hp0.2 (sub_lt_self _ hε))
  obtain ⟨r₁,hpr,hr₁⟩ := exists_cut_between
    (show p.val.1 < min 1 (p.val.1+ε) by exact lt_min p.property.1.2 (lt_add_of_pos_right _ hε))
  obtain ⟨r₂,hqr,hr₂⟩ := exists_cut_between
    (show p.val.2 < min 1 (p.val.2+ε) by exact lt_min p.property.2.1.2 (lt_add_of_pos_right _ hε))
  refine ⟨(l₁,l₂),(r₁,r₂),lt_of_le_of_lt (le_max_left _ _) hl₁,
    hlp.trans hpr,(lt_min_iff.mp hr₁).1,?_,hlq.trans hqr,(lt_min_iff.mp hr₂).1,?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) hl₂
  · intro q hqx hqy
    apply hball
    change max (dist q.val.1 p.val.1) (dist q.val.2 p.val.2) < ε
    rw [max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
    have hx := (max_lt_iff.mp hl₁).2
    have hy := (max_lt_iff.mp hl₂).2
    have hx' := (lt_min_iff.mp hr₁).2
    have hy' := (lt_min_iff.mp hr₂).2
    constructor <;> constructor <;> linarith

noncomputable def smallSquare (a : ℕ) (d : CutRing) : polygonAlgebra a :=
  ⟨halfPlane a 0 d ∩ halfPlane a 1 d,
    BooleanSubalgebra.inf_mem (halfPlane_mem a 0 d) (halfPlane_mem a 1 d)⟩

theorem mem_smallSquare {a : ℕ} (d : CutRing) (p : GenericSquare a) :
    p ∈ (smallSquare a d).val ↔ p.val.1 < ordinary d ∧ p.val.2 < ordinary d := Iff.rfl

theorem smallSquare_nonempty (a : ℕ) {d : CutRing}
    (hd : 0 < ordinary d) (hd1 : ordinary d ≤ 1) :
    (smallSquare a d).val.Nonempty := by
  obtain ⟨p,hx,hy⟩ := generic_rectangle a 0 (ordinary d) 0 (ordinary d)
    le_rfl hd1 hd le_rfl hd1 hd
  exact ⟨p,hx.2,hy.2⟩

noncomputable def fiveRectangleShifts (l : CutRing × CutRing) (d : CutRing)
    (i : Fin 5) : CutRing × CutRing := (l.1 + 2 * (i.val : CutRing)*d, l.2)

theorem fiveRectangleShifts_val {a : ℕ} (l : CutRing × CutRing) (d : CutRing)
    (hlx : 0 < ordinary l.1) (hly : 0 < ordinary l.2)
    (hd : 0 < ordinary d) (hx1 : ordinary l.1 + 9*ordinary d < 1)
    (hy1 : ordinary l.2 + ordinary d < 1) (i : Fin 5)
    (p : (smallSquare a d).val) :
    (translate a (fiveRectangleShifts l d i) p.val).val =
      (p.val.val.1 + ordinary l.1 + 2*(i.val : ℝ)*ordinary d,
       p.val.val.2 + ordinary l.2) := by
  have hp0 := generic_coordinates_pos p.val
  have hpd := (mem_smallSquare d p.val).mp p.property
  have hi : (i.val : ℝ) ≤ 4 := by exact_mod_cast (show i.val ≤ 4 by omega)
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  simp only [translate_val, fiveRectangleShifts, map_add, map_mul, map_ofNat, map_natCast]
  rw [Int.fract_eq_self.mpr ⟨by nlinarith, by nlinarith⟩,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  congr 1
  ring

theorem five_slots_in_polygon {a m : ℕ} (U : polygonAlgebra a)
    (hU : U.val.Nonempty) (t : Fin m) :
    ∃ d : CutRing, 0 < ordinary d ∧ ordinary d < 1 ∧
    ∃ slots : Fin 5 → Fin m × (CutRing × CutRing),
      Function.Injective (SlotMap a m (smallSquare a d) slots) ∧
      Set.range (SlotMap a m (smallSquare a d) slots) ⊆ {p | p.1 = t ∧ p.2 ∈ U.val} := by
  obtain ⟨l,r,hlx,hlr,hrx,hly,hlr',hry,hrect⟩ := polygon_contains_rectangle U hU
  obtain ⟨d,hd,hdlim⟩ := exists_cut_between
    (show (0:ℝ) < min ((ordinary r.1-ordinary l.1)/10) ((ordinary r.2-ordinary l.2)/2) by
      exact lt_min (div_pos (sub_pos.mpr hlr) (by norm_num))
        (div_pos (sub_pos.mpr hlr') (by norm_num)))
  have hxlim := (lt_min_iff.mp hdlim).1
  have hylim := (lt_min_iff.mp hdlim).2
  have hsmall : ordinary d < 1 := by linarith
  have hx1 : ordinary l.1 + 9*ordinary d < 1 := by linarith
  have hy1 : ordinary l.2 + ordinary d < 1 := by linarith
  let slots : Fin 5 → Fin m × (CutRing × CutRing) := fun i => (t,fiveRectangleShifts l d i)
  have hv (i : Fin 5) (p : (smallSquare a d).val) :=
    fiveRectangleShifts_val l d hlx hly hd hx1 hy1 i p
  refine ⟨d,hd,hsmall,slots,?_,?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩ he
    have hx := (mem_smallSquare d x.val).mp x.property
    have hy := (mem_smallSquare d y.val).mp y.property
    have hx0 := generic_coordinates_pos x.val
    have hy0 := generic_coordinates_pos y.val
    have hh := congrArg (fun p : TrackPoint a m => p.2.val.1) he
    change (translate a (fiveRectangleShifts l d i) x.val).val.1 =
      (translate a (fiveRectangleShifts l d j) y.val).val.1 at hh
    rw [hv i x,hv j y] at hh
    have hij : i = j := by
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with h | h | h
      · have h' : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast h
        nlinarith
      · exact h
      · have h' : (j.val : ℝ)+1 ≤ i.val := by exact_mod_cast h
        nlinarith
    subst j
    refine Prod.ext rfl ?_
    apply Subtype.ext
    exact (translation a (fiveRectangleShifts l d i)).injective (congrArg Prod.snd he)
  · rintro p ⟨⟨i,x⟩,rfl⟩
    refine ⟨rfl,?_⟩
    apply hrect
    · change ordinary l.1 < (translate a (fiveRectangleShifts l d i) x.val).val.1 ∧
        (translate a (fiveRectangleShifts l d i) x.val).val.1 < ordinary r.1
      rw [hv i x]
      have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      have hi4 : (i.val : ℝ) ≤ 4 := by exact_mod_cast (show i.val ≤ 4 by omega)
      have hx := (mem_smallSquare d x.val).mp x.property
      have hx0 := generic_coordinates_pos x.val
      constructor <;> nlinarith
    · change ordinary l.2 < (translate a (fiveRectangleShifts l d i) x.val).val.2 ∧
        (translate a (fiveRectangleShifts l d i) x.val).val.2 < ordinary r.2
      rw [hv i x]
      have hx := (mem_smallSquare d x.val).mp x.property
      have hx0 := generic_coordinates_pos x.val
      constructor <;> linarith

noncomputable def translatedPolygon {a : ℕ} (u : CutRing × CutRing)
    (U : polygonAlgebra a) : polygonAlgebra a :=
  ⟨translation a u '' U.val,polygon_image_translation u U.property⟩

private theorem floor_remainder_bounds {a : ℕ} (d : CutRing) (hd : 0 < ordinary d)
    (p : GenericSquare a) (j : Fin 2) :
    let x := ![p.val.1,p.val.2] j
    0 < x - (⌊x/ordinary d⌋ : ℝ)*ordinary d ∧
      x - (⌊x/ordinary d⌋ : ℝ)*ordinary d < ordinary d := by
  dsimp
  let x := ![p.val.1,p.val.2] j
  have hlo : (⌊x/ordinary d⌋ : ℝ)*ordinary d ≤ x :=
    (le_div_iff₀ hd).mp (Int.floor_le _)
  have hhi : x < ((⌊x/ordinary d⌋ : ℝ)+1)*ordinary d :=
    (div_lt_iff₀ hd).mp (Int.lt_floor_add_one _)
  have hne : x ≠ (⌊x/ordinary d⌋ : ℝ)*ordinary d := by
    fin_cases j
    · simpa [x,cutForm] using p.property.2.2 0 ((⌊p.val.1/ordinary d⌋ : ℤ)*d)
    · simpa [x,cutForm] using p.property.2.2 1 ((⌊p.val.2/ordinary d⌋ : ℤ)*d)
  constructor <;> dsimp [x] at *
  · exact sub_pos.mpr (lt_of_le_of_ne hlo (fun h => hne h.symm))
  · linarith

theorem smallSquare_finite_translated_cover (a : ℕ) (d : CutRing)
    (hd : 0 < ordinary d) (hd1 : ordinary d < 1) :
    ∃ s : Finset (CutRing × CutRing), ∀ p : GenericSquare a,
      ∃ u ∈ s, p ∈ (translatedPolygon u (smallSquare a d)).val := by
  classical
  let I := Finset.Icc (0 : ℤ) ⌈1/ordinary d⌉
  let shift : ℤ × ℤ → CutRing × CutRing := fun k => ((k.1 : CutRing)*d,(k.2 : CutRing)*d)
  refine ⟨(I ×ˢ I).image shift,?_⟩
  intro p
  let k : ℤ × ℤ := (⌊p.val.1/ordinary d⌋,⌊p.val.2/ordinary d⌋)
  have hk : k ∈ I ×ˢ I := by
    have hb (x : ℝ) (hx : x ∈ Set.Ico 0 1) : ⌊x/ordinary d⌋ ∈ I := by
      rw [Finset.mem_Icc]
      refine ⟨Int.floor_nonneg.mpr (div_nonneg hx.1 hd.le),?_⟩
      exact (Int.floor_mono (div_le_div_of_nonneg_right hx.2.le hd.le)).trans
        (Int.floor_le_ceil (1/ordinary d))
    exact Finset.mem_product.mpr ⟨hb _ p.property.1,hb _ p.property.2.1⟩
  have hx := floor_remainder_bounds d hd p 0
  have hy := floor_remainder_bounds d hd p 1
  dsimp at hx hy
  let q := translate a (-(shift k)) p
  have hq : q.val = (p.val.1-(k.1:ℝ)*ordinary d,p.val.2-(k.2:ℝ)*ordinary d) := by
    simp only [q,translate_val, Prod.fst_neg,Prod.snd_neg,map_neg,shift,map_mul,map_intCast]
    rw [← sub_eq_add_neg,← sub_eq_add_neg]
    rw [Int.fract_eq_self.mpr ⟨hx.1.le,hx.2.trans hd1⟩,
        Int.fract_eq_self.mpr ⟨hy.1.le,hy.2.trans hd1⟩]
  refine ⟨shift k,Finset.mem_image.mpr ⟨k,hk,rfl⟩,q,?_,?_⟩
  · rw [mem_smallSquare,hq]
    exact ⟨hx.2,hy.2⟩
  · change translate a (shift k) (translate a (-(shift k)) p) = p
    rw [← translate_add, add_neg_cancel, translate_zero]

def bankIndex : Fin 3 × Fin 3 ≃ Fin 9 := finProdFinEquiv

def bankPermutation : Equiv.Perm (Fin 9) :=
  bankIndex.permCongr (Equiv.prodCongr (Equiv.addRight (1 : Fin 3)) (Equiv.refl (Fin 3)))

theorem bankPermutation_even : bankPermutation ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

@[simp] theorem bankPermutation_apply (i j : Fin 3) :
    bankPermutation (bankIndex (i,j)) = bankIndex (i+1,j) := by
  simp [bankPermutation,Equiv.permCongr_apply]

noncomputable def bankSlots {m : ℕ}
    (b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing)) (i : Fin 9) :
    Fin m × (CutRing × CutRing) := b (bankIndex.symm i).1 (bankIndex.symm i).2

@[simp] theorem bankSlots_apply {m : ℕ}
    (b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing)) (i j : Fin 3) :
    bankSlots b (bankIndex (i,j)) = b i j := by
  simp [bankSlots]

theorem bankSlots_injective {a m : ℕ} (U : polygonAlgebra a)
    (b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing))
    (hb : ∀ i, Function.Injective (SlotMap a m U (b i)))
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.range (SlotMap a m U (b i)))
      (Set.range (SlotMap a m U (b j)))) :
    Function.Injective (SlotMap a m U (bankSlots b)) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  obtain ⟨⟨i₁,i₂⟩,rfl⟩ := bankIndex.surjective i
  obtain ⟨⟨j₁,j₂⟩,rfl⟩ := bankIndex.surjective j
  have he' : SlotMap a m U (b i₁) (i₂,x) = SlotMap a m U (b j₁) (j₂,y) := by
    simpa only [SlotMap,bankSlots_apply] using he
  have hij : i₁ = j₁ := by
    by_contra hn
    exact Set.disjoint_left.mp (hdis i₁ j₁ hn) ⟨(i₂,x),rfl⟩ ⟨(j₂,y),he'.symm⟩
  subst j₁
  have hh := hb i₁ he'
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj hh
  subst j₂
  subst y
  rfl

theorem transport_bank {a m : ℕ} (U : polygonAlgebra a)
    (b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing))
    (hb : ∀ i, Function.Injective (SlotMap a m U (b i)))
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.range (SlotMap a m U (b i)))
      (Set.range (SlotMap a m U (b j)))) :
    ∃ g ∈ polygonAlternatingGroup a m, ∀ (i : Fin 3) (x : U.val),
      g.val (SlotMap a m U (b 0) (i,x)) = SlotMap a m U (b 1) (i,x) := by
  let h := bankSlots_injective U b hb hdis
  refine ⟨slotHom U (bankSlots b) h bankPermutation,
    slotHom_alternating_mem U _ h bankPermutation_even,?_⟩
  intro i x
  have he (k : Fin 3) : SlotMap a m U (b k) (i,x) =
      SlotMap a m U (bankSlots b) (bankIndex (k,i),x) := by simp [SlotMap]
  rw [he 0,he 1]
  change slotPerm _ _ _ _ _ = _
  rw [slotPerm_apply,bankPermutation_apply,zero_add]

theorem slot_ranges_disjoint_of_tracks {a m n k : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing))
    (t : Fin k → Fin m × (CutRing × CutRing))
    (h : ∀ i j, (s i).1 ≠ (t j).1) :
    Disjoint (Set.range (SlotMap a m U s)) (Set.range (SlotMap a m U t)) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨⟨i,x⟩,rfl⟩ ⟨⟨j,y⟩,he⟩
  exact h i j (congrArg Prod.fst he).symm

theorem slots_injective_of_tracks {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (h : Function.Injective (fun i => (s i).1)) :
    Function.Injective (SlotMap a m U s) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have htrack : (s i).1 = (s j).1 := congrArg (fun p : TrackPoint a m => p.1) he
  have hij := h htrack
  subst j
  refine Prod.ext rfl ?_
  apply Subtype.ext
  exact (translation a (s i).2).injective (congrArg Prod.snd he)

theorem fresh_nine_tracks {m : ℕ} (hm : 15 ≤ m) (s t : Fin 3 → Fin m) :
    ∃ e : Fin 9 ↪ Fin m, ∀ i j, e i ≠ s j ∧ e i ≠ t j := by
  classical
  let used := Finset.univ.image s ∪ Finset.univ.image t
  have hu : used.card ≤ 6 := by
    apply (Finset.card_union_le _ _).trans
    change _ + _ ≤ 3 + 3
    apply add_le_add <;> exact Finset.card_image_le.trans (by simp)
  have hc : 9 ≤ usedᶜ.card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  have he : Nonempty (Fin 9 ↪ {x : Fin m // x ∈ usedᶜ}) := by
    rw [Function.Embedding.nonempty_iff_card_le,Fintype.card_fin,Fintype.card_coe]
    exact hc
  obtain ⟨e⟩ := he
  refine ⟨e.trans (Function.Embedding.subtype _),?_⟩
  intro i j
  have hn : (e i).val ∉ used := Finset.mem_compl.mp (e i).property
  constructor <;> intro heq <;> apply hn
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,heq.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,heq.symm⟩)

theorem transport_three_slots {a m : ℕ} (hm : 15 ≤ m) (U : polygonAlgebra a)
    (s t : Fin 3 → Fin m × (CutRing × CutRing))
    (hs : Function.Injective (SlotMap a m U s))
    (ht : Function.Injective (SlotMap a m U t)) :
    ∃ g ∈ polygonAlternatingGroup a m, ∀ (i : Fin 3) (x : U.val),
      g.val (SlotMap a m U s (i,x)) = SlotMap a m U t (i,x) := by
  obtain ⟨e,he⟩ := fresh_nine_tracks hm (fun i => (s i).1) (fun i => (t i).1)
  let b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing) :=
    fun k i => (e (bankIndex (k,i)),0)
  have hb (k : Fin 3) : Function.Injective (SlotMap a m U (b k)) := by
    apply slots_injective_of_tracks
    intro i j hij
    exact congrArg Prod.snd (bankIndex.injective (e.injective hij))
  have hbb (k l : Fin 3) (hkl : k ≠ l) :
      Disjoint (Set.range (SlotMap a m U (b k))) (Set.range (SlotMap a m U (b l))) := by
    apply slot_ranges_disjoint_of_tracks
    intro i j hij
    exact hkl (congrArg Prod.fst (bankIndex.injective (e.injective hij)))
  have hsb (k : Fin 3) : Disjoint (Set.range (SlotMap a m U s))
      (Set.range (SlotMap a m U (b k))) := by
    apply slot_ranges_disjoint_of_tracks
    intro i j
    exact (he (bankIndex (k,j)) i).1.symm
  have htb (k : Fin 3) : Disjoint (Set.range (SlotMap a m U t))
      (Set.range (SlotMap a m U (b k))) := by
    apply slot_ranges_disjoint_of_tracks
    intro i j
    exact (he (bankIndex (k,j)) i).2.symm
  have hi₁ : ∀ i, Function.Injective (SlotMap a m U (![s,b 0,b 1] i)) := by
    intro i
    fin_cases i
    · exact hs
    · exact hb 0
    · exact hb 1
  have hd₁ : ∀ i j : Fin 3, i ≠ j →
      Disjoint (Set.range (SlotMap a m U (![s,b 0,b 1] i)))
        (Set.range (SlotMap a m U (![s,b 0,b 1] j))) := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first | exact False.elim (h rfl) | exact hsb 0 | exact hsb 1 |
      exact (hsb 0).symm | exact (hsb 1).symm | exact hbb 0 1 (by decide) |
      exact hbb 1 0 (by decide)
  obtain ⟨g₁,hg₁,hg₁act⟩ := transport_bank U ![s,b 0,b 1] hi₁ hd₁
  have hi₂ : ∀ i, Function.Injective (SlotMap a m U (![b 0,t,b 2] i)) := by
    intro i
    fin_cases i
    · exact hb 0
    · exact ht
    · exact hb 2
  have hd₂ : ∀ i j : Fin 3, i ≠ j →
      Disjoint (Set.range (SlotMap a m U (![b 0,t,b 2] i)))
        (Set.range (SlotMap a m U (![b 0,t,b 2] j))) := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first | exact False.elim (h rfl) | exact htb 0 | exact htb 2 |
      exact (htb 0).symm | exact (htb 2).symm | exact hbb 0 2 (by decide) |
      exact hbb 2 0 (by decide)
  obtain ⟨g₂,hg₂,hg₂act⟩ := transport_bank U ![b 0,t,b 2] hi₂ hd₂
  refine ⟨g₂*g₁,(polygonAlternatingGroup a m).mul_mem hg₂ hg₁,?_⟩
  intro i x
  change g₂.val (g₁.val _) = _
  have h₁ : g₁.val (SlotMap a m U s (i,x)) = SlotMap a m U (b 0) (i,x) := hg₁act i x
  have h₂ : g₂.val (SlotMap a m U (b 0) (i,x)) = SlotMap a m U t (i,x) := hg₂act i x
  rw [h₁,h₂]

end LocalDisplacement
end SimpleAmenable
end
end

end OAI
