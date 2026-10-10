import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PivotPaths02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
noncomputable section
open scoped BigOperators
open MeasureTheory Filter Function
noncomputable section
open scoped BigOperators
namespace SourcePivotPaths
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open ConstructedWordPlan.RationalPivotPlan
open ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (s r : ℕ) (hs : 1 ≤ s)

 
lemma scaleRun_pos (D : Pivot a) (p : Path D) (hp : ∀ o ∈ p, 0 < o.1)
    (j : ℕ) (b : Scale a) (hb : ∀ l, 0 < b l) : ∀ l, 0 < scaleRun D j p b l := by
  induction p generalizing j b with
  | nil => exact hb
  | cons o p ih =>
    apply ih (fun o ho => hp o (List.mem_cons_of_mem _ ho))
    intro l
    exact mul_pos (hb l) (multiplier_pos D.index (tailAt D.tail j)
      (by exact_mod_cast hp o List.mem_cons_self) l)

lemma sourcePlan_positive (Ds : List (Pivot a)) : positivePlan (sourcePlan s r hs Ds) := by
  induction Ds with
  | nil => trivial
  | cons D Ds ih => exact ⟨pivotOptions_paths s r hs D _, ih⟩

lemma source_multipliers_pos (Ds : List (Pivot a)) :
    ∀ b ∈ multipliers (sourcePlan s r hs Ds), ∀ l, 0 < b l := by
  induction Ds with
  | nil =>
    intro b hb
    simp only [multipliers, Finset.mem_singleton] at hb
    subst b
    simp
  | cons D Ds ih =>
    intro b hb
    obtain ⟨p,hp,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hb
    exact fun l => mul_pos
      (scaleRun_pos D p (pivotOptions_paths s r hs D _ p hp).2 0 1 (by simp) l) (ih d hd l)

def nextScales (D : Pivot a) (Ds : List (Pivot a)) (B : Finset (Scale a)) : Finset (Scale a) :=
  B.biUnion (fun b => (pivotOptions s r hs D (multipliers (sourcePlan s r hs Ds))).image
    (fun p => scaleRun D 0 p b))

lemma mem_nextScales (D : Pivot a) (Ds : List (Pivot a)) (B : Finset (Scale a))
    (b : Scale a) (hb : b ∈ B) (p : Path D)
    (hp : p ∈ pivotOptions s r hs D (multipliers (sourcePlan s r hs Ds))) :
    scaleRun D 0 p b ∈ nextScales s r hs D Ds B :=
  Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩

lemma nextScales_pos (D : Pivot a) (Ds : List (Pivot a)) (B : Finset (Scale a))
    (hB : ∀ b ∈ B, ∀ l, 0 < b l) :
    ∀ b ∈ nextScales s r hs D Ds B, ∀ l, 0 < b l := by
  intro b hb
  obtain ⟨b₀,hb₀,hb⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
  exact scaleRun_pos D p (pivotOptions_paths s r hs D _ p hp).2 0 b₀ (hB b₀ hb₀)

 

def planModulus : List (Pivot a) → Finset (Scale a) → ℕ
  | [], _ => 1
  | D :: Ds, B =>
      (pivotModulus s r hs D (multipliers (sourcePlan s r hs Ds)) B *
        ∏ b ∈ B, terminalDenom D s r hs (multipliers (sourcePlan s r hs Ds)) b) *
      planModulus Ds (nextScales s r hs D Ds B)

lemma terminalDenom_pos (D : Pivot a) (Fs : Finset (Scale a)) (b : Scale a) :
    0 < terminalDenom D s r hs Fs b :=
  (source_terminal_arithmetic D (outcomeScales D s r hs Fs b)).choose_spec.1

lemma planModulus_pos (Ds : List (Pivot a)) (B : Finset (Scale a)) :
    0 < planModulus s r hs Ds B := by
  induction Ds generalizing B with
  | nil => exact Nat.zero_lt_one
  | cons D Ds ih =>
    exact Nat.mul_pos (Nat.mul_pos (pivotModulus_pos s r hs D _ B)
      (Finset.prod_pos fun b _ => terminalDenom_pos s r hs D _ b)) (ih _)

lemma planModulus_head (D : Pivot a) (Ds : List (Pivot a)) (B : Finset (Scale a)) :
    pivotModulus s r hs D (multipliers (sourcePlan s r hs Ds)) B ∣ planModulus s r hs (D :: Ds) B :=
  dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _)

lemma planModulus_terminal (D : Pivot a) (Ds : List (Pivot a)) (B : Finset (Scale a))
    (b : Scale a) (hb : b ∈ B) :
    terminalDenom D s r hs (multipliers (sourcePlan s r hs Ds)) b ∣ planModulus s r hs (D :: Ds) B :=
  dvd_trans (Finset.dvd_prod_of_mem _ hb) (dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _))

lemma planModulus_tail (D : Pivot a) (Ds : List (Pivot a)) (B : Finset (Scale a)) :
    planModulus s r hs Ds (nextScales s r hs D Ds B) ∣ planModulus s r hs (D :: Ds) B :=
  dvd_mul_left _ _

end SourcePivotPaths

 

 

 

noncomputable section
open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
namespace SourceChartedAlignment
open RationalLattice MalcevCharacters CubeFaces
open MicrocellScale AdmissibleMicrocellBoundary RoughScales
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open SourceIntegerArrays
open ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
open SourceIntegerArrays.GlobalJoint.SourceExposureSlots ProductExposureLaw SourceResidueAlignment
open ConstructedWordPlan.RationalPivotPlan

structure CommonScales (a : ℕ) where
  w : ℕ → ℕ
  M : ℕ → ℕ
  X : ℕ → Fin a → ℕ
  ht : ℕ → Fin a → ℤ
  L : ℕ → ℤ
  hw : Tendsto w atTop atTop
  hX : ∀ N j, 4 * primorial (w N) ≤ X N j
  hXt : ∀ j, Tendsto (fun N => X N j) atTop atTop
  hWM : ∀ N, (primorial (w N) : ℤ) ∣ (M N : ℤ)
  hM : ∀ N, 0 < M N
  hMs : ∀ N, RoughScales.Smooth (w N) (M N : ℤ)
  hL : ∀ N, 0 < L N
  hLs : ∀ N, RoughScales.Smooth (w N) (L N)
  hWL : ∀ N, (primorial (w N) : ℤ) ∣ L N
  hML : ∀ N, (M N : ℤ) ∣ L N
  hLexact : ∀ N, L N = (M N : ℤ) * (primorial (w N) : ℤ) ^ w N
  hpowWM : ∀ N, primorial (w N) ^ w N ∣ M N
  hht : ∀ N j, 0 < ht N j
  hXL : ∀ j, Tendsto (fun N => (X N j : ℝ) / (L N : ℝ)) atTop atTop

structure PivotScales {a : ℕ} (C : CommonScales a) (D : Pivot a) where
  H : ℕ → ℕ
  J : ℕ → ℕ
  R : ℕ → ℕ
  hJ : ∀ N, 0 < J N
  hRJ : ∀ N, R N = C.M N * J N
  hH : ∀ N, 0 < H N
  hRrad : ∀ N, R N = radius (C.M N) (H N)
  hdom : Dominates (fun N => (H N : ℝ)) (earlierScale C.M (fun N => previousProduct D (C.X N)))
  hxdom : Dominates (fun N => Real.log (C.X N D.index : ℝ)) (fun N => (H N : ℝ))
  hheight : ∀ N e, height (C.ht N) (D.added e) ≤ C.M N
  hdisj : ∀ e, Disjoint (D.added e) (D.tail (D.owner e))
  hratio : ∀ N e, ∃ d : ℤ, height (C.ht N) (D.added e) =
    height (C.ht N) (block D.index D.tail (D.owner e)) *
      ((primorial (C.w N) : ℤ) ^ C.w N * d)

structure ChartedModels {a : ℕ} (s r : ℕ) (D : Pivot a) where
  G : Fin D.targets → ℚ → Fin r → Type
  [group : ∀ t v c, Group (G t v c)]
  [topology : ∀ t v c, TopologicalSpace (G t v c)]
  [topGroup : ∀ t v c, IsTopologicalGroup (G t v c)]
  Γ : ∀ t v c, Subgroup (G t v c)
  dim : Fin D.targets → ℚ → Fin r → ℕ
  coords : ∀ t v c, RealCoordinates (G t v c) (dim t v c)
  second : ∀ t v c, SecondKind (coords t v c)
  filtration : ∀ t v c, CubeFaces.Filtration (G t v c)
  weight : ∀ t v c, Fin (dim t v c) → ℕ
  level_iff : ∀ t v c k (g : G t v c), g ∈ (filtration t v c).level k ↔
    ∀ j, weight t v c j < k → (coords t v c).coord g j = 0
  weight_pos : ∀ t v c j, 0 < weight t v c j
  lattice_iff : ∀ t v c g, g ∈ Γ t v c ↔ ∀ j, ∃ z : ℤ, (coords t v c).coord g j = z
  weight_mono : ∀ t v c, Monotone (weight t v c)
  level0 : ∀ t v c, (filtration t v c).level 0 = ⊤
  level1 : ∀ t v c, (filtration t v c).level 1 = ⊤
  step : ∀ t v c, (filtration t v c).level (s+1) = ⊥
  g : ∀ t, ℕ → ∀ v c, ℤ → ℤ → G t v c
  x : ∀ t, ℕ → ∀ v c, ℤ → ℤ → G t v c
  obs : ∀ t, ℕ → ∀ v c, ℤ → ℤ → ((G t v c) ⧸ Γ t v c) →ᵇ ℝ
  metric : ∀ t v c, MetricSpace ((G t v c) ⧸ Γ t v c)
  compatible : ∀ t v c, QuotientGroup.instTopologicalSpace (Γ t v c) =
    (metric t v c).toUniformSpace.toTopologicalSpace
  K : ℝ≥0
  B : ℝ
  lip : letI : ∀ t v c, MetricSpace ((G t v c) ⧸ Γ t v c) :=
      fun t v c => (metric t v c).replaceTopology (compatible t v c)
    ∀ t N v c b r', LipschitzWith K (obs t N v c b r')
  bound : ∀ t N v c b r' z, |obs t N v c b r' z| ≤ B

attribute [instance] ChartedModels.group ChartedModels.topology ChartedModels.topGroup

variable {a : ℕ}
def CommonScales.law (C : CommonScales a) (N : ℕ) : Measure (Fin a → ℕ) :=
  outsideLaw (C.X N) (primorial (C.w N)) (primorial_pos _) (C.hX N)

instance (C : CommonScales a) (N : ℕ) : IsProbabilityMeasure (C.law N) := by
  unfold CommonScales.law
  infer_instance

def ChartedModels.scalar {s r : ℕ} {D : Pivot a} (C : CommonScales a) (P : PivotScales C D)
    (F : ChartedModels s r D) (N : ℕ) : SourcePivotPaths.ScalarModels D r :=
  SourcePivotPaths.scalarModels D r F.G F.Γ C.M P.H F.g F.x F.obs N

end SourceChartedAlignment

 

 

 

noncomputable section
open scoped Topology BigOperators
namespace SourceProductCoordinates
open RationalLattice MalcevCharacters
attribute [local instance] Classical.propDecidable
variable {d N : ℕ} (n : Fin d → ℕ)
  (G : Fin d → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  (c : ∀ i, RealCoordinates (G i) (n i))
  (e : Fin N ≃ Σ i, Fin (n i))
  (he : ∀ i, StrictMono (fun j : Fin (n i) => e.symm ⟨i,j⟩))

 
def homeomorph : (∀ i, G i) ≃ₜ (Fin N → ℝ) where
  toFun g k := (c (e k).1).coord (g (e k).1) (e k).2
  invFun v i := (c i).coord.symm (fun j => v (e.symm ⟨i,j⟩))
  left_inv g := by
    funext i
    apply (c i).coord.injective
    ext j
    simp only [Homeomorph.apply_symm_apply]
    exact congrArg (fun z : Σ i, Fin (n i) => (c z.1).coord (g z.1) z.2)
      (e.apply_symm_apply ⟨i,j⟩)
  right_inv v := by
    funext k
    simp
  continuous_toFun := continuous_pi fun k =>
    (continuous_apply (e k).2).comp ((c (e k).1).coord.continuous.comp (continuous_apply (e k).1))
  continuous_invFun := continuous_pi fun i =>
    (c i).coord.symm.continuous.comp (continuous_pi fun j => continuous_apply (e.symm ⟨i,j⟩))

 
def lower (k : Fin N) (j : Fin (e k).2.val) : Fin k.val :=
  ⟨(e.symm ⟨(e k).1,⟨j.val,lt_trans j.isLt (e k).2.isLt⟩⟩).val, by
    have h := he (e k).1 (show (⟨j.val,lt_trans j.isLt (e k).2.isLt⟩ : Fin (n (e k).1)) < (e k).2 from j.isLt)
    simpa only [Sigma.eta, Equiv.symm_apply_apply, Fin.lt_def] using h⟩

lemma homeomorph_lower (g : ∀ i, G i) (k : Fin N) (j : Fin (e k).2.val) :
    homeomorph n G c e g ⟨(lower n e he k j).val,lt_trans (lower n e he k j).isLt k.isLt⟩ =
      (c (e k).1).coord (g (e k).1) ⟨j.val,lt_trans j.isLt (e k).2.isLt⟩ := by
  change (c (e (e.symm _)).1).coord (g (e (e.symm _)).1) (e (e.symm _)).2 = _
  exact congrArg (fun z : Σ i, Fin (n i) => (c z.1).coord (g z.1) z.2)
    (e.apply_symm_apply _)

 
def coordinates : RealCoordinates (∀ i, G i) N where
  coord := homeomorph n G c e
  one_coord k := (c (e k).1).one_coord (e k).2
  correction k := MvPolynomial.rename (Sum.map (lower n e he k) (lower n e he k))
    ((c (e k).1).correction (e k).2)
  mul_coord g h k := by
    change (c (e k).1).coord (g (e k).1 * h (e k).1) (e k).2 = _
    rw [(c (e k).1).mul_coord]
    congr 1
    rw [MvPolynomial.eval₂_rename]
    congr 1
    funext j
    cases j with
    | inl j => exact (homeomorph_lower n G c e he g k j).symm
    | inr j => exact (homeomorph_lower n G c e he h k j).symm

 
def select (i : Fin d) (k : Fin N) : Option (Fin (n i)) :=
  if h : (e k).1 = i then some (h ▸ (e k).2) else none

lemma select_some_iff (i : Fin d) (k : Fin N) (j : Fin (n i)) :
    select n e i k = some j ↔ e k = ⟨i,j⟩ := by
  unfold select
  split_ifs with h
  · subst i
    simp only [Option.some.injEq]
    constructor
    · intro h
      cases h
      rfl
    · intro h
      exact eq_of_heq (Sigma.mk.inj h).2
  · constructor
    · intro h'
      cases h'
    · intro h'
      exact False.elim (h (congrArg Sigma.fst h'))

include he in
lemma select_enumeration (i : Fin d) :
    (List.ofFn (fun k : Fin N => k)).filterMap (select n e i) =
      List.ofFn (fun j : Fin (n i) => j) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · apply List.pairwise_filterMap.mpr
    apply List.pairwise_ofFn.mpr
    intro k l hkl j hj j' hj'
    have hk : e.symm ⟨i,j⟩ = k := e.symm_apply_eq.mpr ((select_some_iff n e i k j).mp hj).symm
    have hl : e.symm ⟨i,j'⟩ = l := e.symm_apply_eq.mpr ((select_some_iff n e i l j').mp hj').symm
    exact (he i).lt_iff_lt.mp (by simpa only [hk,hl] using hkl)
  · exact List.pairwise_ofFn.mpr (fun _ _ h => h)
  · intro j
    simp only [List.mem_filterMap, List.mem_ofFn]
    constructor
    · intro h
      exact ⟨j,rfl⟩
    · intro h
      refine ⟨e.symm ⟨i,j⟩,⟨e.symm ⟨i,j⟩,rfl⟩,?_⟩
      exact (select_some_iff n e i _ j).mpr (e.apply_symm_apply _)

lemma axis_selected (k : Fin N) (t : ℝ) (i : Fin d) (j : Fin (n i))
    (hk : e k = ⟨i,j⟩) :
    axis (coordinates n G c e he) k t i = axis (c i) j t := by
  apply (c i).coord.injective
  ext v
  change (c i).coord ((c i).coord.symm (fun v => (Pi.single k t : Fin N → ℝ) (e.symm ⟨i,v⟩))) v = _
  rw [(c i).coord.apply_symm_apply]
  simp only [axis, Homeomorph.apply_symm_apply]
  have hkv : e.symm ⟨i,v⟩ = k ↔ v=j := by
    rw [e.symm_apply_eq, hk]
    constructor
    · intro h
      exact eq_of_heq (Sigma.mk.inj h).2
    · rintro rfl
      rfl
  simp only [Pi.single_apply, hkv]

lemma axis_other (k : Fin N) (t : ℝ) (i : Fin d) (hk : (e k).1 ≠ i) :
    axis (coordinates n G c e he) k t i = 1 := by
  apply (c i).coord.injective
  ext v
  change (c i).coord ((c i).coord.symm (fun v => (Pi.single k t : Fin N → ℝ) (e.symm ⟨i,v⟩))) v = _
  rw [(c i).coord.apply_symm_apply, (c i).one_coord]
  apply Pi.single_eq_of_ne
  intro h
  have h' := e.symm_apply_eq.mp h
  exact hk (congrArg Sigma.fst h').symm

 
lemma prod_select {α β M : Type*} [Monoid M] (l : List α)
    (f : α → Option β) (g : β → M) (h : α → M)
    (hh : ∀ x, h x = (f x).elim 1 g) :
    (l.map h).prod = ((l.filterMap f).map g).prod := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hf : f x with
    | none => simpa [hh x, hf] using ih
    | some y => simpa [hh x, hf] using congrArg (fun z => g y*z) ih

 

theorem secondKind (hs : ∀ i, SecondKind (c i)) :
    SecondKind (coordinates n G c e he) where
  axis_add k s t := by
    funext i
    by_cases hi : (e k).1 = i
    · subst i
      rw [axis_selected n G c e he k (s+t) (e k).1 (e k).2 rfl,
        Pi.mul_apply, axis_selected n G c e he k s (e k).1 (e k).2 rfl,
        axis_selected n G c e he k t (e k).1 (e k).2 rfl]
      exact (hs _).axis_add _ _ _
    · rw [axis_other n G c e he k (s+t) i hi, Pi.mul_apply,
        axis_other n G c e he k s i hi, axis_other n G c e he k t i hi, one_mul]
  ordered g := by
    funext i
    change g i = (Pi.evalMonoidHom G i)
      (List.ofFn (fun k => axis (coordinates n G c e he) k ((coordinates n G c e he).coord g k))).prod
    rw [map_list_prod, List.map_ofFn]
    change g i = (List.ofFn (fun k : Fin N =>
      axis (coordinates n G c e he) k ((coordinates n G c e he).coord g k) i)).prod
    have hprod := prod_select (List.ofFn (fun k : Fin N => k)) (select n e i)
      (fun j => axis (c i) j ((c i).coord (g i) j))
      (fun k => axis (coordinates n G c e he) k ((coordinates n G c e he).coord g k) i) (by
        intro k
        by_cases hi : (e k).1 = i
        · have hk : e k = ⟨i,hi ▸ (e k).2⟩ := by cases hi; rfl
          rw [select, dite_eq_left hi, Option.elim_some, axis_selected n G c e he _ _ _ _ hk]
          congr 1
          change (c (e k).1).coord (g (e k).1) (e k).2 = _
          exact congrArg (fun z : Σ i, Fin (n i) => (c z.1).coord (g z.1) z.2) hk
        · rw [select, dite_eq_right hi, Option.elim_none, axis_other n G c e he _ _ _ hi])
    rw [List.map_ofFn, select_enumeration n e he i, List.map_ofFn] at hprod
    exact ((hs i).ordered (g i)).trans hprod.symm

end SourceProductCoordinates

 

 

 

end
end
end
end
end
end
end

end OAI
