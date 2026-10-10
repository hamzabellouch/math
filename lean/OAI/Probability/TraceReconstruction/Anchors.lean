import OAI.Probability.TraceReconstruction.LeafOracle

namespace OAI

/-!
# Anchors

Forced anchors, extra-leaf closeness, and correlated group square-sum estimates.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

namespace FiniteLaw
/-- Two distinct actual child coordinates are independent. This does not
assert independence of their shared parent-global jitter. -/
theorem coordinateProduct_expect_two {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin n → FiniteLaw α) (a c : Fin n) (hne : a≠c) (f h : α → ℝ) :
    (coordinateProduct P).expect (fun x => f (x a)*h (x c)) = (P a).expect f*(P c).expect h := by
  let F : Fin n → α → ℝ := fun j x => if j=a then f x else if j=c then h x else 1
  have hp : ∀x : Fin n → α, (∏j,F j (x j)) = f (x a)*h (x c) := by
    intro x
    rw [Finset.prod_eq_mul a c hne]
    · simp [F,hne.symm]
    · intro j hj hjs
      simp [F,hjs.1,hjs.2]
    · simp
    · simp
  rw [show (fun x : Fin n → α => f (x a)*h (x c)) = (fun x => ∏j,F j (x j)) by
    funext x; exact (hp x).symm,coordinateProduct_expect_product]
  rw [Finset.prod_eq_mul a c hne]
  · simp [F,hne.symm]
  · intro j hj hjs
    simp [F,hjs.1,hjs.2,expect_const]
  · simp
  · simp

/-- Exact local/global/children factorization with the parent-global draw
outside the product of child expectations. -/
theorem expect_prod_two {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {n : ℕ} (P : FiniteLaw α) (Q : FiniteLaw β) (R : Fin n → FiniteLaw γ)
    (a c : Fin n) (hne : a≠c) (f : α → ℝ) (h k : β → γ → ℝ) :
    (P.prod (Q.prod (coordinateProduct R))).expect (fun x =>
      f x.1 * (h x.2.1 (x.2.2 a)*k x.2.1 (x.2.2 c))) =
      P.expect f * Q.expect (fun z => (R a).expect (h z)*(R c).expect (k z)) := by
  simp_rw [expect_prod,expect_const_mul,coordinateProduct_expect_two R a c hne]
  rw [expect_mul_const]
end FiniteLaw

/-- A concrete binary selection of labels in the complete index tree.
Unlike a free abstract shape this retains every actual column label. -/
def BinaryWindowLabels (T : ℕ → ℕ) : ℕ → Type
  | 0 => PUnit
  | b+1 => Fin (T b) × Fin (T b) × BinaryWindowLabels T b × BinaryWindowLabels T b

noncomputable instance binaryWindowLabelsFintype (T : ℕ → ℕ) :
    (b : ℕ) → Fintype (BinaryWindowLabels T b)
  | 0 => inferInstanceAs (Fintype PUnit)
  | b+1 => by
      letI := binaryWindowLabelsFintype T b
      exact inferInstanceAs (Fintype (Fin (T b) × Fin (T b) × BinaryWindowLabels T b × BinaryWindowLabels T b))

/-- The forced children are distinct at every split. Central restrictions
are separate deterministic predicates, not conditioning events. -/
def BinaryWindowLabels.distinct (T : ℕ → ℕ) : (b : ℕ) → BinaryWindowLabels T b → Prop
  | 0, _ => True
  | b+1, p => p.1≠p.2.1 ∧ distinct T b p.2.2.1 ∧ distinct T b p.2.2.2

/-- Product of the first-child unsigned anchor at every forced nonleaf,
evaluated using the literal complete-tree orientation assignment. -/
def binaryAnchorKernel (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → BinaryWindowLabels T b → WindowAssignments T n g Bool b → ℤ → ℝ
  | 0, _, _, _ => 1
  | b+1, p, bits, incoming =>
      motifIndicator s ((p.1.val:ℤ)-center b+(∑i,(bitIndex (bits.1 i):ℤ))+incoming) *
      (binaryAnchorKernel T n g s center globalShift b p.2.2.1 (bits.2.2 p.1)
        (globalShift b bits.2.1 p.1) *
       binaryAnchorKernel T n g s center globalShift b p.2.2.2 (bits.2.2 p.2.1)
        (globalShift b bits.2.1 p.2.1))

def binaryAnchorAverage (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T b) (d : WindowAssignments T n g (Option Bool) b)
    (incoming : ℤ) : ℝ :=
  (windowPosteriorLaw T n g b d).expect (fun bits =>
    binaryAnchorKernel T n g s center globalShift b p bits incoming)

theorem binaryAnchorAverage_zero (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (p : BinaryWindowLabels T 0) (d : WindowAssignments T n g (Option Bool) 0) (incoming : ℤ) :
    binaryAnchorAverage T n g s center globalShift 0 p d incoming = 1 := by
  apply expect_const

theorem binaryAnchorAverage_succ (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T (b+1)) (d : WindowAssignments T n g (Option Bool) (b+1))
    (incoming : ℤ) (hd : p.1≠p.2.1) :
    binaryAnchorAverage T n g s center globalShift (b+1) p d incoming =
      (posteriorArray d.1).expect (fun loc =>
        motifIndicator s ((p.1.val:ℤ)-center b+(∑i,(bitIndex (loc i):ℤ))+incoming)) *
      (posteriorArray d.2.1).expect (fun glob =>
        binaryAnchorAverage T n g s center globalShift b p.2.2.1 (d.2.2 p.1)
          (globalShift b glob p.1) *
        binaryAnchorAverage T n g s center globalShift b p.2.2.2 (d.2.2 p.2.1)
          (globalShift b glob p.2.1)) := by
  exact FiniteLaw.expect_prod_two (posteriorArray d.1) (posteriorArray d.2.1)
    (fun i => windowPosteriorLaw T n g b (d.2.2 i)) p.1 p.2.1 hd
    (fun loc => motifIndicator s ((p.1.val:ℤ)-center b+(∑i,(bitIndex (loc i):ℤ))+incoming))
    (fun glob bits => binaryAnchorKernel T n g s center globalShift b p.2.2.1 bits
      (globalShift b glob p.1))
    (fun glob bits => binaryAnchorKernel T n g s center globalShift b p.2.2.2 bits
      (globalShift b glob p.2.1))

/-- Local unsigned anchor averaged against its actual known/hidden flags. -/
def localAnchorAverage {m : ℕ} (d : Fin m → Option Bool) (s : ℕ) (z : ℤ) : ℝ :=
  (posteriorArray d).expect (fun bits => motifIndicator s (z+∑i,(bitIndex (bits i):ℤ)))

theorem localAnchorAverage_kernel {m : ℕ} (d : Fin m → Option Bool) (s : ℕ) (z : ℤ) :
    localAnchorAverage d s z = windowKernel (∑i,hiddenTrial (d i)) (2^s)
      (z+∑i,(visibleOnes (d i):ℤ)) := by
  have h := posterior_unsigned_motif d s z
  unfold localAnchorAverage posteriorArray coordinateProduct expect
  convert h using 1
  congr 2
  exact Subsingleton.elim _ _

/-- Product of all lower sibling-group factors. Each group still averages
its own single common global draw, not two independent global draws. -/
def binaryAnchorBelow (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → BinaryWindowLabels T (b+1) → WindowAssignments T n g (Option Bool) (b+1) → ℝ
  | 0, _, _ => 1
  | b+1, p, d =>
      (posteriorArray d.2.1).expect (fun glob =>
        localAnchorAverage (d.2.2 p.1).1 s
          ((p.2.2.1.1.val:ℤ)-center b+globalShift (b+1) glob p.1) *
        localAnchorAverage (d.2.2 p.2.1).1 s
          ((p.2.2.2.1.val:ℤ)-center b+globalShift (b+1) glob p.2.1)) *
      (binaryAnchorBelow T n g s center globalShift b p.2.2.1 (d.2.2 p.1) *
       binaryAnchorBelow T n g s center globalShift b p.2.2.2 (d.2.2 p.2.1))

/-- Exact factorization of the forced anchor expectation into its root
kernel and all correlated sibling groups, at the real metadata/labels. -/
theorem binaryAnchorAverage_factor (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T (b+1)) (d : WindowAssignments T n g (Option Bool) (b+1))
    (incoming : ℤ) (hd : BinaryWindowLabels.distinct T (b+1) p) :
    binaryAnchorAverage T n g s center globalShift (b+1) p d incoming =
      localAnchorAverage d.1 s ((p.1.val:ℤ)-center b+incoming) *
        binaryAnchorBelow T n g s center globalShift b p d := by
  induction b generalizing incoming with
  | zero =>
    rw [binaryAnchorAverage_succ T n g s center globalShift _ p d incoming hd.1]
    simp only [binaryAnchorAverage_zero,expect_const,binaryAnchorBelow,mul_one]
    unfold localAnchorAverage
    congr 1
    funext loc
    congr 1
    omega
  | succ b ih =>
    have hl := fun incoming => ih p.2.2.1 (d.2.2 p.1) incoming hd.2.1
    have hr := fun incoming => ih p.2.2.2 (d.2.2 p.2.1) incoming hd.2.2
    have hroot : (posteriorArray d.1).expect (fun loc =>
        motifIndicator s ((p.1.val:ℤ)-center (b+1)+(∑i,(bitIndex (loc i):ℤ))+incoming)) =
        localAnchorAverage d.1 s ((p.1.val:ℤ)-center (b+1)+incoming) := by
      apply congrArg (FiniteLaw.expect (posteriorArray d.1))
      funext loc
      congr 1
      omega
    have hh : (posteriorArray d.2.1).expect (fun glob =>
        binaryAnchorAverage T n g s center globalShift (b+1) p.2.2.1 (d.2.2 p.1)
          (globalShift (b+1) glob p.1) *
        binaryAnchorAverage T n g s center globalShift (b+1) p.2.2.2 (d.2.2 p.2.1)
          (globalShift (b+1) glob p.2.1)) =
        binaryAnchorBelow T n g s center globalShift (b+1) p d := by
      calc
        _ = (posteriorArray d.2.1).expect (fun glob =>
          (localAnchorAverage (d.2.2 p.1).1 s
            ((p.2.2.1.1.val:ℤ)-center b+globalShift (b+1) glob p.1) *
          localAnchorAverage (d.2.2 p.2.1).1 s
            ((p.2.2.2.1.val:ℤ)-center b+globalShift (b+1) glob p.2.1)) *
          (binaryAnchorBelow T n g s center globalShift b p.2.2.1 (d.2.2 p.1) *
           binaryAnchorBelow T n g s center globalShift b p.2.2.2 (d.2.2 p.2.1))) := by
            apply congrArg (FiniteLaw.expect (posteriorArray d.2.1))
            funext glob
            exact (congrArg₂ (·*·) (hl _) (hr _)).trans (by ring)
        _ = _ := expect_mul_const _ _ _
    exact (binaryAnchorAverage_succ T n g s center globalShift _ p d incoming hd.1).trans
      (congrArg₂ (·*·) hroot hh)

/-- One plateau group's local means are the genuine shared-global joint
anchor, with exactly the affine shift appearing in the layout. -/
theorem localAnchor_pair_plateau {mg m₁ m₂ : ℕ}
    (dg : Fin mg → Option Bool) (d₁ : Fin m₁ → Option Bool) (d₂ : Fin m₂ → Option Bool)
    (s : ℕ) (z₁ z₂ shift : ℤ) :
    (posteriorArray dg).expect (fun glob =>
      localAnchorAverage d₁ s (z₁+(∑i,(bitIndex (glob i):ℤ))-shift) *
      localAnchorAverage d₂ s (z₂+(∑i,(bitIndex (glob i):ℤ))-shift)) =
    posteriorJointAnchors dg d₁ d₂ s (z₁-shift) (z₂-shift) := by
  unfold localAnchorAverage posteriorArray coordinateProduct expect posteriorJointAnchors
  have he : ∀a b c d : ℤ,(a+b-c)+d = (a-c)+b+d := by intros; omega
  simp_rw [he,mul_assoc]
  congr 2
  · exact Subsingleton.elim _ _
  · funext bg
    congr 1
    congr 1
    · congr 2 ; exact Subsingleton.elim _ _
    · congr 2 ; exact Subsingleton.elim _ _

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- A role-selected forced subtree remembers the actual complete-tree labels,
not merely its abstract binary shape. -/
def forcedWindowLabels (T : ℕ → ℕ) : (b : ℕ) →
    (S : Finset (WindowLeaf T (b+1))) → (a : OccupiedWindowChoice T b S) →
    (occupiedWindowTerm T b S a).Forced → BinaryWindowLabels T (b+1)
  | 0, S, _, .node i j _ _ _ _ _ =>
      ((S.equivFin.symm i).val.1,(S.equivFin.symm j).val.1,PUnit.unit,PUnit.unit)
  | b+1, S, a, .node i j _ _ _ left right =>
      (((selectedChildren S).equivFin.symm i).val,
       ((selectedChildren S).equivFin.symm j).val,
       forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)
         (a.1 i) left,
       forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val)
         (a.1 j) right)

theorem forcedWindowLabels_distinct (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    BinaryWindowLabels.distinct T (b+1) (forcedWindowLabels T b S a F) := by
  induction b with
  | zero =>
    cases F with
    | node i j hne hi hj left right =>
      refine ⟨?_,trivial,trivial⟩
      intro he
      apply hne
      apply S.equivFin.symm.injective
      apply Subtype.ext
      exact Prod.ext he (Subsingleton.elim (α := Fin 1) _ _)
  | succ b ih =>
    cases F with
    | node i j hne hi hj left right =>
      refine ⟨?_,ih _ _ left,ih _ _ right⟩
      intro he
      exact hne ((selectedChildren S).equivFin.symm.injective (Subtype.ext he))

theorem motifIndicator_nonneg (s : ℕ) (z : ℤ) : 0 ≤ motifIndicator s z := by
  unfold motifIndicator
  split_ifs <;> norm_num

theorem motifIndicator_le_one (s : ℕ) (z : ℤ) : motifIndicator s z≤1 := by
  unfold motifIndicator
  split_ifs <;> norm_num

theorem binaryAnchorKernel_nonneg (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T b) (bits : WindowAssignments T n g Bool b)
    (incoming : ℤ) : 0≤binaryAnchorKernel T n g s center globalShift b p bits incoming := by
  induction b generalizing incoming with
  | zero => exact zero_le_one
  | succ b ih =>
    exact mul_nonneg (motifIndicator_nonneg _ _) (mul_nonneg (ih _ _ _) (ih _ _ _))

theorem bottomRoleWeight_abs_le_indicator (χ σ : ℝ) (h : IsMotifValue χ σ) (a : Fin 3) :
    |bottomRoleWeight χ σ a|≤χ := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩ <;>
    fin_cases a <;> norm_num [bottomRoleWeight]

theorem internalRoleWeight_active_abs_le_indicator (odd : Prop) [Decidable odd]
    (χ σ : ℝ) (h : IsMotifValue χ σ) (a : Fin 3) (ha : a≠0) :
    |internalRoleWeight odd χ σ a|≤χ := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩ <;>
    fin_cases a <;> by_cases ho : odd <;> norm_num [internalRoleWeight,roleWeight,ho] at *

theorem occupiedRootWeight_bottom_anchor (T : ℕ → ℕ) (s : ℕ)
    (S : Finset (WindowLeaf T 1)) (a : OccupiedWindowChoice T 0 S) (X : ℤ) (i : Fin S.card) :
    |occupiedRootWeight T s 0 S a X|≤
      motifIndicator s (((S.equivFin.symm i).val.1.val:ℤ)-X) := by
  exact (abs_prod_le_coordinate _ i (fun j _ =>
    bottomRoleWeight_abs_le_one _ _ (prouhet_motif_value _ _) _)).trans
      (bottomRoleWeight_abs_le_indicator _ _ (prouhet_motif_value _ _) _)

theorem occupiedRootWeight_internal_anchor (T : ℕ → ℕ) (s b : ℕ)
    (S : Finset (WindowLeaf T (b+1+1))) (a : OccupiedWindowChoice T (b+1) S) (X : ℤ)
    (i : Fin (selectedChildren S).card) (hi : a.2 i≠0) :
    |occupiedRootWeight T s (b+1) S a X|≤
      motifIndicator s ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X) := by
  exact (abs_prod_le_coordinate _ i (fun j _ =>
    internalRoleWeight_abs_le_one _ _ _ (prouhet_motif_value _ _) _)).trans
      (internalRoleWeight_active_abs_le_indicator _ _ _ (prouhet_motif_value _ _) _ hi)

theorem abs_prod_le_two {ι : Type*} [Fintype ι] (f : ι → ℝ) (a c : ι) (hne : a≠c)
    (h : ∀j,j≠a → j≠c → |f j|≤1) : |∏j,f j|≤|f a| * |f c| := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏j, if j=a then |f a| else if j=c then |f c| else 1 := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro j hj
      by_cases hja : j=a
      · simp [hja]
      · by_cases hjc : j=c
        · simp [hjc,hne.symm]
        · simpa only [ite_eq_right hja,ite_eq_right hjc] using h j hja hjc
    _ = _ := by
      rw [Finset.prod_eq_mul a c hne]
      · simp [hne.symm]
      · intro j hj hjs
        simp [hjs.1,hjs.2]
      · simp
      · simp

/-- The real role term is pointwise dominated by its selected unsigned
anchors. No independence assumption is used in this domination. -/
theorem sourceRoleTerm_forced_anchor (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    |sourceRoleTerm T n g s center globalShift b bits incoming S a|≤
      binaryAnchorKernel T n g s center globalShift (b+1) (forcedWindowLabels T b S a F) bits incoming := by
  induction b generalizing incoming with
  | zero =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_zero]
      change _ ≤ motifIndicator s (((S.equivFin.symm i).val.1.val:ℤ)-center 0+
        (∑i,(bitIndex (bits.1 i):ℤ))+incoming)*(1*1)
      rw [mul_one,mul_one]
      convert occupiedRootWeight_bottom_anchor T s S a
        (center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) i using 1 ; congr 1 ; omega
  | succ b ih =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_succ,abs_mul]
      have hroot := occupiedRootWeight_internal_anchor T s b S a
        (center (b+1)-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) i hi
      have hprod := abs_prod_le_two (fun k : Fin (selectedChildren S).card =>
        sourceRoleTerm T n g s center globalShift b
          (bits.2.2 ((selectedChildren S).equivFin.symm k).val)
          (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm k).val)
          (selectedChildLeaves S ((selectedChildren S).equivFin.symm k).val) (a.1 k)) i j hne
          (fun k _ _ => occupiedWindowWeight_abs_le_one T s _ b [] _ _)
      have hl := ih (bits.2.2 ((selectedChildren S).equivFin.symm i).val)
        (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm i).val) _ _ left
      have hr := ih (bits.2.2 ((selectedChildren S).equivFin.symm j).val)
        (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm j).val) _ _ right
      have hp := mul_le_mul hl hr (abs_nonneg _) (binaryAnchorKernel_nonneg T n g s center globalShift _ _ _ _)
      have hh := mul_le_mul hroot (hprod.trans hp) (abs_nonneg _) (motifIndicator_nonneg _ _)
      apply hh.trans_eq
      change motifIndicator s _ * _ = motifIndicator s
        ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-center (b+1)+
          (∑k,(bitIndex (bits.1 k):ℤ))+incoming) * _
      congr 2
      omega

/-- Therefore the coefficient average is bounded by the actual forced
anchor average, with the true posterior law and shared jitter retained. -/
theorem sourceRoleAverage_forced_anchor (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤
      binaryAnchorAverage T n g s center globalShift (b+1) (forcedWindowLabels T b S a F) d incoming := by
  exact ((windowPosteriorLaw T n g (b+1) d).abs_expect_le _).trans
    ((windowPosteriorLaw T n g (b+1) d).expect_mono (fun bits =>
      sourceRoleTerm_forced_anchor T n g s center globalShift b bits incoming S a F))

theorem sourceRoleTerm_valid (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (h : sourceRoleTerm T n g s center globalShift b bits incoming S a ≠ 0) :
    (occupiedWindowTerm T b S a).valid := by
  have hh := (occupiedWindowShape T s
    (sourceTreeAnchors T n g center globalShift (b+1) bits incoming) b [] S).term_valid
    (occupiedWindowChoiceEquiv T s
      (sourceTreeAnchors T n g center globalShift (b+1) bits incoming) b [] S a) h
  simpa only [occupiedWindowTerm_eq] using hh

theorem sourceRoleAverage_valid (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (h : sourceRoleAverage T n g s center globalShift b d incoming S a ≠ 0) :
    (occupiedWindowTerm T b S a).valid := by
  by_contra hn
  have hh : ∀bits, sourceRoleTerm T n g s center globalShift b bits incoming S a=0 := by
    intro bits
    by_contra hz
    exact hn (sourceRoleTerm_valid T n g s center globalShift b bits incoming S a hz)
  apply h
  change (windowPosteriorLaw T n g (b+1) d).expect _ = 0
  rw [show (fun bits => sourceRoleTerm T n g s center globalShift b bits incoming S a) =
    (fun _ => 0) from funext hh,expect_const]

/-- The source's two alternatives now apply to actual posterior coefficient
terms: signed singleton smoothing, or domination by a genuine forced tree. -/
theorem sourceRoleAverage_alternative (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (η : ℝ) (hη : 0≤η) (hcap : MetadataSmoothingCap T n g s η (b+1) d)
    (ho : (occupiedWindowTerm T b S a).isOdd) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤η ∨
    ∃F : (occupiedWindowTerm T b S a).Forced,
      BinaryWindowLabels.distinct T (b+1) (forcedWindowLabels T b S a F) ∧
      |sourceRoleAverage T n g s center globalShift b d incoming S a|≤
        binaryAnchorAverage T n g s center globalShift (b+1) (forcedWindowLabels T b S a F) d incoming := by
  by_cases hz : sourceRoleAverage T n g s center globalShift b d incoming S a=0
  · exact Or.inl (by simpa only [hz,abs_zero] using hη)
  by_cases hn : (occupiedWindowTerm T b S a).noSingleton
  · obtain ⟨F⟩ := OccupiedParityTree.forced_nonempty (occupiedWindowTerm T b S a)
      (sourceRoleAverage_valid T n g s center globalShift b d incoming S a hz) hn ho
    exact Or.inr ⟨F,forcedWindowLabels_distinct T b S a F,
      sourceRoleAverage_forced_anchor T n g s center globalShift b d incoming S a F⟩
  · exact Or.inl (sourceRoleAverage_singleton T n g s center globalShift b d incoming S a η hcap hn)

end TraceReconstruction


namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The unsigned bottom constraint at one literal complete-tree leaf. -/
def sourceBottomIndicator (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → WindowAssignments T n g Bool (b+1) → ℤ → WindowLeaf T (b+1) → ℝ
  | 0, bits, incoming, v =>
      motifIndicator s ((v.1.val:ℤ)-center 0+(∑i,(bitIndex (bits.1 i):ℤ))+incoming)
  | b+1, bits, _, v => sourceBottomIndicator T n g s center globalShift b
      (bits.2.2 v.1) (globalShift (b+1) bits.2.1 v.1) v.2

def sourceLeafProduct (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) : ℝ :=
  ∏v∈S, sourceBottomIndicator T n g s center globalShift b bits incoming v

theorem sourceBottomIndicator_zero_one (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (v : WindowLeaf T (b+1)) :
    sourceBottomIndicator T n g s center globalShift b bits incoming v=0 ∨
    sourceBottomIndicator T n g s center globalShift b bits incoming v=1 := by
  induction b generalizing incoming with
  | zero => unfold sourceBottomIndicator motifIndicator; split_ifs <;> simp
  | succ b ih => exact ih _ _ _

theorem prod_zero_one {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h : ∀i∈S,f i=0 ∨ f i=1) : (∏i∈S,f i)=0 ∨ (∏i∈S,f i)=1 := by
  by_cases hz : ∃i∈S,f i=0
  · obtain ⟨i,hi,hz⟩ := hz
    exact Or.inl (Finset.prod_eq_zero hi hz)
  · right
    apply Finset.prod_eq_one
    intro i hi
    exact (h i hi).resolve_left (fun he => hz ⟨i,hi,he⟩)

theorem sourceLeafProduct_zero_one (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) :
    sourceLeafProduct T n g s center globalShift b bits incoming S=0 ∨
    sourceLeafProduct T n g s center globalShift b bits incoming S=1 :=
  prod_zero_one S _ (fun v _ => sourceBottomIndicator_zero_one T n g s center globalShift b bits incoming v)

theorem binaryAnchorKernel_zero_one (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T b) (bits : WindowAssignments T n g Bool b)
    (incoming : ℤ) :
    binaryAnchorKernel T n g s center globalShift b p bits incoming=0 ∨
    binaryAnchorKernel T n g s center globalShift b p bits incoming=1 := by
  induction b generalizing incoming with
  | zero => exact Or.inr rfl
  | succ b ih =>
    have hl := ih p.2.2.1 (bits.2.2 p.1) (globalShift b bits.2.1 p.1)
    have hr := ih p.2.2.2 (bits.2.2 p.2.1) (globalShift b bits.2.1 p.2.1)
    change (_*(_*_)=0) ∨ (_*(_*_)=1)
    rcases hl with hl|hl <;> rcases hr with hr|hr <;> rw [hl,hr] <;>
      unfold motifIndicator <;> split_ifs <;> norm_num

theorem sourceLeafProduct_succ (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1+1))) :
    sourceLeafProduct T n g s center globalShift (b+1) bits incoming S =
      ∏i : Fin (selectedChildren S).card,
        sourceLeafProduct T n g s center globalShift b
          (bits.2.2 ((selectedChildren S).equivFin.symm i).val)
          (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm i).val)
          (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) := by
  symm
  exact (selected_prod_index (selectedChildren S) (fun h =>
    ∏v∈selectedChildLeaves S h,
      sourceBottomIndicator T n g s center globalShift b (bits.2.2 h)
        (globalShift (b+1) bits.2.1 h) v)).trans
      (selected_prod_children S (fun v =>
        sourceBottomIndicator T n g s center globalShift (b+1) bits incoming v))

/-- Every selected leaf is active in the bottom expansion, including those
outside the forced tree. Their absolute constraints are not lost. -/
theorem sourceRoleTerm_all_leaf_constraints (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) :
    |sourceRoleTerm T n g s center globalShift b bits incoming S a|≤
      sourceLeafProduct T n g s center globalShift b bits incoming S := by
  induction b generalizing incoming with
  | zero =>
    rw [sourceRoleTerm_zero]
    change |∏i : Fin S.card, _|≤_
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏i : Fin S.card, motifIndicator s
          (((S.equivFin.symm i).val.1.val:ℤ)-(center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun i _ => bottomRoleWeight_abs_le_indicator _ _ (prouhet_motif_value _ _) _)
      _ = ∏v∈S, motifIndicator s ((v.1.val:ℤ)-
          (center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)) :=
        selected_prod_index S (fun v : WindowLeaf T 1 => motifIndicator s
          ((v.1.val:ℤ)-(center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro v hv
        change motifIndicator s _ = motifIndicator s _
        congr 1
        omega
  | succ b ih =>
    rw [sourceRoleTerm_succ,abs_mul,sourceLeafProduct_succ]
    apply (mul_le_mul_of_nonneg_right
      (occupiedRootWeight_abs_le_one T s (b+1) S a _) (abs_nonneg _)).trans
    rw [one_mul,Finset.abs_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    intro i hi
    exact ih _ _ _ _

theorem sourceLeafProduct_antitone (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (E S : Finset (WindowLeaf T (b+1))) (hES : E⊆S) :
    sourceLeafProduct T n g s center globalShift b bits incoming S≤
      sourceLeafProduct T n g s center globalShift b bits incoming E := by
  apply Finset.prod_le_prod_of_subset_of_le_one₀ hES
  · intro v hv
    rcases sourceBottomIndicator_zero_one T n g s center globalShift b bits incoming v with h|h <;> norm_num [h]
  · intro v hv he
    rcases sourceBottomIndicator_zero_one T n g s center globalShift b bits incoming v with h|h <;> norm_num [h]

theorem le_mul_of_zero_one {x a b : ℝ} (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1)
    (hxa : x≤a) (hxb : x≤b) : x≤a*b := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> norm_num at * <;> assumption

/-- Actual forced anchor AND extra-leaf constraints in one bit expectation.
In particular E can be precisely the nonforced leaves; keeping it arbitrary
here permits the later label summation without any conditioning gates. -/
theorem sourceRoleAverage_forced_extra (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S E : Finset (WindowLeaf T (b+1))) (hES : E⊆S) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤
      (windowPosteriorLaw T n g (b+1) d).expect (fun bits =>
        binaryAnchorKernel T n g s center globalShift (b+1) (forcedWindowLabels T b S a F) bits incoming *
        sourceLeafProduct T n g s center globalShift b bits incoming E) := by
  apply ((windowPosteriorLaw T n g (b+1) d).abs_expect_le _).trans
  apply FiniteLaw.expect_mono
  intro bits
  exact le_mul_of_zero_one
    (binaryAnchorKernel_zero_one T n g s center globalShift _ _ bits incoming)
    (sourceLeafProduct_zero_one T n g s center globalShift b bits incoming E)
    (sourceRoleTerm_forced_anchor T n g s center globalShift b bits incoming S a F)
    ((sourceRoleTerm_all_leaf_constraints T n g s center globalShift b bits incoming S a).trans
      (sourceLeafProduct_antitone T n g s center globalShift b bits incoming E S hES))

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Deterministic closeness of each forced split; it is a restriction on
labels, never an additional conditioning event for the random bits. -/
def BinaryWindowLabels.close (T : ℕ → ℕ) (s : ℕ) : (b : ℕ) → BinaryWindowLabels T b → Prop
  | 0, _ => True
  | b+1, p => |(p.1.val:ℤ)-p.2.1.val|<(2^s:ℕ) ∧ close T s b p.2.2.1 ∧ close T s b p.2.2.2

theorem motifIndicator_pair_close (s : ℕ) (a c X : ℤ)
    (ha : motifIndicator s (a-X)≠0) (hc : motifIndicator s (c-X)≠0) :
    |a-c|<(2^s:ℕ) := by
  have hsa : 0≤a-X ∧ a-X<(2^s:ℕ) := by
    by_contra h
    exact ha (by simp only [motifIndicator,ite_eq_right h])
  have hsc : 0≤c-X ∧ c-X<(2^s:ℕ) := by
    by_contra h
    exact hc (by simp only [motifIndicator,ite_eq_right h])
  exact abs_lt.mpr ⟨by omega,by omega⟩

theorem nonzero_of_abs_le {x y : ℝ} (h : x≠0) (hle : |x|≤y) : y≠0 := by
  intro hy
  rw [hy] at hle
  exact h (abs_eq_zero.mp (le_antisymm hle (abs_nonneg x)))

/-- A nonzero literal role multiplier enforces all close-child restrictions
of every forced subtree chosen from its fixed role pattern. -/
theorem sourceRoleTerm_forced_close (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced)
    (h : sourceRoleTerm T n g s center globalShift b bits incoming S a≠0) :
    BinaryWindowLabels.close T s (b+1) (forcedWindowLabels T b S a F) := by
  induction b generalizing incoming with
  | zero =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_zero] at h
      change |((S.equivFin.symm i).val.1.val:ℤ)-(S.equivFin.symm j).val.1.val|<(2^s:ℕ) ∧ True ∧ True
      refine ⟨?_,trivial,trivial⟩
      exact motifIndicator_pair_close s _ _ _
        (nonzero_of_abs_le h (occupiedRootWeight_bottom_anchor T s S a _ i))
        (nonzero_of_abs_le h (occupiedRootWeight_bottom_anchor T s S a _ j))
  | succ b ih =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_succ] at h
      have hm := mul_ne_zero_iff.mp h
      have hc := Finset.prod_ne_zero_iff.mp hm.2
      change |(((selectedChildren S).equivFin.symm i).val.val:ℤ)-
        ((selectedChildren S).equivFin.symm j).val.val|<(2^s:ℕ) ∧
        BinaryWindowLabels.close T s (b+1)
          (forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)
            (a.1 i) left) ∧
        BinaryWindowLabels.close T s (b+1)
          (forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val)
            (a.1 j) right)
      refine ⟨?_,ih _ _ _ _ left (hc i (Finset.mem_univ i)),
        ih _ _ _ _ right (hc j (Finset.mem_univ j))⟩
      exact motifIndicator_pair_close s _ _ _
        (nonzero_of_abs_le hm.1 (occupiedRootWeight_internal_anchor T s b S a _ i hi))
        (nonzero_of_abs_le hm.1 (occupiedRootWeight_internal_anchor T s b S a _ j hj))

/-- Closeness remains a pure label condition after averaging, without
conditioning on it. -/
theorem sourceRoleAverage_forced_close (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced)
    (h : sourceRoleAverage T n g s center globalShift b d incoming S a≠0) :
    BinaryWindowLabels.close T s (b+1) (forcedWindowLabels T b S a F) := by
  by_contra hn
  have hh : ∀bits, sourceRoleTerm T n g s center globalShift b bits incoming S a=0 := by
    intro bits
    by_contra hz
    exact hn (sourceRoleTerm_forced_close T n g s center globalShift b bits incoming S a F hz)
  apply h
  change (windowPosteriorLaw T n g (b+1) d).expect _ = 0
  rw [show (fun bits => sourceRoleTerm T n g s center globalShift b bits incoming S a) =
    (fun _ => 0) from funext hh,expect_const]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The literal finite child labels embedded in the integer line. -/
def finIntegerLabels (N : ℕ) : Finset ℤ := Finset.univ.image (fun i : Fin N => (i.val:ℤ))

theorem sum_finIntegerLabels (N : ℕ) (f : ℤ → ℝ) :
    (∑a∈finIntegerLabels N,f a)=∑i : Fin N,f i.val := by
  rw [finIntegerLabels,Finset.sum_image]
  intro a ha b hb he
  apply Fin.ext
  change (a.val:ℤ)=(b.val:ℤ) at he
  exact_mod_cast he

theorem sum_close_finIntegerLabels (N L : ℕ) (a : ℤ) (f : ℤ → ℝ) :
    (∑c∈closeLabels (finIntegerLabels N) L a,f c) =
      ∑i : Fin N, if |(i.val:ℤ)-a|<(L:ℤ) then f i.val else 0 := by
  rw [closeLabels,Finset.sum_filter,sum_finIntegerLabels]

/-- Any deterministic plateau/distinctness restriction can be retained in
child-pair summation. Only closeness is used to upper bound its cost. -/
theorem localAnchor_finite_energy {m N : ℕ} (d : Fin m → Option Bool) (s : ℕ)
    (c : ℤ) (R : Fin N → Fin N → Prop) [DecidableRel R]
    (hR : ∀a b,R a b → |(b.val:ℤ)-a.val|<(2^s:ℕ)) :
    (∑a : Fin N, ∑b : Fin N, if R a b then localAnchorAverage d s ((a.val:ℤ)-c)^2 else 0) ≤
      2*((2^s:ℕ):ℝ)^3*binomialBound (∑i,hiddenTrial (d i)) := by
  have H := root_anchor_energy (∑i,hiddenTrial (d i)) (2^s)
    (finIntegerLabels N) (finIntegerLabels N) (c-(∑i,(visibleOnes (d i):ℤ)))
  rw [sum_finIntegerLabels] at H
  simp_rw [sum_close_finIntegerLabels] at H
  calc
    _ ≤ ∑a : Fin N, ∑b : Fin N,
        if |(b.val:ℤ)-a.val|<(2^s:ℕ) then
          windowKernel (∑i,hiddenTrial (d i)) (2^s)
            ((a.val:ℤ)-(c-∑i,(visibleOnes (d i):ℤ)))^2 else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases h : R a b
      · rw [ite_eq_left h,ite_eq_left (hR a b h),localAnchorAverage_kernel]
        convert le_refl _ using 1 ; congr 2 ; omega
      · rw [ite_eq_right h]
        split_ifs <;> positivity
    _ ≤ _ := H

/-- Actual shared-jitter energy over two finite sibling pairs. Parent-label
plateau restrictions are discharged before applying this lemma; arbitrary
restrictions on these child pairs are kept, not conditioned on. -/
theorem posteriorJoint_finite_energy {mg m₁ m₂ N : ℕ}
    (dg : Fin mg → Option Bool) (d₁ : Fin m₁ → Option Bool) (d₂ : Fin m₂ → Option Bool)
    (s : ℕ) (c₁ c₂ : ℤ) (R : Fin N → Fin N → Prop) [DecidableRel R]
    (hR : ∀a b,R a b → |(b.val:ℤ)-a.val|<(2^s:ℕ)) :
    (∑a : Fin N, ∑c : Fin N, ∑b : Fin N, ∑d : Fin N,
      if R a c ∧ R b d then
        posteriorJointAnchors dg d₁ d₂ s ((a.val:ℤ)-c₁) ((b.val:ℤ)-c₂)^2 else 0) ≤
       4*((2^s:ℕ):ℝ)^6*binomialBound (∑i,hiddenTrial (dg i))*binomialBound (∑i,hiddenTrial (d₂ i)) := by
  have H := posterior_sibling_anchor_energy dg d₁ d₂ s
    (finIntegerLabels N) (finIntegerLabels N) (finIntegerLabels N) (finIntegerLabels N) c₁ c₂
  simp_rw [sum_finIntegerLabels,sum_close_finIntegerLabels] at H
  calc
    _ = ∑a : Fin N, ∑b : Fin N, ∑c : Fin N, ∑d : Fin N,
      if R a c ∧ R b d then
        posteriorJointAnchors dg d₁ d₂ s ((a.val:ℤ)-c₁) ((b.val:ℤ)-c₂)^2 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ ≤ ∑a : Fin N, ∑b : Fin N, ∑c : Fin N,
      if |(c.val:ℤ)-a.val|<(2^s:ℕ) then
        ∑d : Fin N, if |(d.val:ℤ)-b.val|<(2^s:ℕ) then
          posteriorJointAnchors dg d₁ d₂ s ((a.val:ℤ)-c₁) ((b.val:ℤ)-c₂)^2 else 0
      else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      by_cases h : |(c.val:ℤ)-a.val|<(2^s:ℕ)
      · rw [ite_eq_left h]
        apply Finset.sum_le_sum
        intro d hd
        by_cases hr : R a c ∧ R b d
        · rw [ite_eq_left hr,ite_eq_left (hR b d hr.2)]
        · rw [ite_eq_right hr]
          split_ifs <;> positivity
      · rw [ite_eq_right h]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro d hd
        exact ite_eq_right (fun hr => h (hR a c hr.1))
    _ ≤ _ := H

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The actual finite central domain, distinctness and close-label restriction.
It is purely deterministic and is never added to the orientation posterior. -/
def anchorPairAllowed (T : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b))) (s b : ℕ)
    (a c : Fin (T b)) : Prop := a∈A b ∧ c∈A b ∧ a≠c ∧ |(c.val:ℤ)-a.val|<(2^s:ℕ)

/-- The source global plateau identity is required pointwise for bits, not
just in distribution and not after conditioning on successful layout. -/
def HasGlobalPlateau (T g : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) : Prop :=
  ∀b glob u, u∈A b → globalShift b glob u=(∑i,(bitIndex (glob i):ℤ))-shift b

/-- Numerical binomial caps extracted from the literal known/hidden metadata.
In applications these are proved using the source hidden-trial lower bounds. -/
def MetadataBinomialCaps (T n g : ℕ → ℕ) (B C : ℕ → ℝ) :
    (b : ℕ) → WindowAssignments T n g (Option Bool) b → Prop
  | 0, _ => True
  | b+1, d => binomialBound (∑i, hiddenTrial (d.1 i)) ≤ B b ∧
      binomialBound (∑i, hiddenTrial (d.2.1 i)) ≤ C b ∧
      ∀u, MetadataBinomialCaps T n g B C b (d.2.2 u)

/-- One correlated sibling-group anchor, using the actual child metadata
and their parent's one shared global orientation collection. -/
def binarySiblingAnchor (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1+1))
    (u v : Fin (T (b+1))) (a c : Fin (T b)) : ℝ :=
  (posteriorArray d.2.1).expect (fun glob =>
    localAnchorAverage (d.2.2 u).1 s ((a.val:ℤ)-center b+globalShift (b+1) glob u) *
    localAnchorAverage (d.2.2 v).1 s ((c.val:ℤ)-center b+globalShift (b+1) glob v))

theorem binarySiblingAnchor_plateau (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1+1))
    (u v : Fin (T (b+1))) (hu : u∈A (b+1)) (hv : v∈A (b+1)) (a c : Fin (T b)) :
    binarySiblingAnchor T n g s center globalShift b d u v a c =
      posteriorJointAnchors d.2.1 (d.2.2 u).1 (d.2.2 v).1 s
        ((a.val:ℤ)-(center b+shift (b+1))) ((c.val:ℤ)-(center b+shift (b+1))) := by
  calc
    _ = (posteriorArray d.2.1).expect (fun glob =>
        localAnchorAverage (d.2.2 u).1 s ((a.val:ℤ)-center b+(∑i,(bitIndex (glob i):ℤ))-shift (b+1)) *
        localAnchorAverage (d.2.2 v).1 s ((c.val:ℤ)-center b+(∑i,(bitIndex (glob i):ℤ))-shift (b+1))) := by
      apply congrArg (FiniteLaw.expect (posteriorArray d.2.1))
      funext glob
      have hu' := hplat (b+1) glob u hu
      have hv' := hplat (b+1) glob v hv
      rw [hu',hv']
      congr 2 <;> omega
    _ = _ := by
      rw [localAnchor_pair_plateau]
      congr 1 <;> omega

/-- Exact dynamic sum of squared group anchors over the allowed finite
labels below a fixed forced split. Distinct groups retain their own metadata. -/
def binaryDescendantEnergy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) :
    (b : ℕ) → WindowAssignments T n g (Option Bool) (b+1) → Fin (T b) → Fin (T b) → ℝ
  | 0, _, _, _ => 1
  | b+1, d, u, v =>
      ∑a : Fin (T b),∑c : Fin (T b),∑e : Fin (T b),∑f : Fin (T b),
        if anchorPairAllowed T A s b a c ∧ anchorPairAllowed T A s b e f then
          binarySiblingAnchor T n g s center globalShift b d u v a e ^ 2 *
            binaryDescendantEnergy T n g s center globalShift A b (d.2.2 u) a c *
            binaryDescendantEnergy T n g s center globalShift A b (d.2.2 v) e f
        else 0

theorem binaryDescendantEnergy_nonneg (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (u v : Fin (T b)) :
    0≤binaryDescendantEnergy T n g s center globalShift A b d u v := by
  induction b with
  | zero => exact zero_le_one
  | succ b ih =>
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro c hc
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro f hf
    split_ifs
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (ih _ _ _)) (ih _ _ _)
    · exact le_refl _

/-- True common-jitter energy at one group, with its exact finite domains. -/
theorem binarySiblingAnchor_energy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1+1))
    (u v : Fin (T (b+1))) (hu : u∈A (b+1)) (hv : v∈A (b+1)) :
    (∑a : Fin (T b),∑c : Fin (T b),∑e : Fin (T b),∑f : Fin (T b),
        if anchorPairAllowed T A s b a c ∧ anchorPairAllowed T A s b e f then
          binarySiblingAnchor T n g s center globalShift b d u v a e ^ 2 else 0) ≤
      4*((2^s:ℕ):ℝ)^6*binomialBound (∑i,hiddenTrial (d.2.1 i))*
        binomialBound (∑i,hiddenTrial ((d.2.2 v).1 i)) := by
  simp_rw [binarySiblingAnchor_plateau T n g s center globalShift A shift hplat b d u v hu hv]
  exact posteriorJoint_finite_energy d.2.1 (d.2.2 u).1 (d.2.2 v).1 s
    (center b+shift (b+1)) (center b+shift (b+1)) (anchorPairAllowed T A s b)
    (fun a c h => h.2.2.2)

/-- The complete bottom-up forced-label energy estimate. Its only numerical
inputs are actual metadata hidden-count binomial caps. The group bound
keeps one shared global kernel until AFTER squaring. -/
theorem binaryDescendantEnergy_le (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (B C : ℕ → ℝ) (hB : ∀b,0≤B b) (hC : ∀b,0≤C b)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1))
    (hcap : MetadataBinomialCaps T n g B C (b+1) d)
    (u v : Fin (T b)) (hu : u∈A b) (hv : v∈A b) :
    binaryDescendantEnergy T n g s center globalShift A b d u v ≤
      binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b := by
  let K : ℕ → ℝ := fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j
  have hK : ∀j,0≤K j := fun j => mul_nonneg (mul_nonneg (by positivity) (hC _)) (hB _)
  induction b with
  | zero => exact le_refl _
  | succ b ih =>
    have hbudget := binaryTreeBudget_nonneg K hK b
    have hgroup := binarySiblingAnchor_energy T n g s center globalShift A shift hplat b d u v hu hv
    have hnum : 4*((2^s:ℕ):ℝ)^6*binomialBound (∑i,hiddenTrial (d.2.1 i))*
        binomialBound (∑i,hiddenTrial ((d.2.2 v).1 i)) ≤ K b := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hcap.2.1 (by positivity))
        (hcap.2.2 v).1 (by unfold binomialBound; positivity)
        (mul_nonneg (by positivity) (hC _))
    calc
      _ ≤ (∑a : Fin (T b),∑c : Fin (T b),∑e : Fin (T b),∑f : Fin (T b),
        if anchorPairAllowed T A s b a c ∧ anchorPairAllowed T A s b e f then
          binarySiblingAnchor T n g s center globalShift b d u v a e ^ 2 else 0) *
          (binaryTreeBudget K b)^2 := by
        simp only [binaryDescendantEnergy,Finset.sum_mul]
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro c hc
        apply Finset.sum_le_sum
        intro e he
        apply Finset.sum_le_sum
        intro f hf
        split_ifs with hr
        · have hl := ih (d.2.2 u) (hcap.2.2 u) a c hr.1.1 hr.1.2.1
          have hh := ih (d.2.2 v) (hcap.2.2 v) e f hr.2.1 hr.2.2.1
          have hm := mul_le_mul hl hh
            (binaryDescendantEnergy_nonneg T n g s center globalShift A b (d.2.2 v) e f) hbudget
          have hf := mul_le_mul_of_nonneg_left hm
            (sq_nonneg (binarySiblingAnchor T n g s center globalShift b d u v a e))
          simpa only [K,pow_two,mul_assoc] using hf
        · simp only [zero_mul,le_refl]
      _ ≤ K b*(binaryTreeBudget K b)^2 :=
        mul_le_mul_of_nonneg_right (hgroup.trans hnum) (sq_nonneg _)
      _ = _ := rfl

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

def BinaryWindowLabels.allowed (T : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b))) (s : ℕ) :
    (b : ℕ) → BinaryWindowLabels T b → Prop
  | 0, _ => True
  | b+1, p => anchorPairAllowed T A s b p.1 p.2.1 ∧
      allowed T A s b p.2.2.1 ∧ allowed T A s b p.2.2.2

theorem BinaryWindowLabels.allowed_distinct (T : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b)))
    (s b : ℕ) (p : BinaryWindowLabels T b) (hp : allowed T A s b p) : distinct T b p := by
  induction b with
  | zero => trivial
  | succ b ih => exact ⟨hp.1.2.2.1,ih _ hp.2.1,ih _ hp.2.2⟩

/-- Regroup the two real top child labels, without changing the actual
finite label type or declaration order. -/
def joinBinaryLabels {T : ℕ → ℕ} {b : ℕ} (a : Fin (T b) × Fin (T b))
    (p : BinaryWindowLabels T b × BinaryWindowLabels T b) : BinaryWindowLabels T (b+1) :=
  (a.1,a.2,p.1,p.2)

theorem sum_binary_labels (T : ℕ → ℕ) (b : ℕ) (f : BinaryWindowLabels T (b+1) → ℝ) :
    (∑p, f p) = ∑a : Fin (T b) × Fin (T b),
      ∑p : BinaryWindowLabels T b × BinaryWindowLabels T b, f (joinBinaryLabels a p) := by
  let e : BinaryWindowLabels T (b+1) ≃
      (Fin (T b) × Fin (T b)) × (BinaryWindowLabels T b × BinaryWindowLabels T b) :=
    { toFun := fun p => ((p.1,p.2.1),(p.2.2.1,p.2.2.2))
      invFun := fun z => joinBinaryLabels z.1 z.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.sum_equiv e f (fun z => f (joinBinaryLabels z.1 z.2)) (fun _ => rfl)).trans
    (Fintype.sum_prod_type _)

/-- Exact finite tensor summation after preserving both deterministically
allowed label domains. No probabilistic independence is asserted here. -/
theorem sum_pair_tensor {α β σ τ : Type*} [Fintype α] [Fintype β] [Fintype σ] [Fintype τ]
    (R : α → Prop) (S : β → Prop) (P : σ → Prop) (Q : τ → Prop)
    [DecidablePred R] [DecidablePred S] [DecidablePred P] [DecidablePred Q]
    (K : α → β → ℝ) (f : α → σ → ℝ) (h : β → τ → ℝ) :
    (∑a,∑x,∑b,∑y, if R a ∧ P x ∧ S b ∧ Q y then K a b*f a x*h b y else 0) =
      ∑a,∑b,if R a ∧ S b then K a b*(∑x,if P x then f a x else 0)*
        (∑y,if Q y then h b y else 0) else 0 := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hr : R a
  · by_cases hs : S b
    · rw [ite_eq_left ⟨hr,hs⟩]
      simp only [Finset.sum_mul,Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hp : P x <;> by_cases hq : Q y <;> simp only [hr,hs,hp,hq,and_self,
        false_and,and_false,ite_true,ite_false,mul_zero,zero_mul]
    · simp only [hs,and_false,false_and,ite_false,Finset.sum_const_zero]
  · simp only [hr,false_and,ite_false,Finset.sum_const_zero]

/-- Literal sum over all descendant labels is the recursively compiled
sibling-group energy. This is the bridge from the actual anchor average to
bottom-up summation; no coefficient estimate is supplied as a hypothesis. -/
theorem binaryAnchorBelow_sum (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (u v : Fin (T b)) :
    (∑p : BinaryWindowLabels T b × BinaryWindowLabels T b,
      if BinaryWindowLabels.allowed T A s b p.1 ∧ BinaryWindowLabels.allowed T A s b p.2 then
        binaryAnchorBelow T n g s center globalShift b (joinBinaryLabels (u,v) p) d ^ 2 else 0) =
      binaryDescendantEnergy T n g s center globalShift A b d u v := by
  induction b with
  | zero =>
    have hcard : Fintype.card (BinaryWindowLabels T 0) = 1 := rfl
    simp only [BinaryWindowLabels.allowed,binaryAnchorBelow,binaryDescendantEnergy,
      and_self,ite_true,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_prod,hcard,nsmul_eq_mul,
      mul_one,Nat.cast_one]
  | succ b ih =>
    rw [Fintype.sum_prod_type,sum_binary_labels]
    simp_rw [sum_binary_labels]
    have hpoint (a c : Fin (T b) × Fin (T b))
        (p q : BinaryWindowLabels T b × BinaryWindowLabels T b) :
        (if BinaryWindowLabels.allowed T A s (b+1) (joinBinaryLabels a p) ∧
          BinaryWindowLabels.allowed T A s (b+1) (joinBinaryLabels c q) then
          binaryAnchorBelow T n g s center globalShift (b+1)
            (joinBinaryLabels (u,v) (joinBinaryLabels a p,joinBinaryLabels c q)) d ^ 2 else 0) =
        (if anchorPairAllowed T A s b a.1 a.2 ∧
          (BinaryWindowLabels.allowed T A s b p.1 ∧ BinaryWindowLabels.allowed T A s b p.2) ∧
          anchorPairAllowed T A s b c.1 c.2 ∧
          (BinaryWindowLabels.allowed T A s b q.1 ∧ BinaryWindowLabels.allowed T A s b q.2) then
          binarySiblingAnchor T n g s center globalShift b d u v a.1 c.1 ^ 2 *
            binaryAnchorBelow T n g s center globalShift b (joinBinaryLabels a p) (d.2.2 u) ^ 2 *
            binaryAnchorBelow T n g s center globalShift b (joinBinaryLabels c q) (d.2.2 v) ^ 2 else 0) := by
      simp only [BinaryWindowLabels.allowed,joinBinaryLabels,and_assoc,binaryAnchorBelow,binarySiblingAnchor]
      split_ifs <;> ring
    simp_rw [hpoint]
    rw [sum_pair_tensor]
    simp_rw [ih]
    change _ = ∑a : Fin (T b),∑c : Fin (T b),∑e : Fin (T b),∑f : Fin (T b), _
    simp only [Fintype.sum_prod_type]

/-- The square-sum of actual anchor averages over all admissible forced
indices, including the root local smoothing cost exactly once. -/
theorem binaryAnchorAverage_sum (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    (∑p : BinaryWindowLabels T (b+1), if BinaryWindowLabels.allowed T A s (b+1) p then
      binaryAnchorAverage T n g s center globalShift (b+1) p d incoming ^ 2 else 0) =
      ∑u : Fin (T b),∑v : Fin (T b), if anchorPairAllowed T A s b u v then
        localAnchorAverage d.1 s ((u.val:ℤ)-center b+incoming)^2 *
          binaryDescendantEnergy T n g s center globalShift A b d u v else 0 := by
  rw [sum_binary_labels,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hr : anchorPairAllowed T A s b u v
  · rw [ite_eq_left hr,←binaryAnchorBelow_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hsub : BinaryWindowLabels.allowed T A s b p.1 ∧ BinaryWindowLabels.allowed T A s b p.2
    · have ha : BinaryWindowLabels.allowed T A s (b+1) (joinBinaryLabels (u,v) p) := ⟨hr,hsub⟩
      rw [ite_eq_left ha,ite_eq_left hsub,binaryAnchorAverage_factor T n g s center globalShift _ _ _ _
        (BinaryWindowLabels.allowed_distinct T A s _ _ ha),mul_pow]
      rfl
    · have ha : ¬BinaryWindowLabels.allowed T A s (b+1) (joinBinaryLabels (u,v) p) := fun h => hsub h.2
      rw [ite_eq_right ha,ite_eq_right hsub,mul_zero]
  · rw [ite_eq_right hr]
    apply Finset.sum_eq_zero
    intro p hp
    exact ite_eq_right (fun h => hr h.1)

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Full finite forced-anchor squared coefficient budget, with the source
power of one local root cost and one correlated global/local cost per group.
This conclusion is about literal posterior averages and actual labels. -/
theorem binaryAnchorAverage_energy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (B C : ℕ → ℝ) (hB : ∀b,0≤B b) (hC : ∀b,0≤C b)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1))
    (hcap : MetadataBinomialCaps T n g B C (b+1) d) (incoming : ℤ) :
    (∑p : BinaryWindowLabels T (b+1), if BinaryWindowLabels.allowed T A s (b+1) p then
      binaryAnchorAverage T n g s center globalShift (b+1) p d incoming ^ 2 else 0) ≤
        (2*((2^s:ℕ):ℝ)^3*B b) *
          binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b := by
  let K : ℕ → ℝ := fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j
  have hK : ∀j,0≤K j := fun j => mul_nonneg (mul_nonneg (by positivity) (hC _)) (hB _)
  have hbudget := binaryTreeBudget_nonneg K hK b
  have hroot := localAnchor_finite_energy d.1 s (center b-incoming)
    (anchorPairAllowed T A s b) (fun a c h => h.2.2.2)
  have he (u : Fin (T b)) : (u.val:ℤ)-(center b-incoming)=(u.val:ℤ)-center b+incoming := by omega
  simp_rw [he] at hroot
  rw [binaryAnchorAverage_sum]
  calc
    _ ≤ (∑u : Fin (T b),∑v : Fin (T b),if anchorPairAllowed T A s b u v then
        localAnchorAverage d.1 s ((u.val:ℤ)-center b+incoming)^2 else 0) * binaryTreeBudget K b := by
      simp only [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      split_ifs with hr
      · exact mul_le_mul_of_nonneg_left
          (binaryDescendantEnergy_le T n g s center globalShift A shift hplat B C hB hC b d hcap
            u v hr.1 hr.2.1) (sq_nonneg _)
      · simp only [zero_mul,le_refl]
    _ ≤ (2*((2^s:ℕ):ℝ)^3*B b)*binaryTreeBudget K b := by
      apply mul_le_mul_of_nonneg_right _ hbudget
      exact hroot.trans (mul_le_mul_of_nonneg_left hcap.1 (by positivity))

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- A literal unsigned length-L translated motif admits at most L child
labels in any finite window, even when the intended motif does not fit. -/
theorem motifIndicator_finite_sum (s N : ℕ) (X : ℤ) :
    (∑h : Fin N,motifIndicator s ((h.val:ℤ)-X)) ≤ (2^s:ℕ) := by
  let A := Finset.univ.filter (fun h : Fin N => 0≤(h.val:ℤ)-X ∧ (h.val:ℤ)-X<(2^s:ℕ))
  have hc : A.card≤2^s := by
    have H := Finset.card_le_card_of_injOn (s:=A) (t:=Finset.range (2^s))
      (fun h : Fin N => ((h.val:ℤ)-X).toNat) ?_ ?_
    · simpa only [Finset.card_range] using H
    · intro h hh
      have h' := (Finset.mem_filter.mp hh).2
      apply Finset.mem_range.mpr
      dsimp only
      omega
    · intro h hh j hj he
      have h' := (Finset.mem_filter.mp hh).2
      have j' := (Finset.mem_filter.mp hj).2
      apply Fin.ext
      dsimp only at he
      omega
  have he : (∑h : Fin N,motifIndicator s ((h.val:ℤ)-X)) = (A.card:ℝ) := by
    simp only [motifIndicator,A,Finset.sum_ite,Finset.sum_const_zero,add_zero,
      Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [he]
  exact_mod_cast hc

/-- The complete bits law is arbitrary. All extra-leaf offsets may be
mutually correlated and correlated with the retained forced-anchor kernel.
Only the extra leaf label variables themselves are summed here. -/
def extraLabelAverage {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (s N e : ℕ) (f : Ω → ℝ) (X : Ω → Fin e → ℤ) (h : Fin e → Fin N) : ℝ :=
  P.expect (fun ω => f ω*∏j,motifIndicator s (((h j).val:ℤ)-X ω j))

theorem extraLabelAverage_nonneg {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (s N e : ℕ) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (X : Ω → Fin e → ℤ)
    (h : Fin e → Fin N) : 0≤extraLabelAverage P s N e f X h := by
  apply Finset.sum_nonneg
  intro ω hω
  apply mul_nonneg (P.nonneg ω)
  exact mul_nonneg (hf ω) (Finset.prod_nonneg (fun j _ => motifIndicator_nonneg _ _))

/-- Source the correlated-anchor estimate, extra leaf l1 cost before squaring. No free
T_1 cost and no invalid decoupling of global displacements enter. -/
theorem extraLabelAverage_sum {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (s N e : ℕ) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (X : Ω → Fin e → ℤ) :
    (∑h : Fin e → Fin N,extraLabelAverage P s N e f X h) ≤
      ((2^s:ℕ):ℝ)^e*P.expect f := by
  unfold extraLabelAverage expect
  rw [Finset.sum_comm]
  simp_rw [←mul_assoc,←Finset.mul_sum]
  calc
    _ ≤ ∑ω,P.mass ω*f ω*(((2^s:ℕ):ℝ)^e) := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (P.nonneg _) (hf ω))
      have he := Fintype.prod_sum (fun (j : Fin e) (h : Fin N) => motifIndicator s ((h.val:ℤ)-X ω j))
      rw [←he]
      calc
        _ ≤ ∏_j : Fin e,((2^s:ℕ):ℝ) := by
          apply Finset.prod_le_prod₀
          · intro j hj
            exact Finset.sum_nonneg (fun h hh => motifIndicator_nonneg _ _)
          · intro j hj
            exact motifIndicator_finite_sum s N (X ω j)
        _ = _ := by simp
    _ = _ := by rw [←Finset.sum_mul]; ring

/-- The squared extra-leaf cost follows from nonnegativity AFTER the whole
shared-bit average, exactly as in the source (not from independence). -/
theorem extraLabelAverage_energy {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (s N e : ℕ) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (X : Ω → Fin e → ℤ) :
    (∑h : Fin e → Fin N,extraLabelAverage P s N e f X h ^ 2) ≤
      ((2^s:ℕ):ℝ)^(2*e)*(P.expect f)^2 := by
  have hn (h : Fin e → Fin N) := extraLabelAverage_nonneg P s N e f hf X h
  calc
    _ ≤ (∑h : Fin e → Fin N,extraLabelAverage P s N e f X h)^2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun h _ => hn h)
    _ ≤ (((2^s:ℕ):ℝ)^e*P.expect f)^2 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun h _ => hn h))
      exact extraLabelAverage_sum P s N e f hf X
    _ = _ := by rw [mul_pow,←pow_mul]; congr 2; omega
end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
