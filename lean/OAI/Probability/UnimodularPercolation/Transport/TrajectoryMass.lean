import Mathlib
import OAI.Probability.UnimodularPercolation.Splicing.MomentBounds

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldPathWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def finiteFieldIntegral (Q : Finset E) (p : ℝ) (f : Set E → ℝ) : ℝ :=
  ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * f (finiteFieldSet Q ω)

theorem finiteFieldIntegral_nonneg (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ finiteFieldIntegral Q p f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (finiteFieldWeight_nonneg Q p ω) (hf _)

theorem finiteFieldIntegral_sum {I : Type*} (Q : Finset E) (p : ℝ) (S : Finset I)
    (f : I → Set E → ℝ) :
    finiteFieldIntegral Q p (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, finiteFieldIntegral Q p (f i) := by
  simp only [finiteFieldIntegral, Finset.mul_sum]
  exact Finset.sum_comm

 

theorem finiteFamilyIntegral_prod (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : ↥J → Set E → ℝ) :
    finiteFamilyIntegral Q J p (fun η => ∏ i : ↥J, f i (η i)) =
      ∏ i : ↥J, finiteFieldIntegral Q p (f i) := by
  simp only [finiteFamilyIntegral, finiteFamilyWeight, finiteFieldFamily_at,
    ← Finset.prod_mul_distrib, finiteFieldIntegral]
  exact (Fintype.prod_sum (fun (i : ↥J) (ω : FiniteField Q) =>
    finiteFieldWeight Q p ω * f i (finiteFieldSet Q ω))).symm

 

noncomputable def oldPathWeight (k : ℕ) (q : Set E → V → V → ℝ)
    (y : ℕ → V) (η : ℕ → Set E) : ℝ :=
  ∏ i : ↥(Finset.Icc 1 k), q (η i) (y i) (y (i.val-1))

theorem oldPathWeight_nonneg (k : ℕ) (q : Set E → V → V → ℝ)
    (hq : ∀ ω a b, 0 ≤ q ω a b) (y : ℕ → V) (η : ℕ → Set E) :
    0 ≤ oldPathWeight k q y η :=
  Finset.prod_nonneg fun _ _ => hq _ _ _

theorem oldPathWeight_integral (Q : Finset E) (k : ℕ) (p : ℝ)
    (q : Set E → V → V → ℝ) (y : ℕ → V) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p (oldPathWeight k q y) =
      ∏ i : ↥(Finset.Icc 1 k), finiteFieldIntegral Q p (fun ω => q ω (y i) (y (i.val-1))) := by
  unfold oldPathWeight
  exact finiteFamilyIntegral_prod Q (Finset.Icc 1 k) p
    (fun i ω => q ω (y i) (y (i.val-1)))

 

theorem oldPathWeight_support (G : BondGraph V E) (k M : ℕ) (L : ℝ)
    (q : Set E → V → V → ℝ)
    (hs : ∀ ω a b, q ω a b ≠ 0 → b ∈ cluster G ω a ∧
      (cluster G ω a).Finite ∧ (cluster G ω a).ncard ≤ M ∧ GoodForScale G ω a L)
    (y : ℕ → V) (η : ℕ → Set E) (hy : oldPathWeight k q y η ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ k → y (i-1) ∈ cluster G (η i) (y i) ∧
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M ∧
      GoodForScale G (η i) (y i) L := by
  intro i hi hik
  apply hs
  have h := (Finset.prod_ne_zero_iff.mp hy) ⟨i, Finset.mem_Icc.mpr ⟨hi,hik⟩⟩ (Finset.mem_univ _)
  exact h

end OldPathWeight

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}

 
def oldRunConsEquiv (k : ℕ) : (Fin (k+1) → W) ≃ W × (Fin k → W) where
  toFun y := (y 0, Fin.tail y)
  invFun y := Fin.cons y.1 y.2
  left_inv := Fin.cons_self_tail
  right_inv y := by simp

 

noncomputable def oldRunWeight (K : ℕ → W → W → ℝ) : (k : ℕ) → W → (Fin k → W) → ℝ
  | 0, _, _ => 1
  | k+1, z, y => K (k+1) z (y 0) * oldRunWeight K k (y 0) (Fin.tail y)

theorem oldRunWeight_nonneg (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (k : ℕ) (z : W) (y : Fin k → W) : 0 ≤ oldRunWeight K k z y := by
  induction k generalizing z with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (hK _ _ _) (ih _ _)

theorem sum_oldRunWeight_succ [Fintype W] (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) :
    (∑ y : Fin (k+1) → W, oldRunWeight K (k+1) z y) =
      ∑ a : W, K (k+1) z a * ∑ y : Fin k → W, oldRunWeight K k a y := by
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun y => K (k+1) z y.1 * oldRunWeight K k y.1 y.2) (by intro y; rfl),
    Fintype.sum_prod_type]
  simp only [Finset.mul_sum]

 

theorem sum_oldRunWeight_le [Fintype W] (K : ℕ → W → W → ℝ)
    (hK : ∀ i a b, 0 ≤ K i a b) (u : ℝ) (hu : 0 ≤ u)
    (hrow : ∀ i a, ∑ b, K i a b ≤ u) (k : ℕ) (z : W) :
    (∑ y : Fin k → W, oldRunWeight K k z y) ≤ u^k := by
  induction k generalizing z with
  | zero => simp [oldRunWeight]
  | succ k ih =>
    rw [sum_oldRunWeight_succ]
    calc
      _ ≤ ∑ a : W, K (k+1) z a * u^k := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (ih a) (hK _ _ _)
      _ = (∑ a : W, K (k+1) z a) * u^k := (Finset.sum_mul _ _ _).symm
      _ ≤ u * u^k := mul_le_mul_of_nonneg_right (hrow _ _) (pow_nonneg hu _)
      _ = u^(k+1) := by ring

theorem sum_oldRunWeight_eq [Fintype W] (K : ℕ → W → W → ℝ)
    (u : ℝ) (hrow : ∀ i a, ∑ b, K i a b = u) (k : ℕ) (z : W) :
    (∑ y : Fin k → W, oldRunWeight K k z y) = u^k := by
  induction k generalizing z with
  | zero => simp [oldRunWeight]
  | succ k ih =>
    simp only [sum_oldRunWeight_succ, ih, ← Finset.sum_mul, hrow]
    ring

 

def oldRunVertices : (k : ℕ) → W → (Fin k → W) → ℕ → W
  | 0, z, _ => fun _ => z
  | k+1, z, y => fun i => if i ≤ k then oldRunVertices k (y 0) (Fin.tail y) i else z

@[simp] theorem oldRunVertices_last (k : ℕ) (z : W) (y : Fin k → W) :
    oldRunVertices k z y k = z := by
  cases k <;> simp [oldRunVertices]

theorem oldRunVertices_succ_of_le (k : ℕ) (z : W) (y : Fin (k+1) → W)
    (i : ℕ) (hi : i ≤ k) :
    oldRunVertices (k+1) z y i = oldRunVertices k (y 0) (Fin.tail y) i := by
  simp only [oldRunVertices, ite_eq_left hi]

 

theorem oldPathWeight_oldRunVertices (k : ℕ) (q : Set E → W → W → ℝ)
    (η : ℕ → Set E) (z : W) (y : Fin k → W) :
    oldPathWeight k q (oldRunVertices k z y) η =
      oldRunWeight (fun i => q (η i)) k z y := by
  induction k generalizing z with
  | zero =>
    unfold oldPathWeight
    rw [Finset.prod_coe_sort (Finset.Icc 1 0)
      (fun i => q (η i) (oldRunVertices 0 z y i) (oldRunVertices 0 z y (i-1)))]
    simp [oldRunWeight]
  | succ k ih =>
    unfold oldPathWeight
    rw [Finset.prod_coe_sort (Finset.Icc 1 (k+1))
      (fun i => q (η i) (oldRunVertices (k+1) z y i) (oldRunVertices (k+1) z y (i-1))),
      Finset.prod_Icc_succ_top (by omega)]
    have he : (∏ i ∈ Finset.Icc 1 k,
        q (η i) (oldRunVertices (k+1) z y i) (oldRunVertices (k+1) z y (i-1))) =
        oldPathWeight k q (oldRunVertices k (y 0) (Fin.tail y)) η := by
      unfold oldPathWeight
      rw [Finset.prod_coe_sort (Finset.Icc 1 k)
        (fun i => q (η i) (oldRunVertices k (y 0) (Fin.tail y) i)
          (oldRunVertices k (y 0) (Fin.tail y) (i-1)))]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      rw [oldRunVertices_succ_of_le _ _ _ _ hi'.2,
        oldRunVertices_succ_of_le _ _ _ _ (by omega)]
    rw [he, ih, oldRunVertices_last, Nat.add_sub_cancel,
      oldRunVertices_succ_of_le _ _ _ _ (le_refl _), oldRunVertices_last]
    exact mul_comm _ _

end FiniteOldRun

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}

 
noncomputable def finiteOldKernel (Q : Finset E) (p : ℝ)
    (q : Set E → W → W → ℝ) (a b : W) : ℝ :=
  finiteFieldIntegral Q p (fun ω => q ω a b)

theorem finiteOldKernel_nonneg (Q : Finset E) (p : unitInterval)
    (q : Set E → W → W → ℝ) (hq : ∀ ω a b, 0 ≤ q ω a b) (a b : W) :
    0 ≤ finiteOldKernel Q p q a b :=
  finiteFieldIntegral_nonneg Q p _ (fun _ => hq _ _ _)

 

theorem oldRunWeight_integral (Q : Finset E) (p : ℝ) (k : ℕ)
    (q : Set E → W → W → ℝ) (z : W) (y : Fin k → W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p
      (fun η => oldRunWeight (fun i => q (η i)) k z y) =
    oldRunWeight (fun _ => finiteOldKernel Q p q) k z y := by
  calc
    _ = finiteFamilyIntegral Q (Finset.Icc 1 k) p
        (fun η => oldPathWeight k q (oldRunVertices k z y) η) := by
      apply congrArg (finiteFamilyIntegral Q (Finset.Icc 1 k) p)
      funext η
      exact (oldPathWeight_oldRunVertices k q η z y).symm
    _ = ∏ i : ↥(Finset.Icc 1 k), finiteOldKernel Q p q
        (oldRunVertices k z y i) (oldRunVertices k z y (i.val-1)) :=
      oldPathWeight_integral Q k p q _
    _ = oldRunWeight (fun _ => finiteOldKernel Q p q) k z y :=
      oldPathWeight_oldRunVertices k (fun (_ : Set E) => finiteOldKernel Q p q)
        (fun _ => ∅) z y

 

theorem independent_oldRun_success [Fintype W] (Q : Finset E) (p : ℝ) (k : ℕ)
    (q : Set E → W → W → ℝ) (u : ℝ)
    (hrow : ∀ a, ∑ b, finiteOldKernel Q p q a b = u) (z : W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p
      (fun η => ∑ y : Fin k → W, oldRunWeight (fun i => q (η i)) k z y) = u^k := by
  rw [finiteFamilyIntegral_sum]
  simp only [oldRunWeight_integral]
  exact sum_oldRunWeight_eq _ u (fun _ => hrow) k z

 

theorem independent_oldRun_success_le [Fintype W] (Q : Finset E) (p : unitInterval) (k : ℕ)
    (q : Set E → W → W → ℝ) (hq : ∀ ω a b, 0 ≤ q ω a b) (u : ℝ) (hu : 0 ≤ u)
    (hrow : ∀ a, ∑ b, finiteOldKernel Q p q a b ≤ u) (z : W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p
      (fun η => ∑ y : Fin k → W, oldRunWeight (fun i => q (η i)) k z y) ≤ u^k := by
  rw [finiteFamilyIntegral_sum]
  simp only [oldRunWeight_integral]
  exact sum_oldRunWeight_le _ (fun _ => finiteOldKernel_nonneg Q p q hq) u hu (fun _ => hrow) k z

end IndependentOldRun

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedCodeFiber
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem sum_comp_le_sum_of_injective {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ a, w (f a)) ≤ ∑ b, w b := by
  rw [← Finset.sum_image hf.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun b _ _ => hw b)

 
theorem finite_sum_group_weight {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (m : A → ℝ) (w : B → ℝ) :
    (∑ a, m a * w (f a)) = ∑ b, w b * ∑ a, if f a = b then m a else 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact mul_comm _ _

 

theorem finite_choice_fiber_le {A B C P : Type*} [Fintype A] [Fintype P]
    (f : A → B) (ctx : A → C) (choice : A → P)
    (hir : Function.Injective (fun a => (ctx a,choice a,f a)))
    (hctx : ∀ a b, f a = f b → ctx a = ctx b)
    (q : C → P → ℝ) (hq : ∀ c p, 0 ≤ q c p)
    (hrow : ∀ c, ∑ p, q c p ≤ 1) (b : B) :
    (∑ a, if f a = b then q (ctx a) (choice a) else 0) ≤ 1 := by
  let J := {a : A // f a = b}
  by_cases hne : Nonempty J
  · let a₀ : J := Classical.choice hne
    have hc (a : J) : ctx a.val = ctx a₀.val := hctx _ _ (a.property.trans a₀.property.symm)
    have hi : Function.Injective (fun a : J => choice a.val) := by
      intro a a' he
      apply Subtype.ext
      apply hir
      exact Prod.ext (hctx _ _ (a.property.trans a'.property.symm))
        (Prod.ext he (a.property.trans a'.property.symm))
    have hb := sum_comp_le_sum_of_injective (fun a : J => choice a.val) hi
      (q (ctx a₀.val)) (hq _)
    have he : (∑ a, if f a = b then q (ctx a) (choice a) else 0) =
        ∑ a : J, q (ctx a) (choice a) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by intro a; simp) _
    rw [he]
    simpa only [hc] using hb.trans (hrow (ctx a₀.val))
  · have hn (a : A) : f a ≠ b := fun h => hne ⟨⟨a,h⟩⟩
    simp only [ite_eq_right (hn _),Finset.sum_const_zero,zero_le_one]

 

theorem finite_weighted_code_mass_le {A B C P : Type*} [Fintype A] [Fintype B] [Fintype P]
    (f : A → B) (ctx : A → C) (choice : A → P)
    (hir : Function.Injective (fun a => (ctx a,choice a,f a)))
    (hctx : ∀ a b, f a = f b → ctx a = ctx b)
    (q : C → P → ℝ) (hq : ∀ c p, 0 ≤ q c p) (hrow : ∀ c, ∑ p, q c p ≤ 1)
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ a, q (ctx a) (choice a) * w (f a)) ≤ ∑ b, w b := by
  rw [finite_sum_group_weight]
  apply Finset.sum_le_sum
  intro b _
  calc
    _ ≤ w b * 1 := mul_le_mul_of_nonneg_left
      (finite_choice_fiber_le f ctx choice hir hctx q hq hrow b) (hw b)
    _ = w b := mul_one _

end WeightedCodeFiber
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedInverseLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteInverseLoad_weighted_le {I P : Type*} [Fintype I] [Fintype P]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x z : V) (k M : ℕ)
    (L : ℝ) (hL : 1 ≤ L)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (choice : I → P) (hir : Function.Injective (fun a => (inp a,choice a,steps a)))
    (q : SpliceState E → P → ℝ) (hq : ∀ s b, 0 ≤ q s b)
    (hrow : ∀ s, ∑ b, q s b ≤ 1)
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (hz : ∀ a, y a k = z) (hfin : ∀ a, (cluster G (out a).1 x).Finite)
    (hgood : ∀ a i, 1 ≤ i → i ≤ k → (cluster G ((inp a).2 i) (y a i)).Finite ∧
      (cluster G ((inp a).2 i) (y a i)).ncard ≤ M ∧ GoodForScale G ((inp a).2 i) (y a i) L)
    (t : SpliceState E) :
    finiteInverseLoad out (fun a => q (inp a) (choice a) * ∏ i : Fin k,
      (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1):ℝ)⁻¹) t ≤
      inverseCodeMass M L ^ k := by
  let J := {a : I // out a = t}
  let c (a : J) := gapSpliceCode G (out a.val).1 x z (steps a.val)
  have hvalid (a : J) : ValidSparseGapCode k M (c a) := by
    have hv := (htrace a.val).valid_gap_code G hloc x (inp a.val).2 (y a.val) k 0 M
      (inp a.val).1 (out a.val).1 (steps a.val) (hfin a.val) L (hgood a.val)
    simpa only [c,hz a.val] using hv.1
  let arr (a : J) := sparseGapArray k M (c a) (hvalid a)
  let ctx (a : J) := (inp a.val,steps a.val)
  have hc (a b : J) (he : arr a = arr b) : ctx a = ctx b := by
    have ho : out a.val = out b.val := a.property.trans b.property.symm
    have hcode : c a = c b := sparseGapArray_injective k M (c a) (c b)
      (hvalid a) (hvalid b) he
    have htB : SpliceTrace G x (inp b.val).2 (y b.val) k 0
        (inp b.val).1 (steps b.val) (out a.val).1 := by
      rw [ho]
      exact htrace b.val
    have heB : SpliceExecution G x (inp b.val) (steps b.val) (out a.val) := ho.symm ▸ hex b.val
    have hg : gapSpliceCode G (out a.val).1 x (y a.val k) (steps a.val) =
        gapSpliceCode G (out a.val).1 x (y a.val k) (steps b.val) := by
      simpa only [c,hz a.val,ho] using hcode
    have hze : y a.val k = y b.val k := (hz a.val).trans (hz b.val).symm
    have hs := (htrace a.val).code_unique_of_gapCode G x (inp a.val).2 (inp b.val).2
      (y a.val) (y b.val) k 0 (inp a.val).1 (inp b.val).1 (out a.val).1
      (steps a.val) (steps b.val) htB hze (hfin a.val) hg
    have hi := (htrace a.val).input_unique_of_gapCode G x (inp a.val).2 (inp b.val).2
      (y a.val) (y b.val) k 0 (inp a.val).1 (inp b.val).1 (out a.val).1
      (steps a.val) (steps b.val) htB hze (hfin a.val) hg (out a.val).2 (hex a.val) heB
    exact Prod.ext hi hs
  have hi : Function.Injective (fun a : J => (ctx a,choice a.val,arr a)) := by
    intro a b he
    apply Subtype.ext
    apply hir
    have hec := congrArg Prod.fst he
    have hin : inp a.val = inp b.val := congrArg (fun s : SpliceState E × List (ℕ × E) => s.1) hec
    have hst : steps a.val = steps b.val := congrArg (fun s : SpliceState E × List (ℕ × E) => s.2) hec
    exact Prod.ext hin (Prod.ext (congrArg (fun z => z.2.1) he) hst)
  let w (b : Fin k → Fin (M+1)) := ∏ i, gapLetterWeight L (b i).val
  have hb := finite_weighted_code_mass_le arr ctx (fun a : J => choice a.val) hi hc
    (fun s b => q s.1 b) (fun s => hq s.1) (fun s => hrow s.1) w
    (fun b => Finset.prod_nonneg (fun i _ => gapLetterWeight_nonneg L (by linarith) _))
  change (∑ a : J, q (inp a.val) (choice a.val) * w (arr a)) ≤ ∑ b, w b at hb
  have he : finiteInverseLoad out (fun a => q (inp a) (choice a) * ∏ i : Fin k,
      (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1):ℝ)⁻¹) t =
      ∑ a : J, q (inp a.val) (choice a.val) * ∏ i : Fin k,
      (traceContactCount G (inp a.val).2 (y a.val) (out a.val).1 x (steps a.val) (i.val+1):ℝ)⁻¹ := by
    rw [finiteInverseLoad,← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro a; simp) _
  rw [he]
  calc
    _ ≤ ∑ a : J, q (inp a.val) (choice a.val) * w (arr a) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hq _ _)
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro i _
      have h := ((htrace a.val).contact_weight_bound G hloc x (inp a.val).2 (y a.val)
        k 0 M (inp a.val).1 (out a.val).1 (steps a.val) (hfin a.val) L hL
        (hgood a.val) (i.val+1)).2
      simpa only [w,arr,sparseGapArray,c,hz a.val] using h
    _ ≤ ∑ b, w b := hb
    _ = _ := total_gap_code_mass k M L

end WeightedInverseLoad
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldRunInverseLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteInverseLoad_oldRun_le {I W : Type*} [Fintype I] [Fintype W]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x z : V) (k M : ℕ)
    (L : ℝ) (hL : 1 ≤ L)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (start : W) (path : I → Fin k → W)
    (hir : Function.Injective (fun a => (inp a,path a,steps a)))
    (q : Set E → W → W → ℝ) (hq : ∀ ω a b, 0 ≤ q ω a b)
    (hrow : ∀ ω a, ∑ b, q ω a b ≤ 1)
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (hz : ∀ a, y a k = z) (hfin : ∀ a, (cluster G (out a).1 x).Finite)
    (hgood : ∀ a i, 1 ≤ i → i ≤ k → (cluster G ((inp a).2 i) (y a i)).Finite ∧
      (cluster G ((inp a).2 i) (y a i)).ncard ≤ M ∧ GoodForScale G ((inp a).2 i) (y a i) L)
    (t : SpliceState E) :
    finiteInverseLoad out (fun a => oldRunWeight (fun i => q ((inp a).2 i)) k start (path a) *
      ∏ i : Fin k, (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1):ℝ)⁻¹) t ≤
      inverseCodeMass M L ^ k := by
  apply finiteInverseLoad_weighted_le G hloc x z k M L hL inp out steps y path hir
    (fun s b => oldRunWeight (fun i => q (s.2 i)) k start b)
    (fun s b => oldRunWeight_nonneg _ (fun _ => hq _) k start b) _ htrace hex hz hfin hgood t
  intro s
  simpa only [one_pow] using sum_oldRunWeight_le (fun i => q (s.2 i))
    (fun _ => hq _) 1 zero_le_one (fun _ => hrow _) k start

end OldRunInverseLoad
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P : Type*}

 

abbrev FiniteChoiceTraceIndex (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V) :=
  (r : P) × FiniteTraceIndex G x k Q (A r) (y r)

def choiceTraceInput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (a : FiniteChoiceTraceIndex G x k Q A y) : SpliceState E :=
  traceIndexInput G x k Q (A a.1) (y a.1) a.2

def choiceTraceOutput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (a : FiniteChoiceTraceIndex G x k Q A y) : SpliceState E :=
  traceIndexOutput G x k Q (A a.1) (y a.1) a.2

def choiceTraceCode (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (a : FiniteChoiceTraceIndex G x k Q A y) : List (ℕ × E) :=
  traceIndexCode G x k Q (A a.1) (y a.1) a.2

noncomputable def choiceTraceMass (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ) (a : FiniteChoiceTraceIndex G x k Q A y) : ℝ :=
  q (choiceTraceInput G x k Q A y a) a.1 *
    traceIndexMass G x k Q (A a.1) (y a.1) a.2

theorem choiceTrace_injective (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V) :
    Function.Injective (fun a : FiniteChoiceTraceIndex G x k Q A y =>
      (choiceTraceInput G x k Q A y a,a.1,choiceTraceCode G x k Q A y a)) := by
  rintro ⟨r,a⟩ ⟨r',b⟩ he
  have hr : r = r' := congrArg (fun z => z.2.1) he
  subst r'
  have hin : traceIndexInput G x k Q (A r) (y r) a =
      traceIndexInput G x k Q (A r) (y r) b :=
    congrArg (fun z : SpliceState E × P × List (ℕ × E) => z.1) he
  have hcode : traceIndexCode G x k Q (A r) (y r) a =
      traceIndexCode G x k Q (A r) (y r) b :=
    congrArg (fun z : SpliceState E × P × List (ℕ × E) => z.2.2) he
  have hab : a = b := traceIndex_injective G x k Q (A r) (y r) (Prod.ext hin hcode)
  subst b
  rfl

noncomputable def finiteChoiceForwardLoad [Fintype P]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ) : SpliceState E → ℝ :=
  finiteInverseLoad (choiceTraceOutput G x k Q A y) (choiceTraceMass G x k Q A y q)

 
theorem finiteChoiceForwardLoad_bounds [Fintype P]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x z : V) (k M : ℕ)
    (L : ℝ) (hL : 1 ≤ L) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ) (hq : ∀ s r, 0 ≤ q s r)
    (hrow : ∀ s, ∑ r, q s r ≤ 1)
    (hA : ∀ r, A r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hz : ∀ r s, s ∈ A r → y r s k = z)
    (hgood : ∀ r s, s ∈ A r → ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (s.2 i) (y r s i)).Finite ∧
      (cluster G (s.2 i) (y r s i)).ncard ≤ M ∧ GoodForScale G (s.2 i) (y r s i) L)
    (t : SpliceState E) :
    0 ≤ finiteChoiceForwardLoad G x k Q A y q t ∧
      finiteChoiceForwardLoad G x k Q A y q t ≤ inverseCodeMass M L ^ k := by
  constructor
  · apply finiteInverseLoad_nonneg
    intro a
    exact mul_nonneg (hq _ _) (Finset.prod_nonneg (fun _ _ => by positivity))
  · apply finiteInverseLoad_weighted_le G hloc x z k M L hL
      (choiceTraceInput G x k Q A y) (choiceTraceOutput G x k Q A y)
      (choiceTraceCode G x k Q A y) (fun a => y a.1 a.2.1.val) Sigma.fst
      (choiceTrace_injective G x k Q A y) q hq hrow
      (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).1)
      (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).2)
      (fun a => hz a.1 _ a.2.1.property) _
      (fun a => hgood a.1 _ a.2.1.property) t
    intro a
    have hs := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp
      (traceIndexOutput_mem G x k Q (A a.1) (y a.1) (hA a.1) a.2)
    exact cluster_finite_of_finite_edges G (Q.finite_toSet.subset hs.1) x

 

theorem sum_traceIndexMass [Nonempty E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (k M : ℕ) (Q : Finset E) (A : Finset (SpliceState E))
    (y : SpliceState E → ℕ → V) (s : ↥A)
    (hs : s.val ∈ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hy : y s.val 0 ∈ cluster G s.val.1 x)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (s.val.2 i) (y s.val i) (y s.val (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (s.val.2 i) (y s.val i)).Finite ∧
      (cluster G (s.val.2 i) (y s.val i)).ncard ≤ M) :
    (∑ c : ↥(finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q),
      traceIndexMass G x k Q A y ⟨s,c⟩) = 1 := by
  have hs' := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s.val).mp hs
  have hn := sum_finite_trace_probabilities G hloc x s.val.2 (y s.val) k M Q
    (fun i _ _ => hs'.2.1 i) hchain hcaps 0 (Nat.zero_le _) s.val.1 hy
    (cluster_finite_of_finite_edges G (Q.finite_toSet.subset hs'.1) x)
  rw [← Finset.sum_coe_sort (finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q)] at hn
  rw [← hn]
  apply Finset.sum_congr rfl
  intro c _
  have ht := ((mem_finiteTraceCodes_iff G x s.val.2 (y s.val) k 0 s.val.1 Q c.val).mp c.property).2
  have hf := ht.runMasks_first G x s.val.2 (y s.val) k 0 s.val.1 _ c.val s.val.2 (by intros; rfl)
  simp only [traceIndexMass,traceIndexOutput,hf]

 
theorem finiteChoiceForwardLoad_mean [Fintype P] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k M : ℕ) (Q : Finset E) (p : ℝ)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ)
    (hA : ∀ r, A r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hy : ∀ r s, s ∈ A r → y r s 0 ∈ cluster G s.1 x)
    (hchain : ∀ r s, s ∈ A r → ∀ i ∈ Finset.Icc 1 k, Conn G (s.2 i) (y r s i) (y r s (i-1)))
    (hcaps : ∀ r s, s ∈ A r → ∀ i ∈ Finset.Icc 1 k,
      (cluster G (s.2 i) (y r s i)).Finite ∧ (cluster G (s.2 i) (y r s i)).ncard ≤ M) :
    (∑ t ∈ finiteSpliceDomain Q (Finset.Icc 1 k), spliceTupleWeight Q (Finset.Icc 1 k) p t *
      finiteChoiceForwardLoad G x k Q A y q t) =
      ∑ r, ∑ s ∈ A r, spliceTupleWeight Q (Finset.Icc 1 k) p s * q s r := by
  have hd := finiteInverseLoad_density G x k Q p
    (choiceTraceInput G x k Q A y) (choiceTraceOutput G x k Q A y)
    (choiceTraceCode G x k Q A y) (fun a => y a.1 a.2.1.val)
    (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).1)
    (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).2)
    (choiceTraceMass G x k Q A y q) (finiteSpliceDomain Q (Finset.Icc 1 k))
    (fun a => traceIndexOutput_mem G x k Q (A a.1) (y a.1) (hA a.1) a.2) (fun _ => 1)
  simp only [mul_one] at hd
  unfold finiteChoiceForwardLoad
  rw [← hd,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fintype.sum_sigma,← Finset.sum_coe_sort (A r)
    (fun s => spliceTupleWeight Q (Finset.Icc 1 k) p s * q s r)]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ c : ↥(finiteTraceCodes G x s.val.2 (y r s.val) k 0 s.val.1 Q),
    spliceTupleWeight Q (Finset.Icc 1 k) p s.val *
      (q s.val r * traceIndexMass G x k Q (A r) (y r) ⟨s,c⟩)) = _
  simp only [← mul_assoc,← Finset.mul_sum]
  rw [sum_traceIndexMass G hloc x k M Q (A r) (y r) s (hA r s.property)
    (hy r _ s.property) (hchain r _ s.property) (hcaps r _ s.property),mul_one]

end ChoiceForwardDensity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointRootMass
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def auxiliaryTupleWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : SpliceState E) : ℝ := ∏ i ∈ J, bernoulliWeight Q (domainBits Q (s.2 i)) p

theorem auxiliaryTupleWeight_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (s : SpliceState E) : 0 ≤ auxiliaryTupleWeight Q J p s :=
  Finset.prod_nonneg fun _ _ => bernoulliWeight_nonneg _ _ p

 

noncomputable def endpointRootMass {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E)
    (endpoint : I → V) (m : I → ℝ) (ω : Set E) (z : V) : ℝ :=
  ∑ a, if (out a).1 = ω ∧ endpoint a = z then auxiliaryTupleWeight Q J p (out a) * m a else 0

theorem endpointRootMass_nonneg {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : unitInterval) (out : I → SpliceState E)
    (endpoint : I → V) (m : I → ℝ) (hm : ∀ a, 0 ≤ m a) (ω : Set E) (z : V) :
    0 ≤ endpointRootMass Q J p out endpoint m ω z := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact mul_nonneg (auxiliaryTupleWeight_nonneg Q J p _) (hm a)
  · exact le_refl 0

 
theorem finiteRootLoad_eq_sum {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E) (m : I → ℝ)
    (hs : ∀ a, out a ∈ finiteSpliceDomain Q J) (ω : FiniteField Q) :
    finiteRootLoad Q J p (finiteInverseLoad out m) ω =
      ∑ a, if (out a).1 = finiteFieldSet Q ω then auxiliaryTupleWeight Q J p (out a) * m a else 0 := by
  simp only [finiteRootLoad,finiteInverseLoad,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  obtain ⟨⟨r,η⟩,_,ha⟩ := Finset.mem_image.mp (hs a)
  change (finiteFieldSet Q r,finiteFieldFamily Q J η) = out a at ha
  rw [← ha]
  have he (θ : ↥J → FiniteField Q) :
      (finiteFieldSet Q r,finiteFieldFamily Q J η) = (finiteFieldSet Q ω,finiteFieldFamily Q J θ) ↔
      r = ω ∧ η = θ := by
    constructor
    · intro h
      exact ⟨finiteFieldSet_injective Q (congrArg Prod.fst h),
        finiteFieldFamily_injective Q J (congrArg Prod.snd h)⟩
    · rintro ⟨rfl,rfl⟩; rfl
  simp only [he]
  by_cases hr : r = ω
  · subst r
    simp only [true_and,ite_true,Finset.sum_ite_eq,Finset.mem_univ]
    rw [auxiliaryTupleWeight,prod_fieldFamilyWeight]
  · have hr' : finiteFieldSet Q r ≠ finiteFieldSet Q ω := fun h => hr (finiteFieldSet_injective Q h)
    simp [hr,hr']

 

theorem endpointRootMass_le {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : unitInterval) (out : I → SpliceState E)
    (endpoint : I → V) (m : I → ℝ) (hs : ∀ a, out a ∈ finiteSpliceDomain Q J)
    (z : V) (C : ℝ)
    (hC : ∀ t ∈ finiteSpliceDomain Q J, finiteInverseLoad out
      (fun a => if endpoint a = z then m a else 0) t ≤ C) (ω : FiniteField Q) :
    endpointRootMass Q J p out endpoint m (finiteFieldSet Q ω) z ≤ C := by
  have hb := finiteRootLoad_le Q J p _ C hC ω
  rw [finiteRootLoad_eq_sum Q J p out _ hs ω] at hb
  convert hb using 1
  unfold endpointRootMass
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

 

theorem sum_endpointRootMass {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E)
    (endpoint : I → V) (m : I → ℝ) (ω : Set E) (S : Finset V) :
    (∑ z ∈ S, endpointRootMass Q J p out endpoint m ω z) =
      ∑ a, if (out a).1 = ω ∧ endpoint a ∈ S then auxiliaryTupleWeight Q J p (out a) * m a else 0 := by
  simp only [endpointRootMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hr : (out a).1 = ω
  · simp only [hr,true_and,Finset.sum_ite_eq]
  · simp [hr]

end EndpointRootMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearPairMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_near_pair_mass_le_cover {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : unitInterval)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (hm₁ : ∀ a, 0 ≤ m₁ a) (hm₂ : ∀ b, 0 ≤ m₂ b)
    (endpoint : I₂ → V) (R : I₁ → I₂ → Prop) (S : I₁ → Finset V)
    (hS : ∀ a b, (out₁ a).1 = (out₂ b).1 → R a b → endpoint b ∈ S a) :
    (∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧ R a b then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0) ≤
    ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a *
      ∑ z ∈ S a, endpointRootMass Q J₂ p out₂ endpoint m₂ (out₁ a).1 z := by
  apply Finset.sum_le_sum
  intro a _
  rw [sum_endpointRootMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  by_cases h : (out₁ a).1 = (out₂ b).1 ∧ R a b
  · have hh : (out₂ b).1 = (out₁ a).1 ∧ endpoint b ∈ S a :=
      ⟨h.1.symm,hS a b h.1 h.2⟩
    rw [ite_eq_left h,ite_eq_left hh]
    change (spliceTupleWeight Q J₁ p (out₁ a) * auxiliaryTupleWeight Q J₂ p (out₂ b)) *
      m₁ a * m₂ b ≤ _
    ring_nf
    exact le_refl _
  · rw [ite_eq_right h]
    apply mul_nonneg (mul_nonneg (spliceTupleWeight_nonneg Q J₁ p _) (hm₁ a))
    split_ifs
    · exact mul_nonneg (auxiliaryTupleWeight_nonneg Q J₂ p _) (hm₂ b)
    · exact le_refl 0

 

theorem finite_near_pair_mass_le {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : unitInterval)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (hm₁ : ∀ a, 0 ≤ m₁ a) (hm₂ : ∀ b, 0 ≤ m₂ b)
    (endpoint : I₂ → V) (R : I₁ → I₂ → Prop) (S : I₁ → Finset V)
    (hS : ∀ a b, (out₁ a).1 = (out₂ b).1 → R a b → endpoint b ∈ S a)
    (N : ℕ) (hN : ∀ a, (S a).card ≤ N) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a z, z ∈ S a → endpointRootMass Q J₂ p out₂ endpoint m₂ (out₁ a).1 z ≤ C) :
    (∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧ R a b then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0) ≤
    (N:ℝ) * C * ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a := by
  apply (finite_near_pair_mass_le_cover Q J₁ J₂ p out₁ out₂ m₁ m₂ hm₁ hm₂ endpoint R S hS).trans
  calc
    _ ≤ ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a * ((N:ℝ)*C) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (spliceTupleWeight_nonneg Q J₁ p _) (hm₁ a))
      calc
        _ ≤ ∑ _z ∈ S a, C := Finset.sum_le_sum (fun z hz => hb a z hz)
        _ = ((S a).card:ℝ) * C := by simp
        _ ≤ (N:ℝ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hN a) hC
    _ = _ := by rw [← Finset.sum_mul]; ring

end NearPairMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointInverseBound
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finiteInverseLoad_subtype {I : Type*} [Fintype I]
    (out : I → SpliceState E) (m : I → ℝ) (P : I → Prop) (t : SpliceState E) :
    finiteInverseLoad out (fun a => if P a then m a else 0) t =
      finiteInverseLoad (fun a : {a : I // P a} => out a.val) (fun a => m a.val) t := by
  unfold finiteInverseLoad
  have he : (∑ a, if out a = t then if P a then m a else 0 else 0) =
      ∑ a, if P a then if out a = t then m a else 0 else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> rfl
  rw [he,← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro a; simp) _

 

theorem endpointInverseLoad_le {I P : Type*} [Fintype I] [Fintype P]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k M : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (endpoint : I → V) (choice : I → P)
    (hir : Function.Injective (fun a => (inp a,endpoint a,choice a,steps a)))
    (q : V → SpliceState E → P → ℝ) (hq : ∀ z s b, 0 ≤ q z s b)
    (hrow : ∀ z s, ∑ b, q z s b ≤ 1)
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (hz : ∀ a, y a k = endpoint a) (hfin : ∀ a, (cluster G (out a).1 x).Finite)
    (hgood : ∀ a i, 1 ≤ i → i ≤ k → (cluster G ((inp a).2 i) (y a i)).Finite ∧
      (cluster G ((inp a).2 i) (y a i)).ncard ≤ M ∧ GoodForScale G ((inp a).2 i) (y a i) L)
    (z : V) (t : SpliceState E) :
    finiteInverseLoad out (fun a => if endpoint a = z then
      q (endpoint a) (inp a) (choice a) * ∏ i : Fin k,
        (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1):ℝ)⁻¹ else 0) t ≤
      inverseCodeMass M L ^ k := by
  rw [finiteInverseLoad_subtype]
  let J := {a : I // endpoint a = z}
  have hi : Function.Injective (fun a : J => (inp a.val,choice a.val,steps a.val)) := by
    intro a b he
    apply Subtype.ext
    apply hir
    have hin : inp a.val = inp b.val := congrArg (fun s : SpliceState E × P × List (ℕ × E) => s.1) he
    exact Prod.ext hin (Prod.ext (a.property.trans b.property.symm) (congrArg (fun s : SpliceState E × P × List (ℕ × E) => s.2) he))
  have hb := finiteInverseLoad_weighted_le G hloc x z k M L hL
    (fun a : J => inp a.val) (fun a : J => out a.val) (fun a : J => steps a.val)
    (fun a : J => y a.val) (fun a : J => choice a.val) hi (q z) (hq z) (hrow z)
    (fun a => htrace a.val) (fun a => hex a.val) (fun a => (hz a.val).trans a.property)
    (fun a => hfin a.val) (fun a => hgood a.val) t
  convert hb using 1
  apply congrArg (fun f : J → ℝ => finiteInverseLoad (fun a : J => out a.val) f t)
  funext a
  rw [a.property]

end EndpointInverseBound
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearHangingMass
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem SpliceTrace.head_hanging (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf) :
    hangingSide G ωf x e = cluster G ωf x \ cluster G ω x := by
  rw [hangingSide,h.head_cut G x η y k j i ω ωf e rest]

theorem SpliceTrace.head_hanging_cap (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i M : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf)
    (hcaps : ∀ l, 1 ≤ l → l ≤ k →
      (cluster G (η l) (y l)).Finite ∧ (cluster G (η l) (y l)).ncard ≤ M) :
    (hangingSide G ωf x e).ncard ≤ k*M := by
  rw [h.head_hanging G x η y k j i ω ωf e rest]
  exact (h.added_finite_cap G x η y k j M ω ωf ((i,e)::rest) hcaps).2

 

theorem finite_near_hanging_mass_le {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (v d : ℕ)
    (hdeg : ∀ a, degree G a ≤ d)
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : unitInterval)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (hm₁ : ∀ a, 0 ≤ m₁ a) (hm₂ : ∀ b, 0 ≤ m₂ b)
    (z₁ : I₁ → V) (z₂ : I₂ → V) (e₁ : I₁ → E) (e₂ : I₂ → E)
    (hfin : ∀ a, (cluster G (out₁ a).1 x).Finite)
    (hp₁ : ∀ a, OpenMarkedPivotal G (out₁ a).1 {z₁ a} x (e₁ a))
    (hp₂ : ∀ b, OpenMarkedPivotal G (out₂ b).1 {z₂ b} x (e₂ b))
    (hcap₁ : ∀ a, (hangingSide G (out₁ a).1 x (e₁ a)).ncard ≤ v)
    (hcap₂ : ∀ b, (hangingSide G (out₂ b).1 x (e₂ b)).ncard ≤ v)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a z, endpointRootMass Q J₂ p out₂ z₂ m₂ (out₁ a).1 z ≤ C) :
    (∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧
      ¬GraphSeparated G (hangingSide G (out₁ a).1 x (e₁ a))
        (hangingSide G (out₂ b).1 x (e₂ b)) then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0) ≤
    ((v+v^2+d*v^3:ℕ):ℝ) * C * ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a := by
  let R : I₁ → I₂ → Prop := fun a b =>
    ¬GraphSeparated G (hangingSide G (out₁ a).1 x (e₁ a)) (hangingSide G (out₂ b).1 x (e₂ b))
  let S := fun a => nearHangingEndpoints G hloc (out₁ a).1 x (z₁ a) (e₁ a) v (hfin a)
  have hS : ∀ a b, (out₁ a).1 = (out₂ b).1 → R a b → z₂ b ∈ S a := by
    intro a b he hn
    have hp := hp₂ b
    have hc := hcap₂ b
    change ¬GraphSeparated G _ _ at hn
    rw [← he] at hp hc hn
    exact mem_nearHangingEndpoints_of_not_separated G hloc (out₁ a).1 x (z₁ a) (z₂ b)
      (e₁ a) (e₂ b) v (hfin a) (hp₁ a) hp hc hn
  have hN : ∀ a, (S a).card ≤ v+v^2+d*v^3 := fun a =>
    nearHangingEndpoints_card_le G hloc (out₁ a).1 x (z₁ a) (e₁ a) v d
      (hfin a) (hcap₁ a) hdeg
  have ht := finite_near_pair_mass_le Q J₁ J₂ p out₁ out₂ m₁ m₂ hm₁ hm₂ z₂ R S hS
    (v+v^2+d*v^3) hN C hC (fun a z _ => hb a z)
  convert ht using 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : (out₁ a).1 = (out₂ b).1 ∧ R a b
  · rw [ite_eq_left h,ite_eq_left h]
  · rw [ite_eq_right h,ite_eq_right h]

end NearHangingMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldRunArrival
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]

noncomputable def oldRunArrival (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) (A : Finset W) : ℝ :=
  ∑ y : Fin k → W, if oldRunVertices k z y 0 ∈ A then oldRunWeight K k z y else 0

theorem oldRunArrival_nonneg (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (k : ℕ) (z : W) (A : Finset W) : 0 ≤ oldRunArrival K k z A := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact oldRunWeight_nonneg K hK k z y
  · exact le_refl 0

theorem oldRunArrival_zero (K : ℕ → W → W → ℝ) (z : W) (A : Finset W) :
    oldRunArrival K 0 z A = if z ∈ A then 1 else 0 := by
  by_cases h : z ∈ A
  · simp [oldRunArrival,oldRunVertices,oldRunWeight,h]
  · simp [oldRunArrival,oldRunVertices,h]

theorem oldRunArrival_succ (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) (A : Finset W) :
    oldRunArrival K (k+1) z A = ∑ a, K (k+1) z a * oldRunArrival K k a A := by
  unfold oldRunArrival
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun y => if oldRunVertices k y.1 y.2 0 ∈ A then
      K (k+1) z y.1 * oldRunWeight K k y.1 y.2 else 0)
    (by
      intro y
      by_cases h : oldRunVertices k (y 0) (Fin.tail y) 0 ∈ A
      · simp [oldRunVertices_succ_of_le k z y 0 (Nat.zero_le k),oldRunConsEquiv,oldRunWeight,h]
      · simp [oldRunVertices_succ_of_le k z y 0 (Nat.zero_le k),oldRunConsEquiv,h]),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum,mul_ite,mul_zero]

 

theorem sum_oldRunArrival_le (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (u : ℝ) (hu : 0 ≤ u) (hcol : ∀ i b, ∑ a, K i a b ≤ u) (k : ℕ) (A : Finset W) :
    (∑ z, oldRunArrival K k z A) ≤ (A.card:ℝ) * u^k := by
  induction k with
  | zero => simp [oldRunArrival_zero]
  | succ k ih =>
    simp only [oldRunArrival_succ]
    rw [Finset.sum_comm]
    calc
      _ = ∑ a, (∑ z, K (k+1) z a) * oldRunArrival K k a A := by
        simp only [Finset.sum_mul]
      _ ≤ ∑ a, u * oldRunArrival K k a A := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hcol _ _) (oldRunArrival_nonneg K hK k a A)
      _ = u * ∑ a, oldRunArrival K k a A := (Finset.mul_sum _ _ _).symm
      _ ≤ u*((A.card:ℝ)*u^k) := mul_le_mul_of_nonneg_left ih hu
      _ = (A.card:ℝ)*u^(k+1) := by ring

 
theorem sum_oldRunArrival_on_le (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (u : ℝ) (hu : 0 ≤ u) (hcol : ∀ i b, ∑ a, K i a b ≤ u)
    (k : ℕ) (A Z : Finset W) :
    (∑ z ∈ Z, oldRunArrival K k z A) ≤ (A.card:ℝ) * u^k := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Z)
    (fun z _ _ => oldRunArrival_nonneg K hK k z A)).trans
  exact sum_oldRunArrival_le K hK u hu hcol k A

 
theorem noSwitch_arrival_le (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (u : ℝ) (hu : 0 ≤ u) (hcol : ∀ i b, ∑ a, K i a b ≤ u)
    (k n : ℕ) (hn : 0 < n) (A Z : Finset W) (hA : A.card ≤ 2*n) :
    (n:ℝ)⁻¹ * ∑ z ∈ Z, oldRunArrival K k z A ≤ 2*u^k := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (n:ℝ)⁻¹ * ((A.card:ℝ)*u^k) :=
      mul_le_mul_of_nonneg_left (sum_oldRunArrival_on_le K hK u hu hcol k A Z)
        (inv_nonneg.mpr hn'.le)
    _ ≤ (n:ℝ)⁻¹ * ((2*(n:ℝ))*u^k) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hA) (pow_nonneg hu _)) (inv_nonneg.mpr hn'.le)
    _ = 2*u^k := by field_simp

end OldRunArrival

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem RootTransport.real (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (m : V → V → ℝ)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (hc : ∀ y, Summable (fun x => m x y)) :
    (∑ i, weight i * ∑' y, m (root i) y) =
      (∑ i, weight i * ∑' x, m x (root i)) := by
  have ht := htr (fun x y => (m x y:ℂ))
    (fun a ha x y => congrArg Complex.ofReal (hi a ha x y))
    (fun x => Complex.summable_ofReal.mpr (hr x))
    (fun y => Complex.summable_ofReal.mpr (hc y))
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_tsum] using ht

 

theorem transported_column_le (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (m : V → V → ℝ) (hm : ∀ x y, 0 ≤ m x y)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (hcol : ∀ y, Summable (fun x => m x y))
    (B : ℝ) (hB : ∀ x, ∑' y, m x y ≤ B) (y : V) :
    (∑' x, m x y) ≤ c*B := by
  have ht := htr.real root weight Γ m hi hr hcol
  have hb : (∑ i, weight i * ∑' x, m x (root i)) ≤ B := by
    rw [← ht]
    calc
      _ ≤ ∑ i, weight i * B := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hB _) (hw i)
      _ = B := by rw [← Finset.sum_mul,hw1,one_mul]
  obtain ⟨i,a,ha,hay⟩ := hcov y
  have he : (∑' x, m x y) = ∑' x, m x (root i) := by
    rw [← hay,← a.tsum_eq (fun x => m x (a (root i)))]
    exact tsum_congr (fun x => hi a ha x (root i))
  have hn : 0 ≤ ∑' x, m x (root i) := tsum_nonneg (fun x => hm x _)
  have hs : weight i * ∑' x, m x (root i) ≤ ∑ j, weight j * ∑' x, m x (root j) :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (tsum_nonneg (fun x => hm x (root j))))
      (Finset.mem_univ i)
  rw [he]
  calc
    _ ≤ (c*weight i) * ∑' x, m x (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) hn
    _ = c * (weight i * ∑' x, m x (root i)) := by ring
    _ ≤ c * (∑ j, weight j * ∑' x, m x (root j)) := mul_le_mul_of_nonneg_left hs hc
    _ ≤ c*B := mul_le_mul_of_nonneg_left hb hc

 

theorem finite_trajectory_hit_le (m : V → V → ℝ) (hm : ∀ x y, 0 ≤ m x y)
    (hcol : ∀ y, Summable (fun x => m x y)) (B : ℝ)
    (hb : ∀ y, ∑' x, m x y ≤ B) (h : V → ℝ) (A Z : Finset V)
    (hh : ∀ x, h x ≤ ∑ y ∈ A, m x y) :
    (∑ x ∈ Z, h x) ≤ (A.card:ℝ)*B := by
  calc
    _ ≤ ∑ x ∈ Z, ∑ y ∈ A, m x y := Finset.sum_le_sum fun x _ => hh x
    _ = ∑ y ∈ A, ∑ x ∈ Z, m x y := Finset.sum_comm
    _ ≤ ∑ y ∈ A, ∑' x, m x y := Finset.sum_le_sum fun y _ =>
      (hcol y).sum_le_tsum Z (fun x _ => hm x y)
    _ ≤ ∑ _y ∈ A, B := Finset.sum_le_sum fun y _ => hb y
    _ = (A.card:ℝ)*B := by simp

end TrajectoryTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NonnegativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem mem_reachBall_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (ha : IsAut G a b) (x y : V) (n : ℕ) :
    a y ∈ reachBall G (a x) n ↔ y ∈ reachBall G x n := by
  constructor
  · intro h
    simpa only [Equiv.symm_apply_apply] using mem_reachBall_aut G (isAut_symm G ha) h
  · exact mem_reachBall_aut G ha

 
def transportCut (G : BondGraph V E) (n : ℕ) (x y : V) : Prop :=
  y ∈ reachBall G x n ∧ x ∈ reachBall G y n

theorem transportCut_mono (G : BondGraph V E) {n m : ℕ} (h : n ≤ m)
    {x y : V} (hxy : transportCut G n x y) : transportCut G m x y :=
  ⟨reachBall_mono G x h hxy.1, reachBall_mono G y h hxy.2⟩

theorem transportCut_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (ha : IsAut G a b) (n : ℕ) (x y : V) :
    transportCut G n (a x) (a y) ↔ transportCut G n x y := by
  simp only [transportCut,mem_reachBall_aut_iff G ha]

theorem exists_transportCut (G : BondGraph V E) (hconn : Connected G)
    (y : V) (Z : Finset V) : ∃ n, ∀ x ∈ Z, transportCut G n x y := by
  induction Z using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x Z _ ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨r,hr⟩ := exists_mem_reachBall (hconn x y)
    obtain ⟨s,hs⟩ := exists_mem_reachBall (hconn y x)
    refine ⟨max n (max r s), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨reachBall_mono G z (le_trans (le_max_left r s) (le_max_right n _)) hr,
        reachBall_mono G y (le_trans (le_max_right r s) (le_max_right n _)) hs⟩
    · exact transportCut_mono G (le_max_left n _) (hn z hz)

 

theorem transported_column_of_row_bound (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (m : V → V → ℝ) (hm : ∀ x y, 0 ≤ m x y)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (B : ℝ) (hB : ∀ x, ∑' y, m x y ≤ B) :
    ∀ y, Summable (fun x => m x y) ∧ (∑' x, m x y) ≤ c*B := by
  let cut (n : ℕ) (x y : V) : ℝ := if transportCut G n x y then m x y else 0
  have hn (n : ℕ) (x y : V) : 0 ≤ cut n x y := by
    dsimp [cut]; split_ifs; exact hm x y; exact le_refl 0
  have hcRow (n : ℕ) (x : V) : Summable (cut n x) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x n).toFinset)
    intro y hy
    simp only [Set.Finite.mem_toFinset] at hy
    exact ite_eq_right (fun h => hy h.1)
  have hcCol (n : ℕ) (y : V) : Summable (fun x => cut n x y) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y n).toFinset)
    intro x hx
    simp only [Set.Finite.mem_toFinset] at hx
    exact ite_eq_right (fun h => hx h.2)
  have hcInv (n : ℕ) : ∀ a ∈ Γ, ∀ x y, cut n (a x) (a y) = cut n x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    simp only [cut,transportCut_aut G hb,hi a ha]
  have hcBound (n : ℕ) (x : V) : (∑' y, cut n x y) ≤ B := by
    apply le_trans ((hcRow n x).tsum_le_tsum (fun y => ?_) (hr x)) (hB x)
    dsimp [cut]; split_ifs; exact le_refl _; exact hm x y
  have hbound (y : V) (Z : Finset V) : (∑ x ∈ Z, m x y) ≤ c*B := by
    obtain ⟨n,hnZ⟩ := exists_transportCut G hconn y Z
    calc
      _ = ∑ x ∈ Z, cut n x y := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (ite_eq_left (hnZ x hx)).symm
      _ ≤ ∑' x, cut n x y := (hcCol n y).sum_le_tsum Z (fun x _ => hn n x y)
      _ ≤ c*B := transported_column_le root weight Γ htr hcov hw hw1 c hc hmin
        (cut n) (hn n) (hcInv n) (hcRow n) (hcCol n) B (hcBound n) y
  intro y
  exact ⟨summable_of_sum_le (fun x => hm x y) (hbound y),
    Real.tsum_le_of_sum_le (fun x => hm x y) (hbound y)⟩

 

theorem trajectory_hit_tsum_le (m : V → V → ℝ) (hm : ∀ x y, 0 ≤ m x y)
    (hcol : ∀ y, Summable (fun x => m x y)) (B : ℝ)
    (hb : ∀ y, ∑' x, m x y ≤ B) (h : V → ℝ) (hh0 : ∀ x, 0 ≤ h x)
    (A : Finset V) (hh : ∀ x, h x ≤ ∑ y ∈ A, m x y) :
    Summable h ∧ (∑' x, h x) ≤ (A.card:ℝ)*B := by
  have hs := fun Z => finite_trajectory_hit_le m hm hcol B hb h A Z hh
  exact ⟨summable_of_sum_le hh0 hs, Real.tsum_le_of_sum_le hh0 hs⟩

end NonnegativeTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteTrajectoryMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]

theorem finiteFamilyIntegral_mul_const (Q : Finset E) (J : Finset ℕ) (p c : ℝ)
    (f : (ℕ → Set E) → ℝ) :
    finiteFamilyIntegral Q J p (fun η => f η * c) = finiteFamilyIntegral Q J p f * c := by
  simp only [finiteFamilyIntegral,Finset.sum_mul,mul_assoc]

omit [Fintype W] in
theorem oldRunWeight_factor_ne_zero (q : Set E → W → W → ℝ) (k : ℕ)
    (η : ℕ → Set E) (z : W) (y : Fin k → W)
    (hy : oldRunWeight (fun i => q (η i)) k z y ≠ 0) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    q (η i) (oldRunVertices k z y i) (oldRunVertices k z y (i-1)) ≠ 0 := by
  rw [← oldPathWeight_oldRunVertices] at hy
  exact (Finset.prod_ne_zero_iff.mp hy) ⟨i,Finset.mem_Icc.mpr ⟨hi,hik⟩⟩ (Finset.mem_univ _)

 

noncomputable def finiteTrajectoryMass (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : ℝ) (k : ℕ) (q : Set E → W → W → ℝ) (z : W) (a : V) : ℝ :=
  finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    ∑ y : Fin k → W, if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z y) k then
      oldRunWeight (fun i => q (η i)) k z y else 0)

noncomputable def finiteTrajectoryHit (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : ℝ) (k : ℕ) (q : Set E → W → W → ℝ) (z : W) (A : Finset V) : ℝ :=
  finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    ∑ y : Fin k → W, if ((A:Set V) ∩ trajectoryUnion G η (e ∘ oldRunVertices k z y) k).Nonempty then
      oldRunWeight (fun i => q (η i)) k z y else 0)

theorem finiteTrajectoryMass_nonneg (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : unitInterval) (k : ℕ) (q : Set E → W → W → ℝ)
    (hq : ∀ ω a b, 0 ≤ q ω a b) (z : W) (a : V) :
    0 ≤ finiteTrajectoryMass G e Q p k q z a := by
  apply finiteFamilyIntegral_nonneg
  intro η
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact oldRunWeight_nonneg _ (fun _ => hq _) k z y
  · exact le_refl 0

theorem finiteTrajectoryHit_nonneg (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : unitInterval) (k : ℕ) (q : Set E → W → W → ℝ)
    (hq : ∀ ω a b, 0 ≤ q ω a b) (z : W) (A : Finset V) :
    0 ≤ finiteTrajectoryHit G e Q p k q z A := by
  apply finiteFamilyIntegral_nonneg
  intro η
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact oldRunWeight_nonneg _ (fun _ => hq _) k z y
  · exact le_refl 0

theorem finiteTrajectoryHit_le_sum (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : unitInterval) (k : ℕ) (q : Set E → W → W → ℝ)
    (hq : ∀ ω a b, 0 ≤ q ω a b) (z : W) (A : Finset V) :
    finiteTrajectoryHit G e Q p k q z A ≤ ∑ a ∈ A, finiteTrajectoryMass G e Q p k q z a := by
  unfold finiteTrajectoryHit finiteTrajectoryMass
  rw [← finiteFamilyIntegral_sum]
  apply finiteFamilyIntegral_mono
  intro η
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y _
  have hn := oldRunWeight_nonneg (fun i => q (η i)) (fun _ => hq _) k z y
  by_cases h : ((A:Set V) ∩ trajectoryUnion G η (e ∘ oldRunVertices k z y) k).Nonempty
  · rw [ite_eq_left h]
    obtain ⟨a,ha,hat⟩ := h
    have hs := Finset.single_le_sum (s := A)
      (f := fun a => if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z y) k then
        oldRunWeight (fun i => q (η i)) k z y else 0)
      (fun a _ => by split_ifs; exact hn; exact le_refl 0) ha
    simpa only [ite_eq_left hat] using hs
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg fun a _ => by split_ifs; exact hn; exact le_refl 0

 

theorem finiteTrajectoryMass_finite_sum_le (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : unitInterval) (k M : ℕ) (q : Set E → W → W → ℝ)
    (hq : ∀ ω a b, 0 ≤ q ω a b)
    (hcap : ∀ ω a b, q ω a b ≠ 0 →
      (cluster G ω (e a)).Finite ∧ (cluster G ω (e a)).ncard ≤ M)
    (u : ℝ) (hu : 0 ≤ u) (hrow : ∀ a, ∑ b, finiteOldKernel Q p q a b ≤ u)
    (z : W) (A : Finset V) :
    (∑ a ∈ A, finiteTrajectoryMass G e Q p k q z a) ≤ (k*M:ℕ)*u^k := by
  unfold finiteTrajectoryMass
  rw [← finiteFamilyIntegral_sum]
  have hb : ∀ η, (∑ a ∈ A, ∑ y : Fin k → W,
      if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z y) k then
        oldRunWeight (fun i => q (η i)) k z y else 0) ≤
      (∑ y : Fin k → W, oldRunWeight (fun i => q (η i)) k z y) * (k*M:ℕ) := by
    intro η
    rw [Finset.sum_comm,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : oldRunWeight (fun i => q (η i)) k z y = 0
    · simp [hy]
    obtain ⟨hf,hc⟩ := trajectoryUnion_finite_cap G η (e ∘ oldRunVertices k z y) k M
      (fun i hi hik => hcap _ _ _ (oldRunWeight_factor_ne_zero q k η z y hy i hi hik))
    have hsub : A.filter (fun a => a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z y) k) ⊆ hf.toFinset := by
      intro a ha
      exact hf.mem_toFinset.mpr (Finset.mem_filter.mp ha).2
    have hcard : ((A.filter (fun a => a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z y) k)).card:ℝ) ≤ (k*M:ℕ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (by simpa only [← Set.ncard_eq_toFinset_card _ hf] using hc)
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcard
      (oldRunWeight_nonneg _ (fun _ => hq _) k z y)
  calc
    _ ≤ finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
        (∑ y : Fin k → W, oldRunWeight (fun i => q (η i)) k z y) * (k*M:ℕ)) :=
      finiteFamilyIntegral_mono Q (Finset.Icc 1 k) p _ _ hb
    _ = finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
        ∑ y : Fin k → W, oldRunWeight (fun i => q (η i)) k z y) * (k*M:ℕ) :=
      finiteFamilyIntegral_mul_const Q (Finset.Icc 1 k) p _ _
    _ ≤ u^k * (k*M:ℕ) := mul_le_mul_of_nonneg_right
      (independent_oldRun_success_le Q p k q hq u hu hrow z) (Nat.cast_nonneg _)
    _ = (k*M:ℕ)*u^k := mul_comm _ _

 

theorem finiteTrajectoryMass_row_bound (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : unitInterval) (k M : ℕ) (q : Set E → W → W → ℝ)
    (hq : ∀ ω a b, 0 ≤ q ω a b)
    (hcap : ∀ ω a b, q ω a b ≠ 0 →
      (cluster G ω (e a)).Finite ∧ (cluster G ω (e a)).ncard ≤ M)
    (u : ℝ) (hu : 0 ≤ u) (hrow : ∀ a, ∑ b, finiteOldKernel Q p q a b ≤ u) (z : W) :
    Summable (finiteTrajectoryMass G e Q p k q z) ∧
      (∑' a, finiteTrajectoryMass G e Q p k q z a) ≤ (k*M:ℕ)*u^k := by
  have hn := finiteTrajectoryMass_nonneg G e Q p k q hq z
  have hb := finiteTrajectoryMass_finite_sum_le G e Q p k M q hq hcap u hu hrow z
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

end FiniteTrajectoryMass

end Percolation

end OAI
