import OAI.NumberTheory.Ostmann.Construction.DiagonalRegroupingActualMatching
import OAI.NumberTheory.Ostmann.Construction.FavorableGiant
import OAI.NumberTheory.Ostmann.Construction.HalfTransform
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationPriors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem halfTransform_eq_of_value_perm (g giant : (p:ℕ)→ZMod p→ℂ)
    (D : ℕ) (v : ℤ) (q : ℕ) (xs ys : List SmallSlot)
    (hperm : (xs.map SmallSlot.value).Perm (ys.map SmallSlot.value)) :
    halfTransform g giant D v q xs=halfTransform g giant D v q ys := by
  have hH : halfProduct q xs=halfProduct q ys := congrArg (fun n => q*n) hperm.prod_eq
  unfold halfTransform
  rw [hH]
  congr 1
  simpa only [List.map_map,Function.comp_def] using
    (hperm.map (fun p : ℕ => g p (modFraction p v (D*(halfProduct q ys/p))))).prod_eq

def diagonalSmallMultiplier (d : Decomposition) (D : ℕ) (v : ℤ)
    (q : ℕ) (xs : List SmallSlot) : ℝ :=
  (xs.map (fun z => ‖residueTransform d z.value
    (modFraction z.value v (D*(halfProduct q xs/z.value)))‖^2)).prod

lemma diagonalSmallMultiplier_nonneg (d : Decomposition) (D : ℕ) (v : ℤ)
    (q : ℕ) (xs : List SmallSlot) : 0≤diagonalSmallMultiplier d D v q xs := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
  exact sq_nonneg _

lemma complex_list_prod_norm_sq (xs : List ℂ) :
    ‖xs.prod‖^2=(xs.map (fun z => ‖z‖^2)).prod := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.prod_cons,List.map_cons,norm_mul,mul_pow,ih]

theorem halfTransform_norm_sq_le_smallMultiplier (d : Decomposition) (P : Finset ℕ)
    (D : ℕ) (v : ℤ) (q : ℕ) (xs : List SmallSlot) :
    ‖halfTransform (residueTransform d) (favorableGiantResidueTransform d P) D v q xs‖^2≤
      diagonalSmallMultiplier d D v q xs := by
  have hg := favorableGiantResidueTransform_norm_le d P q
    (modFraction q v (D*(halfProduct q xs/q)))
  have hg2 : ‖favorableGiantResidueTransform d P q
      (modFraction q v (D*(halfProduct q xs/q)))‖^2≤1 := by
    nlinarith [norm_nonneg (favorableGiantResidueTransform d P q
      (modFraction q v (D*(halfProduct q xs/q))))]
  unfold halfTransform
  rw [norm_mul,mul_pow,complex_list_prod_norm_sq]
  simp only [List.map_map,Function.comp_def]
  change _ * diagonalSmallMultiplier d D v q xs≤diagonalSmallMultiplier d D v q xs
  exact mul_le_of_le_one_left (diagonalSmallMultiplier_nonneg d D v q xs) hg2

theorem remaining_giant_eq_of_product_eq_of_mass
    (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x y : RemainingSample sources T giant)
    (hx : (remainingPrior sources T giant).mass x≠0)
    (hy : (remainingPrior sources T giant).mass y≠0)
    (hsep : ∀i:Fin T.length,giant.DisjointMass (sources T[i].origin))
    (he : remainingProduct sources T giant x=remainingProduct sources T giant y) :
    x.1.val=y.1.val := by
  change giant.law.mass x.1*(assignmentPrior sources T).mass x.2≠0 at hx
  change giant.law.mass y.1*(assignmentPrior sources T).mass y.2≠0 at hy
  have hp := remainingValues_perm_of_product_eq sources T giant x y he
  have hxmem : x.1.val∈remainingValues sources T giant y := hp.mem_iff.mp List.mem_cons_self
  rcases List.mem_cons.mp hxmem with hsame | hsmall
  · exact hsame
  · obtain ⟨a,ha,hea⟩ := List.mem_map.mp hsmall
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact (hsep i x.1 (y.2 i) (mul_ne_zero_iff.mp hx).1
      (assignmentPrior_component_mass_ne_zero sources T y.2 (mul_ne_zero_iff.mp hy).2 i)
      hea.symm).elim

theorem remaining_halfTransform_eq_of_mass_product
    (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x y : RemainingSample sources T giant)
    (hx : (remainingPrior sources T giant).mass x≠0)
    (hy : (remainingPrior sources T giant).mass y≠0)
    (hsep : ∀i:Fin T.length,giant.DisjointMass (sources T[i].origin))
    (he : remainingProduct sources T giant x=remainingProduct sources T giant y)
    (g gt : (p:ℕ)→ZMod p→ℂ) (D : ℕ) (v : ℤ) :
    halfTransform g gt D v x.1.val (assignedSlots sources T x.2)=
      halfTransform g gt D v y.1.val (assignedSlots sources T y.2) := by
  have hg := remaining_giant_eq_of_product_eq_of_mass sources T giant x y hx hy hsep he
  have hp := remainingValues_perm_of_product_eq sources T giant x y he
  change (x.1.val::_).Perm (y.1.val::_) at hp
  rw [hg] at hp ⊢
  exact halfTransform_eq_of_value_perm g gt D v y.1.val _ _ (List.Perm.cons_inv hp)

end Ostmann.Construction

end

end OAI
