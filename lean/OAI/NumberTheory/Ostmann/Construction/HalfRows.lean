import OAI.NumberTheory.Ostmann.Construction.HalfTransform

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def halfModuli (p : ℕ) (u : List SmallSlot) : Fin (u.length+1)→ℕ :=
  Fin.cons p (fun i => u[i].value)

def halfGiant (u : List SmallSlot) (i : Fin (u.length+1)) : Bool := decide (i.val=0)

theorem halfModuli_product (p : ℕ) (u : List SmallSlot) :
    (∏i,halfModuli p u i)=halfProduct p u := by
  rw [Fin.prod_univ_succ]
  simp only [halfModuli,Fin.cons_zero,Fin.cons_succ,halfProduct]
  congr 1
  rw [←List.prod_ofFn]
  exact congrArg List.prod (List.ofFn_getElem_eq_map u SmallSlot.value)

def coordinateRow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : Decomposition) (p : ι→ℕ) (D : ℕ) (giant : ι→Bool) (t : ZMod (∏i,p i)) : ℂ :=
  ∏i,(if giant i then giantResidueTransform d (p i) else residueTransform d (p i))
    (ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i)) t*
      ((D*otherProduct p i:ℕ):ZMod (p i))⁻¹)

theorem coordinateRow_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : Decomposition) (p : ι→ℕ) (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (D : ℕ) (hD : ∀i,D.Coprime (p i)) (giant : ι→Bool) (t : ZMod (∏i,p i)) :
    coordinateRow d p D giant t=actualExtractedRow d p hcop D hD giant t := by
  rw [actualExtractedRow_apply]
  simp only [coordinateRow,ZMod.prodEquivPi_apply,Nat.cast_mul]

def halfRow (d : Decomposition) (D p : ℕ) (u : List SmallSlot)
    (t : ZMod (halfProduct p u)) : ℂ :=
  coordinateRow d (halfModuli p u) D (halfGiant u)
    (ZMod.ringEquivCongr (halfModuli_product p u).symm t)

theorem ringEquivCongr_modFraction {m n : ℕ} (h : m=n) (v : ℤ) (H : ℕ) :
    ZMod.ringEquivCongr h (modFraction m v H)=modFraction n v H := by
  subst n
  simp only [ZMod.ringEquivCongr_refl_apply]

theorem halfRow_sq_norm_le (d : Decomposition) (D p : ℕ) (u : List SmallSlot)
    [NeZero (halfProduct p u)]
    (hp : ∀i,Nat.Prime (halfModuli p u i))
    (hc : Pairwise (fun i j => (halfModuli p u i).Coprime (halfModuli p u j)))
    (hD : ∀i,D.Coprime (halfModuli p u i)) :
    (∑t:ZMod (halfProduct p u),‖halfRow d D p u t‖^2)≤(halfProduct p u:ℝ) := by
  let : ∀i,NeZero (halfModuli p u i) := fun i => ⟨(hp i).ne_zero⟩
  let : NeZero (∏i,halfModuli p u i) := ⟨by rw [halfModuli_product]; exact NeZero.ne _⟩
  unfold halfRow
  have he := (ZMod.ringEquivCongr (halfModuli_product p u).symm).toEquiv.sum_comp
    (fun t => ‖coordinateRow d (halfModuli p u) D (halfGiant u) t‖^2)
  calc
    _ = ∑t:ZMod (∏i,halfModuli p u i),‖coordinateRow d (halfModuli p u) D (halfGiant u) t‖^2 := he
    _ ≤ _ := by
      simp_rw [coordinateRow_eq d _ hc D hD]
      simpa only [halfModuli_product] using
        actualExtractedRow_sq_norm_le d (halfModuli p u) hp hc D hD (halfGiant u)

theorem halfTransform_as_product (g giant : (p : ℕ)→ZMod p→ℂ) (D p : ℕ)
    (u : List SmallSlot) (v : ℤ) :
    halfTransform g giant D v p u =
      ∏i,(if halfGiant u i then giant (halfModuli p u i) else g (halfModuli p u i))
        (modFraction (halfModuli p u i) v (D*(halfProduct p u/halfModuli p u i))) := by
  rw [Fin.prod_univ_succ]
  simp only [halfGiant,halfModuli,halfTransform]
  simp only [Fin.cons_zero,Fin.cons_succ,Fin.val_zero,Fin.val_succ]
  congr 1
  rw [←List.prod_ofFn]
  exact (congrArg List.prod (List.ofFn_getElem_eq_map u
    (fun q => g q.value (modFraction q.value v (D*(halfProduct p u/q.value)))))).symm

theorem halfRow_modFraction (d : Decomposition) (D p H : ℕ) (u : List SmallSlot)
    (v : ℤ) (hp : ∀i,0<halfModuli p u i)
    (hc : Pairwise (fun i j => (halfModuli p u i).Coprime (halfModuli p u j)))
    (hD : ∀i,D.Coprime (halfModuli p u i)) (hH : H.Coprime (halfProduct p u)) :
    halfRow d D p u (modFraction (halfProduct p u) v H) =
      halfTransform (residueTransform d) (giantResidueTransform d) (D*H) v p u := by
  unfold halfRow
  rw [ringEquivCongr_modFraction,coordinateRow_eq d _ hc D hD,
    actualExtractedRow_modFraction d _ hp hc D H hD (by simpa only [halfModuli_product] using hH),
    halfTransform_as_product]
  apply Finset.prod_congr rfl
  intro i hi
  apply congrArg
  rw [halfModuli_product,mul_div_factor _ _ H (hp i) (by
    rw [←halfModuli_product]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i))]
  unfold modFraction
  congr 2
  ring_nf

end Ostmann.Construction

end

end OAI
