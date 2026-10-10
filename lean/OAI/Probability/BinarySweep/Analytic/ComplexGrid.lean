import Mathlib
import OAI.Probability.BinarySweep.Mixing.BinaryLineDisk
import OAI.Probability.BinarySweep.FiniteLaws.IndependentOperator

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {b : ℕ} (bits : Fin b → ℕ)

def gridStageHom (j : Fin b) :
    (GridOutside bits j → Equiv.Perm (Slot (bits j))) →* Equiv.Perm (GridSlot bits) where
  toFun f := (Equiv.piSplitAt j (fun i => Slot (bits i))).symm.permCongr
    (Equiv.prodCongrLeft f)
  map_one' := by
    have h : Equiv.prodCongrLeft (1 : GridOutside bits j → Equiv.Perm (Slot (bits j)))=1 := by
      ext x <;> rfl
    change (Equiv.piSplitAt j (fun i => Slot (bits i))).symm.permCongrHom
      (Equiv.prodCongrLeft 1)=1
    rw [h,map_one]
  map_mul' f g := by
    ext x
    simp [Equiv.permCongr_apply,Equiv.prodCongrLeft_apply]

lemma gridStageHom_layer (g : GridChoices bits) (j : Fin b) :
    gridStageHom bits j (g j)=gridLayer bits g j := rfl

def complexGridWeight (z : ℂ) (g : GridChoices bits) : ℂ :=
  ∏j, ∏y, complexLineLaw (bits j) z (g j y)

lemma complexGridWeight_real (z : ℝ) (g : GridChoices bits) :
    complexGridWeight bits (z:ℂ) g=(gridWeight bits z g:ℂ) := by
  simp [complexGridWeight,gridWeight,complexLineLaw_real]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) V)

def complexGridAverage (z : ℂ) : V →L[ℂ] V :=
  ∑g : GridChoices bits, complexGridWeight bits z g • continuousRep ρ (gridSweep bits g)

lemma complexGridAverage_product (z : ℂ) :
    complexGridAverage bits ρ z=(List.ofFn (fun j =>
      complexAverage (ρ.comp (gridStageHom bits j))
        (fun f => ∏y,complexLineLaw (bits j) z (f y)))).reverse.prod := by
  unfold complexGridAverage complexGridWeight gridSweep
  simp_rw [map_list_prod,List.map_reverse,List.map_ofFn,Function.comp_def]
  change (∑g : GridChoices bits, (∏j, ∏y, complexLineLaw (bits j) z (g j y)) •
    (List.ofFn (fun j => continuousRep ρ (gridStageHom bits j (g j)))).reverse.prod)=_
  rw [independent_average_product (X := fun j => GridOutside bits j → Equiv.Perm (Slot (bits j)))
    (fun j f => ∏y,complexLineLaw (bits j) z (f y))
    (fun j f => continuousRep ρ (gridStageHom bits j f))]
  congr 3
  funext j
  rw [complexAverage_sum]
  rfl

lemma complexGridAverage_differentiable : Differentiable ℂ (complexGridAverage bits ρ) := by
  unfold complexGridAverage
  apply Differentiable.fun_sum
  intro g _
  apply Differentiable.fun_smul
  · unfold complexGridWeight
    apply Differentiable.fun_finsetProd
    intro j _
    apply Differentiable.fun_finsetProd
    intro y _
    unfold complexLineLaw
    fun_prop
  · fun_prop

lemma complexGridAverage_norm_le_one [Nontrivial V] (z : ℂ)
    (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hline : ∀j : Fin b,
      ∀σ : Representation ℂ (Equiv.Perm (Slot (bits j))) V,
      (∀g v, ‖σ g v‖=‖v‖) → ‖complexAverage σ (complexLineLaw (bits j) z)‖ ≤ 1) :
    ‖complexGridAverage bits ρ z‖ ≤ 1 := by
  rw [complexGridAverage_product]
  apply reverse_product_norm_le_one
  intro j
  exact pi_comp_average_norm_le_one (I := GridOutside bits j)
    (G := Equiv.Perm (Slot (bits j))) (H := Equiv.Perm (GridSlot bits)) (V := V)
    ρ (gridStageHom bits j)
    (complexLineLaw (bits j) z) hρ (hline j)

theorem complex_grid_disk (m : ℕ) : ∃ R : ℝ, 1 < R ∧
    ∀ (b : ℕ) (bits : Fin b → ℕ), (∀ j, bits j ≤ m) →
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] [Nontrivial V],
    ∀ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) V,
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖ ≤ R →
        ‖complexGridAverage bits ρ z‖ ≤ 1 := by
  obtain ⟨R,hR,h⟩ := binary_lines_disk m
  refine ⟨R,hR,?_⟩
  intro b bits hm V _ _ _ _ ρ hρ z hz
  apply complexGridAverage_norm_le_one bits ρ z hρ
  intro j σ hσ
  exact h (bits j) (hm j) V σ hσ z hz

end BinaryCoordinateSweeps

end

end OAI
