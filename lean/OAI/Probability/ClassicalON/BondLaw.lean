import OAI.Probability.ClassicalON.BondSubspace

namespace OAI

universe uE uV uX

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def bondProduct (t : E → ℝ) (η : E → Bool) : ℝ := ∏ e,if η e then t e else 1

def bondWeight (left right : E → V) (t : E → ℝ) (η : E → Bool) : ℝ :=
  clusterWeight left right η*bondProduct t η

theorem bondProduct_nonneg {t : E → ℝ} (ht : ∀ e,0 ≤ t e) (η : E → Bool) :
    0 ≤ bondProduct t η := Finset.prod_nonneg fun e _ => by split <;> [exact ht e; exact zero_le_one]

omit [Fintype V] in
theorem bondWeight_nonneg (left right : E → V) {t : E → ℝ} (ht : ∀ e,0 ≤ t e)
    (η : E → Bool) : 0 ≤ bondWeight left right t η :=
  mul_nonneg (clusterWeight_pos _ _ _).le (bondProduct_nonneg ht η)

theorem bondProduct_holley {t s : E → ℝ} (ht : ∀ e,0 ≤ t e) (hts : t ≤ s)
    (η ξ : E → Bool) :
    bondProduct t η*bondProduct s ξ ≤ bondProduct t (η⊓ξ)*bondProduct s (η⊔ξ) := by
  unfold bondProduct
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro e _
    exact mul_nonneg (by split <;> [exact ht e; exact zero_le_one]) (by split <;> [exact le_trans (ht e) (hts e); exact zero_le_one])
  · intro e _
    simp only [Pi.inf_apply,Pi.sup_apply]
    have hh (a b : Bool) : (if a then t e else 1)*(if b then s e else 1) ≤
        (if a⊓b then t e else 1)*(if a⊔b then s e else 1) := by
      cases a <;> cases b <;> simp [hts e]
    exact hh _ _

theorem bondWeight_holley (left right : E → V) {t s : E → ℝ}
    (ht : ∀ e,0 ≤ t e) (hts : t ≤ s) (η ξ : E → Bool) :
    bondWeight left right t η*bondWeight left right s ξ ≤
      bondWeight left right t (η⊓ξ)*bondWeight left right s (η⊔ξ) := by
  unfold bondWeight
  rw [mul_mul_mul_comm,mul_mul_mul_comm (clusterWeight left right (η⊓ξ))]
  exact mul_le_mul (clusterWeight_supermodular _ _ η ξ) (bondProduct_holley ht hts η ξ)
    (mul_nonneg (bondProduct_nonneg ht η) (bondProduct_nonneg (fun e => le_trans (ht e) (hts e)) ξ))
    (mul_nonneg (clusterWeight_pos _ _ _).le (clusterWeight_pos _ _ _).le)

def finiteMean {X : Type uX} [Fintype X] (w f : X → ℝ) : ℝ := (∑ x,w x*f x)/(∑ x,w x)

omit [Fintype V] in
theorem bondWeight_sum_pos (left right : E → V) {t : E → ℝ} (ht : ∀ e,0 ≤ t e) :
    0 < ∑ η,bondWeight left right t η := by
  apply Finset.sum_pos' (fun η _ => bondWeight_nonneg left right ht η)
  refine ⟨fun _ => false,Finset.mem_univ _,?_⟩
  simpa [bondWeight,bondProduct] using clusterWeight_pos left right (fun _ => false)

section Finite
variable {X : Type uX} [Fintype X]

theorem finiteMean_nonneg {w f : X → ℝ} (hw : ∀ x,0 ≤ w x) (hf : ∀ x,0 ≤ f x) :
    0 ≤ finiteMean w f :=
  div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)) (Finset.sum_nonneg fun x _ => hw x)

theorem finiteMean_le {w f : X → ℝ} {a : ℝ} (hw : ∀ x,0 ≤ w x)
    (hp : 0 < ∑ x,w x) (hf : ∀ x,f x ≤ a) : finiteMean w f ≤ a := by
  apply (div_le_iff₀ hp).2
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hf x) (hw x)

theorem finiteMean_mono {w f g : X → ℝ} (hw : ∀ x,0 ≤ w x) (hf : f ≤ g) :
    finiteMean w f ≤ finiteMean w g := by
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg fun x _ => hw x)
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x) (hw x)

variable [DistribLattice X]

theorem finiteMean_associated {w f g : X → ℝ} (hw : ∀ x,0 ≤ w x) (hp : 0 < ∑ x,w x)
    (hLS : ∀ x y,w x*w y ≤ w (x⊓y)*w (x⊔y))
    (hf : ∀ x,0 ≤ f x) (hg : ∀ x,0 ≤ g x) (hfm : Monotone f) (hgm : Monotone g) :
    finiteMean w f*finiteMean w g ≤ finiteMean w (fun x => f x*g x) := by
  have hh := fkg f g w hw hf hg hfm hgm hLS
  unfold finiteMean
  rw [div_mul_div_comm,div_le_div_iff₀ (mul_pos hp hp) hp]
  nlinarith

theorem finiteMean_holley {w v f : X → ℝ} (hw : ∀ x,0 ≤ w x) (hv : ∀ x,0 ≤ v x)
    (hp : 0 < ∑ x,w x) (hvp : 0 < ∑ x,v x) (hf : ∀ x,0 ≤ f x) (hfm : Monotone f)
    (hH : ∀ x y,w x*v y ≤ w (x⊓y)*v (x⊔y)) : finiteMean w f ≤ finiteMean v f := by
  have hh := four_functions_theorem_univ v (fun x => w x*f x) w (fun x => v x*f x)
    hv (fun x => mul_nonneg (hw x) (hf x)) hw (fun x => mul_nonneg (hv x) (hf x))
    (fun x y => show v x*(w y*f y) ≤ w (x⊓y)*(v (x⊔y)*f (x⊔y)) from by
      have h := mul_le_mul (hH y x) (hfm (show y ≤ x⊔y from le_sup_right))
        (hf y) (mul_nonneg (hw (y⊓x)) (hv (y⊔x)))
      simpa only [inf_comm,sup_comm,mul_assoc,mul_left_comm] using h)
  unfold finiteMean
  apply (div_le_div_iff₀ hp hvp).2
  nlinarith
end Finite

theorem bondMean_mono (left right : E → V) {t s : E → ℝ}
    (ht : ∀ e,0 ≤ t e) (hts : t ≤ s) {f : (E → Bool) → ℝ}
    (hf : ∀ η,0 ≤ f η) (hfm : Monotone f) :
    finiteMean (bondWeight left right t) f ≤ finiteMean (bondWeight left right s) f :=
  finiteMean_holley (bondWeight_nonneg left right ht)
    (bondWeight_nonneg left right (fun e => le_trans (ht e) (hts e)))
    (bondWeight_sum_pos left right ht) (bondWeight_sum_pos left right (fun e => le_trans (ht e) (hts e)))
    hf hfm (bondWeight_holley left right ht hts)

theorem bondMean_associated (left right : E → V) {t : E → ℝ} (ht : ∀ e,0 ≤ t e)
    {f g : (E → Bool) → ℝ} (hf : ∀ η,0 ≤ f η) (hg : ∀ η,0 ≤ g η)
    (hfm : Monotone f) (hgm : Monotone g) :
    finiteMean (bondWeight left right t) f*finiteMean (bondWeight left right t) g ≤
      finiteMean (bondWeight left right t) (fun η => f η*g η) :=
  finiteMean_associated (bondWeight_nonneg left right ht) (bondWeight_sum_pos left right ht)
    (bondWeight_holley left right ht le_rfl) hf hg hfm hgm

end ClassicalON

end

end OAI
