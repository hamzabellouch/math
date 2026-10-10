import OAI.NumberTheory.Ostmann.Construction.TransformExtraction

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def halfProduct (p : ℕ) (u : List SmallSlot) : ℕ := p*(u.map SmallSlot.value).prod

def halfTransform (g giant : (p : ℕ)→ZMod p→ℂ) (D : ℕ) (v : ℤ)
    (p : ℕ) (u : List SmallSlot) : ℂ :=
  giant p (modFraction p v (D*(halfProduct p u/p))) *
    (u.map fun q => g q.value (modFraction q.value v (D*(halfProduct p u/q.value)))).prod

theorem mul_div_factor (n A B : ℕ) (hn : 0<n) (hdiv : n∣A) :
    A*B/n=(A/n)*B := by
  obtain ⟨R,rfl⟩ := hdiv
  simp [Nat.mul_assoc,hn.ne']

theorem halfProduct_dvd_giant (p : ℕ) (u : List SmallSlot) : p∣halfProduct p u :=
  dvd_mul_right _ _

theorem halfProduct_dvd_small (p : ℕ) (u : List SmallSlot) (q : SmallSlot)
    (hq : q∈u) : q.value∣halfProduct p u := by
  exact dvd_mul_of_dvd_right (List.dvd_prod (List.mem_map.mpr ⟨q,hq,rfl⟩)) p

theorem state_product_halves (a : State) (u h : List SmallSlot)
    (hs : a.small.Perm (u++h)) :
    a.product=halfProduct a.giantPlus u*halfProduct a.giantMinus h := by
  simp only [State.product,State.values,List.prod_cons,halfProduct]
  rw [(hs.map SmallSlot.value).prod_eq,List.map_append,List.prod_append]
  ring

theorem regularTransform_halves (g giant : (p : ℕ)→ZMod p→ℂ)
    (outside : List ℕ) (a : State) (u h : List SmallSlot)
    (hs : a.small.Perm (u++h)) (hp : 0<a.giantPlus) (hq : 0<a.giantMinus)
    (hu : ∀q∈u,0<q.value) (hh : ∀q∈h,0<q.value) :
    regularTransform g giant outside a =
      halfTransform g giant (outsideProduct outside*halfProduct a.giantMinus h)
        a.frequency a.giantPlus u *
      halfTransform g giant (outsideProduct outside*halfProduct a.giantPlus u)
        a.frequency a.giantMinus h := by
  have hden (n P H : ℕ) (hn : 0<n) (hd : n∣P) :
      outsideProduct outside*(P*H/n)=(outsideProduct outside*H)*(P/n) := by
    rw [mul_div_factor n P H hn hd]
    ring
  have hdu : ∀q∈u,outsideProduct outside*(a.product/q.value)=
      (outsideProduct outside*halfProduct a.giantMinus h)*(halfProduct a.giantPlus u/q.value) := by
    intro q hqu
    rw [state_product_halves a u h hs]
    exact hden _ _ _ (hu q hqu) (halfProduct_dvd_small _ _ q hqu)
  have hdh : ∀q∈h,outsideProduct outside*(a.product/q.value)=
      (outsideProduct outside*halfProduct a.giantPlus u)*(halfProduct a.giantMinus h/q.value) := by
    intro q hqh
    rw [state_product_halves a u h hs,mul_comm (halfProduct a.giantPlus u)]
    exact hden _ _ _ (hh q hqh) (halfProduct_dvd_small _ _ q hqh)
  have hdp : outsideProduct outside*(a.product/a.giantPlus)=
      (outsideProduct outside*halfProduct a.giantMinus h)*(halfProduct a.giantPlus u/a.giantPlus) := by
    rw [state_product_halves a u h hs]
    exact hden _ _ _ hp (halfProduct_dvd_giant _ _)
  have hdq : outsideProduct outside*(a.product/a.giantMinus)=
      (outsideProduct outside*halfProduct a.giantPlus u)*(halfProduct a.giantMinus h/a.giantMinus) := by
    rw [state_product_halves a u h hs,mul_comm (halfProduct a.giantPlus u)]
    exact hden _ _ _ hq (halfProduct_dvd_giant _ _)
  unfold regularTransform halfTransform
  dsimp only
  rw [(hs.map (fun q => g q.value
    (modFraction q.value a.frequency (outsideProduct outside*(a.product/q.value))))).prod_eq,
    List.map_append,List.prod_append,hdp,hdq]
  have heu : u.map (fun q => g q.value
      (modFraction q.value a.frequency (outsideProduct outside*(a.product/q.value)))) =
      u.map (fun q => g q.value (modFraction q.value a.frequency
        ((outsideProduct outside*halfProduct a.giantMinus h)*(halfProduct a.giantPlus u/q.value)))) := by
    apply List.map_congr_left
    intro q hqu
    rw [hdu q hqu]
  have heh : h.map (fun q => g q.value
      (modFraction q.value a.frequency (outsideProduct outside*(a.product/q.value)))) =
      h.map (fun q => g q.value (modFraction q.value a.frequency
        ((outsideProduct outside*halfProduct a.giantPlus u)*(halfProduct a.giantMinus h/q.value)))) := by
    apply List.map_congr_left
    intro q hqh
    rw [hdh q hqh]
  rw [heu,heh]
  ring

end Ostmann.Construction

end

end OAI
