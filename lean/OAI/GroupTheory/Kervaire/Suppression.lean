import OAI.GroupTheory.Kervaire.Components

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

def erase (σ : Equiv.Perm D) (x : D) : Equiv.Perm D := swap x (σ x) * σ

omit [Fintype D] in
lemma erase_fixed (σ : Equiv.Perm D) (x : D) : erase σ x x = x := by simp [erase]

omit [Fintype D] in
lemma erase_apply (σ : Equiv.Perm D) (x d : D) (hd : d ≠ x) :
    erase σ x d = if σ d = x then σ x else σ d := by
  change swap x (σ x) (σ d) = _
  split_ifs with he
  · rw [he,swap_apply_left]
  · exact swap_apply_of_ne_of_ne he (fun hh ↦ hd (σ.injective hh))

lemma numCycles_erase (σ : Equiv.Perm D) {x : D} (hx : σ x ≠ x) :
    numCycles (erase σ x) = numCycles σ + 1 :=
  numCycles_swap_split σ hx.symm SameCycle.rfl.apply_right

lemma cycles_erase_le (σ : Equiv.Perm D) (x : D) :
    SameCycle.setoid (erase σ x) ≤ SameCycle.setoid σ := by
  have h := cycles_swap_le σ (SameCycle.setoid σ) le_rfl x (σ x)
  rw [joinPair_eq _ SameCycle.rfl.apply_right] at h
  exact h

lemma sameCycle_erase (σ : Equiv.Perm D) {x d e : D} (hx : σ x ≠ x)
    (hd : d ≠ x) (he : e ≠ x) :
    (erase σ x).SameCycle d e ↔ σ.SameCycle d e := by
  refine ⟨fun h ↦ cycles_erase_le σ x h,?_⟩
  intro h
  let τ := erase σ x
  let f : D → Cycles τ := fun a ↦ Quotient.mk _ (if a = x then σ x else a)
  have hf (a : D) : f (σ a) = f a := by
    by_cases ha : a = x
    · subst a
      simp [f,hx]
    by_cases hs : σ a = x
    · have ht : τ a = σ x := by simp only [τ,erase_apply σ x a ha,ite_eq_left hs]
      change Quotient.mk _ (if σ a = x then σ x else σ a) = Quotient.mk _ (if a = x then σ x else a)
      rw [ite_eq_left hs,ite_eq_right ha,← ht]
      exact Quotient.sound SameCycle.rfl.apply_left
    · have ht : τ a = σ a := by simp only [τ,erase_apply σ x a ha,ite_eq_right hs]
      change Quotient.mk _ (if σ a = x then σ x else σ a) = Quotient.mk _ (if a = x then σ x else a)
      rw [ite_eq_right hs,ite_eq_right ha,← ht]
      exact Quotient.sound SameCycle.rfl.apply_left
  have hh := sameCycle_map_eq σ f hf h
  apply Quotient.exact (s := SameCycle.setoid τ)
  simpa only [f,ite_eq_right hd,ite_eq_right he] using hh

omit [DecidableEq D] in
lemma classes_le_of_le {r s : Setoid D} (h : r ≤ s) : classes s ≤ classes r := by
  apply Fintype.card_le_of_surjective (Quotient.map id (fun _ _ hh ↦ h hh))
  intro z
  induction z using Quotient.inductionOn with | h d => exact ⟨Quotient.mk _ d,rfl⟩

lemma classes_joinPair_le (r : Setoid D) (x y : D) : classes r ≤ classes (joinPair r x y) + 1 := by
  by_cases h : r x y
  · rw [joinPair_eq r h]; omega
  · rw [classes_joinPair r h]

def components (σ θ : Equiv.Perm D) : Setoid D := SameCycle.setoid σ ⊔ SameCycle.setoid θ

def planar (σ θ : Equiv.Perm D) : Prop :=
  numCycles σ + numCycles θ + numCycles (σ*θ) = Fintype.card D + 2*classes (components σ θ)

lemma components_swap_sup (σ θ : Equiv.Perm D) (x y : D) :
    joinPair (components (swap x y * σ) θ) x y = joinPair (components σ θ) x y := by
  unfold joinPair components
  have h := cycles_swap_sup σ x y
  simpa only [sup_right_comm] using congrArg (fun r : Setoid D ↦ r ⊔ SameCycle.setoid θ) h

/-- Splitting a vertex of a planar ribbon permutation preserves planarity.
The proof uses only the finite Euler inequality and the exact cycle split/merge count. -/
lemma planar_vertex_split (σ θ : Equiv.Perm D) {x y : D} (hne : x ≠ y)
    (hxy : σ.SameCycle x y) (hp : planar σ θ) : planar (swap x y * σ) θ := by
  let r := components (swap x y * σ) θ
  have hr : joinPair r x y = components σ θ := by
    dsimp [r]
    rw [components_swap_sup]
    exact joinPair_eq (components σ θ) ((le_sup_left : SameCycle.setoid σ ≤ components σ θ) hxy)
  have hv := numCycles_swap_split σ hne hxy
  by_cases hc : r x y
  · have hre : r = components σ θ := by simpa only [joinPair_eq _ hc] using hr
    have hi := euler_inequality (swap x y * σ) θ
    change _ ≤ _ + 2*classes r at hi
    rw [hre,hv,mul_assoc] at hi
    have hf : ¬ (σ*θ).SameCycle x y := by
      intro hh
      have hn := numCycles_swap_split (σ*θ) hne hh
      unfold planar at hp
      omega
    have hf' := numCycles_swap_merge (σ*θ) hf
    unfold planar at hp ⊢
    change numCycles (swap x y * σ) + numCycles θ + numCycles ((swap x y * σ)*θ) = _ + 2*classes r
    rw [hv,hre,mul_assoc]
    omega
  · have hφle : SameCycle.setoid ((swap x y * σ)*θ) ≤ r := by
      apply cycle_le_of_step
      intro d
      exact r.trans' ((le_sup_left : SameCycle.setoid (swap x y * σ) ≤ r) SameCycle.rfl.apply_left)
        ((le_sup_right : SameCycle.setoid θ ≤ r) SameCycle.rfl.apply_left)
    have hf' := numCycles_swap_merge ((swap x y * σ)*θ) (fun h ↦ hc (hφle h))
    have he : swap x y * ((swap x y * σ)*θ) = σ*θ := by simp [← mul_assoc]
    rw [he] at hf'
    have hcr := classes_joinPair r hc
    rw [hr] at hcr
    unfold planar at hp ⊢
    change _ = _ + 2*classes r
    omega
end
section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma cycles_mul_le (σ θ : Equiv.Perm D) (r : Setoid D)
    (hs : SameCycle.setoid σ ≤ r) (ht : SameCycle.setoid θ ≤ r) :
    SameCycle.setoid (σ*θ) ≤ r := by
  apply cycle_le_of_step
  intro d
  exact r.trans' (hs SameCycle.rfl.apply_left) (ht SameCycle.rfl.apply_left)

lemma components_fixed_le (σ θ : Equiv.Perm D) {x : D} (hs : σ x = x) (ht : θ x = x) :
    components σ θ ≤ Setoid.ker (fun d ↦ d = x) := by
  apply sup_le
  · apply cycle_le_of_step
    intro d
    change (σ d = x) = (d = x)
    exact propext ⟨fun h ↦ σ.injective (h.trans hs.symm),fun h ↦ h ▸ hs⟩
  · apply cycle_le_of_step
    intro d
    change (θ d = x) = (d = x)
    exact propext ⟨fun h ↦ θ.injective (h.trans ht.symm),fun h ↦ h ▸ ht⟩

lemma components_eq_of_fixed (σ θ : Equiv.Perm D) {x d : D}
    (hs : σ x = x) (ht : θ x = x) (h : components σ θ x d) : x = d := by
  have hh := components_fixed_le σ θ hs ht h
  change (x = x) = (d = x) at hh
  exact (hh ▸ rfl : d = x).symm

lemma planar_vertex_split_separates (σ θ : Equiv.Perm D) {x y : D} (hne : x ≠ y)
    (hxy : σ.SameCycle x y) (hφ : (σ*θ).SameCycle x y) (hp : planar σ θ) :
    ¬ components (swap x y * σ) θ x y := by
  intro hc
  have hr : components (swap x y * σ) θ = components σ θ := by
    have hh := components_swap_sup σ θ x y
    rw [joinPair_eq _ hc] at hh
    have he := joinPair_eq (components σ θ) ((le_sup_left : SameCycle.setoid σ ≤ components σ θ) hxy)
    exact hh.trans he
  have hv := numCycles_swap_split σ hne hxy
  have hf := numCycles_swap_split (σ*θ) hne hφ
  have he := planar_vertex_split σ θ hne hxy hp
  unfold planar at he hp
  rw [mul_assoc,hv,hf,hr] at he
  omega

/-- Suppress a two-valent vertex, retaining its two darts as isolated markers. -/
def suppress (θ : Equiv.Perm D) (x y : D) : Equiv.Perm D :=
  swap x y * (swap y (θ x) * θ * swap y (θ x))

omit [Fintype D] in
lemma suppress_apply (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    suppress θ x y x = x ∧ suppress θ x y y = y ∧
    suppress θ x y (θ x) = θ y ∧ suppress θ x y (θ y) = θ x := by
  have hyx : θ y ≠ x := fun he ↦ hxy' (by simpa only [hθ] using (congrArg θ he).symm)
  have hpq : θ x ≠ θ y := fun he ↦ hxy (θ.injective he)
  simp only [suppress,mul_apply,swap_apply_of_ne_of_ne hxy hx.symm,
    swap_apply_left,swap_apply_right,hθ,swap_apply_of_ne_of_ne hy hpq.symm,
    swap_apply_of_ne_of_ne hyx hy,swap_apply_of_ne_of_ne hx hxy',true_and]

omit [Fintype D] in
lemma suppress_other (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y d : D} (hdx : d ≠ x) (hdy : d ≠ y) (hdp : d ≠ θ x) (hdq : d ≠ θ y) :
    suppress θ x y d = θ d := by
  have htx : θ d ≠ x := fun h ↦ hdp (by simpa only [hθ] using congrArg θ h)
  have hty : θ d ≠ y := fun h ↦ hdq (by simpa only [hθ] using congrArg θ h)
  have htp : θ d ≠ θ x := fun h ↦ hdx (θ.injective h)
  simp only [suppress,mul_apply,swap_apply_of_ne_of_ne hdy hdp,
    swap_apply_of_ne_of_ne hty htp,swap_apply_of_ne_of_ne htx hty]

omit [Fintype D] in
lemma suppress_involutive (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    ∀ d, suppress θ x y (suppress θ x y d) = d := by
  have hh := suppress_apply θ hθ hxy hx hxy' hy
  intro d
  by_cases hdx : d = x
  · subst d; rw [hh.1,hh.1]
  by_cases hdy : d = y
  · subst d; rw [hh.2.1,hh.2.1]
  by_cases hdp : d = θ x
  · subst d; rw [hh.2.2.1,hh.2.2.2]
  by_cases hdq : d = θ y
  · subst d; rw [hh.2.2.2,hh.2.2.1]
  rw [suppress_other θ hθ hdx hdy hdp hdq]
  have htx : θ d ≠ x := fun h ↦ hdp (by simpa only [hθ] using (congrArg θ h))
  have hty : θ d ≠ y := fun h ↦ hdq (by simpa only [hθ] using (congrArg θ h))
  rw [suppress_other θ hθ htx hty (fun h ↦ hdx (θ.injective h)) (fun h ↦ hdy (θ.injective h)),hθ]

lemma numCycles_suppress (θ : Equiv.Perm D)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) :
    numCycles (suppress θ x y) = numCycles θ + 1 := by
  let δ := swap y (θ x)
  have ht : (δ*θ*δ⁻¹) x = y := by
    simp only [δ,swap_inv,mul_apply,swap_apply_of_ne_of_ne hxy hx.symm,swap_apply_right]
  have hc := numCycles_swap_split (δ*θ*δ⁻¹) hxy (ht ▸ SameCycle.rfl.apply_right)
  rw [numCycles_conj] at hc
  exact hc

omit [Fintype D] in
lemma suppress_faces (σ θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hsx : σ x = y) (hsy : σ y = x)
    (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    (swap x y * σ) * suppress θ x y = erase (erase (σ*θ) x) y := by
  have hyx : θ y ≠ x := fun he ↦ hxy' (by simpa only [hθ] using (congrArg θ he).symm)
  have hpq : θ x ≠ θ y := fun he ↦ hxy (θ.injective he)
  have hpy : σ (θ x) ≠ y := fun he ↦ hx (σ.injective (he.trans hsx.symm))
  have hqx : σ (θ y) ≠ x := fun he ↦ hy (σ.injective (he.trans hsy.symm))
  have hσsw : σ * swap x y = swap x y * σ := by
    rw [mul_swap_eq_swap_mul,hsx,hsy,swap_comm]
  have hφy : erase (σ*θ) x y = σ (θ y) := by
    rw [erase_apply _ _ _ hxy.symm,mul_apply,ite_eq_right hqx]
  have hstart : (swap x y * σ) * suppress θ x y = σ * swap y (θ x) * θ * swap y (θ x) := by
    unfold suppress
    rw [mul_assoc (swap x y) σ,← mul_assoc σ,hσsw]
    simp only [← mul_assoc,swap_mul_self,one_mul]
  rw [hstart,erase,hφy,erase,mul_apply]
  have hcomm : swap x (σ (θ x)) * swap y (σ (θ y)) = swap y (σ (θ y)) * swap x (σ (θ x)) := by
    rw [swap_mul_eq_mul_swap]
    simp only [swap_inv,swap_apply_of_ne_of_ne hxy hqx.symm,
      swap_apply_of_ne_of_ne hpy (fun he ↦ hpq (σ.injective he))]
  calc
    σ * swap y (θ x) * θ * swap y (θ x) =
        swap x (σ (θ x)) * ((σ*θ)*swap y (θ x)) := by
      rw [mul_swap_eq_swap_mul σ y (θ x),hsy]
      simp only [mul_assoc]
    _ = swap x (σ (θ x)) * (swap (σ (θ y)) y * (σ*θ)) := by
      rw [mul_swap_eq_swap_mul (σ*θ) y (θ x),mul_apply,mul_apply,hθ,hsx]
    _ = swap y (σ (θ y)) * (swap x (σ (θ x)) * (σ*θ)) := by
      rw [swap_comm (σ (θ y)) y,← mul_assoc,hcomm,mul_assoc]

end
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma components_suppress (σ θ : Equiv.Perm D) {x y : D} (hsx : σ x = y) :
    joinPair (joinPair (components (swap x y * σ) (suppress θ x y)) x (θ x)) y (θ x) =
      components σ θ := by
  let r := components σ θ
  let r' := components (swap x y * σ) (suppress θ x y)
  let R := joinPair (joinPair r' x (θ x)) y (θ x)
  have hrxy : r x y := (le_sup_left : SameCycle.setoid σ ≤ r) (hsx ▸ SameCycle.rfl.apply_right)
  have hrxp : r x (θ x) := (le_sup_right : SameCycle.setoid θ ≤ r) SameCycle.rfl.apply_right
  have ha : SameCycle.setoid (swap x y) ≤ r := cycle_swap_le r x y hrxy
  have hb : SameCycle.setoid (swap y (θ x)) ≤ r := cycle_swap_le r y (θ x) (r.trans' (r.symm' hrxy) hrxp)
  have hr' : r' ≤ r := by
    apply sup_le
    · exact cycles_mul_le _ _ r ha le_sup_left
    · exact cycles_mul_le _ _ r ha (cycles_mul_le _ _ r (cycles_mul_le _ _ r hb le_sup_right) hb)
  have hRr : R ≤ r := sup_le (sup_le hr' (cycle_swap_le r x (θ x) hrxp)) hb
  have hr'R : r' ≤ R := (le_joinPair r' x (θ x)).trans (le_joinPair _ y (θ x))
  have hRyp : R y (θ x) := joinPair_rel _ _ _
  have hRxp : R x (θ x) := le_joinPair _ _ _ (joinPair_rel _ _ _)
  have hRa : SameCycle.setoid (swap x y) ≤ R := cycle_swap_le R x y (R.trans' hRxp (R.symm' hRyp))
  have hRb : SameCycle.setoid (swap y (θ x)) ≤ R := cycle_swap_le R y (θ x) hRyp
  have hs : SameCycle.setoid σ ≤ R := by
    have hh := cycles_mul_le (swap x y) (swap x y * σ) R hRa (le_sup_left.trans hr'R)
    simpa only [← mul_assoc,swap_mul_self,one_mul] using hh
  have ht : SameCycle.setoid θ ≤ R := by
    have hh := cycles_mul_le _ (swap y (θ x)) R
      (cycles_mul_le (swap y (θ x)) _ R hRb
        (cycles_mul_le (swap x y) (suppress θ x y) R hRa (le_sup_right.trans hr'R))) hRb
    simp only [suppress,← mul_assoc,swap_mul_self,one_mul] at hh
    simpa only [mul_assoc,swap_mul_self,mul_one] using hh
  exact le_antisymm hRr (sup_le hs ht)

lemma classes_suppress (σ θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hsx : σ x = y) (hsy : σ y = x)
    (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    classes (components (swap x y * σ) (suppress θ x y)) = classes (components σ θ) + 2 := by
  let r := components (swap x y * σ) (suppress θ x y)
  have hsp := suppress_apply θ hθ hxy hx hxy' hy
  have hs'x : (swap x y * σ) x = x := by simp [hsx]
  have hs'y : (swap x y * σ) y = y := by simp [hsy]
  have hnx : ¬ r x (θ x) := fun h ↦ hx (components_eq_of_fixed _ _ hs'x hsp.1 h).symm
  have hyker : r ≤ Setoid.ker (fun d ↦ d = y) := components_fixed_le _ _ hs'y hsp.2.1
  have hker : joinPair r x (θ x) ≤ Setoid.ker (fun d ↦ d = y) := by
    apply sup_le hyker
    apply cycle_swap_le
    change (x = y) = (θ x = y)
    simp only [hxy,hxy']
  have hny : ¬ joinPair r x (θ x) y (θ x) := by
    intro h
    have he := hker h
    change (y = y) = (θ x = y) at he
    exact hxy' (he ▸ rfl)
  have h1 := classes_joinPair r hnx
  have h2 := classes_joinPair (joinPair r x (θ x)) hny
  have he := components_suppress σ θ hsx
  change joinPair (joinPair r x (θ x)) y (θ x) = _ at he
  rw [he] at h2
  change classes r = _
  calc
    classes r = classes (joinPair r x (θ x)) + 1 := h1.symm
    _ = (classes (components σ θ) + 1) + 1 := by rw [h2.symm]
    _ = _ := by omega

lemma planar_suppress (σ θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hsx : σ x = y) (hsy : σ y = x)
    (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) (hp : planar σ θ) :
    planar (swap x y * σ) (suppress θ x y) := by
  have hyx : θ y ≠ x := fun he ↦ hxy' (by simpa only [hθ] using (congrArg θ he).symm)
  have hpx : (σ*θ) x ≠ x := fun he ↦ hxy' (σ.injective (he.trans hsy.symm))
  have hqx : (σ*θ) y ≠ x := fun he ↦ hy (σ.injective (he.trans hsy.symm))
  have hqy : (σ*θ) y ≠ y := fun he ↦ hyx (σ.injective (he.trans hsx.symm))
  have hey : erase (σ*θ) x y ≠ y := by rw [erase_apply _ _ _ hxy.symm,ite_eq_right hqx]; exact hqy
  have hv := numCycles_swap_split σ hxy (hsx ▸ SameCycle.rfl.apply_right)
  have ht := numCycles_suppress θ hxy hx
  have hf : numCycles ((swap x y * σ)*suppress θ x y) = numCycles (σ*θ) + 2 := by
    rw [suppress_faces σ θ hθ hxy hsx hsy hx hxy' hy,numCycles_erase _ hey,numCycles_erase _ hpx]
  have hc := classes_suppress σ θ hθ hxy hsx hsy hx hxy' hy
  unfold planar at hp ⊢
  rw [hv,ht,hf,hc]
  omega
end KervaireRibbon

end

end OAI
