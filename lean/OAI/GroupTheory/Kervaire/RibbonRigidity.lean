import OAI.GroupTheory.Kervaire.BoundaryFlow

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireRibbon

section
open Equiv Equiv.Perm KervaireCycle
open scoped Classical
variable {D A : Type*} [Group A]

lemma orbitWeight_coboundary (σ : Equiv.Perm D) (u : D → A) (n : ℕ) (d : D) :
    orbitWeight σ (fun x ↦ u (σ x) * (u x)⁻¹) n d = u ((σ^n) d) * (u d)⁻¹ := by
  induction n with
  | zero => simp [orbitWeight]
  | succ n ih =>
    rw [orbitWeight_succ,ih,pow_succ',mul_apply]
    group

lemma list_prod_single_difference {B : Type*} (l : List B) (hl : l.Nodup) (f g : B → A)
    (x : B) (hx : x ∈ l) (hfg : ∀ y ∈ l, y ≠ x → f y = g y)
    (hp : (l.map f).prod = (l.map g).prod) : f x = g x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    obtain ⟨hy,hl⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons,List.prod_cons] at hp
    by_cases hxy : x = y
    · subst y
      have ht : l.map f = l.map g := List.map_congr_left (fun z hz ↦
        hfg z (List.mem_cons_of_mem _ hz) (fun he ↦ hy (he ▸ hz)))
      rw [ht] at hp
      exact mul_right_cancel hp
    · have hyx := Ne.symm hxy
      rw [hfg y (List.mem_cons_self ..) hyx] at hp
      exact ih hl (List.mem_of_ne_of_mem hxy hx)
        (fun z hz ↦ hfg z (List.mem_cons_of_mem _ hz)) (mul_left_cancel hp)

lemma orbitWeight_as_list (σ : Equiv.Perm D) (b : D → A) (n : ℕ) (d : D) :
    orbitWeight σ b n d = ((List.ofFn (fun i : Fin n ↦ (σ^i.val) d)).reverse.map b).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orbitWeight_succ,ih,List.ofFn_succ',List.concat_eq_append,List.reverse_concat]
    simp only [List.map_cons,List.prod_cons]
    rfl

lemma rotate_orbit_list (n : ℕ) [NeZero n] :
    List.ofFn (fun i : Fin n ↦ ((finRotate n)^i.val) 0) = List.ofFn (fun i : Fin n ↦ i) := by
  congr 1
  funext i
  rw [rotate_pow_apply]
  simp

lemma orbitWeight_single_difference (n : ℕ) [NeZero n] (f g : Fin n → A)
    (j : Fin n) (hfg : ∀ i, i ≠ j → f i = g i)
    (hp : orbitWeight (finRotate n) f n 0 = orbitWeight (finRotate n) g n 0) : f j = g j := by
  rw [orbitWeight_as_list,orbitWeight_as_list,rotate_orbit_list] at hp
  apply list_prod_single_difference _ _ f g j _ (fun i _ ↦ hfg i) hp
  · exact List.nodup_reverse.mpr (List.nodup_ofFn.mpr Function.injective_id)
  · simp only [List.mem_reverse,List.mem_ofFn]
    exact ⟨j,rfl⟩

/-- A connection which is a pure gauge away from one directed corner is a pure
 gauge everywhere as soon as its exceptional face has trivial holonomy. -/
lemma one_defect_of_holonomy [Fintype D] (σ : Equiv.Perm D) (b u : D → A) (p : D)
    {Z : Type*} (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D)
    (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (hu : ∀ d, d ≠ p → b d = u (σ d) * (u d)⁻¹)
    (hm : ∀ z, orbitWeight (finRotate (n z+1)) (fun i ↦ b (e ⟨z,i⟩)) (n z+1) 0 = 1) :
    b p = u (σ p) * (u p)⁻¹ := by
  obtain ⟨⟨z,j⟩,rfl⟩ := e.surjective p
  let v : Fin (n z+1) → A := fun i ↦ u (e ⟨z,i⟩)
  have hv := orbitWeight_coboundary (finRotate (n z+1)) v (n z+1) 0
  rw [rotate_pow_self] at hv
  simp only [one_apply,mul_inv_cancel] at hv
  have hh := orbitWeight_single_difference (n z+1) (fun i ↦ b (e ⟨z,i⟩))
    (fun i ↦ v (finRotate _ i) * (v i)⁻¹) j (by
      intro i hij
      rw [hu _ (fun h ↦ hij (eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2))]
      rw [he]) ((hm z).trans hv.symm)
  simpa only [v,← he] using hh

lemma holonomy_of_coboundary [Fintype D] (σ : Equiv.Perm D) (b u : D → A)
    {Z : Type*} (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D)
    (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (z : Z) (hu : ∀ i, b (e ⟨z,i⟩) = u (σ (e ⟨z,i⟩)) * (u (e ⟨z,i⟩))⁻¹) :
    orbitWeight (finRotate (n z+1)) (fun i ↦ b (e ⟨z,i⟩)) (n z+1) 0 = 1 := by
  have hf : (fun i ↦ b (e ⟨z,i⟩)) = (fun i ↦ u (e ⟨z,finRotate _ i⟩) * (u (e ⟨z,i⟩))⁻¹) := by
    funext i
    rw [hu,he]
  rw [hf]
  have hh := orbitWeight_coboundary (finRotate (n z+1)) (fun i ↦ u (e ⟨z,i⟩)) (n z+1) 0
  rw [rotate_pow_self] at hh
  simpa using hh
end

open Equiv Equiv.Perm KervaireCycle KervaireMixing KervaireTraversal KervaireBoundary
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

omit [Fintype I] [Fintype K] in
lemma successor_pow_inl (ρ : Perm I) (k : K) (i : I) (n : ℕ) :
    ((successor (K := K) ρ)^n) (Sum.inl k,i) = (Sum.inl k,(ρ^n) i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',mul_apply,ih,pow_succ']; rfl

omit [Fintype I] [Fintype K] in
lemma successor_pow_inr (ρ : Perm I) (k : K) (i : I) (n : ℕ) :
    ((successor (K := K) ρ)^n) (Sum.inr k,i) = (Sum.inr k,(ρ.symm^n) i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',mul_apply,ih,pow_succ']; rfl

lemma successor_cycles (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (x y : Slot I K) :
    (successor ρ).SameCycle x y ↔ x.1 = y.1 := by
  constructor
  · intro h
    exact sameCycle_map_eq (successor ρ) Prod.fst (by rintro ⟨k|k,i⟩ <;> rfl) h
  · rcases x with ⟨k,i⟩
    rcases y with ⟨l,j⟩
    intro h
    dsimp at h
    subst l
    cases k with
    | inl k =>
      obtain ⟨n,hn⟩ := (hρ i j).exists_nat_pow_eq
      have hh : ((successor (K := K) ρ)^n) (Sum.inl k,i) = (Sum.inl k,j) := by
        rw [successor_pow_inl,hn]
      exact hh ▸ SameCycle.rfl.pow_right
    | inr k =>
      obtain ⟨n,hn⟩ := (hρ i j).inv.exists_nat_pow_eq
      have hh : ((successor (K := K) ρ)^n) (Sum.inr k,i) = (Sum.inr k,j) := by
        rw [successor_pow_inr]
        exact congrArg (fun q ↦ (Sum.inr k,q)) hn
      exact hh ▸ SameCycle.rfl.pow_right

lemma numCycles_successor [Nonempty I] (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) :
    numCycles (successor (K := K) ρ) = 2*Fintype.card K := by
  have hh := numCycles_eq_card_of_projection (successor (K := K) ρ) Prod.fst
    (fun k ↦ ⟨(k,Classical.arbitrary I),rfl⟩) (successor_cycles ρ hρ)
  simpa only [Fintype.card_sum,two_mul] using hh

omit [Fintype I] [Fintype K] in
lemma traversal_ne_zero (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (d : Slot I K) :
    traversalSign s d ≠ 0 := by
  rcases d with ⟨k|k,i⟩ <;> rcases hs i with h | h <;> simp [traversalSign,h]

/-- A single deviating corner on a connected planar assembly of literal word
 disks cannot carry a nontrivial defect. This is the analytic boundary theorem,
 with all other circuit products discharged by gauge telescoping. -/
theorem planar_corner_rigidity [Nonempty I] [Nonempty K]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = - traversalSign s d)
    (hconn : components (successor ρ) θ = ⊤) (hp : planar (successor ρ) θ)
    (u : Slot I K → A) (p : Slot I K)
    (hu : ∀ d, d ≠ p → (labels ρ a d)⁻¹ = u (θ d) * (u (successor ρ d))⁻¹) :
    (labels ρ a p)⁻¹ = u (θ p) * (u (successor ρ p))⁻¹ := by
  let σ := successor (K := K) ρ
  let φ := σ*θ
  obtain ⟨n,e,he⟩ := exists_cycle_coordinates φ
  let z₀ : Cycles φ := (e.symm (θ p)).1
  have hc : ∀ z, z ≠ z₀ → orbitWeight (finRotate (n z+1))
      (fun i ↦ labels ρ a (θ (e ⟨z,i⟩))) (n z+1) 0 = 1 := by
    intro z hz
    apply holonomy_of_coboundary φ (fun d ↦ labels ρ a (θ d)) u n e he z
    intro i
    have hne : θ (e ⟨z,i⟩) ≠ p := by
      intro hh
      have hh' : e ⟨z,i⟩ = θ p := by simpa only [hθ] using congrArg θ hh
      have hh'' := congrArg (fun d ↦ (e.symm d).1) hh'
      exact hz (by simpa only [e.symm_apply_apply] using hh'')
    have hh := congrArg Inv.inv (hu _ hne)
    simpa only [φ,σ,Equiv.Perm.mul_apply,inv_inv,_root_.mul_inv_rev,hθ] using hh
  have htne (d : Slot I K) : θ d ≠ d := by
    intro hd
    have hh := hop d
    rw [hd] at hh
    have hn := traversal_ne_zero s hs d
    omega
  have ht := numCycles_involution θ hθ htne
  have hv := numCycles_successor (K := K) ρ hρ
  have hall := hp
  unfold planar at hall
  rw [hconn,classes_top,hv] at hall
  have hcard : Fintype.card (Slot I K) = 2*(Fintype.card I*Fintype.card K) := by
    simp only [Slot,Fintype.card_prod,Fintype.card_sum]
    ring
  rw [hcard] at ht hall
  have hEuler : Fintype.card (Cycles φ) + 2*Fintype.card K = 2+Fintype.card I*Fintype.card K := by
    change numCycles φ + _ = _
    dsimp [φ,σ] at *
    omega
  have hb := KervaireBoundary.planar_boundary ρ a s hs hsum θ hθ hop n e he
    (fun d f ↦ reachable_of_component σ θ (x := d) (y := f) (by rw [hconn]; trivial)) hEuler z₀ hc
  have hm (z : Cycles φ) : orbitWeight (finRotate (n z+1))
      (fun i ↦ labels ρ a (θ (e ⟨z,i⟩))) (n z+1) 0 = 1 := by
    by_cases hz : z = z₀
    · subst z; exact hb
    · exact hc z hz
  have hh := one_defect_of_holonomy φ (fun d ↦ labels ρ a (θ d)) u (θ p) n e he (by
    intro d hd
    have hdp : θ d ≠ p := fun h ↦ hd (by simpa only [hθ] using congrArg θ h)
    have hh := congrArg Inv.inv (hu (θ d) hdp)
    simpa only [φ,σ,Equiv.Perm.mul_apply,inv_inv,_root_.mul_inv_rev,hθ] using hh) hm
  have hi := congrArg Inv.inv hh
  simpa only [φ,σ,Equiv.Perm.mul_apply,hθ,_root_.mul_inv_rev,inv_inv] using hi
end KervaireRibbon

end

end OAI
