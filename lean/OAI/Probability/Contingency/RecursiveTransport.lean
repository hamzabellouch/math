import Mathlib
import OAI.Probability.Contingency.Transport

namespace OAI

/-! Recursive Transport. -/

noncomputable section

open scoped BigOperators
open QuadraticMap
open scoped BigOperators
open QuadraticMap

namespace Contingency

universe u

 

@[reducible] def PairCoords (ι : Type u) : ℕ → Type u
  | 0 => ι
  | n+1 => PairCoords (ι ⊕ Bool) n

instance pairCoordsFintype (ι : Type u) [Fintype ι] : (n : ℕ) → Fintype (PairCoords ι n)
  | 0 => inferInstanceAs (Fintype ι)
  | n+1 => pairCoordsFintype (ι ⊕ Bool) n

instance pairCoordsDecidableEq (ι : Type u) [DecidableEq ι] :
    (n : ℕ) → DecidableEq (PairCoords ι n)
  | 0 => inferInstanceAs (DecidableEq ι)
  | n+1 => pairCoordsDecidableEq (ι ⊕ Bool) n

noncomputable def pairBox {ι : Type u} (C : ℕ) :
    (n : ℕ) → (ι → ℤ) → PairCoords ι n → ℤ
  | 0, B => B
  | n+1, B => pairBox C n (pairAssembly B (C:ℤ) C)

noncomputable def allBalance {ι : Type u} (C : ℕ) :
    (n : ℕ) → ((PairCoords ι n → ℤ) → ℝ) → (ι → ℤ) → ℝ
  | 0, f => f
  | n+1, f => balancedMarginal (allBalance C n f) C

 

noncomputable def allRaise {ι : Type u} (C : ℕ) :
    (n : ℕ) → ((PairCoords ι n → ℤ) → ℝ) → (ι → ℤ) → ℝ
  | 0, _ => fun _ => 0
  | n+1, f => fun p => raisedFull (allBalance C n f) C p +
      balancedMarginal (allRaise C n f) C p

section Closure
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem allBalance_closure (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f : (PairCoords ι n → ℤ) → ℝ) (B : ι → ℤ) (T : ℤ)
    (hp : PositiveSlice f (pairBox C n B) T)
    (hs : HasSignature f (pairBox C n B) T) :
    PositiveSlice (allBalance C n f) B (T-(n:ℤ)*C) ∧
    HasSignature (allBalance C n f) B (T-(n:ℤ)*C) := by
  induction n generalizing ι with
  | zero => simpa only [allBalance, Nat.cast_zero, zero_mul, sub_zero] using ⟨hp,hs⟩
  | succ n ih =>
    obtain ⟨hp',hs'⟩ := ih f (pairAssembly B (C:ℤ) C) hp hs
    have hp'' := balancedMarginal_positive _ B C (T-(n:ℤ)*C) hp'
    have hs'' := balancedMarginal_signature _ B C hC (T-(n:ℤ)*C) hp' hs'
    have ht : T-(n:ℤ)*C-C = T-((n+1:ℕ):ℤ)*C := by push_cast; ring
    simpa only [allBalance, ht] using And.intro hp'' hs''

theorem allRaise_positive (C : ℕ) (hC : 2 ≤ C) (n : ℕ) (hn : 0 < n)
    (f : (PairCoords ι n → ℤ) → ℝ) (B : ι → ℤ) (T : ℤ)
    (hp : PositiveSlice f (pairBox C n B) T)
    (hs : HasSignature f (pairBox C n B) T) :
    PositiveSlice (allRaise C n f) B (T-(n:ℤ)*C-1) := by
  induction n generalizing ι with
  | zero => omega
  | succ n ih =>
    have hg := (allBalance_closure C hC n f (pairAssembly B (C:ℤ) C) T hp hs).1
    have hr := raisedFull_positive _ B C (by omega) (T-(n:ℤ)*C) hg
    have ht : T-(n:ℤ)*C-(C+1:ℕ) = T-((n+1:ℕ):ℤ)*C-1 := by push_cast; ring
    rw [ht] at hr
    cases n with
    | zero =>
      simpa only [allRaise, balancedMarginal, Finset.sum_const_zero, add_zero] using hr
    | succ n =>
      have hg' := ih (by omega) f (pairAssembly B (C:ℤ) C) hp hs
      have hb := balancedMarginal_positive _ B C (T-((n+1:ℕ):ℤ)*C-1) hg'
      have ht' : T-((n+1:ℕ):ℤ)*C-1-C = T-((n+1+1:ℕ):ℤ)*C-1 := by push_cast; ring
      rw [ht'] at hb
      exact hr.add hb

end Closure

 

@[reducible] def Branches (C : ℕ) : ℕ → Type
  | 0 => PUnit
  | n+1 => Fin (C+1) × Branches C n

instance branchesFintype (C : ℕ) : (n : ℕ) → Fintype (Branches C n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => @instFintypeProd _ _ inferInstance (branchesFintype C n)

noncomputable def leafDisplay {ι : Type u} (C : ℕ) :
    (n : ℕ) → (ι → ℤ) → Branches C n → PairCoords ι n → ℤ
  | 0, p, _ => p
  | n+1, p, a => leafDisplay C n (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ))) a.2

noncomputable def leafCoefficient {ι : Type u} [Fintype ι] [DecidableEq ι] (C : ℕ) :
    (n : ℕ) → ((PairCoords ι n → ℤ) → ℝ) → (ι → ℤ) → (ι → ℝ) →
      Branches C n → PairCoords ι n → ℝ
  | 0, _, _, h, _ => h
  | n+1, f, p, h, a =>
      let F := allBalance C n f
      let g := pairCumulative (C+1) (pairU F p (C+1)) (pairS F p (C+1)) h
      leafCoefficient C n f (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ)))
        (pairAssembly h (g (a.1:ℕ)) (-g ((a.1:ℕ)+1))) a.2

section LeafConservation
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def BoxSupported {κ : Type*} (f : (κ → ℤ) → ℝ) (B : κ → ℤ) : Prop :=
  ∀ p, ¬InBox B p → f p = 0

omit [DecidableEq ι] in
theorem PositiveSlice.boxSupported {f : (ι → ℤ) → ℝ} {B : ι → ℤ} {T : ℤ}
    (hf : PositiveSlice f B T) : BoxSupported f B := by
  intro p hp
  exact hf.2 p (fun h => hp h.1)

theorem allBalance_boxSupported (C n : ℕ) (f : (PairCoords ι n → ℤ) → ℝ)
    (B : ι → ℤ) (hf : BoxSupported f (pairBox C n B)) :
    BoxSupported (allBalance C n f) B := by
  induction n generalizing ι with
  | zero => exact hf
  | succ n ih =>
    intro p hp
    change (∑ j ∈ Finset.range (C+1),
      allBalance C n f (pairAssembly p (j:ℤ) ((C:ℤ)-j))) = 0
    apply Finset.sum_eq_zero
    intro j _
    apply ih f (pairAssembly B (C:ℤ) C) hf
    intro hh
    rw [pairAssembly_inBox] at hh
    exact hp hh.1

 

theorem leaf_demand_conservation (C n : ℕ) (f : (PairCoords ι n → ℤ) → ℝ)
    (B : ι → ℤ) (hf : BoxSupported f (pairBox C n B))
    (H : (PairCoords ι n → ℤ) → ℝ) (p : ι → ℤ) (h : ι → ℝ) :
    (∑ a : Branches C n, holeFunctional (fun x => f x * H x)
      (leafDisplay C n p a) (leafCoefficient C n f p h a)) =
      holeFunctional (allBalance C n (fun x => f x * H x)) p h := by
  induction n generalizing ι with
  | zero =>
    change (∑ _ : PUnit, holeFunctional (fun x => f x * H x) p h) =
      holeFunctional (fun x => f x * H x) p h
    simp
  | succ n ih =>
    let F := allBalance C n f
    let g := pairCumulative (C+1) (pairU F p (C+1)) (pairS F p (C+1)) h
    let FH := allBalance C n (fun x => f x * H x)
    have hFH : BoxSupported FH (pairAssembly B (C:ℤ) C) := by
      apply allBalance_boxSupported
      intro x hx
      simp only [hf x hx, zero_mul]
    have hz0 : pairU FH p (C+1) 0 = 0 := by
      apply hFH
      intro hb
      have ht := hb (Sum.inr true)
      simp [pairAssembly] at ht
    have hzC : pairU FH p (C+1) (C+1) = 0 := by
      apply hFH
      intro hb
      have ht := hb (Sum.inr false)
      simp [pairAssembly] at ht
    change (∑ a : Fin (C+1) × Branches C n,
      holeFunctional (fun x => f x * H x)
        (leafDisplay C n (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ))) a.2)
        (leafCoefficient C n f (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ)))
          (pairAssembly h (g (a.1:ℕ)) (-g ((a.1:ℕ)+1))) a.2)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [ih f (pairAssembly B (C:ℤ) C) hf H]
    rw [Fin.sum_univ_eq_sum_range (fun j => holeFunctional FH
      (pairAssembly p (j:ℤ) ((C:ℤ)-j)) (pairAssembly h (g j) (-g (j+1))))]
    exact branch_demand_conservation_endpoints FH C p h g hz0 hzC

end LeafConservation

section LeafPotential
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

 

theorem allRaise_future_monotone (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f : (PairCoords (ι ⊕ Bool) n → ℤ) → ℝ) (B : ι → ℤ) (T : ℤ)
    (hp : PositiveSlice f (pairBox C n (pairAssembly B (C:ℤ) C)) T)
    (hs : HasSignature f (pairBox C n (pairAssembly B (C:ℤ) C)) T)
    (p : ι → ℤ) (h : ι → ℝ) (g : ℕ → ℝ) :
    matrixForm (twoRemoval (balancedMarginal (allRaise C n f) C) p) h ≤
      ∑ j ∈ Finset.range (C+1),
        matrixForm (twoRemoval (allRaise C n f) (pairAssembly p (j:ℤ) ((C:ℤ)-j)))
          (pairAssembly h (g j) (-g (j+1))) := by
  by_cases hn : n = 0
  · subst n
    have hz : balancedMarginal (fun _ : ι ⊕ Bool → ℤ => (0:ℝ)) C = fun _ => 0 := by
      funext x
      simp [balancedMarginal]
    simp only [allRaise, hz, matrixForm_zero, Finset.sum_const_zero, le_refl]
  · exact actual_future_monotone _ B (C:ℤ) (T-(n:ℤ)*C-1)
      (allRaise_positive C hC n (Nat.pos_of_ne_zero hn) f _ T hp hs) p C h g

 

theorem leaf_potential_bound (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f : (PairCoords ι n → ℤ) → ℝ) (B : ι → ℤ) (T : ℤ)
    (hf : PositiveSlice f (pairBox C n B) T)
    (hs : HasSignature f (pairBox C n B) T)
    (p : ι → ℤ) (hp : InBox B p) (ht : (∑ i, p i)+(n:ℤ)*C = T+1)
    (h : ι → ℝ) (hbal : holeFunctional (allBalance C n f) p h = 0) :
    (∑ a : Branches C n, holePotential f (leafDisplay C n p a)
      (leafCoefficient C n f p h a)) ≤
      holePotential (allBalance C n f) p h - matrixForm (twoRemoval (allRaise C n f) p) h := by
  induction n generalizing ι with
  | zero =>
    change (∑ _ : PUnit, holePotential f p h) ≤ holePotential f p h -
      matrixForm (twoRemoval (fun _ => 0) p) h
    simp [matrixForm_zero]
  | succ n ih =>
    let F := allBalance C n f
    let g := pairCumulative (C+1) (pairU F p (C+1)) (pairS F p (C+1)) h
    obtain ⟨hF,hFs⟩ := allBalance_closure C hC n f (pairAssembly B (C:ℤ) C) T hf hs
    have htotal : (∑ i, p i)+(C+1:ℕ) = (T-(n:ℤ)*C)+2 := by
      push_cast at ht ⊢
      nlinarith
    have hb (j : Fin (C+1)) : holeFunctional F
        (pairAssembly p (j:ℕ) ((C:ℤ)-(j:ℕ)))
        (pairAssembly h (g (j:ℕ)) (-g ((j:ℕ)+1))) = 0 :=
      balanced_child F B C hC (T-(n:ℤ)*C) hF p hp htotal h hbal j (by omega)
    have hi (j : Fin (C+1)) := ih f (pairAssembly B (C:ℤ) C) hf hs
      (pairAssembly p (j:ℕ) ((C:ℤ)-(j:ℕ)))
      (by rw [pairAssembly_inBox]; exact ⟨hp, by omega, by omega⟩)
      (by rw [pairAssembly_sum]; push_cast at ht ⊢; nlinarith)
      (pairAssembly h (g (j:ℕ)) (-g ((j:ℕ)+1))) (hb j)
    have hinc := balanced_potential_bound F B C hC (T-(n:ℤ)*C) hF hFs p hp htotal h hbal
    have hfuture := allRaise_future_monotone C hC n f B T hf hs p h g
    have hsums : (∑ a : Branches C (n+1), holePotential f (leafDisplay C (n+1) p a)
        (leafCoefficient C (n+1) f p h a)) ≤
        (∑ j ∈ Finset.range (C+1), holePotential F
          (pairAssembly p (j:ℤ) ((C:ℤ)-j)) (pairAssembly h (g j) (-g (j+1)))) -
        (∑ j ∈ Finset.range (C+1), matrixForm (twoRemoval (allRaise C n f)
          (pairAssembly p (j:ℤ) ((C:ℤ)-j))) (pairAssembly h (g j) (-g (j+1)))) := by
      change (∑ a : Fin (C+1) × Branches C n, _) ≤ _
      rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_le_sum (fun j _ => hi j)
    have he : matrixForm (twoRemoval (allRaise C (n+1) f) p) h =
        (∑ j ∈ Finset.range (C+2), ((j:ℝ)*(C+1-j)) • pairQ F p (C+1) j) h +
        matrixForm (twoRemoval (balancedMarginal (allRaise C n f) C) p) h := by
      rw [allRaise, matrixForm_twoRemoval_add, matrixForm_raisedFull]
    rw [he]
    change _ ≤ holePotential (balancedMarginal F C) p h - _
    dsimp only at hinc
    linarith

 

theorem leaf_balanced (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f : (PairCoords ι n → ℤ) → ℝ) (B : ι → ℤ) (T : ℤ)
    (hf : PositiveSlice f (pairBox C n B) T)
    (hs : HasSignature f (pairBox C n B) T)
    (p : ι → ℤ) (hp : InBox B p) (ht : (∑ i, p i)+(n:ℤ)*C = T+1)
    (h : ι → ℝ) (hbal : holeFunctional (allBalance C n f) p h = 0)
    (a : Branches C n) :
    holeFunctional f (leafDisplay C n p a) (leafCoefficient C n f p h a) = 0 := by
  induction n generalizing ι with
  | zero => exact hbal
  | succ n ih =>
    let F := allBalance C n f
    let g := pairCumulative (C+1) (pairU F p (C+1)) (pairS F p (C+1)) h
    obtain ⟨hF,hFs⟩ := allBalance_closure C hC n f (pairAssembly B (C:ℤ) C) T hf hs
    have htotal : (∑ i, p i)+(C+1:ℕ) = (T-(n:ℤ)*C)+2 := by
      push_cast at ht ⊢
      nlinarith
    have hb : holeFunctional F
        (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ)))
        (pairAssembly h (g (a.1:ℕ)) (-g ((a.1:ℕ)+1))) = 0 :=
      balanced_child F B C hC (T-(n:ℤ)*C) hF p hp htotal h hbal a.1 (by omega)
    exact ih f (pairAssembly B (C:ℤ) C) hf hs
      (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ)))
      (by rw [pairAssembly_inBox]; exact ⟨hp, by omega, by omega⟩)
      (by rw [pairAssembly_sum]; push_cast at ht ⊢; nlinarith)
      (pairAssembly h (g (a.1:ℕ)) (-g ((a.1:ℕ)+1))) hb a.2

noncomputable def leafStarEnergy (C n : ℕ) (f H : (PairCoords ι n → ℤ) → ℝ)
    (p : ι → ℤ) (center : Branches C n → ℝ) : ℝ :=
  ∑ a : Branches C n, ∑ i : PairCoords ι n,
    f (removeOne (leafDisplay C n p a) i) *
      (H (removeOne (leafDisplay C n p a) i) - center a)^2

 

theorem recursive_star_transport (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f H : (PairCoords ι n → ℤ) → ℝ) (B : ι → ℤ) (T : ℤ)
    (hf : PositiveSlice f (pairBox C n B) T)
    (hs : HasSignature f (pairBox C n B) T)
    (p : ι → ℤ) (hp : InBox B p) (ht : (∑ i, p i)+(n:ℤ)*C = T+1)
    (h : ι → ℝ) (hbal : holeFunctional (allBalance C n f) p h = 0)
    (center : Branches C n → ℝ) :
    (holeFunctional (allBalance C n (fun x => f x * H x)) p h)^2 ≤
      (holePotential (allBalance C n f) p h - matrixForm (twoRemoval (allRaise C n f) p) h) *
        leafStarEnergy C n f H p center := by
  have hleaf (a : Branches C n) :
      (holeFunctional (fun x => f x * H x) (leafDisplay C n p a)
        (leafCoefficient C n f p h a))^2 ≤
      holePotential f (leafDisplay C n p a) (leafCoefficient C n f p h a) *
        ∑ i, f (removeOne (leafDisplay C n p a) i) *
          (H (removeOne (leafDisplay C n p a) i) - center a)^2 := by
    have hh := weighted_star_bound (fun i => f (removeOne (leafDisplay C n p a) i))
      (leafCoefficient C n f p h a) (fun i => H (removeOne (leafDisplay C n p a) i))
      (fun i => hf.nonneg _) (leaf_balanced C hC n f B T hf hs p hp ht h hbal a) (center a)
    have he : holeFunctional (fun x => f x * H x) (leafDisplay C n p a)
        (leafCoefficient C n f p h a) =
        ∑ i, f (removeOne (leafDisplay C n p a) i) * leafCoefficient C n f p h a i *
          H (removeOne (leafDisplay C n p a) i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact hh
  have he (a : Branches C n) : 0 ≤ ∑ i, f (removeOne (leafDisplay C n p a) i) *
      (H (removeOne (leafDisplay C n p a) i) - center a)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hf.nonneg _) (sq_nonneg _))
  have hphi (a : Branches C n) :
      0 ≤ holePotential f (leafDisplay C n p a) (leafCoefficient C n f p h a) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hf.nonneg _) (sq_nonneg _))
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Branches C n))
    (fun a _ => hphi a) (fun a _ => he a) (fun a _ => hleaf a)
  rw [leaf_demand_conservation C n f B hf.boxSupported H p h] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (leaf_potential_bound C hC n f B T hf hs p hp ht h hbal)
    (Finset.sum_nonneg (fun a _ => he a)))

end LeafPotential

end Contingency

 

 

open scoped BigOperators

namespace Contingency

universe u

section Holes
variable {ι : Type u} [DecidableEq ι]

theorem removeOne_injective (p : ι → ℤ) : Function.Injective (removeOne p) := by
  intro i j he
  by_contra hn
  have hi := congrFun he i
  simp [removeOne, hn] at hi

theorem removeOne_sup (p : ι → ℤ) (i j : ι) (hij : i ≠ j) :
    removeOne p i ⊔ removeOne p j = p := by
  funext k
  change max (p k - if k = i then 1 else 0) (p k - if k = j then 1 else 0) = p k
  by_cases hki : k = i
  · subst k
    simp only [ite_eq_right hij, sub_zero]
    exact max_eq_right (by omega)
  · simp only [ite_eq_right hki, sub_zero]
    exact max_eq_left (by split_ifs <;> omega)

 

theorem holeEdge_display {p q : ι → ℤ} {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (he : s(removeOne p i, removeOne p j) = s(removeOne q k, removeOne q l)) : p = q := by
  have hm := congrArg (Sym2.lift ⟨fun x y : ι → ℤ => x ⊔ y, fun x y => sup_comm x y⟩) he
  simpa only [Sym2.lift_mk, removeOne_sup p i j hij, removeOne_sup q k l hkl] using hm

end Holes

 

theorem leafDisplay_inj {ι : Type u} (C n : ℕ) (p q : ι → ℤ)
    (a b : Branches C n) (he : leafDisplay C n p a = leafDisplay C n q b) :
    p = q ∧ a = b := by
  induction n generalizing ι with
  | zero => exact ⟨he, Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨hp,ht⟩ := ih (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ)))
      (pairAssembly q (b.1:ℕ) ((C:ℤ)-(b.1:ℕ))) a.2 b.2 he
    have hbase : p = q := funext fun i => congrFun hp (Sum.inl i)
    have hhead : a.1 = b.1 := by
      apply Fin.ext
      have hh := congrFun hp (Sum.inr true)
      simp only [pairAssembly_first] at hh
      exact_mod_cast hh
    exact ⟨hbase, Prod.ext hhead ht⟩

 
noncomputable def edgeEnergy {X : Type*} (f H : X → ℝ) : Sym2 X → ℝ :=
  Sym2.lift ⟨fun x y => min (f x) (f y) * (H x-H y)^2, by
    intro x y
    dsimp only
    rw [min_comm]
    ring⟩

@[simp] theorem edgeEnergy_mk {X : Type*} (f H : X → ℝ) (x y : X) :
    edgeEnergy f H s(x,y) = min (f x) (f y) * (H x-H y)^2 := rfl

theorem edgeEnergy_nonneg {X : Type*} (f H : X → ℝ) (hf : ∀ x, 0 ≤ f x) (e : Sym2 X) :
    0 ≤ edgeEnergy f H e := by
  induction e using Sym2.ind with
  | _ x y => exact mul_nonneg (le_min (hf x) (hf y)) (sq_nonneg _)

section LeafStars
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

noncomputable def starEdge (C n : ℕ) (p : ι → ℤ)
    (hub : Branches C n → PairCoords ι n) (a : Branches C n × PairCoords ι n) :
    Sym2 (PairCoords ι n → ℤ) :=
  s(removeOne (leafDisplay C n p a.1) a.2, removeOne (leafDisplay C n p a.1) (hub a.1))

noncomputable def starIndices (C n : ℕ) (hub : Branches C n → PairCoords ι n) :
    Finset (Branches C n × PairCoords ι n) := by
  classical
  exact Finset.univ.filter (fun a => a.2 ≠ hub a.1)

noncomputable def leafStarEdges (C n : ℕ) (p : ι → ℤ)
    (hub : Branches C n → PairCoords ι n) : Finset (Sym2 (PairCoords ι n → ℤ)) := by
  classical
  exact (starIndices C n hub).image (starEdge C n p hub)

 

theorem starEdge_injOn (C n : ℕ) (p : ι → ℤ) (hub : Branches C n → PairCoords ι n) :
    Set.InjOn (starEdge C n p hub) (starIndices C n hub : Set _) := by
  classical
  intro a ha b hb he
  have ha' : a.2 ≠ hub a.1 := (Finset.mem_filter.mp ha).2
  have hb' : b.2 ≠ hub b.1 := (Finset.mem_filter.mp hb).2
  have hd := holeEdge_display ha' hb' he
  have hl := (leafDisplay_inj C n p p a.1 b.1 hd).2
  rcases a with ⟨a,i⟩
  rcases b with ⟨b,j⟩
  dsimp only at hl ha' hb'
  subst b
  have hij : i = j := by
    rcases Sym2.eq_iff.mp he with h | h
    · exact removeOne_injective _ h.1
    · exact (ha' (removeOne_injective _ h.1)).elim
  exact congrArg (fun k => (a,k)) hij

 

theorem leafStarEnergy_eq_edges (C n : ℕ) (f H : (PairCoords ι n → ℤ) → ℝ)
    (p : ι → ℤ) (hub : Branches C n → PairCoords ι n)
    (hmax : ∀ a i, f (removeOne (leafDisplay C n p a) i) ≤
      f (removeOne (leafDisplay C n p a) (hub a))) :
    leafStarEnergy C n f H p (fun a => H (removeOne (leafDisplay C n p a) (hub a))) =
      ∑ e ∈ leafStarEdges C n p hub, edgeEnergy f H e := by
  classical
  rw [leafStarEdges, Finset.sum_image (starEdge_injOn C n p hub)]
  rw [starIndices, Finset.sum_filter, leafStarEnergy, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : i = hub a
  · simp [he]
  · simp only [ite_eq_left he, starEdge, edgeEnergy_mk,
      min_eq_left (hmax a i)]

 

theorem leafStarEnergy_le_graph (C n : ℕ) (f H : (PairCoords ι n → ℤ) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (p : ι → ℤ) (hub : Branches C n → PairCoords ι n)
    (hmax : ∀ a i, f (removeOne (leafDisplay C n p a) i) ≤
      f (removeOne (leafDisplay C n p a) (hub a)))
    (E : Finset (Sym2 (PairCoords ι n → ℤ)))
    (hE : ∀ a i, i ≠ hub a → 0 < f (removeOne (leafDisplay C n p a) i) →
      starEdge C n p hub (a,i) ∈ E) :
    leafStarEnergy C n f H p (fun a => H (removeOne (leafDisplay C n p a) (hub a))) ≤
      ∑ e ∈ E, edgeEnergy f H e := by
  classical
  rw [leafStarEnergy_eq_edges C n f H p hub hmax]
  let S := (leafStarEdges C n p hub).filter (fun e => edgeEnergy f H e ≠ 0)
  have he : (∑ e ∈ S, edgeEnergy f H e) = ∑ e ∈ leafStarEdges C n p hub, edgeEnergy f H e := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e he hnot
    have hn := not_and.mp (fun hh => hnot (Finset.mem_filter.mpr hh)) he
    exact Classical.not_not.mp hn
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨he,hne⟩ := Finset.mem_filter.mp he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    have hi : a.2 ≠ hub a.1 := (Finset.mem_filter.mp ha).2
    apply hE a.1 a.2 hi
    have hw : f (removeOne (leafDisplay C n p a.1) a.2) ≠ 0 := by
      intro hz
      apply hne
      change min (f (removeOne (leafDisplay C n p a.1) a.2))
        (f (removeOne (leafDisplay C n p a.1) (hub a.1))) * _ = 0
      rw [min_eq_left (hmax a.1 a.2), hz, zero_mul]
    exact lt_of_le_of_ne (hf _) (Ne.symm hw)
  · intro e _ _
    exact edgeEnergy_nonneg f H hf e

end LeafStars

end Contingency

end

end OAI
