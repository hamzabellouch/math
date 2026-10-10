import Mathlib
import OAI.Probability.SKFluctuations.ClockForkCost

namespace OAI

/-! Clock Pair Fork Ledger. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

 
def pairAbsSum {as : List PositiveMass} (T : ClockTree S as)
    (F : (p : MarkedPlacement T) → MarkedPlacement p.tree → ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p => |p.coeff| *
    ((p.tree.markedAttach 0).map fun s => |s.coeff| * F p s).sum).sum

theorem pairAbsSum_mono {as : List PositiveMass} (T : ClockTree S as)
    {F G : (p : MarkedPlacement T) → MarkedPlacement p.tree → ℝ}
    (h : ∀ p ∈ T.markedAttach 0, ∀ s ∈ p.tree.markedAttach 0, F p s ≤ G p s) :
    T.pairAbsSum F ≤ T.pairAbsSum G := by
  apply List.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply List.sum_le_sum
  intro s hs
  exact mul_le_mul_of_nonneg_left (h p hp s hs) (abs_nonneg _)

theorem pairAbsSum_const_mul {as : List PositiveMass} (T : ClockTree S as)
    (c : ℝ) (F : (p : MarkedPlacement T) → MarkedPlacement p.tree → ℝ) :
    T.pairAbsSum (fun p s => c*F p s) = c*T.pairAbsSum F := by
  simp only [pairAbsSum,mul_left_comm _ c,List.sum_map_mul_left]

theorem pairAbsSum_add {as : List PositiveMass} (T : ClockTree S as)
    (F G : (p : MarkedPlacement T) → MarkedPlacement p.tree → ℝ) :
    T.pairAbsSum (fun p s => F p s+G p s) = T.pairAbsSum F+T.pairAbsSum G := by
  simp only [pairAbsSum,mul_add,List.sum_map_add]

theorem pairAbsSum_nonneg {as : List PositiveMass} (T : ClockTree S as)
    {F : (p : MarkedPlacement T) → MarkedPlacement p.tree → ℝ}
    (h : ∀ p ∈ T.markedAttach 0, ∀ s ∈ p.tree.markedAttach 0, 0 ≤ F p s) :
    0 ≤ T.pairAbsSum F := by
  have hx := T.pairAbsSum_mono h
  simp only [pairAbsSum,mul_zero,List.sum_map_zero] at hx
  exact hx

theorem abs_list_sum_le (xs : List ℝ) : |xs.sum| ≤ (xs.map (fun x => |x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.sum_cons,List.map_cons] using (abs_add_le x xs.sum).trans (add_le_add (le_refl |x|) ih)

theorem signedPair_abs_le_pairAbsSum {as : List PositiveMass} (T : ClockTree S as)
    (F : (p : MarkedPlacement T) → MarkedPlacement p.tree → ℝ) :
    |((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun s => s.coeff*F p s).sum).sum| ≤
      T.pairAbsSum (fun p s => |F p s|) := by
  apply (abs_list_sum_le _).trans
  simp only [List.map_map,Function.comp_def,abs_mul,pairAbsSum]
  apply List.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [List.map_map,Function.comp_def,abs_mul] using
    (abs_list_sum_le ((p.tree.markedAttach 0).map fun s => s.coeff*F p s))

theorem pairAbsSum_constant_le {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) {r : ℕ} (hT : T.leaves ≤ r) {D : ℝ} (hD : 0 ≤ D) :
    T.pairAbsSum (fun _ _ => D) ≤ 4*(r:ℝ)*(r+1)*D := by
  have hinner (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0) :
      ((p.tree.markedAttach 0).map fun s => |s.coeff| * D).sum ≤ 2*((r:ℝ)+1)*D := by
    rw [List.sum_map_mul_right,p.tree.markedAttach_variation ho,sub_zero]
    have hh := (T.markedAttach_leaves 0 p hp).trans (Nat.add_le_add_right hT 1)
    apply mul_le_mul_of_nonneg_right _ hD
    have hr : (p.tree.leaves:ℝ) ≤ (r:ℝ)+1 := by exact_mod_cast hh
    linarith
  have h : T.pairAbsSum (fun _ _ => D) ≤
      ((T.markedAttach 0).map fun p => |p.coeff| * (2*((r:ℝ)+1)*D)).sum := by
    exact List.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hinner p hp) (abs_nonneg _))
  rw [List.sum_map_mul_right,T.markedAttach_variation ho,sub_zero] at h
  have hr : (T.leaves:ℝ) ≤ r := by exact_mod_cast hT
  have hx := mul_le_mul_of_nonneg_right hr (show 0 ≤ 2*(2*((r:ℝ)+1)*D) by positivity)
  nlinarith

def pairForkVariation (r : ℕ) : ℝ := forkVariation r 2+4*(r:ℝ)*(r+1)

theorem pairForkVariation_nonneg (r : ℕ) : 0 ≤ pairForkVariation r :=
  add_nonneg (forkVariation_nonneg r 2) (by positivity)

 

theorem pairAbsSum_forkBudget_le {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) {r : ℕ} (hT : T.leaves ≤ r)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) {d : ℝ} (hd : 0 ≤ d) :
    T.pairAbsSum (fun _ s => s.tree.forkCost f+edgeBudget 0 as f+d) ≤
      pairForkVariation r*(T.forkCost f+edgeBudget 0 as f+d) := by
  rw [T.pairAbsSum_add (fun _ s => s.tree.forkCost f+edgeBudget 0 as f) (fun _ _ => d),
    T.pairAbsSum_add (fun _ s => s.tree.forkCost f) (fun _ _ => edgeBudget 0 as f)]
  have h₁ := T.forkLedger_le ho hf hT 2
  have h₂ := T.pairAbsSum_constant_le ho hT (edgeBudget_nonneg ho hf)
  have h₃ := T.pairAbsSum_constant_le ho hT hd
  change T.pairAbsSum (fun _ s => s.tree.forkCost f) ≤ _ at h₁
  have hF := T.forkCost_nonneg hf
  have hB := edgeBudget_nonneg ho hf
  have hC := forkVariation_nonneg r 2
  have hr : (0:ℝ) ≤ r := Nat.cast_nonneg _
  dsimp only [pairForkVariation]
  have h4 : 0 ≤ 4*(r:ℝ)*(r+1)*T.forkCost f := by positivity
  have h5 : 0 ≤ forkVariation r 2*d := mul_nonneg hC hd
  nlinarith

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations
open scoped BigOperators

 

theorem weighted_holder {ι : Type*} (s : Finset ι) (w A B : ι → ℝ)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hA : ∀ i ∈ s, 0 ≤ A i) (hB : ∀ i ∈ s, 0 ≤ B i) :
    ∑ i ∈ s, w i*A i^(1/p)*B i^(1/q) ≤
      (∑ i ∈ s, w i*A i)^(1/p)*(∑ i ∈ s, w i*B i)^(1/q) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
    (f := fun i => (w i*A i)^(1/p)) (g := fun i => (w i*B i)^(1/q))
    (fun i hi => Real.rpow_nonneg (mul_nonneg (hw i hi) (hA i hi)) _)
    (fun i hi => Real.rpow_nonneg (mul_nonneg (hw i hi) (hB i hi)) _)
  have hh : ∑ i ∈ s, (w i*A i)^(1/p)*(w i*B i)^(1/q) =
      ∑ i ∈ s, w i*A i^(1/p)*B i^(1/q) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.mul_rpow (hw i hi) (hA i hi),Real.mul_rpow (hw i hi) (hB i hi)]
    calc
      _ = (w i^(1/p)*w i^(1/q))*(A i^(1/p)*B i^(1/q)) := by ring
      _ = _ := by
        rw [← Real.rpow_add_of_nonneg (hw i hi) (one_div_nonneg.mpr hpq.nonneg)
          (one_div_nonneg.mpr hpq.symm.nonneg),
          show 1/p+1/q=1 by simpa only [one_div] using hpq.inv_add_inv_eq_one,Real.rpow_one]
        ring
  rw [hh] at h
  have h₁ : ∑ i ∈ s, ((w i*A i)^(1/p))^p = ∑ i ∈ s, w i*A i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (mul_nonneg (hw i hi) (hA i hi)),one_div_mul_cancel hpq.pos.ne',Real.rpow_one]
  have h₂ : ∑ i ∈ s, ((w i*B i)^(1/q))^q = ∑ i ∈ s, w i*B i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (mul_nonneg (hw i hi) (hB i hi)),one_div_mul_cancel hpq.symm.pos.ne',Real.rpow_one]
  rwa [h₁,h₂] at h

theorem list_weighted_holder {ι : Type*} (xs : List ι) (w A B : ι → ℝ)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hw : ∀ i ∈ xs, 0 ≤ w i) (hA : ∀ i ∈ xs, 0 ≤ A i) (hB : ∀ i ∈ xs, 0 ≤ B i) :
    (xs.map fun i => w i*A i^(1/p)*B i^(1/q)).sum ≤
      (xs.map fun i => w i*A i).sum^(1/p)*(xs.map fun i => w i*B i).sum^(1/q) := by
  have h := weighted_holder Finset.univ (fun i : Fin xs.length => w (xs.get i))
    (fun i => A (xs.get i)) (fun i => B (xs.get i)) hpq
    (fun i _ => hw _ (List.get_mem _ _)) (fun i _ => hA _ (List.get_mem _ _))
    (fun i _ => hB _ (List.get_mem _ _))
  have hs (f : ι → ℝ) : (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
    rw [← List.sum_ofFn,List.ofFn_comp',List.ofFn_get]
  change (∑ i : Fin xs.length, (fun z => w z*A z^(1/p)*B z^(1/q)) (xs.get i)) ≤
    (∑ i : Fin xs.length, (fun z => w z*A z) (xs.get i))^(1/p)*
    (∑ i : Fin xs.length, (fun z => w z*B z) (xs.get i))^(1/q) at h
  rw [← hs (fun z => w z*A z^(1/p)*B z^(1/q)),
    ← hs (fun z => w z*A z),← hs (fun z => w z*B z)]
  exact h

end SKFluctuations

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

 

theorem pairAbsSum_holder {as : List PositiveMass} (T : ClockTree S as)
    (F G : (p : MarkedPlacement T) → MarkedPlacement p.tree → ℝ)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hF : ∀ a ∈ T.markedAttach 0, ∀ b ∈ a.tree.markedAttach 0, 0 ≤ F a b)
    (hG : ∀ a ∈ T.markedAttach 0, ∀ b ∈ a.tree.markedAttach 0, 0 ≤ G a b) :
    T.pairAbsSum (fun a b => F a b^(1/p)*G a b^(1/q)) ≤
      (T.pairAbsSum F)^(1/p)*(T.pairAbsSum G)^(1/q) := by
  let A (a : MarkedPlacement T) :=
    ((a.tree.markedAttach 0).map fun b => |b.coeff| *F a b).sum
  let B (a : MarkedPlacement T) :=
    ((a.tree.markedAttach 0).map fun b => |b.coeff| *G a b).sum
  have hA (a : MarkedPlacement T) (ha : a ∈ T.markedAttach 0) : 0 ≤ A a := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (abs_nonneg _) (hF a ha b hb)
  have hB (a : MarkedPlacement T) (ha : a ∈ T.markedAttach 0) : 0 ≤ B a := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (abs_nonneg _) (hG a ha b hb)
  have hi : T.pairAbsSum (fun a b => F a b^(1/p)*G a b^(1/q)) ≤
      ((T.markedAttach 0).map fun a => |a.coeff| *A a^(1/p)*B a^(1/q)).sum := by
    apply List.sum_le_sum
    intro a ha
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [A,B,mul_assoc] using
      (list_weighted_holder (a.tree.markedAttach 0) (fun b => |b.coeff|) (F a) (G a) hpq
        (fun b _ => abs_nonneg _) (hF a ha) (hG a ha))
  exact hi.trans (list_weighted_holder (T.markedAttach 0) (fun a => |a.coeff|) A B hpq
    (fun a _ => abs_nonneg _) hA hB)

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

def errorJetVariation : ℕ → ℕ → ℕ → ℝ
  | r, 0, l => jetVariation (r+2) l*pairForkVariation r
  | r, k+1, l => errorJetVariation (r+2) k l*pairForkVariation r

theorem errorJetVariation_nonneg (r k l : ℕ) : 0 ≤ errorJetVariation r k l := by
  induction k generalizing r with
  | zero => exact mul_nonneg (jetVariation_nonneg _ _) (pairForkVariation_nonneg _)
  | succ k ih => exact mul_nonneg (ih _) (pairForkVariation_nonneg _)

omit [Nonempty S] in
 
theorem rootProfileJets_cons_abs_le (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    |rootProfileJets w φ q₀ q x (K::Ks) T P| ≤
      T.pairAbsSum (fun p s => |rootProfileJets w φ q₀ q x Ks s.tree (profilePairTest P K p s)|) := by
  rw [rootProfileJets,abs_div,show |(2:ℝ)|=2 by norm_num]
  have h := T.signedPair_abs_le_pairAbsSum
    (fun p s => rootProfileJets w φ q₀ q x Ks s.tree (profilePairTest P K p s))
  have hn := T.pairAbsSum_nonneg (fun p _ s _ =>
    abs_nonneg (rootProfileJets w φ q₀ q x Ks s.tree (profilePairTest P K p s)))
  linarith

 

theorem rootProfileJets_oneError_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (pre post : List (ℕ → S → S → ℝ))
    (E : ℕ → S → S → ℝ) (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hP : ∀ σ, |P σ| ≤ C)
    (hpre : ∀ K ∈ pre, ∀ j σ τ, |K j σ τ| ≤ M)
    (hsuf : ∀ K ∈ post, ∀ j σ τ, |K j σ τ| ≤ M)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) {d : ℝ} (hd : 0 ≤ d)
    (hdiag : ∀ σ, |E as.length σ σ| ≤ d) (x : Fin (n+1) → ℝ)
    (he : ∀ j, pairRootMean w φ as q₀ q j (fun σ τ => |E j σ τ|) x ≤ f j) :
    |rootProfileJets w φ q₀ q x (pre++E::post) T P| ≤
      errorJetVariation r pre.length post.length*C*M^(pre.length+post.length)*
        (T.forkCost f+edgeBudget 0 as f+d) := by
  induction pre generalizing T r C with
  | nil =>
    apply (T.rootProfileJets_cons_abs_le w φ P E post q₀ q x).trans
    have hb := T.pairAbsSum_forkBudget_le ho hT hf hd
    have hbase : T.pairAbsSum (fun p s =>
        |rootProfileJets w φ q₀ q x post s.tree (profilePairTest P E p s)|) ≤
        (jetVariation (r+2) post.length*C*M^post.length)*
          T.pairAbsSum (fun _ s => s.tree.forkCost f+edgeBudget 0 as f+d) := by
      rw [← T.pairAbsSum_const_mul]
      apply T.pairAbsSum_mono
      intro p hp s hs
      have hl : s.tree.leaves ≤ r+2 := by
        have h₁ := T.markedAttach_leaves 0 p hp
        have h₂ := p.tree.markedAttach_leaves 0 s hs
        omega
      have hrel := rootProfileJets_relative_abs_le hw φ ho post s.tree hl
        (profilePairTest P E p s) hM hsuf q₀ q x
      have he1 := T.profilePairTest_root_envelope hw φ ho q₀ q P hC hP E hf hd hdiag x he p s
      have he2 : s.tree.rootExpect w φ (fun σ => |profilePairTest P E p s σ|) q₀ q x ≤
          C*(s.tree.forkCost f+edgeBudget 0 as f+d) := by
        apply he1.trans
        apply mul_le_mul_of_nonneg_left _ hC
        linarith [edgeBudget_nonneg ho hf]
      calc
        _ ≤ jetVariation (r+2) post.length*
            (C*(s.tree.forkCost f+edgeBudget 0 as f+d))*M^post.length :=
          hrel.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left he2 (jetVariation_nonneg _ _)) (pow_nonneg hM _))
        _ = _ := by ring
    apply hbase.trans
    have hscale : 0 ≤ jetVariation (r+2) post.length*C*M^post.length :=
      mul_nonneg (mul_nonneg (jetVariation_nonneg _ _) hC) (pow_nonneg hM _)
    have hh := mul_le_mul_of_nonneg_left hb hscale
    simpa only [List.length_nil,zero_add,errorJetVariation,mul_assoc,mul_left_comm,mul_comm] using hh
  | cons K pre ih =>
    apply (T.rootProfileJets_cons_abs_le w φ P K (pre++E::post) q₀ q x).trans
    have hb := T.pairAbsSum_forkBudget_le ho hT hf hd
    let D := errorJetVariation (r+2) pre.length post.length*(C*M)*M^(pre.length+post.length)
    have hD : 0 ≤ D := mul_nonneg
      (mul_nonneg (errorJetVariation_nonneg _ _ _) (mul_nonneg hC hM)) (pow_nonneg hM _)
    have hbase : T.pairAbsSum (fun p s =>
        |rootProfileJets w φ q₀ q x (pre++E::post) s.tree (profilePairTest P K p s)|) ≤
        D*T.pairAbsSum (fun _ s => s.tree.forkCost f+edgeBudget 0 as f+d) := by
      rw [← T.pairAbsSum_const_mul]
      apply T.pairAbsSum_mono
      intro p hp s hs
      have hl : s.tree.leaves ≤ r+2 := by
        have h₁ := T.markedAttach_leaves 0 p hp
        have h₂ := p.tree.markedAttach_leaves 0 s hs
        omega
      apply ih s.tree hl (profilePairTest P K p s) (mul_nonneg hC hM) _
        (fun L hL => hpre L (List.mem_cons_of_mem _ hL))
      intro σ
      rw [profilePairTest,abs_mul]
      exact mul_le_mul (hP _) (hpre K List.mem_cons_self _ _ _) (abs_nonneg _) hC
    apply hbase.trans
    apply (mul_le_mul_of_nonneg_left hb hD).trans_eq
    change D*_ = (errorJetVariation (r+2) pre.length post.length*pairForkVariation r)*C*
      M^((pre.length+1)+post.length)*_
    rw [show (pre.length+1)+post.length = (pre.length+post.length)+1 by omega,pow_succ]
    dsimp only [D]
    ring

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

def rootAbsProfileJets (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) : List (ℕ → S → S → ℝ) →
      (T : ClockTree S as) → (T.Assignment → ℝ) → ℝ
  | [], T, P => T.rootExpect w φ (fun σ => |P σ|) q₀ q x
  | K::Ks, T, P => T.pairAbsSum (fun a b =>
      rootAbsProfileJets w φ q₀ q x Ks b.tree (profilePairTest P K a b))

theorem rootAbsProfileJets_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) (Ks : List (ℕ → S → S → ℝ))
    (T : ClockTree S as) (P : T.Assignment → ℝ) :
    0 ≤ rootAbsProfileJets w φ q₀ q x Ks T P := by
  induction Ks generalizing T with
  | nil => exact T.rootExpect_nonneg hw φ ho (fun σ => abs_nonneg _) q₀ q x
  | cons K Ks ih => exact T.pairAbsSum_nonneg (fun a _ b _ => ih b.tree _)

theorem rootProfileJets_le_absoluteLedger {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) (Ks : List (ℕ → S → S → ℝ))
    (T : ClockTree S as) (P : T.Assignment → ℝ) :
    |rootProfileJets w φ q₀ q x Ks T P| ≤ rootAbsProfileJets w φ q₀ q x Ks T P := by
  induction Ks generalizing T with
  | nil => exact T.abs_rootExpect_le hw φ ho P q₀ q x
  | cons K Ks ih =>
    exact (T.rootProfileJets_cons_abs_le w φ P K Ks q₀ q x).trans
      (T.pairAbsSum_mono fun a _ b _ => ih b.tree _)

omit [Fintype S] [Nonempty S] in
theorem profilePairTest_mul {as : List PositiveMass} (T : ClockTree S as)
    (P Q : T.Assignment → ℝ) (K L : ℕ → S → S → ℝ)
    (a : MarkedPlacement T) (b : MarkedPlacement a.tree) :
    profilePairTest (fun σ => P σ*Q σ) (fun j σ τ => K j σ τ*L j σ τ) a b =
      fun σ => profilePairTest P K a b σ*profilePairTest Q L a b σ := by
  funext σ
  simp only [profilePairTest]
  ring

omit [Fintype S] [Nonempty S] in
theorem profilePairTest_abs_rpow {as : List PositiveMass} (T : ClockTree S as)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (p : ℝ)
    (a : MarkedPlacement T) (b : MarkedPlacement a.tree) :
    profilePairTest (fun σ => |P σ|^p) (fun j σ τ => |K j σ τ|^p) a b =
      fun σ => |profilePairTest P K a b σ|^p := by
  funext σ
  simp only [profilePairTest,abs_mul,Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

 

theorem rootAbsProfileJets_holder {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) {ι : Type*} (is : List ι) (K L : ι → ℕ → S → S → ℝ)
    (T : ClockTree S as) (P Q : T.Assignment → ℝ)
    {p s : ℝ} (hps : p.HolderConjugate s) :
    rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => K i j σ τ*L i j σ τ)
      T (fun σ => P σ*Q σ) ≤
      (rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |K i j σ τ|^p)
        T (fun σ => |P σ|^p))^(1/p)*
      (rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |L i j σ τ|^s)
        T (fun σ => |Q σ|^s))^(1/s) := by
  induction is generalizing T with
  | nil =>
    simpa only [List.map_nil,rootAbsProfileJets,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      using T.rootExpect_holder hw φ ho P Q q₀ q x hps
  | cons i is ih =>
    simp only [List.map_cons,rootAbsProfileJets]
    let F (a : MarkedPlacement T) (b : MarkedPlacement a.tree) :=
      rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |K i j σ τ|^p)
        b.tree (profilePairTest (fun σ => |P σ|^p) (fun j σ τ => |K i j σ τ|^p) a b)
    let G (a : MarkedPlacement T) (b : MarkedPlacement a.tree) :=
      rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |L i j σ τ|^s)
        b.tree (profilePairTest (fun σ => |Q σ|^s) (fun j σ τ => |L i j σ τ|^s) a b)
    have hi : T.pairAbsSum (fun a b =>
        rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => K i j σ τ*L i j σ τ)
          b.tree (profilePairTest (fun σ => P σ*Q σ)
            (fun j σ τ => K i j σ τ*L i j σ τ) a b)) ≤
        T.pairAbsSum (fun a b => F a b^(1/p)*G a b^(1/s)) := by
      apply T.pairAbsSum_mono
      intro a ha b hb
      dsimp [F,G]
      rw [T.profilePairTest_mul,T.profilePairTest_abs_rpow,T.profilePairTest_abs_rpow]
      exact ih b.tree (profilePairTest P (K i) a b) (profilePairTest Q (L i) a b)
    exact hi.trans (T.pairAbsSum_holder F G hps
      (fun a _ b _ => rootAbsProfileJets_nonneg hw φ ho q₀ q x _ b.tree _)
      (fun a _ b _ => rootAbsProfileJets_nonneg hw φ ho q₀ q x _ b.tree _))

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

def absJetVariation : ℕ → ℕ → ℝ
  | _, 0 => 1
  | r, k+1 => 4*(r:ℝ)*(r+1)*absJetVariation (r+2) k

theorem absJetVariation_nonneg (r k : ℕ) : 0 ≤ absJetVariation r k := by
  induction k generalizing r with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (by positivity) (ih _)

 

theorem rootAbsProfileJets_relative_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ K ∈ Ks, ∀ j σ τ, |K j σ τ| ≤ M)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    rootAbsProfileJets w φ q₀ q x Ks T P ≤
      absJetVariation r Ks.length*T.rootExpect w φ (fun σ => |P σ|) q₀ q x*M^Ks.length := by
  induction Ks generalizing T r with
  | nil => simp only [rootAbsProfileJets,absJetVariation,List.length_nil,pow_zero,mul_one,one_mul,le_refl]
  | cons K Ks ih =>
    let E := T.rootExpect w φ (fun σ => |P σ|) q₀ q x
    let D := absJetVariation (r+2) Ks.length*(M*E)*M^Ks.length
    have hE : 0 ≤ E := T.rootExpect_nonneg hw φ ho (fun σ => abs_nonneg _) q₀ q x
    have hD : 0 ≤ D := mul_nonneg
      (mul_nonneg (absJetVariation_nonneg _ _) (mul_nonneg hM hE)) (pow_nonneg hM _)
    have hi : T.pairAbsSum (fun p s =>
        rootAbsProfileJets w φ q₀ q x Ks s.tree (profilePairTest P K p s)) ≤
        T.pairAbsSum (fun _ _ => D) := by
      apply T.pairAbsSum_mono
      intro p hp s hs
      have hleaf : s.tree.leaves ≤ r+2 := by
        have h₁ := T.markedAttach_leaves 0 p hp
        have h₂ := p.tree.markedAttach_leaves 0 s hs
        omega
      apply (ih s.tree hleaf (profilePairTest P K p s)
        (fun L hL => hK L (List.mem_cons_of_mem _ hL))).trans
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM _)
      apply mul_le_mul_of_nonneg_left _ (absJetVariation_nonneg _ _)
      exact T.profilePairTest_root_abs_le hw φ ho P K (hK K List.mem_cons_self) p hp s hs q₀ q x
    apply (hi.trans (T.pairAbsSum_constant_le ho hT hD)).trans_eq
    simp only [D,E,List.length_cons,absJetVariation,pow_succ]
    ring

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

def absErrorJetVariation : ℕ → ℕ → ℕ → ℝ
  | r, 0, l => absJetVariation (r+2) l*pairForkVariation r
  | r, k+1, l => absErrorJetVariation (r+2) k l*pairForkVariation r

theorem absErrorJetVariation_nonneg (r k l : ℕ) : 0 ≤ absErrorJetVariation r k l := by
  induction k generalizing r with
  | zero => exact mul_nonneg (absJetVariation_nonneg _ _) (pairForkVariation_nonneg _)
  | succ k ih => exact mul_nonneg (ih _) (pairForkVariation_nonneg _)

 

theorem rootAbsProfileJets_oneError_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (pre post : List (ℕ → S → S → ℝ))
    (E : ℕ → S → S → ℝ) (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hP : ∀ σ, |P σ| ≤ C)
    (hpre : ∀ K ∈ pre, ∀ j σ τ, |K j σ τ| ≤ M)
    (hsuf : ∀ K ∈ post, ∀ j σ τ, |K j σ τ| ≤ M)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) {d : ℝ} (hd : 0 ≤ d)
    (hdiag : ∀ σ, |E as.length σ σ| ≤ d) (x : Fin (n+1) → ℝ)
    (he : ∀ j, pairRootMean w φ as q₀ q j (fun σ τ => |E j σ τ|) x ≤ f j) :
    rootAbsProfileJets w φ q₀ q x (pre++E::post) T P ≤
      absErrorJetVariation r pre.length post.length*C*M^(pre.length+post.length)*
        (T.forkCost f+edgeBudget 0 as f+d) := by
  induction pre generalizing T r C with
  | nil =>
    change T.pairAbsSum _ ≤ _
    have hb := T.pairAbsSum_forkBudget_le ho hT hf hd
    have hbase : T.pairAbsSum (fun p s =>
        rootAbsProfileJets w φ q₀ q x post s.tree (profilePairTest P E p s)) ≤
        (absJetVariation (r+2) post.length*C*M^post.length)*
          T.pairAbsSum (fun _ s => s.tree.forkCost f+edgeBudget 0 as f+d) := by
      rw [← T.pairAbsSum_const_mul]
      apply T.pairAbsSum_mono
      intro p hp s hs
      have hl : s.tree.leaves ≤ r+2 := by
        have h₁ := T.markedAttach_leaves 0 p hp
        have h₂ := p.tree.markedAttach_leaves 0 s hs
        omega
      have hrel := rootAbsProfileJets_relative_le hw φ ho post s.tree hl
        (profilePairTest P E p s) hM hsuf q₀ q x
      have he1 := T.profilePairTest_root_envelope hw φ ho q₀ q P hC hP E hf hd hdiag x he p s
      have he2 : s.tree.rootExpect w φ (fun σ => |profilePairTest P E p s σ|) q₀ q x ≤
          C*(s.tree.forkCost f+edgeBudget 0 as f+d) := by
        apply he1.trans
        apply mul_le_mul_of_nonneg_left _ hC
        linarith [edgeBudget_nonneg ho hf]
      calc
        _ ≤ absJetVariation (r+2) post.length*
            (C*(s.tree.forkCost f+edgeBudget 0 as f+d))*M^post.length :=
          hrel.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left he2 (absJetVariation_nonneg _ _)) (pow_nonneg hM _))
        _ = _ := by ring
    apply hbase.trans
    have hscale : 0 ≤ absJetVariation (r+2) post.length*C*M^post.length :=
      mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hC) (pow_nonneg hM _)
    have hh := mul_le_mul_of_nonneg_left hb hscale
    simpa only [List.length_nil,zero_add,absErrorJetVariation,mul_assoc,mul_left_comm,mul_comm] using hh
  | cons K pre ih =>
    change T.pairAbsSum _ ≤ _
    have hb := T.pairAbsSum_forkBudget_le ho hT hf hd
    let D := absErrorJetVariation (r+2) pre.length post.length*(C*M)*M^(pre.length+post.length)
    have hD : 0 ≤ D := mul_nonneg
      (mul_nonneg (absErrorJetVariation_nonneg _ _ _) (mul_nonneg hC hM)) (pow_nonneg hM _)
    have hbase : T.pairAbsSum (fun p s =>
        rootAbsProfileJets w φ q₀ q x (pre++E::post) s.tree (profilePairTest P K p s)) ≤
        D*T.pairAbsSum (fun _ s => s.tree.forkCost f+edgeBudget 0 as f+d) := by
      rw [← T.pairAbsSum_const_mul]
      apply T.pairAbsSum_mono
      intro p hp s hs
      have hl : s.tree.leaves ≤ r+2 := by
        have h₁ := T.markedAttach_leaves 0 p hp
        have h₂ := p.tree.markedAttach_leaves 0 s hs
        omega
      apply ih s.tree hl (profilePairTest P K p s) (mul_nonneg hC hM) _
        (fun L hL => hpre L (List.mem_cons_of_mem _ hL))
      intro σ
      rw [profilePairTest,abs_mul]
      exact mul_le_mul (hP _) (hpre K List.mem_cons_self _ _ _) (abs_nonneg _) hC
    apply hbase.trans
    apply (mul_le_mul_of_nonneg_left hb hD).trans_eq
    change D*_ = (absErrorJetVariation (r+2) pre.length post.length*pairForkVariation r)*C*
      M^((pre.length+1)+post.length)*_
    rw [show (pre.length+1)+post.length = (pre.length+post.length)+1 by omega,pow_succ]
    dsimp only [D]
    ring

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory Set
open scoped BigOperators

 

def edgeDensity (a : ℝ) : List PositiveMass → (ℕ → ℝ) → ℝ → ℝ
  | [], f => (Ioc a 1).indicator (fun _ => f 0)
  | b::as, f => fun u => (Ioc a b.val).indicator (fun _ => f 0) u+
      edgeDensity b.val as (fun j => f (1+j)) u

theorem edgeDensity_integrable (a : ℝ) (as : List PositiveMass) (f : ℕ → ℝ) :
    Integrable (edgeDensity a as f) := by
  induction as generalizing a f with
  | nil => exact (integrableOn_const (C := f 0) (s := Ioc a 1) (μ := volume) measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc
  | cons b as ih =>
    exact
      ((integrableOn_const (C := f 0) (s := Ioc a b.val) (μ := volume) measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc).add
        (ih b.val (fun j => f (1+j)))

theorem edgeDensity_integral {a : ℝ} {as : List PositiveMass}
    (ho : MassOrdered a as) (f : ℕ → ℝ) :
    ∫ u, edgeDensity a as f u = edgeBudget a as f := by
  induction as generalizing a f with
  | nil =>
    simp only [edgeDensity,edgeBudget,integral_indicator_const _ measurableSet_Ioc,
      measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr ho.2),smul_eq_mul]
  | cons b as ih =>
    rw [edgeDensity,integral_add
      ((integrableOn_const (C := f 0) (s := Ioc a b.val) (μ := volume) measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc)
      (edgeDensity_integrable b.val as (fun j => f (1+j))),ih ho.2.2]
    simp only [edgeBudget,integral_indicator_const _ measurableSet_Ioc,
      measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr ho.2.1),smul_eq_mul]

theorem edgeDensity_nonneg (a : ℝ) (as : List PositiveMass) {f : ℕ → ℝ}
    (hf : ∀ j, 0 ≤ f j) (u : ℝ) : 0 ≤ edgeDensity a as f u := by
  induction as generalizing a f with
  | nil => exact indicator_nonneg (fun _ _ => hf 0) u
  | cons b as ih =>
    exact add_nonneg (indicator_nonneg (fun _ _ => hf 0) u)
      (ih b.val (fun j => hf (1+j)))

 

theorem edgeBudget_le_integral {a : ℝ} {as : List PositiveMass}
    (ho : MassOrdered a as) (f : ℕ → ℝ) {F : ℝ → ℝ} (hF : Integrable F)
    (h : ∀ u, edgeDensity a as f u ≤ F u) : edgeBudget a as f ≤ ∫ u, F u := by
  rw [← edgeDensity_integral ho f]
  exact integral_mono (edgeDensity_integrable a as f) hF h

variable {S : Type*}

 

theorem forkLedger_integral_le {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    {r : ℕ} (hT : T.leaves ≤ r) (k : ℕ) :
    forkLedger a f k T ≤ forkVariation r k*(T.forkCost f+∫ u, edgeDensity a as f u) := by
  rw [edgeDensity_integral ha]
  exact T.forkLedger_le ha hf hT k

end SKFluctuations.Hierarchy.ClockTree

end

end OAI
