import OAI.Probability.TraceReconstruction.Energy
import OAI.Probability.TraceReconstruction.Metadata

namespace OAI

/-!
# Simulation

Canonical and filled simulations, central fit, root words, chronology, slots, finite codes, and complete-trace decoding.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Heterogeneous emissions retain their actual outcome type while moving to
 the one fixed public chronological order. -/
theorem dependentProduct_approximates {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀i,Fintype (A i)] {k : ℕ} {q : ℝ} (hq : q∈Set.Icc 0 1)
    (e : Fin k ≃ ι) (P : ∀i,FiniteLaw (A i)) (f : ∀i,A i → List Bool)
    (w : ι → List Bool) (E : ι → ℝ)
    (h : ∀i,ApproximatesTrace q (P i) (f i) (w i) (E i)) :
    ApproximatesTrace q (FiniteLaw.dependentProduct P)
      (fun x => coordinateWord (fun j => f (e j) (x (e j))))
      (coordinateWord (fun j => w (e j))) (∑i,E i) := by
  intro F hF
  let G := Equiv.piCongrLeft A e
  have he (x : ∀j,A (e j)) (j : Fin k) :
      cast (congrArg A (e.apply_symm_apply (e j))) (x (e.symm (e j)))=x j := by
    rw [←Equiv.piCongrLeft_apply_eq_cast]
    exact Equiv.piCongrLeft_apply_apply A e x j
  rw [FiniteLaw.dependentProduct_expect_equiv P e]
  simp_rw [he]
  have H := dependentCoordinate_approximates hq (fun j => P (e j))
    (fun j => f (e j)) (fun j => w (e j)) (fun j => E (e j)) (fun j => h (e j)) F hF
  rwa [e.sum_comp] at H

/-- Each paired mechanism owns two distinct side slots; fillers and old leaf
 oracles have their own IDs. This type is independent of every orientation. -/
abbrev EmissionSlot (m k n : ℕ) := (Fin m × Bool) ⊕ (Fin k ⊕ Fin n)

def EmissionOutcome (Side Leaf : Type) {m k n : ℕ} : EmissionSlot m k n → Type
  | .inl _ => Side
  | .inr (.inl _) => Side
  | .inr (.inr _) => Leaf

instance emissionOutcomeFintype {Side Leaf : Type} [Fintype Side] [Fintype Leaf]
    {m k n : ℕ} (i : EmissionSlot m k n) : Fintype (EmissionOutcome Side Leaf i) := by
  rcases i with a | a
  · exact inferInstanceAs (Fintype Side)
  · rcases a with a | a
    · exact inferInstanceAs (Fintype Side)
    · exact inferInstanceAs (Fintype Leaf)

/-- Actual arrays and slot observations are bijective, not a lossy interface. -/
def emissionAssignmentEquiv (Side Leaf : Type) (m k n : ℕ) :
    ((Fin m → Side × Side) × (Fin k → Side) × (Fin n → Leaf)) ≃
      (∀i : EmissionSlot m k n,EmissionOutcome Side Leaf i) where
  toFun x i := match i with
    | .inl (j,false) => (x.1 j).1
    | .inl (j,true) => (x.1 j).2
    | .inr (.inl j) => x.2.1 j
    | .inr (.inr j) => x.2.2 j
  invFun x := (fun j => (x (.inl (j,false)),x (.inl (j,true))),
    fun j => x (.inr (.inl j)),fun j => x (.inr (.inr j)))
  left_inv x := by
    rcases x with ⟨z,f,l⟩
    change (fun j => ((z j).1,(z j).2),f,l)=(z,f,l)
    simp only [Prod.mk.eta]
  right_inv x := by
    funext i
    rcases i with ⟨j,b⟩ | i
    · cases b <;> rfl
    · cases i <;> rfl

namespace PairedMechanisms
variable {Side Leaf : Type} [Fintype Side] [Fintype Leaf] {m k n : ℕ}
variable (M : PairedMechanisms Side m)

def slotLaw (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (bits : Fin m → Bool) (θ : Fin n → Bool) :
    (i : EmissionSlot m k n) → FiniteLaw (EmissionOutcome Side Leaf i)
  | .inl (j,false) => if bits j then M.second j else M.first j
  | .inl (j,true) => if bits j then M.first j else M.second j
  | .inr (.inl j) => R j
  | .inr (.inr j) => if θ j then Q else P

theorem slotLaw_mass (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (bits : Fin m → Bool) (θ : Fin n → Bool)
    (x : (Fin m → Side × Side) × (Fin k → Side) × (Fin n → Leaf)) :
    (FiniteLaw.dependentProduct (M.slotLaw R P Q bits θ)).mass
      (emissionAssignmentEquiv Side Leaf m k n x)=
    ((FiniteLaw.coordinateProduct (fun j => FiniteLaw.orientedProd (M.first j) (M.second j) (bits j))).prod
      ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ))).mass x := by
  change (∏i : EmissionSlot m k n,_)=_
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type,Fintype.prod_prod_type]
  simp only [Fintype.prod_bool,slotLaw,emissionAssignmentEquiv,Equiv.coe_fn_mk]
  change (∏j : Fin m,_) * ((∏j : Fin k,_) * ∏j : Fin n,_)=
    (∏j : Fin m,_) * ((∏j : Fin k,_) * ∏j : Fin n,_)
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  cases hb : bits j <;> simp [FiniteLaw.orientedProd,hb,FiniteLaw.prod,mul_comm]

theorem slotLaw_expect (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (bits : Fin m → Bool) (θ : Fin n → Bool)
    (F : (∀i : EmissionSlot m k n,EmissionOutcome Side Leaf i) → ℝ) :
    ((FiniteLaw.coordinateProduct (fun j => FiniteLaw.orientedProd (M.first j) (M.second j) (bits j))).prod
      ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ))).expect
        (fun x => F (emissionAssignmentEquiv Side Leaf m k n x))=
      (FiniteLaw.dependentProduct (M.slotLaw R P Q bits θ)).expect F := by
  unfold FiniteLaw.expect
  rw [←(emissionAssignmentEquiv Side Leaf m k n).sum_comp]
  simp_rw [slotLaw_mass]

/-- Forgetting only the visible flags recovers the genuine independent side,
 filler and leaf laws at every orientation, before any fit restriction. -/
theorem reportsGiven_slot_expect (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (bits : Fin m → Bool) (θ : Fin n → Bool)
    (F : (∀i : EmissionSlot m k n,EmissionOutcome Side Leaf i) → ℝ) :
    ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ))).expect
      (fun x => F (emissionAssignmentEquiv Side Leaf m k n (fun j => (x.1 j).2,x.2)))=
      (FiniteLaw.dependentProduct (M.slotLaw R P Q bits θ)).expect F := by
  rw [FiniteLaw.expect_prod]
  change (M.reportsGiven bits).expect ((fun z : Fin m → Side × Side =>
    ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ)).expect
      (fun b => F (emissionAssignmentEquiv Side Leaf m k n (z,b)))) ∘
        (fun z j => (z j).2))=_
  rw [←FiniteLaw.expect_map]
  rw [reportsGiven_forget]
  have H := slotLaw_expect M R P Q bits θ F
  rw [FiniteLaw.expect_prod] at H
  exact H

/-- The common, bit-blind projection simply forgets flags and concatenates in
 the publicly fixed ID order. -/
def slotDecode (f : Side → List Bool) (g : Leaf → List Bool) :
    (i : EmissionSlot m k n) → EmissionOutcome Side Leaf i → List Bool
  | .inl _,x => f x
  | .inr (.inl _),x => f x
  | .inr (.inr _),x => g x

def slotWord (U V : Fin m → List Bool) (W : Fin k → List Bool)
    (atom : Bool → List Bool) (bits : Fin m → Bool) (θ : Fin n → Bool) :
    EmissionSlot m k n → List Bool
  | .inl (j,false) => if bits j then V j else U j
  | .inl (j,true) => if bits j then U j else V j
  | .inr (.inl j) => W j
  | .inr (.inr j) => atom (θ j)

def slotCost (E : ℝ) : EmissionSlot m k n → ℝ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr _) => E

theorem slotCost_sum (E : ℝ) : (∑i : EmissionSlot m k n,slotCost E i)=(n:ℝ)*E := by
  simp only [Fintype.sum_sum_type,slotCost,Finset.sum_const_zero,
    zero_add,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem slotLaw_simulation {q E : ℝ} (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool) (U V : Fin m → List Bool)
    (W : Fin k → List Bool) (atom : Bool → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (U j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (V j))
    (hW : ∀j,SimulatesTrace q (R j) f (W j))
    (hP : ApproximatesTrace q P g (atom false) E) (hQ : ApproximatesTrace q Q g (atom true) E)
    (bits : Fin m → Bool) (θ : Fin n → Bool) (i : EmissionSlot m k n) :
    ApproximatesTrace q (M.slotLaw R P Q bits θ i) (slotDecode f g i)
      (slotWord U V W atom bits θ i) (slotCost E i) := by
  rcases i with ⟨j,b⟩ | i
  · cases b <;> cases hb : bits j <;>
      simp only [slotLaw,slotWord,slotCost,hb,Bool.false_eq_true,ite_false,ite_true]
    · exact (hU j).approximate
    · exact (hV j).approximate
    · exact (hV j).approximate
    · exact (hU j).approximate
  · rcases i with j | j
    · exact (hW j).approximate
    · cases hb : θ j <;> simp only [slotLaw,slotWord,slotCost,hb,Bool.false_eq_true]
      · exact hP
      · exact hQ

/-- Exact conditional-on-orientation simulation boundary. The orientation is
 not part of the common projection, and no fit conditioning enters its law. -/
theorem reportsGiven_simulation {q E : ℝ} (hq : q∈Set.Icc 0 1)
    {L : ℕ} (e : Fin L ≃ EmissionSlot m k n)
    (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool) (U V : Fin m → List Bool)
    (W : Fin k → List Bool) (atom : Bool → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (U j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (V j))
    (hW : ∀j,SimulatesTrace q (R j) f (W j))
    (hP : ApproximatesTrace q P g (atom false) E) (hQ : ApproximatesTrace q Q g (atom true) E)
    (bits : Fin m → Bool) (θ : Fin n → Bool) :
    ApproximatesTrace q
      ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ)))
      (fun x => coordinateWord (fun j => slotDecode f g (e j)
        (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1 i).2,x.2) (e j))))
      (coordinateWord (fun j => slotWord U V W atom bits θ (e j))) ((n:ℝ)*E) := by
  intro F hF
  dsimp only
  rw [M.reportsGiven_slot_expect R P Q bits θ
    (fun z => F (coordinateWord (fun j => slotDecode f g (e j) (z (e j)))))]
  have H := dependentProduct_approximates hq e (M.slotLaw R P Q bits θ) (slotDecode f g)
    (slotWord U V W atom bits θ) (slotCost E)
    (M.slotLaw_simulation R P Q f g U V W atom hU hV hW hP hQ bits θ) F hF
  rwa [slotCost_sum] at H

end PairedMechanisms
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace PairedMechanisms
variable {Side Leaf : Type} [Fintype Side] [Fintype Leaf] {m k n : ℕ}
variable (M : PairedMechanisms Side m)

/-- The actual metadata-first oracle with independent genuine fillers has
 exactly the orientation-first product experiment, in the displayed order. -/
theorem canonical_filled_expect (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (θ : (Fin m → Bool) → Fin n → Bool)
    (F : Reports Side m × (Fin k → Side) × (Fin n → Leaf) → ℝ) :
    ((M.canonicalOracle P Q θ).prod (FiniteLaw.coordinateProduct R)).expect
      (fun x => F (x.1.1,x.2,x.1.2))=
    (fairOrientations m).expect (fun bits =>
      ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod
        (selectedLeafLaw P Q (θ bits)))).expect F) := by
  rw [←M.oracle_factorization,orientationOracle,FiniteLaw.expect_prod,FiniteLaw.expect_mixture]
  simp_rw [FiniteLaw.expect_prod]
  congr 1
  funext bits
  congr 1
  funext z
  exact FiniteLaw.expect_comm _ _ (fun leaf fill => F (z,fill,leaf))

/-- Unconditional common simulation of the actual full canonical oracle.
 The only layout charge is the unconditional fair-orientation failure mass.
 No orientation or side metadata is conditioned on successful fitting. -/
theorem canonical_filled_simulation {q E : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
    {L : ℕ} (e : Fin L ≃ EmissionSlot m k n)
    (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool) (U V : Fin m → List Bool)
    (W : Fin k → List Bool) (atom : Bool → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (U j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (V j))
    (hW : ∀j,SimulatesTrace q (R j) f (W j))
    (hP : ApproximatesTrace q P g (atom false) E) (hQ : ApproximatesTrace q Q g (atom true) E)
    (θ : (Fin m → Bool) → Fin n → Bool) (w : List Bool)
    (good : (Fin m → Bool) → Prop) [DecidablePred good]
    (hword : ∀bits,good bits → coordinateWord
      (fun j => slotWord U V W atom bits (θ bits) (e j))=w) :
    ApproximatesTrace q ((M.canonicalOracle P Q θ).prod (FiniteLaw.coordinateProduct R))
      (fun x => coordinateWord (fun j => slotDecode f g (e j)
        (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1.1 i).2,x.2,x.1.2) (e j))))
      w ((n:ℝ)*E+(fairOrientations m).expect (fun bits => if good bits then 0 else 1)) := by
  intro F hF
  dsimp only
  rw [M.canonical_filled_expect R P Q θ (fun x => F (coordinateWord (fun j => slotDecode f g (e j)
    (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1 i).2,x.2) (e j)))))]
  rw [←FiniteLaw.expect_const (fairOrientations m) (listDeletionExpectation q w F),←FiniteLaw.expect_sub]
  apply (FiniteLaw.abs_expect_le _ _).trans
  calc
    _ ≤ (fairOrientations m).expect (fun bits => (n:ℝ)*E+(if good bits then 0 else 1)) := by
      apply FiniteLaw.expect_mono
      intro bits
      by_cases hb : good bits
      · simp only [ite_eq_left hb,add_zero]
        have H := M.reportsGiven_simulation hq e R P Q f g U V W atom hU hV hW hP hQ bits (θ bits) F hF
        rwa [hword bits hb] at H
      · simp only [ite_eq_right hb]
        have hc := listDeletionExpectation_range hq w F hF
        have hlo := FiniteLaw.expect_mono
          ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q (θ bits))))
          (fun x => (hF (coordinateWord (fun j => slotDecode f g (e j)
            (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1 i).2,x.2) (e j))))).1)
        have hhi := FiniteLaw.expect_mono
          ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q (θ bits))))
          (fun x => (hF (coordinateWord (fun j => slotDecode f g (e j)
            (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1 i).2,x.2) (e j))))).2)
        rw [FiniteLaw.expect_const] at hlo hhi
        have hne : 0≤(n:ℝ)*E := mul_nonneg (Nat.cast_nonneg _) hE
        apply abs_sub_le_iff.mpr
        constructor <;> linarith [hc.1,hc.2]
    _ = _ := by
      unfold FiniteLaw.expect
      simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,(fairOrientations m).total,one_mul]

end PairedMechanisms
end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The one-based source offset still puts the complete motif in the central
 third under the true fit threshold. The stronger numerical margin is an
 eventual consequence of L=o(T), not an additional stochastic event. -/
theorem source_motif_central (T t s : ℕ) (bits : Fin t → Bool) (v : ℤ)
    (hT : 24 ≤ T) (he : Even T) (hL : 24*2^s ≤ T)
    (hfit : |8*((∑i,(bitIndex (bits i):ℤ))-(t/2:ℕ)+v)| ≤ (T:ℤ))
    (u : Fin T)
    (hu : motifIndicator s ((u.val:ℤ)-((T/2:ℕ)-1+(t/2:ℕ))+
      (∑i,(bitIndex (bits i):ℤ))+v)≠0) : u∈centralThird T := by
  have hsupport : 0≤(u.val:ℤ)-((T/2:ℕ)-1+(t/2:ℕ))+
      (∑i,(bitIndex (bits i):ℤ))+v ∧
      (u.val:ℤ)-((T/2:ℕ)-1+(t/2:ℕ))+(∑i,(bitIndex (bits i):ℤ))+v < (2^s:ℕ) := by
    by_contra h
    apply hu
    exact ite_eq_right h
  have hh := abs_le.mp hfit
  obtain ⟨k,hk⟩ := he
  have hhalf : 2*(T/2)=T := by omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  omega

/-- Fit controls every internal source motif, retaining all orientations in
 the law. The incoming displacement of the root is supplied separately. -/
theorem sourceTreeFit_central (T n : ℕ → ℕ) (s b : ℕ)
    (center : ℕ → ℤ) (hc : ∀j≤b,center j=sourceLocalCenter T n j)
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hL : ∀j≤b,24*2^s≤T j)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) (incoming : ℤ)
    (hroot : |8*((∑i,(bitIndex (bits.1 i):ℤ))-(n b/2:ℕ)+incoming)|≤(T b:ℤ))
    (hfit : SourceTreeFit T n (b+1) bits) :
    SourceCentral T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
      (fun j => centralThird (T j)) (b+1) bits incoming := by
  induction b generalizing incoming with
  | zero =>
    constructor
    · intro u hu
      rw [hc 0 (by omega)] at hu
      exact source_motif_central (T 0) (n 0) s bits.1 incoming
        (hT 0 (by omega)) (he 0 (by omega)) (hL 0 (by omega)) hroot u hu
    · intro u; trivial
  | succ b ih =>
    constructor
    · intro u hu
      rw [hc (b+1) (by omega)] at hu
      exact source_motif_central (T (b+1)) (n (b+1)) s bits.1 incoming
        (hT (b+1) (by omega)) (he (b+1) (by omega)) (hL (b+1) (by omega)) hroot u hu
    · intro u
      apply ih (fun j hj => hc j (by omega)) (fun j hj => hT j (by omega))
        (fun j hj => he j (by omega)) (fun j hj => hL j (by omega)) _ _ _ (hfit.2 u)
      exact hfit.1 u

/-- The actual root side count has no parity restriction. Its entire range
 lies inside the fit displacement interval when J=o(T). -/
theorem source_root_fit (T J : ℕ) (bits : Fin J → Bool) (h : 4*(J+1)≤T) :
    |8*((∑i,(bitIndex (bits i):ℤ))-(J/2:ℕ))|≤(T:ℤ) := by
  have hlo : (0:ℤ)≤∑i,(bitIndex (bits i):ℤ) := Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hhi : (∑i,(bitIndex (bits i):ℤ))≤J := by
    calc
      _ ≤ ∑_i : Fin J,(1:ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        cases bits i <;> norm_num [bitIndex]
      _ = J := by simp
  apply abs_le.mpr
  omega

theorem sourceNoncentralMass_le_fit (T n : ℕ → ℕ) (s b : ℕ)
    (center : ℕ → ℤ) (hc : ∀j≤b,center j=sourceLocalCenter T n j)
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hL : ∀j≤b,24*2^s≤T j)
    (hroot : 4*(n b+1)≤T b)
    (d : WindowAssignments T n (sourceScheduledTrials T n) (Option Bool) (b+1)) :
    sourceNoncentralMass T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
      (fun j => centralThird (T j)) (b+1) d 0 ≤
    (windowPosteriorLaw T n (sourceScheduledTrials T n) (b+1) d).expect
      (fun bits => if SourceTreeFit T n (b+1) bits then 0 else 1) := by
  apply FiniteLaw.expect_mono
  intro bits
  by_cases hf : SourceTreeFit T n (b+1) bits
  · have hh := sourceTreeFit_central T n s b center hc hT he hL bits 0
      (by simpa only [add_zero] using source_root_fit (T b) (n b) bits.1 hroot) hf
    simp only [ite_eq_left hf,ite_eq_left hh,le_refl]
  · simp only [ite_eq_right hf]
    split_ifs <;> norm_num

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Only interior trials are paired in even bundles. The top J may be odd. -/
theorem sourceTreeWord_eq_center_interior (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ)
    (atom : Bool → List Bool) (b : ℕ) (H : SourceLayoutMargins s P T n h (b-1))
    (htop : ∀j<b,0<T j)
    (hc : ∀j, j+1<b → center j=sourceLocalCenter T n j)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) (hfit : SourceTreeFit T n b bits) :
    sourceTreeWord s P T n h center atom b bits incoming τ=
      sourceCenterWord s P T n center atom b bits incoming τ := by
  induction b using Nat.twoStepInduction generalizing incoming τ with
  | zero => rfl
  | one => rfl
  | more b ih₁ ih₂ =>
    change (Fin (n (b+1)) → Bool) × (Fin ((T (b+1)/4)*n b) → Bool) ×
      (Fin (T (b+1)) → WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) at bits
    let loc : Fin (T (b+1)) → Fin (n b) → Bool := fun u => (bits.2.2 u).1
    let glob := bits.2.1
    let a := P b/2-1
    let A := sourceNominalPre P T b
    let B := sourceNominalPost P T b
    let start := sourceWindowStart (T (b+1)) A (n b) loc glob
    let θ := integerTemplateType (T (b+1)) s (sourceNodeAnchor T n center (b+1) bits incoming) τ
    have hb : b<b+2-1 := by omega
    have htotal := sourceNominal_total P T b (by have hh := H.ambient b hb; omega)
    have hf (u : Fin (T (b+1))) := sourceWindowStart_oneBased_fit (T (b+1)) (P b) (T b) (n b)
      (2^s) loc glob (H.ambient b hb) (H.large b hb) (H.even_window b hb) (H.motif b hb) u (hfit.1 u)
    have hx (u : Fin (T (b+1))) :
        sourceNodeAnchor T n center b (bits.2.2 u) (sourceScheduledShift T n (b+1) glob u)=((a-start u:ℕ):ℤ) := by
      change sourceNodeAnchor T n center b (bits.2.2 u) (sourceScheduledShift T n (b+1) glob u)=
        ((P b/2-1-sourceWindowStart (T (b+1)) ((P b-T b)/2) (n b) loc glob u:ℕ):ℤ)
      rw [sourceWindowStart_oneBased_anchor (T (b+1)) (P b) (T b) (n b) (2^s) loc glob
        (H.ambient b hb) (H.large b hb) (H.even_window b hb) (H.motif b hb) u (hfit.1 u)]
      simp only [sourceNodeAnchor,hc b (by omega),sourceLocalCenter,sourceScheduledShift,loc]
    have hchild (u : Fin (T (b+1))) :
        sourceTreeWord s P T n h center atom (b+1) (bits.2.2 u)
          (sourceScheduledShift T n (b+1) glob u) (θ u)=
        complementaryWords (T b) (a-start u) (2^s) (prouhetBool s) (sourceBlockWord s P atom b) (θ u) := by
      rw [ih₂ (H.restrict (by omega)) (fun j hj => htop j (by omega)) (fun j hj => hc j (by omega)) _ _ _ (hfit.2 u)]
      simp only [sourceCenterWord,hx,integerTemplateType_nat,complementaryWords]
    have hstartnonneg (u : Fin (T (b+1))) : 0≤(A:ℤ)+sourceDisplacement (T (b+1)) (n b) loc glob u := by
      have he := sourceWindowStart_cast_of_fit (T (b+1)) (P b) (T b) (n b) loc glob
        (H.ambient b hb) (H.large b hb) u (hfit.1 u)
      have hn : (0:ℤ)≤(start u:ℕ) := Int.natCast_nonneg _
      change (start u:ℤ)=(A:ℤ)+_ at he
      omega
    have hp := htop (b+1) (by omega)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T (b+1)≠0)
    have hpart : (List.ofFn (fun u => complementaryWords (P b) a (2^s) (prouhetBool s)
          (sourceBlockWord s P atom b) (θ u))).flatten=
        coordinateWord (fun u => pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++
          complementaryWords (T b) (a-start u) (2^s) (prouhetBool s) (sourceBlockWord s P atom b) (θ u) ++
          pureAtomRun (sourceBlockWord s P atom b false) (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u)) := by
      have hh := sourceLayout_literal_partition k A (T b) B (n b) (h b) a (2^s)
      have hk' : k+1=T (b+1) := hk.symm
      rw [hk'] at hh
      rw [show A+T b+B=P b from htotal] at hh
      exact hh (H.even_trials b hb) (H.pre_reserve b hb) (H.post_reserve b hb) loc glob
        (prouhetBool s) (sourceBlockWord s P atom b) θ hstartnonneg
        (fun u => (hf u).2.1) (fun u => (hf u).2.2) (fun u => (hf u).1)
    change coordinateWord (fun u : Fin (T (b+1)) =>
      pureAtomRun (sourceBlockWord s P atom b false) (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++
      sourceTreeWord s P T n h center atom (b+1) (bits.2.2 u)
        (sourceScheduledShift T n (b+1) glob u) (θ u) ++
      pureAtomRun (sourceBlockWord s P atom b false) (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u))=
        atomString (T (b+1)) (sourceBlockWord s P atom (b+1)) θ
    calc
      _ = coordinateWord (fun u : Fin (T (b+1)) =>
        pureAtomRun (sourceBlockWord s P atom b false) (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++
        complementaryWords (T b) (a-start u) (2^s) (prouhetBool s) (sourceBlockWord s P atom b) (θ u) ++
        pureAtomRun (sourceBlockWord s P atom b false) (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u)) := by
          apply congrArg coordinateWord
          funext u
          exact congrArg (fun w => pureAtomRun (sourceBlockWord s P atom b false)
            (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++ w ++
              pureAtomRun (sourceBlockWord s P atom b false)
                (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u)) (hchild u)
      _ = _ := hpart.symm



/-- Full literal unconditioned root partition, including both members of
 every outer paired side. Its top trial count is the source's J, even or odd. -/
def sourceFullWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) (τ : Bool) : List Bool :=
  pureAtomRun (sourceBlockWord s P atom b false) (n b*h b+∑i,bitIndex (bits.1 i)) ++
  sourceTreeWord s P T n h (sourceLocalCenter T n) atom (b+1) bits 0 τ ++
  pureAtomRun (sourceBlockWord s P atom b false) (n b*(h b+1)-∑i,bitIndex (bits.1 i))

theorem bitIndex_sum_le {J : ℕ} (bits : Fin J → Bool) : (∑i,bitIndex (bits i))≤J := by
  calc
    _ ≤ ∑_i : Fin J,1 := by
      apply Finset.sum_le_sum
      intro i _
      cases bits i <;> norm_num [bitIndex]
    _ = J := by simp

/-- The source root's floor anchor and paired side counts have their literal
 unmarked word interpretation, without requiring J to be even. -/
theorem sourceFullWord_eq_block (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool)
    (b : ℕ) (H : SourceLayoutMargins s P T n h b) (hpos : 0<T b)
    (hroot : P b=n b*(2*h b+1)+T b) (he : Even (T b))
    (hJ : 4*(n b+1)≤T b) (hL : 8*2^s≤T b)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1))
    (τ : Bool) (hfit : SourceTreeFit T n (b+1) bits) :
    sourceFullWord s P T n h atom b bits τ=sourceBlockWord s P atom (b+1) τ := by
  let E : ℕ := ∑i,bitIndex (bits.1 i)
  let t := n b*h b+E
  let z := n b*(h b+1)-E
  let a := P b/2-1
  have hE : E≤n b := bitIndex_sum_le bits.1
  have hnat : n b≤n b*(h b+1) := by nlinarith
  have htotal : t+T b+z=P b := by
    have hprod : n b*(h b+1)=n b*h b+n b := by ring
    have hprod2 : n b*(2*h b+1)=2*(n b*h b)+n b := by ring
    dsimp [t,z]
    omega
  obtain ⟨k,hk⟩ := he
  have hhalf : 2*(T b/2)=T b := by omega
  have hP : P b=2*(n b*h b)+n b+T b := by rw [hroot]; ring
  have hPa : P b/2=n b*h b+T b/2+n b/2 := by omega
  have ht : t≤a := by dsimp [t,a]; omega
  have hz : a+2^s≤t+T b := by dsimp [t,a]; omega
  have hanchor : sourceNodeAnchor T n (sourceLocalCenter T n) b bits 0=((a-t:ℕ):ℤ) := by
    have hEc : (E:ℤ)=∑i,(bitIndex (bits.1 i):ℤ) := by simp [E]
    dsimp only [sourceNodeAnchor,sourceLocalCenter]
    have ha : a-t=T b/2-1+n b/2-E := by dsimp [a,t]; omega
    have hTe : 1≤T b/2 := by omega
    have hEe : E≤T b/2-1+n b/2 := by omega
    rw [ha,Nat.cast_sub hEe,Nat.cast_add,Nat.cast_sub hTe,hEc]
    push_cast
    ring
  have ho (j : ℕ) (hj : j<b+1) : 0<T j := by
    by_cases heq : j=b
    · simpa only [heq] using hpos
    · exact H.positive j (by omega)
  have hcenter := sourceTreeWord_eq_center_interior s P T n h (sourceLocalCenter T n) atom
    (b+1) (by simpa using H) ho (fun _ _ => rfl) bits 0 τ hfit
  have hpart := template_word_window t (T b) z a (2^s) (prouhetBool s) τ
    (sourceBlockWord s P atom b) ht hz
  rw [htotal] at hpart
  rw [atomString_constant,atomString_constant] at hpart
  unfold sourceFullWord
  rw [hcenter]
  change pureAtomRun (sourceBlockWord s P atom b false) t ++
    atomString (T b) (sourceBlockWord s P atom b)
      (integerTemplateType (T b) s (sourceNodeAnchor T n (sourceLocalCenter T n) b bits 0) τ) ++
    pureAtomRun (sourceBlockWord s P atom b false) z = _
  rw [hanchor,integerTemplateType_nat]
  exact hpart.symm

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Pure filler IDs. At bottom leaf windows the two fillers have zero length;
 they are deterministic empty outputs, not extra information. -/
def WindowFiller (T : ℕ → ℕ) : ℕ → Type
  | 0 => PEmpty
  | b+1 => (Fin (T b) × Bool) ⊕ (Fin (T b) × WindowFiller T b)

noncomputable instance windowFillerFintype (T : ℕ → ℕ) : (b : ℕ) → Fintype (WindowFiller T b)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | b+1 => by
    letI := windowFillerFintype T b
    exact inferInstanceAs (Fintype ((Fin (T b) × Bool) ⊕ (Fin (T b) × WindowFiller T b)))

abbrev TreeEmission (T n g : ℕ → ℕ) (b : ℕ) :=
  (WindowTrial T n g b × Bool) ⊕ (WindowFiller T b ⊕ WindowLeaf T b)

def TreeEmission.up (T n g : ℕ → ℕ) (b : ℕ) (u : Fin (T b)) :
    TreeEmission T n g b → TreeEmission T n g (b+1)
  | .inl (i,p) => .inl (.inr (.inr (u,i)),p)
  | .inr (.inl f) => .inr (.inl (.inr (u,f)))
  | .inr (.inr v) => .inr (.inr (u,v))

def treeLocalSlots (T n g : ℕ → ℕ) (b : ℕ) (p : Bool) : List (TreeEmission T n g (b+1)) :=
  List.ofFn (fun k : Fin (n b) => Sum.inl (Sum.inl k,p))

def treeGlobalSlots (T n g : ℕ → ℕ) (b : ℕ) (p : Bool)
    (pos : Fin (g b) → Fin (T b)) (u : Fin (T b)) : List (TreeEmission T n g (b+1)) :=
  ((List.ofFn id : List (Fin (g b))).filter (fun k => pos k=u)).map
    (fun k => Sum.inl (Sum.inr (Sum.inl k),p))

/-- Public chronological IDs. Each child carries its own local paired sides;
 the group's global sides and deterministic fillers surround that child.
 The order is fixed independently of all bits and both hypotheses. -/
def treeChronology (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) :
    (b : ℕ) → List (TreeEmission T n g b)
  | 0 => [.inr (.inr (show WindowLeaf T 0 from (0 : Fin 1)))]
  | b+1 => treeLocalSlots T n g b false ++
      (List.ofFn (fun u : Fin (T b) =>
        treeGlobalSlots T n g b false (pre b) u ++
        [.inr (.inl (.inl (u,false)))] ++
        (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) ++
        treeGlobalSlots T n g b true (post b) u ++
        [.inr (.inl (.inl (u,true)))])).flatten ++
      treeLocalSlots T n g b true

theorem sum_fiber_list_length {α ι : Type*} [Fintype ι] [DecidableEq ι] (pos : α → ι) (l : List α) :
    (∑i,(l.filter (fun a => pos a=i)).length)=l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hh (i : ι) : ((a::l).filter (fun a => pos a=i)).length=
        (if pos a=i then 1 else 0)+(l.filter (fun a => pos a=i)).length := by
      by_cases h : pos a=i <;> simp [h,Nat.add_comm]
    simp_rw [hh]
    rw [Finset.sum_add_distrib,ih]
    simp [Nat.add_comm]

theorem treeChronology_length (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ) :
    (treeChronology T n g pre post b).length=Fintype.card (TreeEmission T n g b) := by
  induction b with
  | zero =>
    change 1=Fintype.card ((PEmpty × Bool) ⊕ (PEmpty ⊕ Fin 1))
    simp
  | succ b ih =>
    have hp := sum_fiber_list_length (pre b) (List.ofFn id : List (Fin (g b)))
    have hq := sum_fiber_list_length (post b) (List.ofFn id : List (Fin (g b)))
    simp only [List.length_ofFn] at hp hq
    change _=Fintype.card (((Fin (n b) ⊕ (Fin (g b) ⊕ (Fin (T b) × WindowTrial T n g b))) × Bool) ⊕
      (((Fin (T b) × Bool) ⊕ (Fin (T b) × WindowFiller T b)) ⊕ (Fin (T b) × WindowLeaf T b)))
    simp only [treeChronology,treeLocalSlots,treeGlobalSlots,List.length_append,
      List.length_flatten,List.map_ofFn,Function.comp_apply,List.length_ofFn,List.length_map,List.length_cons,List.length_nil,
      Finset.sum_add_distrib,List.sum_ofFn,ih,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    rw [hp,hq]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring

theorem treeChronology_mem (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ)
    (x : TreeEmission T n g b) : x∈treeChronology T n g pre post b := by
  induction b with
  | zero =>
    rcases x with ⟨i,p⟩ | f | v
    · exact PEmpty.elim i
    · exact PEmpty.elim f
    · change Fin 1 at v
      have hv : v=0 := Subsingleton.elim _ _
      subst v; exact List.mem_singleton.mpr rfl
  | succ b ih =>
    have hc (u : Fin (T b)) (x : TreeEmission T n g (b+1))
        (hx : x∈treeGlobalSlots T n g b false (pre b) u ++ [.inr (.inl (.inl (u,false)))] ++
          (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) ++
          treeGlobalSlots T n g b true (post b) u ++ [.inr (.inl (.inl (u,true)))]) :
        x∈treeChronology T n g pre post (b+1) := by
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_flatten.mpr
      exact ⟨_,List.mem_ofFn.mpr ⟨u,rfl⟩,hx⟩
    rcases x with ⟨k,p⟩ | f | v
    · rcases k with k | k | ⟨u,k⟩
      · cases p <;>
          simp [treeChronology,treeLocalSlots,List.mem_ofFn]
      · cases p
        · apply hc (pre b k)
          simp only [List.mem_append,treeGlobalSlots,List.mem_map,List.mem_filter,List.mem_ofFn]
          exact Or.inl (Or.inl (Or.inl (Or.inl ⟨k,⟨⟨k,rfl⟩,by simp⟩,rfl⟩)))
        · apply hc (post b k)
          simp only [List.mem_append,treeGlobalSlots,List.mem_map,List.mem_filter,List.mem_ofFn]
          exact Or.inl (Or.inr ⟨k,⟨⟨k,rfl⟩,by simp⟩,rfl⟩)
      · apply hc u
        have hm : TreeEmission.up T n g b u (.inl (k,p))∈
            (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) := List.mem_map.mpr ⟨_,ih _,rfl⟩
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))
    · rcases f with ⟨u,p⟩ | ⟨u,f⟩
      · cases p <;> apply hc u <;> simp
      · apply hc u
        have hm : TreeEmission.up T n g b u (.inr (.inl f))∈
            (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) := List.mem_map.mpr ⟨_,ih _,rfl⟩
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))
    · rcases v with ⟨u,v⟩
      apply hc u
      have hm : TreeEmission.up T n g b u (.inr (.inr v))∈
          (treeChronology T n g pre post b).map (TreeEmission.up T n g b u) := List.mem_map.mpr ⟨_,ih _,rfl⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))

theorem treeChronology_nodup (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ) :
    (treeChronology T n g pre post b).Nodup := by
  have hs : (treeChronology T n g pre post b).toFinset=Finset.univ := by
    ext x
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact treeChronology_mem T n g pre post b x
  have hh : (treeChronology T n g pre post b).toFinset.card=(treeChronology T n g pre post b).length := by
    rw [hs,Finset.card_univ,treeChronology_length]
  exact Multiset.coe_nodup.mp ((Multiset.toFinset_card_eq_card_iff_nodup
    (m := (treeChronology T n g pre post b : Multiset (TreeEmission T n g b)))).mp hh)


/-- A genuine complete chronological bijection, not an assumed layout. -/
def treeChronologyEquiv (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ) :
    Fin (treeChronology T n g pre post b).length ≃ TreeEmission T n g b :=
  List.Nodup.getEquivOfForallMemList _ (treeChronology_nodup T n g pre post b)
    (treeChronology_mem T n g pre post b)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def pairedSideCount (h : ℕ) (bit side : Bool) : ℕ := h+bitIndex (Bool.xor bit side)

theorem pairedSideCount_false (h : ℕ) (bit : Bool) :
    pairedSideCount h bit false=h+bitIndex bit := by cases bit <;> rfl

theorem pairedSideCount_true (h : ℕ) (bit : Bool) :
    pairedSideCount h bit true=h+1-bitIndex bit := by cases bit <;> simp [pairedSideCount,bitIndex]

theorem pairedSideCount_sum_pre {t h : ℕ} (bits : Fin t → Bool) :
    (∑i,pairedSideCount h (bits i) false)=t*h+∑i,bitIndex (bits i) := by
  simp only [pairedSideCount_false,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]

theorem pairedSideCount_sum_total {t h : ℕ} (bits : Fin t → Bool) :
    (∑i,pairedSideCount h (bits i) true)+(∑i,bitIndex (bits i))=t*(h+1) := by
  rw [←Finset.sum_add_distrib]
  calc
    _ = ∑_i : Fin t,(h+1) := by
      apply Finset.sum_congr rfl
      intro i _
      cases bits i <;> simp [pairedSideCount,bitIndex]
    _ = _ := by simp

theorem pairedSideCount_sum_post {t h : ℕ} (bits : Fin t → Bool) :
    (∑i,pairedSideCount h (bits i) true)=t*(h+1)-∑i,bitIndex (bits i) := by
  have := pairedSideCount_sum_total (h:=h) bits
  omega

/-- Global trial positions are ID functions, not positions inferred from a
 realized output or orientation. -/
def sourceGlobalPre (N t : ℕ) (k : Fin ((N/4)*t)) : Fin N :=
  ⟨((globalTrialEquiv N t).symm k).1.val,by
    have := ((globalTrialEquiv N t).symm k).1.isLt; omega⟩

def sourceGlobalPost (N t : ℕ) (k : Fin ((N/4)*t)) : Fin N :=
  ⟨N-1-((globalTrialEquiv N t).symm k).1.val,by
    have := ((globalTrialEquiv N t).symm k).1.isLt; omega⟩

theorem sum_globalSides (N t h : ℕ) (bits : Fin ((N/4)*t) → Bool)
    (side : Bool) (pos : Fin (N/4) → Fin N) (u : Fin N) :
    (∑k : Fin ((N/4)*t), if pos ((globalTrialEquiv N t).symm k).1=u then
      pairedSideCount h (bits k) side else 0)=
    ∑v : Fin (N/4),if pos v=u then
      (∑a : Fin t,pairedSideCount h (bits (globalTrialIndex N t v a)) side) else 0 := by
  rw [←(globalTrialEquiv N t).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Equiv.symm_apply_apply]
  split_ifs with hv
  · rfl
  · simp only [Finset.sum_const_zero]

theorem sourcePreCount_slots (N A t h : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) (u : Fin N) :
    sourcePreCount N A t h loc glob u=
      (∑k : Fin ((N/4)*t),if sourceGlobalPre N t k=u then pairedSideCount h (glob k) false else 0)+
      sourcePreFiller N A t h u+(∑i,pairedSideCount h (loc u i) false) := by
  rw [pairedSideCount_sum_pre]
  change sourcePreFiller N A t h u+(∑v : SourceBundle N,
    if sourceBundleLeft N v=u then sourceBundleCount N t h loc glob v else 0)=_
  rw [Fintype.sum_sum_type]
  have hl : (∑v : Fin N,if sourceBundleLeft N (.inl v)=u then
      sourceBundleCount N t h loc glob (.inl v) else 0)=t*h+∑i,bitIndex (loc u i) := by
    change (∑v : Fin N,if v=u then (t*h+(∑i,bitIndex (loc v i))) else 0)=_
    simp
  rw [hl]
  have hg := sum_globalSides N t h glob false
    (fun v => ⟨v.val,by have := v.isLt; omega⟩) u
  simp only [pairedSideCount_sum_pre] at hg
  change (∑k,if sourceGlobalPre N t k=u then pairedSideCount h (glob k) false else 0)=_ at hg
  rw [hg]
  change _+(_+_) = _+_+_
  have he : (∑v : Fin (N/4),if sourceBundleLeft N (.inr v)=u then
      sourceBundleCount N t h loc glob (.inr v) else 0)=
      ∑v : Fin (N/4),if (⟨v.val,by have := v.isLt; omega⟩ : Fin N)=u then
        (t*h+∑i,bitIndex (glob (globalTrialIndex N t v i))) else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    rfl
  rw [he]
  omega

theorem sourcePostCount_slots (N B t h : ℕ) (ht : Even t) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) (u : Fin N) :
    sourcePostCount N B t h loc glob u=
      (∑i,pairedSideCount h (loc u i) true)+
      (∑k : Fin ((N/4)*t),if sourceGlobalPost N t k=u then pairedSideCount h (glob k) true else 0)+
      sourcePostFiller N B t h u := by
  have hh : 2*(t/2)=t := Nat.mul_div_cancel' ((even_iff_two_dvd).mp ht)
  have hc (bits : Fin t → Bool) :
      2*sourceLayoutReserve t h-(t*h+∑i,bitIndex (bits i))=
        ∑i,pairedSideCount h (bits i) true := by
    rw [pairedSideCount_sum_post]
    dsimp only [sourceLayoutReserve]
    have hs := bitIndex_sum_le bits
    have he : 2*(t*h+t/2)=t*h+t*(h+1) := by
      rw [Nat.mul_add,Nat.mul_add,Nat.mul_one,hh]
      omega
    rw [he]
    omega
  change sourcePostFiller N B t h u+(∑v : SourceBundle N,
    if sourceBundleRight N v=u then 2*sourceLayoutReserve t h-sourceBundleCount N t h loc glob v else 0)=_
  rw [Fintype.sum_sum_type]
  have hl : (∑v : Fin N,if sourceBundleRight N (.inl v)=u then
      2*sourceLayoutReserve t h-sourceBundleCount N t h loc glob (.inl v) else 0)=
      ∑i,pairedSideCount h (loc u i) true := by
    simp only [sourceBundleRight,sourceBundleCount,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hc]
  rw [hl]
  have hg := sum_globalSides N t h glob true
    (fun v => ⟨N-1-v.val,by have := v.isLt; omega⟩) u
  change (∑k,if sourceGlobalPost N t k=u then pairedSideCount h (glob k) true else 0)=_ at hg
  rw [hg]
  simp only [sourceBundleRight,sourceBundleCount,hc]
  omega

/-- Flattening selected equal-atom chunks sums exactly their genuine lengths. -/
theorem filter_chunks_flatten {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List ι) (p : ι → Bool) (c : ι → ℕ) (w : List Bool) :
    ((l.filter p).map (fun i => pureAtomRun w (c i))).flatten=
      pureAtomRun w ((l.map (fun i => if p i then c i else 0)).sum) := by
  calc
    _ = pureAtomRun w (((l.filter p).map c).sum) := by
      simpa only [List.map_map,Function.comp_def] using pureAtomRun_partition w ((l.filter p).map c)
    _ = _ := by
      congr 1
      induction l with
      | nil => rfl
      | cons i l ih => cases hp : p i <;> simp [hp,ih]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceScheduledPre (T n : ℕ → ℕ) :
    (b : ℕ) → Fin (sourceScheduledTrials T n b) → Fin (T b)
  | 0,k => Fin.elim0 k
  | b+1,k => sourceGlobalPre (T (b+1)) (n b) k

def sourceScheduledPost (T n : ℕ → ℕ) :
    (b : ℕ) → Fin (sourceScheduledTrials T n b) → Fin (T b)
  | 0,k => Fin.elim0 k
  | b+1,k => sourceGlobalPost (T (b+1)) (n b) k

/-- Two actual deterministic pure binary side words for each paired trial ID. -/
def sourceTrialWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowTrial T n (sourceScheduledTrials T n) b → Bool → List Bool
  | 0,i,_ => PEmpty.elim i
  | b+1,.inl _,c => pureAtomRun (sourceBlockWord s P atom b false) (h b+bitIndex c)
  | 1,.inr (.inl k),_ => Fin.elim0 k
  | b+2,.inr (.inl _),c => pureAtomRun (sourceBlockWord s P atom b false) (h b+bitIndex c)
  | b+1,.inr (.inr (_,i)),c => sourceTrialWord s P T n h atom b i c

/-- Fixed pure fillers, including the deterministic empty bottom fillers. -/
def sourceFillerWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowFiller T b → List Bool
  | 0,i => PEmpty.elim i
  | b+1,.inl (u,p) => match b,u with
    | 0,_ => []
    | b+1,u => pureAtomRun (sourceBlockWord s P atom b false)
        (if p then sourcePostFiller (T (b+1)) (sourceNominalPost P T b) (n b) (h b) u
          else sourcePreFiller (T (b+1)) (sourceNominalPre P T b) (n b) (h b) u)
  | b+1,.inr (_,i) => sourceFillerWord s P T n h atom b i

def sourceSlotWord (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) : TreeEmission T n (sourceScheduledTrials T n) b → List Bool
  | .inl (i,side) => sourceTrialWord s P T n h atom b i
      (Bool.xor (windowAssignmentEquiv T n (sourceScheduledTrials T n) Bool b bits i) side)
  | .inr (.inl i) => sourceFillerWord s P T n h atom b i
  | .inr (.inr v) => atom (sourceTreeLeafBool T n s center b bits incoming τ v)

def sourceChronologicalWord (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) : List Bool :=
  ((treeChronology T n (sourceScheduledTrials T n) (sourceScheduledPre T n) (sourceScheduledPost T n) b).map
    (sourceSlotWord s P T n h center atom b bits incoming τ)).flatten

theorem sourceSlotWord_up (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1))
    (incoming : ℤ) (τ : Bool) (u : Fin (T b)) (x : TreeEmission T n (sourceScheduledTrials T n) b) :
    sourceSlotWord s P T n h center atom (b+1) bits incoming τ (TreeEmission.up T n (sourceScheduledTrials T n) b u x)=
      sourceSlotWord s P T n h center atom b (bits.2.2 u) (sourceScheduledShift T n b bits.2.1 u)
        (integerTemplateType (T b) s (sourceNodeAnchor T n center b bits incoming) τ u) x := by
  rcases x with ⟨i,p⟩ | f | v <;> rfl

theorem treeChronology_eval (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ)
    (f : TreeEmission T n g (b+1) → List Bool) :
    ((treeChronology T n g pre post (b+1)).map f).flatten=
    ((treeLocalSlots T n g b false).map f).flatten ++
      coordinateWord (fun u => ((treeGlobalSlots T n g b false (pre b) u).map f).flatten ++
        f (.inr (.inl (.inl (u,false)))) ++
        ((treeChronology T n g pre post b).map (fun x => f (TreeEmission.up T n g b u x))).flatten ++
        ((treeGlobalSlots T n g b true (post b) u).map f).flatten ++
        f (.inr (.inl (.inl (u,true))))) ++
      ((treeLocalSlots T n g b true).map f).flatten := by
  simp only [treeChronology,List.map_append,List.flatten_append,List.map_flatten,
    List.map_ofFn,coordinateWord]
  congr 2
  rw [List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext u
  simp only [Function.comp_apply,List.map_append,List.flatten_append,List.map_cons,List.map_nil,
    List.flatten_cons,List.flatten_nil,List.append_nil,List.map_map]
  rfl

theorem sourceLocalSlots_word (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1))
    (incoming : ℤ) (τ side : Bool) :
    ((treeLocalSlots T n (sourceScheduledTrials T n) b side).map
      (sourceSlotWord s P T n h center atom (b+1) bits incoming τ)).flatten=
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (bits.1 i) side) := by
  rcases bits with ⟨loc,glob,kids⟩
  simp only [treeLocalSlots,List.map_ofFn]
  change (List.ofFn (fun i : Fin (n b) => pureAtomRun (sourceBlockWord s P atom b false)
    (pairedSideCount (h b) (loc i) side))).flatten=_
  exact coordinateWord_pureAtomRun _ _

theorem sourceGlobalSlots_word (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2))
    (incoming : ℤ) (τ side : Bool) (pos : Fin ((T (b+1)/4)*n b) → Fin (T (b+1))) (u : Fin (T (b+1))) :
    ((treeGlobalSlots T n (sourceScheduledTrials T n) (b+1) side pos u).map
      (sourceSlotWord s P T n h center atom (b+2) bits incoming τ)).flatten=
      pureAtomRun (sourceBlockWord s P atom b false)
        (∑k,if pos k=u then pairedSideCount (h b) (bits.2.1 k) side else 0) := by
  rcases bits with ⟨loc,glob,kids⟩
  change Fin ((T (b+1)/4)*n b) → Bool at glob
  simp only [treeGlobalSlots,List.map_map]
  change ((List.filter (fun k => decide (pos k=u)) (List.ofFn id)).map
    (fun i => pureAtomRun (sourceBlockWord s P atom b false) (pairedSideCount (h b) (glob i) side))).flatten=_
  rw [filter_chunks_flatten,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply,id_eq,decide_eq_true_eq]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def sourceFramedWord (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℤ → Bool → List Bool
  | 0,_,_,τ => atom τ
  | b+1,bits,incoming,τ =>
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (bits.1 i) false) ++
      sourceTreeWord s P T n h center atom (b+1) bits incoming τ ++
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (bits.1 i) true)

theorem sourceChronologicalWord_eq_framed (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ)
    (atom : Bool → List Bool) (b : ℕ) (hev : ∀j,j+1<b → Even (n j))
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b) (incoming : ℤ) (τ : Bool) :
    sourceChronologicalWord s P T n h center atom b bits incoming τ=
      sourceFramedWord s P T n h center atom b bits incoming τ := by
  induction b generalizing incoming τ with
  | zero => simp [sourceChronologicalWord,treeChronology,sourceSlotWord,sourceTreeLeafBool,sourceFramedWord]
  | succ b ih =>
    rcases bits with ⟨loc,glob,kids⟩
    unfold sourceChronologicalWord
    rw [treeChronology_eval]
    erw [sourceLocalSlots_word,sourceLocalSlots_word]
    change _=pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (loc i) false) ++
      sourceTreeWord s P T n h center atom (b+1) (loc,glob,kids) incoming τ ++
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (loc i) true)
    apply congrArg (fun w => pureAtomRun (sourceBlockWord s P atom b false)
      (∑i,pairedSideCount (h b) (loc i) false) ++ w ++
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (loc i) true))
    have child (u : Fin (T b)) :
        ((treeChronology T n (sourceScheduledTrials T n) (sourceScheduledPre T n) (sourceScheduledPost T n) b).map
          (fun x => sourceSlotWord s P T n h center atom (b+1) (loc,glob,kids) incoming τ
            (TreeEmission.up T n (sourceScheduledTrials T n) b u x))).flatten=
        sourceFramedWord s P T n h center atom b (kids u) (sourceScheduledShift T n b glob u)
          (integerTemplateType (T b) s (sourceNodeAnchor T n center b (loc,glob,kids) incoming) τ u) := by
      have he : (fun x : TreeEmission T n (sourceScheduledTrials T n) b =>
          sourceSlotWord s P T n h center atom (b+1) (loc,glob,kids) incoming τ
            (TreeEmission.up T n (sourceScheduledTrials T n) b u x)) =
          sourceSlotWord s P T n h center atom b (kids u) (sourceScheduledShift T n b glob u)
            (integerTemplateType (T b) s (sourceNodeAnchor T n center b (loc,glob,kids) incoming) τ u) := by
        funext x
        exact sourceSlotWord_up s P T n h center atom b (loc,glob,kids) incoming τ u x
      erw [he]
      exact ih (fun j hj => hev j (by omega)) (kids u) _ _
    cases b with
    | zero =>
      change coordinateWord _=atomString (T 0) atom _
      apply congrArg coordinateWord
      funext u
      rw [child]
      simp only [treeGlobalSlots,sourceScheduledTrials,List.ofFn_zero,List.filter_nil,List.map_nil,
        List.flatten_nil,List.nil_append,List.append_nil,sourceSlotWord,sourceFillerWord,sourceFramedWord]
    | succ b =>
      change coordinateWord _=coordinateWord _
      apply congrArg coordinateWord
      funext u
      erw [sourceGlobalSlots_word,sourceGlobalSlots_word,child]
      change _=pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePreCount (T (b+1)) (sourceNominalPre P T b) (n b) (h b) (fun v => (kids v).1) glob u) ++
        sourceTreeWord s P T n h center atom (b+1) (kids u) (sourceScheduledShift T n (b+1) glob u)
          (integerTemplateType (T (b+1)) s (sourceNodeAnchor T n center (b+1) (loc,glob,kids) incoming) τ u) ++
        pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePostCount (T (b+1)) (sourceNominalPost P T b) (n b) (h b) (fun v => (kids v).1) glob u)
      erw [sourcePreCount_slots,sourcePostCount_slots _ _ _ _ (hev b (by omega))]
      change pureAtomRun _ _ ++ pureAtomRun _ _ ++
        (pureAtomRun _ _ ++ sourceTreeWord s P T n h center atom (b+1) (kids u)
          (sourceScheduledShift T n (b+1) glob u)
          (integerTemplateType (T (b+1)) s (sourceNodeAnchor T n center (b+1) (loc,glob,kids) incoming) τ u) ++
          pureAtomRun _ _) ++ pureAtomRun _ _ ++ pureAtomRun _ _ = _
      simp only [sourceScheduledPre,sourceScheduledPost,pureAtomRun_add,List.append_assoc,
        Bool.false_eq_true,ite_false,ite_true]
      rfl

/-- Chronological side/filler/leaf slots produce the SAME full source word
 on the joint fit event. No orientation is removed or conditioned away. -/
theorem sourceChronologicalWord_eq_block (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool)
    (b : ℕ) (H : SourceLayoutMargins s P T n h b)
    (hP : P b=n b*(2*h b+1)+T b) (hT : Even (T b))
    (hlarge : 4*(n b+1)≤T b) (hmotif : 8*2^s≤T b)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) (τ : Bool)
    (hfit : SourceTreeFit T n (b+1) bits) :
    sourceChronologicalWord s P T n h (sourceLocalCenter T n) atom (b+1) bits 0 τ=
      sourceBlockWord s P atom (b+1) τ := by
  rw [sourceChronologicalWord_eq_framed s P T n h (sourceLocalCenter T n) atom (b+1)
    (fun j hj => H.even_trials j (by omega))]
  have hf := sourceFullWord_eq_block s P T n h atom b H (by omega) hP hT hlarge hmotif bits τ hfit
  change sourceFullWord s P T n h atom b bits τ=_ at hf
  simpa only [sourceFramedWord,sourceFullWord,pairedSideCount_sum_pre,pairedSideCount_sum_post] using hf

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def finEnumeration (α : Type) [Fintype α] : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm

abbrev SourceTrialCount (T n : ℕ → ℕ) (b : ℕ) := Fintype.card (WindowTrial T n (sourceScheduledTrials T n) b)
abbrev SourceFillerCount (T : ℕ → ℕ) (b : ℕ) := Fintype.card (WindowFiller T b)
abbrev SourceLeafCount (T : ℕ → ℕ) (b : ℕ) := Fintype.card (WindowLeaf T b)

def sourceEmissionEnum (T n : ℕ → ℕ) (b : ℕ) :
    EmissionSlot (SourceTrialCount T n b) (SourceFillerCount T b) (SourceLeafCount T b) ≃
      TreeEmission T n (sourceScheduledTrials T n) b :=
  Equiv.sumCongr (Equiv.prodCongr (finEnumeration _) (Equiv.refl Bool))
    (Equiv.sumCongr (finEnumeration _) (finEnumeration _))

def sourceAssignmentCode (T n : ℕ → ℕ) (A : Type) (b : ℕ) :
    WindowAssignments T n (sourceScheduledTrials T n) A b ≃ (Fin (SourceTrialCount T n b) → A) where
  toFun bits j := windowAssignmentEquiv T n (sourceScheduledTrials T n) A b bits (finEnumeration _ j)
  invFun bits := (windowAssignmentEquiv T n (sourceScheduledTrials T n) A b).symm
    (fun i => bits ((finEnumeration _).symm i))
  left_inv bits := by simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  right_inv bits := by
    funext j
    simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply]

theorem sourceAssignmentCode_eval (T n : ℕ → ℕ) (A : Type) (b : ℕ)
    (bits : Fin (SourceTrialCount T n b) → A) (j : Fin (SourceTrialCount T n b)) :
    windowAssignmentEquiv T n (sourceScheduledTrials T n) A b
      ((sourceAssignmentCode T n A b).symm bits) (finEnumeration _ j)=bits j := by
  change (sourceAssignmentCode T n A b ((sourceAssignmentCode T n A b).symm bits)) j=bits j
  rw [Equiv.apply_symm_apply]

def sourceChronologyCode (T n : ℕ → ℕ) (b : ℕ) :
    Fin (treeChronology T n (sourceScheduledTrials T n) (sourceScheduledPre T n) (sourceScheduledPost T n) b).length ≃
      EmissionSlot (SourceTrialCount T n b) (SourceFillerCount T b) (SourceLeafCount T b) :=
  (treeChronologyEquiv T n (sourceScheduledTrials T n) (sourceScheduledPre T n) (sourceScheduledPost T n) b).trans
    (sourceEmissionEnum T n b).symm

def sourceFlatLeafType (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ) (b : ℕ) (incoming : ℤ) (τ : Bool)
    (bits : Fin (SourceTrialCount T n b) → Bool) (j : Fin (SourceLeafCount T b)) : Bool :=
  sourceTreeLeafBool T n s center b ((sourceAssignmentCode T n Bool b).symm bits) incoming τ (finEnumeration _ j)

def sourceFlatTrialWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (c : Bool) (j : Fin (SourceTrialCount T n b)) : List Bool :=
  sourceTrialWord s P T n h atom b (finEnumeration _ j) c

def sourceFlatFillerWord (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (j : Fin (SourceFillerCount T b)) : List Bool :=
  sourceFillerWord s P T n h atom b (finEnumeration _ j)

theorem sourceSlotWord_code (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : Fin (SourceTrialCount T n b) → Bool) (incoming : ℤ) (τ : Bool)
    (x : EmissionSlot (SourceTrialCount T n b) (SourceFillerCount T b) (SourceLeafCount T b)) :
    sourceSlotWord s P T n h center atom b ((sourceAssignmentCode T n Bool b).symm bits) incoming τ
        (sourceEmissionEnum T n b x)=
      PairedMechanisms.slotWord (sourceFlatTrialWord s P T n h atom b false)
        (sourceFlatTrialWord s P T n h atom b true) (sourceFlatFillerWord s P T n h atom b) atom bits
        (sourceFlatLeafType T n s center b incoming τ bits) x := by
  rcases x with ⟨j,p⟩ | f | v
  · cases p <;>
      change sourceTrialWord s P T n h atom b (finEnumeration _ j)
        (Bool.xor (windowAssignmentEquiv T n (sourceScheduledTrials T n) Bool b
          ((sourceAssignmentCode T n Bool b).symm bits) (finEnumeration _ j)) _) = _ <;>
      rw [sourceAssignmentCode_eval] <;> cases he : bits j <;> simp [PairedMechanisms.slotWord,he,sourceFlatTrialWord]
  · rfl
  · rfl

theorem treeChronologyEquiv_word (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ)
    (f : TreeEmission T n g b → List Bool) :
    coordinateWord (fun j => f (treeChronologyEquiv T n g pre post b j))=
      ((treeChronology T n g pre post b).map f).flatten := by
  unfold coordinateWord treeChronologyEquiv
  change (List.ofFn (fun j => f ((treeChronology T n g pre post b).get j))).flatten=_
  have hh : List.map f (List.ofFn (treeChronology T n g pre post b).get) =
      List.ofFn (f ∘ (treeChronology T n g pre post b).get) := List.map_ofFn
  rw [List.ofFn_get] at hh
  exact congrArg List.flatten hh.symm

theorem source_slotCode_word (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : Fin (SourceTrialCount T n b) → Bool) (incoming : ℤ) (τ : Bool) :
    coordinateWord (fun j => PairedMechanisms.slotWord (sourceFlatTrialWord s P T n h atom b false)
      (sourceFlatTrialWord s P T n h atom b true) (sourceFlatFillerWord s P T n h atom b) atom bits
      (sourceFlatLeafType T n s center b incoming τ bits) (sourceChronologyCode T n b j))=
    sourceChronologicalWord s P T n h center atom b ((sourceAssignmentCode T n Bool b).symm bits) incoming τ := by
  simp_rw [←sourceSlotWord_code]
  simp only [sourceChronologyCode,Equiv.trans_apply,Equiv.apply_symm_apply]
  exact treeChronologyEquiv_word T n (sourceScheduledTrials T n) (sourceScheduledPre T n)
    (sourceScheduledPost T n) b _

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Reindex the genuine independent orientations, retaining the whole source tree. -/
theorem source_fair_code_expect (T n : ℕ → ℕ) (b : ℕ)
    (F : WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℝ) :
    (PairedMechanisms.fairOrientations (SourceTrialCount T n b)).expect
      (fun bits => F ((sourceAssignmentCode T n Bool b).symm bits)) =
    (windowPosteriorLaw T n (sourceScheduledTrials T n) b
      (noReveals T n (sourceScheduledTrials T n) b)).expect F := by
  rw [windowPosterior_fair_flat,FiniteLaw.indexedProduct_expect_equiv _ (finEnumeration _)]
  simp only [PairedMechanisms.fairOrientations,FiniteLaw.expect,FiniteLaw.product,
    FiniteLaw.indexedProduct,sourceAssignmentCode,Equiv.coe_fn_symm_mk]
  apply Finset.sum_congr (by ext; simp)
  intro bits _
  rfl

/-- The fit event uses only interior even bundles. In particular no parity
 assumption is made on the top root count J. -/
theorem sourceTreeFit_tail_interior (T n : ℕ → ℕ) (b : ℕ)
    (hn : ∀j,j+1<b → 0<n j) (he : ∀j,j+1<b → Even (n j)) :
    (windowPosteriorLaw T n (sourceScheduledTrials T n) b
      (noReveals T n (sourceScheduledTrials T n) b)).expect
        (fun bits => if SourceTreeFit T n b bits then 0 else 1) ≤ sourceFitTail T n b := by
  induction b using Nat.twoStepInduction with
  | zero =>
    have hh (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool 0) : SourceTreeFit T n 0 bits := trivial
    simp only [ite_eq_left (hh _),FiniteLaw.expect_const,sourceFitTail,le_refl]
  | one =>
    have hh (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool 1) : SourceTreeFit T n 1 bits := trivial
    simp only [ite_eq_left (hh _),FiniteLaw.expect_const,sourceFitTail,le_refl]
  | more b ih0 ih =>
    let P := windowPosteriorLaw T n (sourceScheduledTrials T n) (b+2)
      (noReveals T n (sourceScheduledTrials T n) (b+2))
    let badShift : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2) → Fin (T (b+1)) → Prop :=
      fun bits u => (T b:ℝ)/8≤|(sourceDisplacement (T (b+1)) (n b)
        (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)|
    have hp (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2)) :
        (if SourceTreeFit T n (b+2) bits then (0:ℝ) else 1)≤
          (∑u : Fin (T (b+1)),if badShift bits u then 1 else 0)+
          (∑u : Fin (T (b+1)),if SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1) := by
      let p := fun u : Fin (T (b+1)) => |8*sourceDisplacement (T (b+1)) (n b)
        (fun v => (bits.2.2 v).1) bits.2.1 u|≤(T b:ℤ)
      have hh : (if SourceTreeFit T n (b+2) bits then (0:ℝ) else 1)≤
          (if ∀u,p u then 0 else 1)+(if ∀u,SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1) := by
        by_cases H : SourceTreeFit T n (b+2) bits
        · rw [ite_eq_left H]
          split_ifs <;> norm_num
        · rw [ite_eq_right H]
          by_cases h1 : ∀u,p u
          · have h2 : ¬∀u,SourceTreeFit T n (b+1) (bits.2.2 u) := fun h2 => H ⟨h1,h2⟩
            rw [ite_eq_left h1,ite_eq_right h2]
            norm_num
          · rw [ite_eq_right h1]
            split_ifs <;> norm_num
      apply hh.trans
      apply add_le_add
      · apply (failure_forall_le_sum p).trans
        apply Finset.sum_le_sum
        intro u _
        by_cases hu : p u
        · simp only [ite_eq_left hu]
          split_ifs <;> norm_num
        · have hr : (T b:ℝ)<8*|(sourceDisplacement (T (b+1)) (n b)
              (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)| := by
            have hi : (T b:ℤ) < |8*sourceDisplacement (T (b+1)) (n b)
              (fun v => (bits.2.2 v).1) bits.2.1 u| := lt_of_not_ge hu
            have hi' : (T b:ℝ) < |(8*sourceDisplacement (T (b+1)) (n b)
              (fun v => (bits.2.2 v).1) bits.2.1 u:ℤ)| := by exact_mod_cast hi
            norm_num only [Int.cast_abs,Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<8)] at hi'
            exact hi'
          have hb : badShift bits u := by dsimp [badShift]; linarith
          simp [hu,hb]
      · exact failure_forall_le_sum _
    calc
      _ ≤ P.expect (fun bits => (∑u : Fin (T (b+1)),if badShift bits u then 1 else 0)+
          (∑u : Fin (T (b+1)),if SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1)) :=
            P.expect_mono hp
      _ = (∑u : Fin (T (b+1)),P.expect (fun bits => if badShift bits u then 1 else 0))+
          (∑u : Fin (T (b+1)),P.expect (fun bits => if SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1)) := by
            rw [FiniteLaw.expect_add,FiniteLaw.expect_fintype_sum,FiniteLaw.expect_fintype_sum]
      _ ≤ (∑_u : Fin (T (b+1)),2*Real.exp (-2*((T b:ℝ)/8)^2/(((T (b+1):ℝ)+1)*(n b:ℝ))))+
          ∑_u : Fin (T (b+1)),sourceFitTail T n (b+1) := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro u _
              exact sourceDisplacement_tail T n b (he b (by omega)) (hn b (by omega)) u (by positivity)
            · apply Finset.sum_le_sum
              intro u _
              dsimp only [P]
              rw [windowPosterior_child T n (sourceScheduledTrials T n) (b+1)
                (noReveals T n (sourceScheduledTrials T n) (b+2)) u
                (fun x => if SourceTreeFit T n (b+1) x then 0 else 1)]
              rw [noReveals_succ]
              exact ih (fun j hj => hn j (by omega)) (fun j hj => he j (by omega))
      _ = sourceFitTail T n (b+2) := by simp [sourceFitTail,mul_add]


/-- Honest source joint-fit failure after the actual finite coding. -/
theorem source_flat_fit_tail (T n : ℕ → ℕ) (b : ℕ)
    (hn : ∀j,j+1<b → 0<n j) (he : ∀j,j+1<b → Even (n j)) :
    (PairedMechanisms.fairOrientations (SourceTrialCount T n b)).expect
      (fun bits => if SourceTreeFit T n b ((sourceAssignmentCode T n Bool b).symm bits) then 0 else 1)
      ≤ sourceFitTail T n b := by
  rw [source_fair_code_expect T n b (fun bits => if SourceTreeFit T n b bits then 0 else 1)]
  exact sourceTreeFit_tail_interior T n b hn he

/-- A fixed public decoder. It does not know the hidden orientations or the
 input hypothesis, and it drops rather than reveals all pairing flags. -/
def sourceOracleDecode {Side Leaf : Type} (T n : ℕ → ℕ) (b : ℕ)
    (f : Side → List Bool) (g : Leaf → List Bool) :
    ((Reports Side (SourceTrialCount T n b) × (Fin (SourceLeafCount T b) → Leaf)) ×
      (Fin (SourceFillerCount T b) → Side)) → List Bool := fun x =>
  coordinateWord (fun j => PairedMechanisms.slotDecode f g (sourceChronologyCode T n b j)
    (emissionAssignmentEquiv Side Leaf (SourceTrialCount T n b) (SourceFillerCount T b)
      (SourceLeafCount T b) (fun i => (x.1.1 i).2,x.2,x.1.2) (sourceChronologyCode T n b j)))

/-- The complete canonical oracle now simulates the LITERAL source block.
 All IDs, words, leaf types and chronology instantiate the actual construction.
 The only failed-layout cost is its original unconditional fair-bit mass. -/
theorem source_canonical_simulation {Side Leaf : Type} [Fintype Side] [Fintype Leaf]
    {q E : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (H : SourceLayoutMargins s P T n h b)
    (hP : P b=n b*(2*h b+1)+T b) (hT : Even (T b))
    (hlarge : 4*(n b+1)≤T b) (hmotif : 8*2^s≤T b)
    (hn : ∀j<b,0<n j)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (R : Fin (SourceFillerCount T (b+1)) → FiniteLaw Side) (A B : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (sourceFlatTrialWord s P T n h atom (b+1) false j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (sourceFlatTrialWord s P T n h atom (b+1) true j))
    (hW : ∀j,SimulatesTrace q (R j) f (sourceFlatFillerWord s P T n h atom (b+1) j))
    (hA : ApproximatesTrace q A g (atom false) E) (hB : ApproximatesTrace q B g (atom true) E)
    (τ : Bool) :
    ApproximatesTrace q
      ((M.canonicalOracle A B (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)).prod
        (FiniteLaw.coordinateProduct R))
      (sourceOracleDecode T n (b+1) f g) (sourceBlockWord s P atom (b+1) τ)
      ((SourceLeafCount T (b+1):ℝ)*E+sourceFitTail T n (b+1)) := by
  let good := fun bits : Fin (SourceTrialCount T n (b+1)) → Bool =>
    SourceTreeFit T n (b+1) ((sourceAssignmentCode T n Bool (b+1)).symm bits)
  have hw (bits : Fin (SourceTrialCount T n (b+1)) → Bool) (hg : good bits) :=
    sourceChronologicalWord_eq_block s P T n h atom b H hP hT hlarge hmotif
      ((sourceAssignmentCode T n Bool (b+1)).symm bits) τ hg
  have hs := M.canonical_filled_simulation hq hE (sourceChronologyCode T n (b+1)) R A B f g
    (sourceFlatTrialWord s P T n h atom (b+1) false)
    (sourceFlatTrialWord s P T n h atom (b+1) true)
    (sourceFlatFillerWord s P T n h atom (b+1)) atom hU hV hW hA hB
    (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)
    (sourceBlockWord s P atom (b+1) τ) good (fun bits hg => by
      rw [source_slotCode_word]
      exact hw bits hg)
  intro F hF
  exact (hs F hF).trans (add_le_add le_rfl (source_flat_fit_tail T n (b+1) (fun j hj => hn j (by omega))
    (fun j hj => H.even_trials j (by omega))))

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end

end OAI
