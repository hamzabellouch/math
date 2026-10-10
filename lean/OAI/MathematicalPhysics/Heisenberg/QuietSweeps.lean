import OAI.MathematicalPhysics.Heisenberg.KilledContractions

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.MeshPair

section
open Heisenberg.MeshEnergy Heisenberg.MatrixContraction Matrix Filter Topology
open scoped RealInnerProductSpace
variable {V : Type*} [Fintype V] [DecidableEq V]

def quietSweep (H D : Set V) (a b : ℕ → V) (t : ℝ) : ℕ → EuclideanSpace ℝ V → EuclideanSpace ℝ V
  | 0,v => v
  | n+1,v => euclideanMap (residualMatrix D (a n ∉ H ∨ b n ∉ H) false (a n) (b n) (t/2))
      (quietSweep H D a b t n v)

lemma residual_supported (D : Set V) (R : Prop) (c : Bool) (a b : V) (p : ℝ)
    (v : EuclideanSpace ℝ V) (i : V) (hi : i ∉ D) :
    (euclideanMap (residualMatrix D R c a b p) v).ofLp i=0 := by
  have hh (σ : Equiv.Perm V) : ∀ j,killedMatrix D σ i j=0 := by
    intro j
    by_cases he : i=σ j
    · have hn : σ j ∉ D := he ▸ hi
      simp [killedMatrix,hn]
    · simp [killedMatrix,he]
  simp only [euclideanMap_apply,Matrix.mulVec,dotProduct,residualMatrix]
  split_ifs <;> simp [hh,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

lemma quietSweep_supported (H D : Set V) (a b : ℕ → V) (t : ℝ) (n : ℕ)
    (v : EuclideanSpace ℝ V) (hv : ∀ i ∉ D,v.ofLp i=0) :
    ∀ i ∉ D,(quietSweep H D a b t n v).ofLp i=0 := by
  cases n with
  | zero => exact hv
  | succ n => exact residual_supported D _ _ _ _ _ _

def maskedGenerator (H D : Set V) (a b : ℕ → V) (i : ℕ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  if a i ∈ H ∧ b i ∈ H then generator (edgeVector D (a i) (b i)) else 0

lemma quietSweep_eq (H D : Set V) (a b : ℕ → V) (n : ℕ)
    (hab : ∀ i,i<n → a i ≠ b i) (t : ℝ) (v : EuclideanSpace ℝ V)
    (hv : ∀ i ∉ D,v.ofLp i=0) :
    quietSweep H D a b t n v=sweep (maskedGenerator H D a b) n t v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [quietSweep,residual_quiet H D (a n) (b n) (t/2) _
      (quietSweep_supported H D a b t n v hv)]
    have he : 2*(t/2)=t := by ring
    rw [he]
    by_cases hh : a n ∈ H ∧ b n ∈ H
    · rw [ite_eq_left hh,killedCoin_generator D (hab n (by omega)) t _
        (quietSweep_supported H D a b t n v hv),ih (fun i hi => hab i (by omega))]
      simp only [sweep,maskedGenerator,ite_eq_left hh,mul_apply_eq_comp]
    · rw [ite_eq_right hh,ih (fun i hi => hab i (by omega))]
      simp only [sweep,maskedGenerator,ite_eq_right hh,smul_zero,add_zero,one_mul]

def quietEnergy (H : Set V) (a b : ℕ → V) (n : ℕ) (v : EuclideanSpace ℝ V) : ℝ :=
  ∑ i ∈ Finset.range n,if a i ∈ H ∧ b i ∈ H then (v.ofLp (a i)-v.ofLp (b i))^2 else 0

omit [Fintype V] [DecidableEq V] in
lemma quietEnergy_nonneg (H : Set V) (a b : ℕ → V) (n : ℕ) (v : EuclideanSpace ℝ V) :
    0≤quietEnergy H a b n v := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

lemma masked_dirichlet (H D : Set V) (a b : ℕ → V) (n : ℕ)
    (v : EuclideanSpace ℝ V) (hv : ∀ i ∉ D,v.ofLp i=0) :
    -⟪v,(∑ i ∈ Finset.range n,maskedGenerator H D a b i) v⟫ =
      (1/2:ℝ)*quietEnergy H a b n v := by
  simp only [_root_.sum_apply,inner_sum,←Finset.sum_neg_distrib,quietEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold maskedGenerator
  split_ifs
  · rw [generator_energy,edge_inner]
    have he (j : V) : (if j ∈ D then v.ofLp j else 0)=v.ofLp j := by
      split_ifs with h
      · rfl
      · exact (hv j h).symm
    simp only [he]
  · simp

theorem quietSweep_energy (a b : ℕ → V) (n : ℕ) (hab : ∀ i,i<n → a i ≠ b i)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ),∀ (H D : Set V) (v : EuclideanSpace ℝ V),
      (∀ i ∉ D,v.ofLp i=0) →
      |‖quietSweep H D a b t n v‖^2-‖v‖^2+t*quietEnergy H a b n v| ≤ ε * |t| * ‖v‖^2 := by
  have hh : ∀ H D : Set V,∀ᶠ t in 𝓝 (0:ℝ),∀ (v : EuclideanSpace ℝ V),
      (∀ i ∉ D,v.ofLp i=0) →
      |‖quietSweep H D a b t n v‖^2-‖v‖^2+t*quietEnergy H a b n v| ≤ ε * |t| * ‖v‖^2 := by
    intro H D
    have h := uniform_energy_error (sweep_zero (maskedGenerator H D a b) n)
      (sweep_derivative (maskedGenerator H D a b) n) hε
    filter_upwards [h] with t ht
    intro v hv
    rw [quietSweep_eq H D a b n hab t v hv]
    have he := masked_dirichlet H D a b n v hv
    convert ht v using 1
    congr 1
    nlinarith [congrArg (fun z : ℝ => t*z) he]
  exact Filter.eventually_all.mpr fun H => Filter.eventually_all.mpr (hh H)

lemma quietSweep_contraction (H D : Set V) (a b : ℕ → V) (t : ℝ)
    (ht : 0≤t) (ht2 : t≤2) (n : ℕ) (v : EuclideanSpace ℝ V) :
    ‖quietSweep H D a b t n v‖ ≤ ‖v‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (euclideanMap_contraction _ (residualMatrix_substochastic D _ false _ _ (t/2)
      (by positivity) (by linarith)) _).trans ih

end

open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

def killedBetween (D E : Set V) (σ : Equiv.Perm V) : Matrix V V ℝ :=
  fun i j => if j∈D ∧ i∈E ∧ i=σ j then 1 else 0

lemma killedBetween_substochastic (D E : Set V) (σ : Equiv.Perm V) :
    DoublySubstochastic (killedBetween D E σ) := by
  let p : V → Option V := fun j => if j∈D ∧ σ j∈E then some (σ j) else none
  have hp : ∀ i j a,p i=some a → p j=some a → i=j := by
    intro i j a hi hj
    dsimp [p] at hi hj
    split_ifs at hi hj
    exact σ.injective ((Option.some.inj hi).trans (Option.some.inj hj).symm)
  have hh := of_partial_permutation p hp
  have he : killedBetween D E σ = fun i j => if p j=some i then 1 else 0 := by
    funext i j
    dsimp [killedBetween,p]
    by_cases hj : j∈D
    · by_cases he : σ j∈E
      · simp only [hj,he,and_self,ite_true,true_and,Option.some.injEq]
        by_cases h : i=σ j
        · subst i; simp [he]
        · simp [h,Ne.symm h]
      · simp only [hj,he,and_false,ite_false,true_and,reduceCtorEq,ite_false]
        split_ifs with h
        · exact False.elim (he (h.2 ▸ h.1))
        · rfl
    · simp [hj]
  rw [he]
  convert hh using 1
  apply Iff.of_eq
  apply congrArg DoublySubstochastic
  funext i j
  split_ifs <;> rfl

omit [Fintype V] in
lemma killedBetween_same (D : Set V) (σ : Equiv.Perm V) :
    killedBetween D D σ=killedMatrix D σ := by
  ext i j
  simp only [killedBetween,killedMatrix]
  by_cases h : i=σ j
  · subst i; simp
  · simp [h]

omit [Fintype V] in
lemma killedBetween_transpose (D E : Set V) (σ : Equiv.Perm V) :
    (killedBetween D E σ).transpose=killedBetween E D σ.symm := by
  ext i j
  simp only [killedBetween,Matrix.transpose_apply]
  have he : j=σ i ↔ i=σ.symm j := by rw [eq_comm,Equiv.eq_symm_apply,eq_comm]
  simp only [he]
  congr 1
  exact propext (by tauto)

def residualBetween (D E : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) : Matrix V V ℝ :=
  if revealed then killedBetween D E (if c then Equiv.swap a b else 1)
  else (1-p) • killedBetween D E 1+p • killedBetween D E (Equiv.swap a b)

lemma residualBetween_substochastic (D E : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    DoublySubstochastic (residualBetween D E revealed c a b p) := by
  by_cases hr : revealed
  · simp only [residualBetween,ite_eq_left hr]
    exact killedBetween_substochastic _ _ _
  · simp only [residualBetween,ite_eq_right hr]
    have h := weighted_average (fun z : Bool => if z then p else 1-p)
      (by intro z; cases z <;> simp <;> linarith)
      (by simp) (fun z => killedBetween D E (if z then Equiv.swap a b else 1))
      (fun _ => killedBetween_substochastic _ _ _)
    have he : (1-p) • killedBetween D E 1 + p • killedBetween D E (Equiv.swap a b) =
        (fun i j => ∑ z : Bool,(if z then p else 1-p)*killedBetween D E (if z then Equiv.swap a b else 1) i j) := by
      ext i j
      simp [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_comm]
    rw [he]
    exact h

omit [Fintype V] in
lemma residualBetween_same (D : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) :
    residualBetween D D revealed c a b p=residualMatrix D revealed c a b p := by
  unfold residualBetween residualMatrix
  simp only [killedBetween_same]

omit [Fintype V] in
lemma residualBetween_transpose (D E : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) :
    (residualBetween D E revealed c a b p).transpose = residualBetween E D revealed c a b p := by
  unfold residualBetween
  by_cases hr : revealed
  · simp only [ite_eq_left hr,killedBetween_transpose]
    cases c <;> simp [show (Equiv.symm (1:Equiv.Perm V))=1 from rfl]
  · simp only [ite_eq_right hr,Matrix.transpose_add,Matrix.transpose_smul,killedBetween_transpose]
    simp [show (Equiv.symm (1:Equiv.Perm V))=1 from rfl]

lemma residualBetween_supported (D E : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) (v : EuclideanSpace ℝ V) :
    ∀ i∉E,(euclideanMap (residualBetween D E revealed c a b p) v).ofLp i=0 := by
  intro i hi
  simp only [euclideanMap_apply,Matrix.mulVec,dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  have hz : ∀ σ : Equiv.Perm V,killedBetween D E σ i j=0 := by
    intro σ
    simp [killedBetween,hi]
  by_cases hr : revealed <;> simp [residualBetween,hr,Matrix.add_apply,Matrix.smul_apply,hz]

end Heisenberg.MeshPair

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

def holeCut (s : Equiv.Perm T) (τ : T → Equiv.Perm V) (base : T → Bool)
    (P : Set (T×V)) (t : T) : Set V :=
  {v | (t,v)∉MissingSet (layerHistory s τ base) P}

omit [Fintype T] [Fintype V] [DecidableEq V] in
lemma holeCut_transport (s : Equiv.Perm T) (τ : T → Equiv.Perm V) (base : T → Bool)
    (P : Set (T×V)) (t : T) (v : V) :
    (if base t then τ t else 1) v∈holeCut s τ base P (s t) ↔
      v∈holeCut s τ base P t := by
  exact not_congr (missing_apply (layerHistory s τ base) P (t,v))

omit [Fintype T] [Fintype V] [DecidableEq V] in
lemma holeCut_quiet (s : Equiv.Perm T) (τ : T → Equiv.Perm V) (base : T → Bool)
    (P : Set (T×V)) (t : T) (ht : base t=false) :
    holeCut s τ base P (s t)=holeCut s τ base P t := by
  ext v
  simpa only [ht,Bool.false_eq_true,↓reduceIte,Equiv.Perm.one_apply] using
    holeCut_transport s τ base P t v

omit [Fintype T] [Fintype V] in
lemma layerRevealed_swap (a b : T → V) (A : Set (T×V)) (t : T) (hab : a t≠b t) :
    layerRevealed (fun i => Equiv.swap (a i) (b i)) A t ↔ (t,a t)∈A ∨ (t,b t)∈A := by
  constructor
  · rintro ⟨v,hv,hn⟩
    by_cases ha : v=a t
    · exact Or.inl (ha ▸ hv)
    · have hb : v=b t := by
        by_contra hb
        exact hn (Equiv.swap_apply_of_ne_of_ne ha hb)
      exact Or.inr (hb ▸ hv)
  · rintro (ha|hb)
    · exact ⟨a t,ha,by simpa using hab.symm⟩
    · exact ⟨b t,hb,by simpa using hab⟩

def exposedStep (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (t : T) : Matrix V V ℝ :=
  let τ := fun i => Equiv.swap (a i) (b i)
  residualBetween (holeCut s τ base P t∩I) (holeCut s τ base P (s t)∩I)
    (layerRevealed τ (MissingSet (layerHistory s τ base) P) t) (base t) (a t) (b t) (p t)

omit [Fintype T] [Fintype V] in
lemma exposedStep_quiet (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (t : T)
    (ht : base t=false) (hab : a t≠b t) :
    exposedStep s a b base P I p t =
      residualMatrix (holeCut s (fun i => Equiv.swap (a i) (b i)) base P t∩I)
        (a t∉holeCut s (fun i => Equiv.swap (a i) (b i)) base P t ∨
          b t∉holeCut s (fun i => Equiv.swap (a i) (b i)) base P t)
        false (a t) (b t) (p t) := by
  unfold exposedStep
  dsimp only
  rw [holeCut_quiet s _ base P t ht,ht,residualBetween_same]
  congr 1
  rw [layerRevealed_swap a b _ t hab]
  simp only [holeCut,Set.mem_ofPred_eq,not_not]

def exposedSweep (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) :
    ℕ → EuclideanSpace ℝ V → EuclideanSpace ℝ V
  | 0,v => v
  | n+1,v => euclideanMap (exposedStep s a b base P I p (r n))
      (exposedSweep s a b base P I p r n v)

omit [Fintype T] [Fintype V] [DecidableEq V] in
lemma holeCut_quiet_segment (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (base : T → Bool) (P : Set (T×V)) (r : ℕ → T) (n : ℕ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (hb : ∀ i,i<n → base (r i)=false) :
    holeCut s τ base P (r n)=holeCut s τ base P (r 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hr n (by omega),holeCut_quiet s τ base P (r n) (hb n (by omega))]
    exact ih (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega))

omit [Fintype T] in

theorem exposedSweep_quiet (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (r : ℕ → T) (n : ℕ) (t : ℝ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (hb : ∀ i,i<n → base (r i)=false)
    (hab : ∀ i,i<n → a (r i)≠b (r i)) (v : EuclideanSpace ℝ V) :
    exposedSweep s a b base P I (fun _ => t/2) r n v =
      quietSweep (holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0))
        (holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0)∩I)
        (a ∘ r) (b ∘ r) t n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exposedSweep,exposedStep_quiet s a b base P I _ (r n) (hb n (by omega))
      (hab n (by omega)),holeCut_quiet_segment s _ base P r n
      (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega)),
      ih (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega))
        (fun i hi => hab i (by omega))]
    rfl

end Heisenberg.Exposure
end

end OAI
