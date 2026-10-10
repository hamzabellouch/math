import OAI.Dynamics.ConditionalShuffle.HybridPrefix

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Scheduled
open Thorp Thorp.Conditional Thorp.Conditional.Hybrid Revealed.Split Revealed.Instrument Revealed.Disintegration
variable {ι α : Type} [fintype_ι : Fintype ι] [fintype_α : Fintype α] [decidableEq_α : DecidableEq α]

abbrev Symbol (ι α : Type) (d : ℕ) := Outside ι α (Position d) × Option (Coins d)

def stepInstrument (d : ℕ) (σ : ℕ → Bool) :
    Data (ℕ × Outside ι α (Position d)) (Symbol ι α d) (Equiv.Perm α) (Coins d) where
  obs e c := (nextOutside e.2 (step d c), if σ e.1 then none else some c)
  inc e c := increment e.2 (step d c)
  next e s := (e.1+1, s.1)

lemma base_clock (d : ℕ) (σ : ℕ → Bool) (τ : ℕ) (e : Outside ι α (Position d))
    (t : ℕ) (p : Fin t → Symbol ι α d) :
    (base (stepInstrument d σ) (τ,e) t p).1 = τ+t := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  induction t with
  | zero => rfl
  | succ t ih =>
      change (base (stepInstrument d σ) (τ,e) t (Fin.init p)).1+1 = _
      rw [ih]; omega

lemma base_outside (d : ℕ) (σ : ℕ → Bool) (τ : ℕ) (e : Outside ι α (Position d))
    (t : ℕ) (p : Fin t → Symbol ι α d) :
    (base (stepInstrument d σ) (τ,e) t p).2 =
      base (Physical.instrument d) e t (fun i => (p i).1) := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  cases t with
  | zero => rfl
  | succ t => rfl

lemma observed_outside (d : ℕ) (σ : ℕ → Bool) (τ : ℕ) (e : Outside ι α (Position d))
    (t : ℕ) (ω : History d t) :
    (fun i => (observed (stepInstrument d σ) (τ,e) t ω i).1) =
      observed (Physical.instrument d) e t ω := by
  induction t with
  | zero => exact Subsingleton.elim _ _
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [observed, Fin.snoc_last]
        change nextOutside (base (stepInstrument d σ) (τ,e) t
          (observed (stepInstrument d σ) (τ,e) t (Fin.init ω))).2 (step d (ω (Fin.last t))) = _
        rw [base_outside, ih]; rfl
      · simpa only [observed, Fin.snoc_castSucc] using congrFun (ih (Fin.init ω)) j

lemma observed_public (d : ℕ) (σ : ℕ → Bool) (τ : ℕ) (e : Outside ι α (Position d))
    (t : ℕ) (ω : History d t) :
    (fun i => (observed (stepInstrument d σ) (τ,e) t ω i).2) =
      publicHistory (fun i : Fin t => σ (τ+i.val)) ω := by
  induction t with
  | zero => exact Subsingleton.elim _ _
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [observed, Fin.snoc_last]
        change (if σ (base (stepInstrument d σ) (τ,e) t
          (observed (stepInstrument d σ) (τ,e) t (Fin.init ω))).1 then none else some (ω (Fin.last t))) = _
        rw [base_clock]; rfl
      · simpa only [observed, Fin.snoc_castSucc, publicHistory, Fin.init_def, Fin.val_castSucc] using congrFun (ih (Fin.init ω)) j

lemma group_eq (d : ℕ) (σ : ℕ → Bool) (τ : ℕ) (e : Outside ι α (Position d))
    (t : ℕ) (ω : History d t) :
    groupRun (stepInstrument d σ) (τ,e) t ω = groupRun (Physical.instrument d) e t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [groupRun]
      change increment (base (stepInstrument d σ) (τ,e) t
        (observed (stepInstrument d σ) (τ,e) t (Fin.init ω))).2 (step d (ω (Fin.last t))) * _ = _
      rw [base_outside, observed_outside, ih]; rfl

lemma kernel_dichotomy [Nontrivial α] (d : ℕ) (σ : ℕ → Bool)
    (e : ℕ × Outside ι α (Position (d+1))) (s : Symbol ι α (d+1)) :
    Trim.signDichotomy (kernel (stepInstrument (d+1) σ) e s) := by
  by_cases hp : σ e.1 = false
  · apply Trim.signDichotomy_conditional_injective
      ((stepInstrument (d+1) σ).obs e) ((stepInstrument (d+1) σ).inc e) _ s
    intro c c' hh
    have h := congrArg Prod.snd hh
    simpa only [stepInstrument, hp, Bool.false_eq_true, ite_false, Option.some.injEq] using h
  · have hp' : σ e.1 = true := by cases h : σ e.1 <;> simp_all
    let L := sectionFrame e.2
    by_cases h : ∀ x : Position d, ∃ i : ι, Fin.tail (L (.inl i)) = x
    · apply Trim.signDichotomy_conditional_injective
        ((stepInstrument (d+1) σ).obs e) ((stepInstrument (d+1) σ).inc e) _ s
      intro c c' hh
      exact outside_step_injective d L h (congrArg Prod.fst hh)
    · push Not at h
      obtain ⟨x,hx⟩ := h
      obtain ⟨a,b,hab,ha,hb⟩ := pair_free_labels d L x hx
      apply Trim.signDichotomy_conditional_symmetry
        ((stepInstrument (d+1) σ).obs e) ((stepInstrument (d+1) σ).inc e)
        (toggleCoin x) (Equiv.swap a b) _ _ _ s
      · intro c
        apply Prod.ext
        · change Split.outside (L.trans (step (d+1) (toggleCoin x c))) = Split.outside (L.trans (step (d+1) c))
          rw [free_pair_toggle d L x a b ha hb c, outside_pre]
        · simp only [stepInstrument, hp', ite_true]
      · intro c
        change assignment (L.trans (step (d+1) (toggleCoin x c))) = assignment (L.trans (step (d+1) c)) * _
        rw [free_pair_toggle d L x a b ha hb c, assignment_pre]
      · rw [Specht.complexSign_eq, Equiv.Perm.sign_swap hab]; simp

def interval (d t : ℕ) (σ : ℕ → Bool) :
    Data (Outside ι α (Position d)) (Fin t → Symbol ι α d) (Equiv.Perm α) (History d t) where
  obs e ω := observed (stepInstrument d σ) (0,e) t ω
  inc e ω := groupRun (stepInstrument d σ) (0,e) t ω
  next e p := (base (stepInstrument d σ) (0,e) t p).2

lemma interval_kernel (d t : ℕ) (σ : ℕ → Bool) (e : Outside ι α (Position d)) (p) :
    kernel (interval d t σ) e p = kernel (block (stepInstrument d σ) t) (0,e) p := by
  let retained_fintype_ι := fintype_ι
  exact rfl

lemma interval_probability (d t : ℕ) (σ : ℕ → Bool) (e : Outside ι α (Position d)) (p) :
    probability (interval d t σ) e p = probability (block (stepInstrument d σ) t) (0,e) p := by
  let retained_fintype_ι := fintype_ι
  exact rfl

lemma interval_dichotomy [Nontrivial α] (d t : ℕ) (σ : ℕ → Bool)
    (e : Outside ι α (Position (d+1))) (p) :
    Trim.signDichotomy (kernel (interval (d+1) t σ) e p) :=
  block_kernel_dichotomy (stepInstrument (d+1) σ) (kernel_dichotomy d σ) (0,e) t p

def decode {d t : ℕ} (e : Outside ι α (Position d)) (p : Fin t → Symbol ι α d) :
    Public d t × (Fin (t+1) → ι → Position d) :=
  (fun i => (p i).2, Physical.fullPath e (fun i => (p i).1))

lemma decode_injective {d t : ℕ} (e : Outside ι α (Position d)) :
    Function.Injective (decode (t:=t) e) := by
  intro p q hh
  have h₁ := congrArg Prod.fst hh
  have h₂ := Physical.fullPath_injective e (congrArg Prod.snd hh)
  funext i
  exact Prod.ext (congrFun h₂ i) (congrFun h₁ i)

lemma decode_observed (d t : ℕ) (σ : ℕ → Bool) (e : Outside ι α (Position d)) (ω : History d t) :
    decode e (observed (stepInstrument d σ) (0,e) t ω) =
      (publicHistory (fun i : Fin t => σ i.val) ω, splitPath (sectionFrame e) t ω) := by
  unfold decode
  rw [observed_public, observed_outside, Physical.physical_path_frame]
  simp only [Nat.zero_add]

lemma interval_weighted_cost (d t : ℕ) (σ : ℕ → Bool) (e : Outside ι α (Position d))
    (c : (Equiv.Perm α → ℝ) → ℝ) :
    (∑ p, probability (interval d t σ) e p * c (kernel (interval d t σ) e p)) =
    let μ := fairMass (fun ω : History d t =>
      ((publicHistory (fun i : Fin t => σ i.val) ω, splitPath (sectionFrame e) t ω),
        assignment ((sectionFrame e).trans (run d t ω))))
    ∑ p, marginal μ p * c (conditional μ p) := by
  have h := weighted_conditional_map (observed (stepInstrument d σ) (0,e) t)
    (groupRun (stepInstrument d σ) (0,e) t) (decode e) (decode_injective e) c
  simp_rw [decode_observed, group_eq, Physical.physical_group_frame] at h
  simpa only [probability, kernel, joint, interval, group_eq, Physical.physical_group_frame] using h.symm

end Revealed.Scheduled

end

end OAI
