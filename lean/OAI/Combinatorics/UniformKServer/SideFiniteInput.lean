import Mathlib
import OAI.Combinatorics.UniformKServer.StarSchedules
import OAI.Combinatorics.UniformKServer.SideRecurrence

namespace OAI

                                      
section

/-! Actual posterior/core inputs in a finite reveal law. Conditions describe the
 held, measurable data, not a movement conclusion. Empty and null-fiber cases
 still use the zero conventions of the conditional kernel. -/
noncomputable section
namespace UniformKServer.SideFiniteInput
open Finset UniformKServer.AdaptiveSide UniformKServer.ConditionalLaw
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

structure Data (Ω ι R : Type*) [Fintype Ω] [Fintype ι] [Fintype R] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  hidden : ℕ → Ω → ι × R → ℝ
  hidden_range : ∀ t ω ir, hidden t ω ir ∈ Set.Icc (0:ℝ) 1
  param : ℕ → Ω → Config ι
  param_valid : ∀ t ω, valid (param t ω)
  param_measurable : ∀ t ω v, (filtration t).r ω v → param t ω=param t v
  flag : ℕ → Ω → ι → R → Bool
  flag_measurable : ∀ t ω v, (filtration t).r ω v → flag t ω=flag t v
  supported : ∀ t ω i, i ∉ (param t ω).active → ∀ r, flag t ω i r=false
  deficit : ℕ → Ω → ℝ
  deficit_nonneg : ∀ t ω, 0 ≤ deficit t ω
  deficit_measurable : ∀ t ω v, (filtration t).r ω v → deficit t ω=deficit t v
  mass : ℕ → Ω → ℝ
  mass_measurable : ∀ t ω v, (filtration t).r ω v → mass t ω=mass t v
  mass_bound : ∀ t ω, (∑ i, SyntheticCore.input
    (fun r => posterior weight (filtration t) (fun v => hidden t v (i,r)) ω) (flag t ω i)) ≤ mass t ω

def post (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) (r : R) : ℝ :=
  posterior d.weight (d.filtration t) (fun v => d.hidden t v (i,r)) ω

def activeFlag (p : Config ι) : ι → Bool := fun i => decide (i ∈ p.active)

def input (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  SyntheticCore.input (post d t ω i) (d.flag t ω i)

def star (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι → ℝ :=
  SyntheticCore.core (activeFlag (d.param t ω)) (activeFlag (d.param (t+1) ω))
    (post d (t+1) ω) (d.flag (t+1) ω)

def oldMask (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  SyntheticCore.input (post d (t+1) ω i) (d.flag t ω i)

def changes (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ i, SyntheticCore.changes (d.flag t ω i) (d.flag (t+1) ω i)

def tracker (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι → ℝ :=
  SideRecurrence.trajectory (fun s => d.param s ω) (fun s => star d s ω)
    (fun s => input d s ω) (fun s => d.deficit s ω) (fun s => d.mass s ω) t

def prepared (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι → ℝ :=
  SideRecurrence.prepared (fun s => d.param s ω) (fun s => star d s ω)
    (fun s => input d s ω) (fun s => d.deficit s ω) (fun s => d.mass s ω) t

theorem post_range (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) (r : R) :
    post d t ω i r ∈ Set.Icc (0:ℝ) 1 :=
  ⟨posterior_nonneg d.nonneg (fun v => (d.hidden_range t v (i,r)).1) _ ω,
    posterior_le_one d.nonneg (fun v => (d.hidden_range t v (i,r)).2) _ ω⟩

theorem flag_supported (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    SyntheticCore.Supported (activeFlag (d.param t ω)) (d.flag t ω) := by
  intro i hi r
  exact d.supported t ω i (by simpa [activeFlag] using hi) r

theorem input_nonneg (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) : 0 ≤ input d t ω i :=
  SyntheticCore.input_nonneg (fun r => (post_range d t ω i r).1) _

theorem input_supported (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.Supported ((d.param t ω).active) (input d t ω) := by
  intro i hi
  exact SyntheticCore.no_flags _ (d.supported t ω i hi)

theorem star_supported_old (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.Supported ((d.param t ω).active) (star d t ω) := by
  intro i hi
  simp [star,SyntheticCore.core,activeFlag,hi]

theorem star_supported_new (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.Supported ((d.param (t+1) ω).active) (star d t ω) := by
  intro i hi
  simp [star,SyntheticCore.core,activeFlag,hi]

theorem valid_input (d : Data Ω ι R) (ω : Ω) :
    SideRecurrence.InputValid (fun s => d.param s ω) (fun s => star d s ω)
      (fun s => input d s ω) (fun s => d.deficit s ω) (fun s => d.mass s ω) := by
  refine ⟨fun t => d.param_valid t ω,fun t => d.deficit_nonneg t ω,?_,
    fun t => input_nonneg d t ω,fun t => d.mass_bound t ω,
    fun t => star_supported_old d t ω,fun t => star_supported_new d t ω,
    fun t => input_supported d t ω⟩
  intro t i
  exact (SyntheticCore.core_le_new _ _ _ _ (fun i r => (post_range d (t+1) ω i r).1) i).1

theorem errors (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    (∑ i, |oldMask d t ω i-star d t ω i|) ≤ changes d t ω ∧
    (∑ i, |input d (t+1) ω i-star d t ω i|) ≤ changes d t ω ∧
    0 ≤ (∑ i, input d (t+1) ω i)-(∑ i, star d t ω i) ∧
    (∑ i, input d (t+1) ω i)-(∑ i, star d t ω i) ≤ changes d t ω :=
  SyntheticCore.errors _ _ _ _ _ (post_range d (t+1) ω)
    (flag_supported d t ω) (flag_supported d (t+1) ω)

theorem tracker_state (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.domain (d.param t ω).active 11 (tracker d t ω) := SideRecurrence.trajectory_state (valid_input d ω) t

theorem step (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    SideRecurrence.StepSpec (d.param t ω) (d.param (t+1) ω) (star d t ω) (input d (t+1) ω)
      (tracker d t ω) (tracker d (t+1) ω) (prepared d t ω) (d.deficit (t+1) ω) (d.mass (t+1) ω) :=
  SideRecurrence.trajectory_step (valid_input d ω) t

theorem refining (d : Data Ω ι R) {s t : ℕ} (hst : s ≤ t) {ω v : Ω}
    (h : (d.filtration t).r ω v) : (d.filtration s).r ω v := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => exact ih (d.refines t ω v h)

theorem input_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : input d t ω=input d t v := by
  funext i
  unfold input
  rw [d.flag_measurable t ω v h]
  congr 1
  funext r
  exact posterior_measurable _ _ _ ω v h

theorem star_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.filtration (t+1)).r ω v) : star d t ω=star d t v := by
  unfold star
  rw [d.param_measurable t ω v (d.refines t ω v h),
    d.param_measurable (t+1) ω v h,d.flag_measurable (t+1) ω v h]
  congr 1
  funext i r
  exact posterior_measurable _ _ _ ω v h

theorem tracker_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : tracker d t ω=tracker d t v := by
  apply SideRecurrence.causal_through
  · intro s hs
    exact d.param_measurable s ω v (refining d hs h)
  · intro s hs
    exact star_measurable d s (refining d (Nat.succ_le_iff.mpr hs) h)
  · intro s hs
    exact input_measurable d s (refining d hs h)
  · intro s hs
    exact d.deficit_measurable s ω v (refining d hs h)
  · intro s hs
    exact d.mass_measurable s ω v (refining d hs h)

end UniformKServer.SideFiniteInput

end


end

end OAI
