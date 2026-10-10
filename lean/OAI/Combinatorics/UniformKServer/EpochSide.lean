import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlphaStatic
import OAI.Combinatorics.UniformKServer.SideParameterChanges

namespace OAI

                                
section

/-! Exact side configuration of a marked held-vector epoch. An unmarked
star has the actual empty side domain. -/
noncomputable section
namespace UniformKServer.EpochSide
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def active (a : ι → ℝ) (s : EpochGeometry.State ι) : Finset ι :=
  match EpochGeometry.dominant s with
  | none => ∅
  | some o => (EpochParameters.active a).erase o

def config (a : ι → ℝ) (s : EpochGeometry.State ι) (ell cw b : ℝ) : AdaptiveSide.Config ι where
  active := active a s
  A := EpochGeometry.total s.base
  a := fun i => a i
  ell := ell
  cw := cw
  b := b

theorem mem {a : ι → ℝ} {s : EpochGeometry.State ι} {i : ι} (hi : i ∈ active a s) :
    0 < a i ∧ EpochGeometry.dominant s ≠ some i := by
  unfold active at hi
  cases ho : EpochGeometry.dominant s with
  | none => simp [ho] at hi
  | some o =>
    rw [ho] at hi
    obtain ⟨hne,ha⟩ := mem_erase.mp hi
    exact ⟨EpochParameters.mem_active.mp ha,by simpa only [ho,ne_eq,Option.some.injEq] using hne.symm⟩

theorem valid {a : ι → ℝ} {s : EpochGeometry.State ι} (hs : EpochGeometry.valid a s)
    {ell cw b : ℝ} (hl : 1 ≤ ell) (hcw : 0 < cw) (hc : cw*50000 ≤ 1)
    (hb : 0 < b) (hb4 : b ≤ 4)
    (hh : ∀ i : active a s, SideParameters.height (EpochGeometry.total s.base) (a i) ≤ 50000*ell) :
    AdaptiveSide.valid (config a s ell cw b) := by
  refine ⟨hl,hcw,hb,hb4,?_,?_⟩
  · intro i
    have hi := mem i.property
    exact ⟨hi.1,(EpochGeometry.regular_size hs hi.2).trans
      (by change (86/100:ℝ)*EpochGeometry.total s.base ≤ EpochGeometry.total s.base; nlinarith [EpochGeometry.total_nonneg hs.1])⟩
  · intro i
    exact EpochAlpha.eta_bound hcw (by change 0 < ell; linarith) hc (hh i)

theorem size_formula {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (s : EpochGeometry.State ι)
    (ell cw b : ℝ) (i : ι) : SideParameterChanges.size (config a s ell cw b) i =
      match EpochGeometry.dominant s with
      | none => 0
      | some o => if i=o then 0 else a i := by
  unfold SideParameterChanges.size DomainTransport.extend config active
  dsimp only
  cases ho : EpochGeometry.dominant s with
  | none => simp
  | some o =>
    by_cases he : i=o
    · simp [he]
    · by_cases hp : 0 < a i
      · simp [he,EpochParameters.mem_active.mpr hp]
      · have hz : a i=0 := le_antisymm (le_of_not_gt hp) (ha i)
        simp [hz,he]

theorem size_same {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {s r : EpochGeometry.State ι} (he : s.base=r.base) (ell cw v v' : ℝ)
    {i : ι} (hi : a i=b i) :
    SideParameterChanges.size (config a s ell cw v) i=SideParameterChanges.size (config b r ell cw v') i := by
  rw [size_formula ha,size_formula hb,EpochAlphaStatic.dominant_base he]
  cases EpochGeometry.dominant r <;> simp only [hi]

def param (a : ℕ → ι → ℝ) (p : ℕ → Bool) (ell cw : ℝ) (b : ℕ → ℝ) (t : ℕ) : AdaptiveSide.Config ι :=
  config (a t) (EpochGeometry.schedule a p t) ell cw (b t)

theorem schedule_valid {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (k : ℕ) {cw : ℝ} (hcw : 0 < cw) (hc : cw*50000 ≤ 1)
    (b : ℕ → ℝ) (hb : ∀ t, 0 < b t ∧ b t ≤ 4)
    (hm : ∀ t, EpochGeometry.total (a t) ≤ 2*k)
    (hmin : ∀ t i, 0 < a t i → (9/100000:ℝ) ≤ a t i) (t : ℕ) :
    AdaptiveSide.valid (param a p (EpochAlpha.ell k) cw b t) := by
  have hs := EpochGeometry.schedule_valid ha p t
  apply valid hs (EpochAlpha.ell_one k) hcw hc (hb t).1 (hb t).2
  intro i
  have hi := (mem i.property).1
  exact EpochAlpha.height_upper (EpochParameters.active_total_pos hs hi)
    (EpochAlphaSchedule.base_bound p hm t) (hmin t i hi)

end UniformKServer.EpochSide

end


end

end OAI
