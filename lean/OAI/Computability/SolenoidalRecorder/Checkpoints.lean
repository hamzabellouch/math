import Mathlib
import OAI.Computability.SolenoidalRecorder.Scans

namespace OAI

/-! Recording cycles and finite simulation of machine prefixes. -/

namespace Solenoidal
namespace Recorder
variable {M : Machine}
def checkpoint (q : M.State) (k : ℤ) (W : ℤ → M.Symbol) (H : ℤ → History M) : Config M :=
  ⟨.S q, k, tracks W H (fun _ => false)⟩

 

theorem recording_cycle (r : M.Instruction) (W : ℤ → M.Symbol) (H : ℤ → History M)
    (k g : ℤ) (hH : Frontier H g) (hk : k ≠ g)
    (hnew : k + r.move.displacement < g) (hread : W k = r.read) :
    Steps (2 * (g - (k + r.move.displacement)).toNat + 4)
      (checkpoint r.oldState k W H)
      (checkpoint r.nextState (k + r.move.displacement)
        (Function.update W k r.write) (appendHistory H g r)) := by
  let k' := k + r.move.displacement
  change k' < g at hnew
  let W' := Function.update W k r.write
  let marked : ℤ → Bool := Function.update (fun _ => false) k' true
  let H₁ := Function.update H g (.record r)
  let H₂ := appendHistory H g r
  let n := (g - k' - 1).toNat
  have hn : (n : ℤ) = g - k' - 1 := Int.toNat_of_nonneg (by omega)
  have hnR : k' + 1 + (n : ℤ) = g := by omega
  have hnL : g - (↑(n + 1) : ℤ) = k' := by omega
  have hkF : H k ≠ .frontier := fun he => hk ((hH.1 k).mp he)
  have hk'F : H k' ≠ .frontier := by
    intro he
    have := (hH.1 k').mp he
    omega
  have hgMark : marked g = false := by
    have hne : g ≠ k' := by omega
    simp [marked, hne]
  have hg1Mark : marked (g + 1) = false := by
    have hne : g + 1 ≠ k' := by omega
    simp [marked, hne]
  have hg1Hist : H₁ (g + 1) = .empty := by
    simp [H₁, hH.2 (g + 1) (by omega)]
  have h1 : Step (checkpoint r.oldState k W H)
      ⟨.A r, k', tracks W' H (fun _ => false)⟩ := by
    have ht := tracks_step W H (fun _ => false) k (.S r.oldState) (.A r)
      r.write (H k) false r.move (by simpa only [hread] using Rule.work r (H k) hkF)
    simpa only [checkpoint, Function.update_eq_self] using ht
  have h2 : Step (⟨.A r, k', tracks W' H (fun _ => false)⟩ : Config M)
      ⟨.R r, k' + 1, tracks W' H marked⟩ := by
    have ht := tracks_step W' H (fun _ => false) k' (.A r) (.R r)
      (W' k') (H k') true .right (Rule.mark r (W' k') (H k') hk'F)
    simpa only [Move.displacement, Function.update_eq_self] using ht
  have hscanR : Steps n (⟨.R r, k' + 1, tracks W' H marked⟩ : Config M)
      ⟨.R r, g, tracks W' H marked⟩ := by
    rw [← hnR]
    apply scanRight_steps
    intro j hj
    change H (k' + 1 + j) ≠ .frontier ∧ marked (k' + 1 + j) = false
    constructor
    · intro he
      have := (hH.1 _).mp he
      omega
    · have hne : k' + 1 + (j : ℤ) ≠ k' := by omega
      simp [marked, hne]
  have h3 : Step (⟨.R r, g, tracks W' H marked⟩ : Config M)
      ⟨.F r.nextState, g + 1, tracks W' H₁ marked⟩ := by
    have ht := tracks_step W' H marked g (.R r) (.F r.nextState)
      (W' g) (.record r) false .right
        (by simpa [((hH.1 g).mpr rfl), hgMark] using Rule.record r (W' g))
    simpa only [Move.displacement, ← hgMark, Function.update_eq_self] using ht
  have h4 : Step (⟨.F r.nextState, g + 1, tracks W' H₁ marked⟩ : Config M)
      ⟨.L r.nextState, g, tracks W' H₂ marked⟩ := by
    have ht := tracks_step W' H₁ marked (g + 1) (.F r.nextState) (.L r.nextState)
      (W' (g + 1)) .frontier false .left
        (by simpa [hg1Hist, hg1Mark] using Rule.advance r.nextState (W' (g + 1)))
    simpa only [Move.displacement, Int.add_neg_cancel_right, ← hg1Mark,
      Function.update_eq_self, H₂, appendHistory, H₁] using ht
  have hH₂ : Frontier H₂ (g + 1) := frontier_append hH r
  have hscanL : Steps (n + 1) (⟨.L r.nextState, g, tracks W' H₂ marked⟩ : Config M)
      ⟨.L r.nextState, k', tracks W' H₂ marked⟩ := by
    rw [← hnL]
    apply scanLeft_steps
    intro j hj
    change H₂ (g - j) ≠ .frontier ∧ marked (g - j) = false
    constructor
    · intro he
      have := (hH₂.1 _).mp he
      omega
    · have hne : g - (j : ℤ) ≠ k' := by omega
      simp [marked, hne]
  have h6 : Step (⟨.L r.nextState, k', tracks W' H₂ marked⟩ : Config M)
      (checkpoint r.nextState k' W' H₂) := by
    have hk₂ : H₂ k' ≠ .frontier := by
      intro he
      have := (hH₂.1 k').mp he
      omega
    have ht := tracks_step W' H₂ marked k' (.L r.nextState) (.S r.nextState)
      (W' k') (H₂ k') false .stay
        (by simpa [marked] using Rule.finish r.nextState (W' k') (H₂ k') hk₂)
    simpa only [Move.displacement, add_zero, checkpoint, marked, Function.update_eq_self,
      Function.update_idem] using ht
  have hsteps := (((((Steps.one h1).tail h2).trans hscanR).tail h3).tail h4).trans hscanL
  have htotal := hsteps.tail h6
  have hcount : (1 + 1 + n + 1 + 1) + (n + 1) + 1 = 2 * (g - k').toNat + 4 := by
    omega
  simpa only [hcount] using htotal

 
theorem checkpoint_next (w : List M.Symbol) (n : ℕ) (r₀ : ℤ) (hr₀ : 2 ≤ r₀)
    (H : ℤ → History M) (hH : Frontier H (r₀ + n))
    (hRun : M.halt (M.run w n).state = false) :
    ∃ r : M.Instruction,
      Steps (2 * (r₀ + n - (M.run w (n + 1)).head).toNat + 4)
        (checkpoint (M.run w n).state (M.run w n).head (M.run w n).tape H)
        (checkpoint (M.run w (n + 1)).state (M.run w (n + 1)).head (M.run w (n + 1)).tape
          (appendHistory H (r₀ + n) r)) := by
  let c := M.run w n
  let r : M.Instruction := ⟨(c.state, c.tape c.head), hRun⟩
  refine ⟨r, ?_⟩
  have hhead : c.head ≤ (n : ℤ) := (le_abs_self c.head).trans (M.run_head_bound w n)
  have hd : r.move.displacement ≤ 1 := (le_abs_self _).trans r.move.abs_displacement_le
  have hcycle := recording_cycle r c.tape H c.head (r₀ + n) hH (by omega) (by omega) rfl
  have heq : M.run w (n + 1) =
      (⟨r.nextState, c.head + r.move.displacement, Function.update c.tape c.head r.write⟩ : M.Config) := by
    rw [M.run_succ]
    simp only [Machine.step, hRun, Bool.false_eq_true, ↓reduceIte]
    rfl
  simpa only [heq, Machine.Instruction.oldState, c, r] using hcycle

 
theorem checkpoint_count_ge_six (w : List M.Symbol) (n : ℕ) (r₀ : ℤ) (hr₀ : 2 ≤ r₀) :
    6 ≤ 2 * (r₀ + n - (M.run w (n + 1)).head).toNat + 4 := by
  have hh := (le_abs_self _).trans (M.run_head_bound w (n + 1))
  omega

def initial (w : List M.Symbol) (r₀ : ℤ) : Config M :=
  checkpoint M.initial 0 (M.inputTape w) (initialHistory r₀)

 

theorem simulate_prefix (w : List M.Symbol) (r₀ : ℤ) (hr₀ : 2 ≤ r₀) (n : ℕ) :
    (∀ j : ℕ, j < n → M.halt (M.run w j).state = false) →
    ∃ (N : ℕ) (H : ℤ → History M),
      6 * n ≤ N ∧ Frontier H (r₀ + n) ∧
      Steps N (initial w r₀)
        (checkpoint (M.run w n).state (M.run w n).head (M.run w n).tape H) := by
  induction n with
  | zero =>
    intro _
    refine ⟨0, initialHistory r₀, by omega, ?_, ?_⟩
    · simpa using frontier_initial (M := M) r₀
    · simpa [initial, Machine.run, Machine.initialConfig] using Steps.zero (initial w r₀)
  | succ n ih =>
    intro hrun
    obtain ⟨N, H, hN, hH, hsteps⟩ := ih (fun j hj => hrun j (by omega))
    obtain ⟨r, hcycle⟩ := checkpoint_next w n r₀ hr₀ H hH (hrun n (by omega))
    refine ⟨N + (2 * (r₀ + n - (M.run w (n + 1)).head).toNat + 4),
      appendHistory H (r₀ + n) r, ?_, ?_, hsteps.trans hcycle⟩
    · have := checkpoint_count_ge_six w n r₀ hr₀
      omega
    · simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using frontier_append hH r
end Recorder
end Solenoidal

end OAI
