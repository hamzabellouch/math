import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylWitnessResidues

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem sum_fin_succ_residues {d : ℕ} [NeZero d] (f : ZMod d → ℝ) :
    (∑ r : Fin d,f ((r.val+1:ℕ):ZMod d))=∑ z : ZMod d,f z := by
  let e : Fin d ≃ ZMod d := (ZMod.finEquiv d).toEquiv.trans (Equiv.addRight 1)
  have he (r : Fin d) : e r=((r.val+1:ℕ):ZMod d) := by
    have hcast : (ZMod.finEquiv d) r=(r.val:ZMod d) := by
      have hv : ((ZMod.finEquiv d) r).val=r.val := by
        cases d with
        | zero => exact False.elim (NeZero.ne 0 rfl)
        | succ d => rfl
      rw [← hv]
      exact (ZMod.natCast_zmod_val _).symm
    change (ZMod.finEquiv d) r+1=((r.val+1:ℕ):ZMod d)
    rw [hcast]
    push_cast
    rfl
  simpa only [he] using e.sum_comp f

theorem centered_witness_amplitude_l1 {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i,p i)]
    (hp : ∀ i,(p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i,Finset (ZMod (p i))) (c : ZMod (∏ i,p i)) :
    (∑ r : Fin (∏ i,p i),‖centeredProductTransform p hcop S
      (c*(((r.val+1:ℕ):ZMod (∏ i,p i)))^2)‖) ≤
      (∏ i,p i:ℕ)*Real.sqrt ((2:ℝ)^Fintype.card ι) := by
  calc
    _ = ∑ z : ZMod (∏ i,p i),‖centeredProductTransform p hcop S (c*z^2)‖ :=
      sum_fin_succ_residues (fun z => ‖centeredProductTransform p hcop S (c*z^2)‖)
    _ ≤ _ := centeredProductTransform_square_l1_le p hp hcop S c

def witnessBlockCount (d : ℕ) (N : ℝ) : ℕ := ⌊N/d⌋₊+1

theorem witnessBlockCount_bounds {d : ℕ} [NeZero d] {N : ℝ} (hN : 0 < N) :
    ⌊N⌋₊ ≤ witnessBlockCount d N*d ∧
      (witnessBlockCount d N:ℝ) ≤ N/d+1 := by
  have hd : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_neZero d
  have hlo : N/d < (witnessBlockCount d N:ℝ) := by
    simpa [witnessBlockCount] using Nat.lt_floor_add_one (N/d)
  have hhi : (witnessBlockCount d N:ℝ) ≤ N/d+1 := by
    dsimp [witnessBlockCount]
    push_cast
    have hh : (⌊N/d⌋₊:ℝ) ≤ N/d := Nat.floor_le (by positivity)
    linarith
  refine ⟨?_,hhi⟩
  have hn := (div_lt_iff₀ hd).mp hlo
  have hfloor := Nat.floor_le hN.le
  exact_mod_cast (show (⌊N⌋₊:ℝ) ≤ (witnessBlockCount d N*d:ℕ) by
    push_cast
    linarith)

theorem centered_quadratic_witness_progression {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i,NeZero (p i)] [NeZero (∏ i,p i)]
    (hp : ∀ i,(p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i,Finset (ZMod (p i))) (mInv : ZMod (∏ i,p i))
    (s v : ℕ) (R h θ ε : ℝ)
    (hN : 0 < Real.sqrt (R/((s:ℝ)*v/(∏ i,p i:ℕ))))
    (hlarge : Real.sqrt ((2:ℝ)^Fintype.card ι)*ε ≤
      ‖centeredQuadraticSum p hcop S mInv s v 1 R h θ‖) :
    let d := ∏ i,p i
    let N := Real.sqrt (R/((s:ℝ)*v/(d:ℕ)))
    ∃ r : Fin d,(N/d)*ε ≤ ‖witnessProgression d (witnessBlockCount d N)
      N ((h+θ)*((s:ℝ)*v/d)) r‖ := by
  let d := ∏ i,p i
  let N := Real.sqrt (R/((s:ℝ)*v/(d:ℕ)))
  let c : ZMod d := -((s*v:ℕ):ZMod d)*mInv
  have ha : centeredQuadraticAmplitude p hcop S mInv s v =
      (fun w : ℕ => centeredProductTransform p hcop S (c*(w:ZMod d)^2)) := by
    funext w
    exact centeredQuadraticAmplitude_scalar_square p hcop S mInv s v w
  unfold centeredQuadraticSum at hlarge
  rw [ha] at hlarge
  exact exists_large_witness_progression d (witnessBlockCount d N) hN
    (Real.sqrt_pos.mpr (by positivity)) (witnessBlockCount_bounds hN).1
    (fun w => centeredProductTransform p hcop S (c*w^2)) _
    (centered_witness_amplitude_l1 p hp hcop S c) hlarge

end Ostmann.QuadraticCenter

end

end OAI
