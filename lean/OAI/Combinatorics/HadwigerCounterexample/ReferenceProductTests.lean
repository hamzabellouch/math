import OAI.Combinatorics.HadwigerCounterexample.KeyReferenceLaws
import OAI.Combinatorics.HadwigerCounterexample.EndpointTemplateConcentration

namespace OAI

/-! # Reference Product Tests -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Function Finset Filter
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

set_option maxHeartbeats 600000 in
theorem reference_product (t : Tagging p I) (q : I → F)
    (f : ∀ i,Wgt (AtomKey (p:=p) (t i) N))
    (hf : ∀ i x,|f i x|≤1) (hN : 2*num (I×Toast p)-(N:ℝ)≤ -1) :
    |avg (lawNu p N t q) (prodW f)- ∏ i,avg (lawOmega p N (t i) (q i)) (f i)|≤
      2*netFact (trayPort p t)*bp (-(N:ℝ)/2) := by
  classical
  let F (i : I) := (f i)∘(mug p (t i) N).symm
  let g := trayPort p t
  let A := trayMap p t q
  have hpL i := show 2*num (Port g i)-(N:ℝ)≤ -1 by linarith only [hN,port_limit g i]
  have he :
      avg (rackWave A N) (brightProd F) =avg (lawNu p N t q) (prodW f) := by
    unfold A; rw [←lawtray,mapW_avg]
    have hh x : brightProd F (tray p t N x)=prodW f x := by
      simp_rw [brightProd,tray_sips,F,Function.comp_apply,Equiv.symm_apply_apply]
      rfl
    simp_rw [hh]
  have hw i : avg (rackWave (laneM A i) N) (F i)=avg (lawOmega p N (t i) (q i)) (f i) := by
    unfold A; rw [←lawmug,mapW_avg]
    simp_rw [F,Function.comp_apply, Equiv.symm_apply_apply]
  have h := compare_waves A F (fun i x => hf _ _) hpL
  simp_rw [he,hw] at h; exact h

theorem priceNu (t : Tagging p I) (q : I→F) (hN : 2*num (I×Toast p)-(N:ℝ) ≤ -1) :
    (netFact (trayPort p t))⁻¹ ≤ pr unif (ownPart (p:=p) t q (N:=N)) := by
  classical
  let g := trayPort p t; let A := trayMap p t q
  have hpL i := show 2*num (Port g i)-(N:ℝ)≤ -1 by linarith only [hN,port_limit g i]
  have he : pr unif (gramPart A (N:=N))=pr unif (ownPart (p:=p) t q (N:=N)) := by
    rw [← unif_equiv (tray p t N),mapW_pr]
    unfold A
    congr 1; ext i
    exact (tray_wave ..).symm
  rw [←he]
  exact wave_norm A N hpL
theorem nuLaw (t : Tagging p I) (q : I → F) (hN : 2*num (I×Toast p)-(N:ℝ) ≤ -1) :
    IsLaw (lawNu p N t q) := by
  classical
  rw [lawNu,←on_unif]
  exact on_law unif_law.nz ((inv_pos_of_pos netFact_pos).trans_le (priceNu t q hN))

theorem priceOmega (t : Tagging p I) (q : I→F) (i : I) (hN : 2*num (I×Toast p)-(N:ℝ) ≤ -1) :
    (netFact (street (trayPort p t) i))⁻¹ ≤ pr unif (ownOne p (t i) (q i) (N:=N)) := by
  classical
  let g := street (trayPort p t) i; let A := laneM (trayMap p t q) i
  have hh j : num (Port g j)≤num (I×Toast p) := by
    apply le_trans (port_limit g j)
    exact_mod_cast Fintype.card_le_of_injective (fun j : Toast p => (i,j)) (fun i j h =>
      congrArg Prod.snd h)
  have hpL j := show 2*num (Port g j)-(N:ℝ)≤ -1 by linarith only [hN,hh j]
  have he : pr unif (gramPart A (N:=N))=pr unif (ownOne p (t i) (q i) (N:=N)) := by
    rw [← unif_equiv (mug p (t i) N),mapW_pr]
    unfold A
    congr 1; ext x
    exact (mug_wave ..).symm
  rw [←he]
  exact wave_norm A N hpL

theorem omegaLaw (p : Shape) (l : Tag p.g) (q : F) (hN : 2*num (Toast p)-(N:ℝ)≤ -1) :
    IsLaw (lawOmega p N l q) := by
  classical
  let t := fun (_ : Unit) => l
  have hh : 2*num (Unit×Toast p)-(N:ℝ)≤ -1 := by simpa [num] using hN
  rw [lawOmega,←on_unif]
  exact on_law unif_law.nz ((inv_pos_of_pos netFact_pos).trans_le
    (priceOmega t (fun _ : Unit => q) () hh))
end HadwigerCounterexample

end

end OAI
