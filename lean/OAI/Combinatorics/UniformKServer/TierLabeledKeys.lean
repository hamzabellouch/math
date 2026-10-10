import Mathlib
import OAI.Combinatorics.UniformKServer.TierLabels
import OAI.Combinatorics.UniformKServer.TierKeyProcess

namespace OAI

                                      
section

noncomputable section
namespace UniformKServer.TierLabeledKeys
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

abbrev Slot (X : Type) [Fintype X] (K : ℕ) := CooldownLabels.Slot (Fintype.card X*K^2)

def anchor (a : X) (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (l : Slot X K) : X :=
  if h : ∃ i∈TierLabels.reserved r K q c t, (TierLabels.labels r K q c t).label i=l then
    c (Classical.choose h) else a

theorem anchor_record (a : X) (r : ℝ) (hr : 0≤r) (K : ℕ) (q : Fin N → Prop)
    (c : Fin N → X) (t : ℕ) (i : Fin N) (hi : i∈TierLabels.reserved r K q c t) :
    anchor a r K q c t ((TierLabels.labels r K q c t).label i)=c i := by
  have he : ∃ j∈TierLabels.reserved r K q c t,
      (TierLabels.labels r K q c t).label j=(TierLabels.labels r K q c t).label i := ⟨i,hi,rfl⟩
  rw [anchor,dite_eq_left he]
  have hc := Classical.choose_spec he
  rw [TierLabels.injective r hr K q c t hc.1 hi hc.2]

def key (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) : Option (Slot X K) :=
  (TierKeyProcess.key r K q c t τ ω p).map (TierLabels.labels r K q c t).label

theorem key_witness (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r)
    (p : X) (l : Slot X K) (hl : key r K q c t τ ω p=some l) :
    ∃ i∈TierLabels.reserved r K q c t, TierKeyProcess.key r K q c t τ ω p=some i ∧
      (TierLabels.labels r K q c t).label i=l := by
  obtain ⟨i,hi,hlabel⟩ := Option.map_eq_some_iff.mp hl
  refine ⟨i,?_,hi,hlabel⟩
  exact TierLabels.live_reserved r K hK hq q c t τ
    ((mem_sort _).mp (TierKeys.key_mem _ _ _ c ω p i hi))

theorem covers (a : X) (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r)
    (p : X) (l : Slot X K) (hl : key r K q c t τ ω p=some l) :
    dist p (anchor a r K q c t l)≤2*r := by
  obtain ⟨i,hi,hkey,rfl⟩ := key_witness r K hK hq q c t τ ω p l hl
  rw [anchor_record a r hr.le K q c t i hi]
  exact TierKeyProcess.covers r hr K hK q c t τ ω p i hkey

theorem common_anchor (a : X) (r : ℝ) (hr : 0≤r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r)
    (x y : X) (l : Slot X K) (hx : key r K q c t τ ω x=some l)
    (hy : key r K q c (t+1) τ ω y=some l) :
    anchor a r K q c t l=anchor a r K q c (t+1) l := by
  obtain ⟨i,hi,hxi,hli⟩ := key_witness r K hK hq q c t τ ω x l hx
  obtain ⟨j,hj,hyj,hlj⟩ := key_witness r K hK hq q c (t+1) τ ω y l hy
  have hij := TierLabels.common_record r hr K q c t i j hi hj (hli.trans hlj.symm)
  rw [←hli,anchor_record a r hr K q c t i hi,hli,←hlj,anchor_record a r hr K q c (t+1) j hj,hij]

end UniformKServer.TierLabeledKeys

end


end

end OAI
