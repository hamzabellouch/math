import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotAlphabet

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {n : ℕ} {b τ P H : ℝ}

theorem Input.choose_allowed
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
    {A : Finset (Projectivization K V)} {B : Finset (Projectivization K (Module.Dual K V))}
    (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (hW : d.W∈book.library (d.U,d.UT) (A∩d.U).card (B∩d.UT).card)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (c : Code (K:=K) (V:=V) b) (hc : d.choose hdim z w=some c) :
    c∈book.allowed z (d.U,d.UT) := by
  unfold Input.choose at hc
  split at hc
  · cases hc
  · rename_i i hi
    let row := rowAt _ (z d.firstCall.address) i
    let call := d.secondCall hdim row (index_valid _ _ _ i hi)
    change (call.bankIndex (b+log 1000000) n w).map
      (fun j=>(⟨d.firstCall.address,i⟩,⟨call.address,j⟩))=some c at hc
    obtain ⟨j,hj,he⟩ := Option.map_eq_some_iff.mp hc
    cases he
    have hW' : d.W∈book.library (d.U,d.UT) call.address.2.2 d.firstCall.address.2.2 := by
      change d.W∈book.library (d.U,d.UT)
        ((A∩d.U).image (bidual (K:=K) (V:=V))).card (B∩d.UT).card
      simpa only [card_image_of_injective _ (bidual (K:=K) (V:=V)).injective] using hW
    let v : book.LocalRaw (d.U,d.UT) :=
      ⟨call.address.2.2,d.firstCall.address.2.2,⟨d.W,hW'⟩,i,j⟩
    apply book.mem_allowed z (d.U,d.UT) v
    have hWn : d.W.Nonempty := d.source_nonempty.mono inter_subset_right
    have hBn : (cap SharpLogRamsey.Incidence.Incident (Nat.card K) d.UT row).Nonempty :=
      call.source_nonempty.mono call.source_proposal
    dsimp only [Book.decodeRaw,v]
    rw [dite_eq_left hWn]
    change (if hc : (cap SharpLogRamsey.Incidence.Incident (Nat.card K) d.UT row).Nonempty then _ else _)=_
    rw [dite_eq_left hBn]
    rfl

theorem Book.choose_allowed (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
    (hτ : 0≤τ) (hτsmall : τ≤1/40000)
    (s : Original (K:=K) (V:=V) n b) (z : Banks (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (c : Code (K:=K) (V:=V) b) (hc : book.choose hdim hτ hτsmall s z U=some c) :
    c∈book.allowed z.1 U := by
  unfold Book.choose at hc
  split at hc
  · rename_i hr
    let d := book.prepare hdim hτ hτsmall s U hr
    have hs := book.prepare_spec hdim hτ hτsmall s U hr
    dsimp only at hs
    have hW : d.W∈book.library (d.U,d.UT) (s.A∩d.U).card (s.B∩d.UT).card := by
      have hu : d.U=U.1 := congrArg Prod.fst hs.1
      have hv : d.UT=U.2 := congrArg Prod.snd hs.1
      simpa only [hu,hv] using hs.2.1
    have hh := d.choose_allowed book hdim hW z.1 z.2 c hc
    rw [hs.1] at hh
    exact hh
  · cases hc

end
end SharpLogRamsey.ActualPivot

end

end OAI
