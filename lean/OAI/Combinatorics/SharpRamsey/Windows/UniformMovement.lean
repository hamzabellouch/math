import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.OpenScales
import OAI.Combinatorics.SharpRamsey.Windows.OpenMovement

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance movementFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance movementSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
local instance movementBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _

theorem eventually_open_movement (d : ℕ) (η c ε : ℝ)
    (hη : 0<η) (hc : 0<c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ (D : ℝ), σ^beta η≤D → D≤σ^(1-η/2) →
      ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J : ℝ),
        c*σ^(1+η/2)≤(w:ℝ)*D → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,OpenBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        ∀ (t : Fin k) (hp : ∀ z,0<(model w n k p θ G t).remaining z)
          (z : (model w n k p θ G t).FreshHistory),
          ((model w n k p θ G t).freshLaw hp).mass z≠0 →
          let M:=model w n k p θ G t
          let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
          let bad:=badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1)
            (fun _ _=>0) J (D*σ^beta η) a z.2
          let live:=univ\badWindows (M.representative z) bad
          ((live.filter (fun i=>scaleKstar σ η D<
            u z.1.1 (M.origin z.1 (M.representative z (i,false)))-
              u z.1.1 (M.origin z.1 (M.representative z (i,true))))).card:ℝ)≤ε*w := by
  filter_upwards [eventually_prepared_reciprocal d (beta η) (beta_pos hη),
    eventually_integer_regime η hη,eventually_open_regime η d hη,
    eventually_open_deletion_small η c ε hη hc hε,eventually_ge_atTop (1:ℝ)]
    with σ hsupp hreg hopen hdelete hσ
  intro K V _ _ _ _ _ _ _ hdim hlog D hDl hDu Ω Θ _ _ w n k p θ G S u r J hw hr hJ hS hf hcon hcap hband t hp z hz
  let M:=model w n k p θ G t
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  let κ:=scaleK σ η D
  let gap:=scaleKstar σ η D
  have hσ0 : 0<σ := lt_of_lt_of_le zero_lt_one hσ
  have hD : 0<D := (rpow_pos_of_pos hσ0 _).trans_le hDl
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  have hg : 0<gap := by dsimp [gap,scaleKstar]; positivity
  have hpb : ∀ i,OpenBand r (log (Nat.card K)) gap (u z.1.1 (M.origin z.1 i)) := by
    have hh:=prepared_context_property n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz (fun θ=>∀ i,OpenBand r σ gap (u θ i)) hband
    intro i
    rw [hlog]
    exact hh _
  have hh:=open_window_deletion w n k p θ G t hp z hz hdim r hr κ gap J (D*σ^beta η) a hg.le
    (fun i=>u z.1.1 (M.origin z.1 i)) hpb (hopen D (Nat.card K) hDl hq).1
    (hreg D hDl hDu).2.1 (hopen D (Nat.card K) hDl hq).2 hcon (by
      dsimp only
      intro i hi
      have hh:=hsupp K V hdim hlog Ω Θ (Slot w (n+k)) (Block w) p θ G S u n k
        (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp D J a hS hf hcap hDl hJ z (fun _ _=>0) hz i hi
      simpa only [hlog,κ,scaleK] using And.intro hh.1 hh.2.1)
  rw [hlog] at hh
  have hb:=hdelete D (w:ℝ) hDl (by positivity) hw
  dsimp only [gap,κ] at hh hg
  dsimp only
  nlinarith
end
end SharpLogRamsey.Selection.Windows

end

end OAI
