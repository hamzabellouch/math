import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.IntegerQuarter
import OAI.Combinatorics.SharpRamsey.Execution.PreparedOutput

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}
local instance outputBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
local instance outputFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance outputSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
local instance outputBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _

theorem eventually_integer_output (d : ℕ) (η C A C0 c : ℝ)
    (hη : 0<η) (hC : 0<C) (hC0 : 0≤C0) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (_ : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
        (_ : 0≤b) (_ : 0≤H) (_ : 4≤P) (_ : b+log 1000000≤P)
        (_ : 0≤τ) (_ : τ≤1/40000)
        (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J M budget : ℝ),
        2≤n → 0<k → k≤n → (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J → 0≤M →
        (∀ z i,log (S z i).card≤J) →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,IntegerBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        (∀ ω,p.mass ω≠0→∀ W : Submodule K V,
          ((univ.filter (fun i=>G ω i∈orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ)≤M) →
        (∑ z,(p.map θ).mass z*((Fintype.card (Slot w (n+k)):ℝ)*J-
          entropy ((p.cond θ z).map G)))≤budget →
        budget≤C0*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) → M≤C0*σ →
        c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
        c*(Nat.card K:ℝ)*σ^(1+η/2)≤n →
        Fin w →
        Nonempty (ContextOutput p (fun ω=>flattenTuple (G ω)) (w*(n+k))
          (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
          (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H)
            w (Nat.log 2 w+1) (2*(n+k))) 2) := by
  filter_upwards [eventually_integer_quarter d η C A C0 c hη hC hC0 hc] with σ hex
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hb hH hP haP hτ hτsmall Ω Θ _ _ w n k p θ G S u r J M budget hn hk hkn hw hr hJ hM hSJ hS hf hcon hcap hband ho hbudget hbudget0 hM0 hk0 hn0 fallback
  obtain ⟨t,e,he⟩:=hex K V hdim hlog D P H hDl hDu book hτ hτsmall Ω Θ w n k p θ G S u r J M budget
    hn hk hkn hw hr hJ hM hSJ hS hf hcon hcap hband ho hbudget hbudget0 hM0 hk0 hn0 fallback
  let hp:=contextual_positive n k (by omega : 0<n) p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t
  exact prepared_context_of_mean w n k p θ G t hp e
    (integerBad (d:=d) w n k p θ G t r J (D*σ^beta η) (σ^(-2000*beta η)/(Nat.card K:ℝ)))
    (integerLive (d:=d) w n k p θ G t r J (D*σ^beta η) (σ^(-2000*beta η)/(Nat.card K:ℝ)))
    fallback hdim book hb hH hP haP hτ hτsmall (by omega) he
end
end SharpLogRamsey.Selection.Windows

end

end OAI
