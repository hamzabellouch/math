import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.OpenExperiment
import OAI.Combinatorics.SharpRamsey.Entropy.InformationScales

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
local instance openQuarterBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
local instance openQuarterFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance openQuarterSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
local instance openQuarterBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _

theorem eventually_open_quarter (d : ℕ) (η C A C0 c : ℝ)
    (hη : 0<η) (hC : 0<C) (hC0 : 0≤C0) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      ∀ (hdim : Module.finrank K V=d+3), log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
        (hτ : 0≤τ) (hτsmall : τ≤1/40000)
        (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J budget : ℝ),
        ∀ (hn : 2≤n), 0<k → k≤n → (w:ℝ)≤C*σ^A → c*σ^(1+η/2)≤(w:ℝ)*D → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J →
        (∀ z i,log (S z i).card≤J) →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,OpenBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        (∑ z,(p.map θ).mass z*((Fintype.card (Slot w (n+k)):ℝ)*J-
          entropy ((p.cond θ z).map G)))≤budget →
        budget≤C0*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) →
        c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
        ∀ fallback : Fin w, ∃ t : Fin k,
        let hp:=contextual_positive n k (by omega : 0<n) p θ G
          (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t
        ∃ e : ∀ z : PositiveHistory w n k p θ G t hp,
          Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
            (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))),
        let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
        let expmt:=attachedPrepared w n k p θ G t hp e
        (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
          ∑ ω,expmt.μ.mass ω*((w*(2*(n+k)):ℝ)-
            (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
              (fun i=>book.chronoChoose hdim hτ hτsmall ((e ω.1.1).supports ω.1.2 i))
              (fun _=>chronoRead b) (openTargets w n k p θ G t hp e J (D*σ^beta η) a ω.1) tab
              (openTree w n k p θ G t hp e u (scaleKstar σ η D) J (D*σ^beta η) a fallback ω.1) (univ,univ)).length))≤
          (w*(2*(n+k)):ℝ)/4 := by
  filter_upwards [eventually_open_experiment d η C A c (1/16) hη hC hc (by norm_num),
    eventually_information_bad_small η C0 c (1/40) hη hC0 hc (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ hex hsmall hσ
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hτ hτsmall Ω Θ _ _ w n k p θ G S u r J budget hn hk hkn hw hcw hr hJ hSJ hS hf hcon hcap hband hbudget hb hk0 fallback
  obtain ⟨t,e,he⟩:=hex K V hdim hlog D P H hDl hDu book hτ hτsmall Ω Θ w n k p θ G S u r J budget
    hn hk hkn hw hcw hr hJ hSJ hS hf hcon hcap hband hbudget fallback
  refine ⟨t,e,?_⟩
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  have hσ0 : 0<σ := by linarith
  have hD : 0<D := (rpow_pos_of_pos hσ0 _).trans_le hDl
  have hbad:=hsmall (Nat.card K) D (w*(2*(n+k)):ℝ) budget k hq hD (by positivity) hb hk0
  dsimp only at he hbad ⊢
  exact he.trans (by nlinarith)
end
end SharpLogRamsey.Selection.Windows

end

end OAI
