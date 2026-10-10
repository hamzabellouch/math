import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.TreeHeight
import OAI.Combinatorics.SharpRamsey.Windows.OpenRealization
import OAI.Combinatorics.SharpRamsey.Parameters.OpenScales

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance uniformIntOpenBanks {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
    [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
    (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
local instance uniformIntOpenFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance uniformIntOpenSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
local instance uniformIntOpenBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _

theorem eventually_open_decoder (d : ℕ) (η C A loss : ℝ)
    (hη : 0<η) (hC : 0<C) (hloss : 0<loss) :
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
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J : ℝ),
        (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J →
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
          ∀ fallback : Fin w,
          let M:=model w n k p θ G t
          let q:=M.tupleLaw z.1
          let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
          let c:=fun (_ _ : M.Index z.1)=>(0:NNReal)
          let bad:=badIndices q (M.embedding z.1) (M.owner z.1) c J (D*σ^beta η) a z.2
          let live:=(univ\badWindows (M.representative z) bad).filter
            (fun i=>u z.1.1 (M.origin z.1 (M.representative z (i,false)))-
              u z.1.1 (M.origin z.1 (M.representative z (i,true)))≤ scaleKstar σ η D)
          ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) q,
            (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
              ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
              (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
                (fun i=>book.chronoChoose hdim hτ hτsmall (e.supports ω i))
                (fun _=>chronoRead b)
                (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) tab
                (liveTree live fallback) (univ,univ)).length))≤
              (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*loss := by
  let E:=20000*((d:ℝ)+3)^2
  let CE:=E+3251
  have hb:=beta_pos hη
  have hCE : 0≤CE := by dsimp [CE,E]; positivity
  filter_upwards [eventually_prepared_reciprocal d (beta η) hb,
    eventually_integer_regime η hη,eventually_open_regime η d hη,eventually_liveTree_height (beta η) C A hb hC,
    eventually_tree_small (beta η) CE loss hb hCE hloss,
    eventually_ge_atTop (1:ℝ)] with σ hsupp hreg hopen hheight htree hσ
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hτ0 hτsmall Ω Θ _ _ w n k p θ G S u r J hw hr hJ hS hf hcon hcap hband t hp z hz fallback
  let M:=model w n k p θ G t
  let q:=M.tupleLaw z.1
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  let κ:=scaleK σ η D
  let gap:=scaleKstar σ η D
  let b:=16*gap
  let τ:=σ^(-100*beta η)
  let c:=fun (_ _ : M.Index z.1)=>(0:NNReal)
  let bad:=badIndices q (M.embedding z.1) (M.owner z.1) c J (D*σ^beta η) a z.2
  let live:=(univ\badWindows (M.representative z) bad).filter
            (fun i=>u z.1.1 (M.origin z.1 (M.representative z (i,false)))-
              u z.1.1 (M.origin z.1 (M.representative z (i,true)))≤ scaleKstar σ η D)
  have hσ0 : 0<σ := by linarith
  have hD : 0<D := (rpow_pos_of_pos hσ0 _).trans_le hDl
  have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  have hreg':=hreg D hDl hDu
  have hpb : ∀ i,OpenBand r (log (Nat.card K)) gap (u z.1.1 (M.origin z.1 i)) := by
    have hh:=prepared_context_property n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz
      (fun θ=>∀ i,OpenBand r σ gap (u θ i)) hband
    intro i
    rw [hlog]
    exact hh _
  obtain ⟨e,he⟩:=open_population_realization w n k p θ G t hp z hz hdim book
    (by dsimp [b,gap,scaleKstar]; positivity) hreg'.2.2.2.1 hreg'.2.2.2.2
    r hr κ gap J (D*σ^beta η) a (3251*σ^(-2*beta η))
    (fun i=>u z.1.1 (M.origin z.1 i)) hpb
    (hopen D (Nat.card K) hDl hq0).1 hreg'.2.1
    (by have hg : 0≤gap := by dsimp [gap,scaleKstar]; positivity
        have hh:=hreg'.2.2.1; dsimp only [gap,b] at *; linarith)
    (by dsimp [a]; positivity) hcon hf fallback (by
      dsimp only
      intro i hi
      have hh:=hsupp K V hdim hlog Ω Θ (Slot w (n+k)) (Block w) p θ G S u n k
        (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp D J a hS hf hcap hDl hJ z c hz i hi
      simpa only [hlog,κ,scaleK] using hh)
  refine ⟨e,he.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply htree (Nat.card K) ((liveTree live fallback).height:ℝ) (E*a) (E*a) (E*a)
    (3251*σ^(-2*beta η)) (3251*σ^(-2*beta η))
  · rw [←hlog]
    exact (log_le_sub_one_of_pos hq0).trans (by linarith)
  · positivity
  · exact hheight w hw live fallback
  · dsimp [E,a]; positivity
  · dsimp [E,a]; positivity
  · dsimp [E,a]; positivity
  all_goals first
    | (have heq : (Nat.card K:ℝ)*(E*a)=E*σ^(-2000*beta η) := by dsimp [a]; field_simp [ne_of_gt hq0]
       rw [heq]
       apply mul_le_mul_of_nonneg_right _ (by positivity)
       dsimp [CE]; linarith)
    | (apply mul_le_mul_of_nonneg_right _ (by positivity)
       dsimp [CE,E]
       nlinarith [sq_nonneg ((d:ℝ)+3)])
end
end SharpLogRamsey.Selection.Windows

end

end OAI
