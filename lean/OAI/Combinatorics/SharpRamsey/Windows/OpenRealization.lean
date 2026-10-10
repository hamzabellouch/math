import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.GoodRealization
import OAI.Combinatorics.SharpRamsey.Reciprocal.PreparedReciprocal
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalProduct

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance openBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
local instance openDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
local instance openSlotDec : DecidableEq (Slot w (n+k)) :=
  @instDecidableEqProd (Fin w) (Fin (4*(n+k))) (@instDecidableEqFin w) (@instDecidableEqFin (4*(n+k)))
local instance openBlockDec : DecidableEq (Block w) := Classical.decEq _
variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (z : (model w n k p θ G t).FreshHistory)
  (hz : ((model w n k p θ G t).freshLaw hp).mass z≠0)
local notation "M" => model w n k p θ G t
local notation "q" => ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst z)

include hp hz

theorem open_population_realization
    (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/40000)
    (r : ℕ) (hr : r≤d+3) (κ gap J D a δ : ℝ)
    (u : (M).Index z.1→ℝ)
    (hband : ∀ i,OpenBand r (log (Nat.card K)) gap (u i))
    (hsmall : log 1024+3*κ<gap) (hκ : log (200/97)≤κ)
    (hbudget : gap+2*κ+log 4≤b) (ha : 0≤a)
    (hcon : ∀ ω,p.mass ω≠0→∀ i j,position i<position j→
      (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0)
    (hf : ∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0)
    (fallback : Fin w)
    (hsupp :
      let c:=fun (_ _ : (M).Index z.1)=> (0 : NNReal)
      let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
      ∀ i,i∉bad→
      let qi:=(q).marginal i
      let MA:=1024*exp (((d+3:ℕ):ℝ)*log (Nat.card K)-u i)
      let MB:=1024*exp (u i)
      let L:=((d+2:ℕ):ℝ)*log (Nat.card K)
      Nonempty (AuxiliarySupport qi.fst (univ.filter (goodFirst qi MA L κ (1/50))) MA κ) ∧
      Nonempty (AuxiliarySupport qi.snd (univ.filter (goodSecond qi MB L κ (1/50))) MB κ) ∧
      qi.fst.event (univ.filter (fun x=>¬goodFirst qi MA L κ (1/50) x))≤δ ∧
      qi.snd.event (univ.filter (fun x=>¬goodSecond qi MB L κ (1/50) x))≤δ) :
    let c:=fun (_ _ : (M).Index z.1)=> (0 : NNReal)
    let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
    let live:=(univ\badWindows ((M).representative z) bad).filter
      (fun i=>u ((M).representative z (i,false))-u ((M).representative z (i,true))≤gap)
    ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) q,
      (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
        ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
        (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
          (fun _=>chronoRead b)
          (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) tab
          (liveTree live fallback) (univ,univ)).length))≤
        (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*
          treeError (Nat.card K) τ (liveTree live fallback).height
            ((20000*((d:ℝ)+3)^2)*a) ((20000*((d:ℝ)+3)^2)*a)
            ((20000*((d:ℝ)+3)^2)*a) δ δ := by
  dsimp only
  let c:=fun (_ _ : (M).Index z.1)=> (0 : NNReal)
  let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
  let live:=(univ\badWindows ((M).representative z) bad).filter
      (fun i=>u ((M).representative z (i,false))-u ((M).representative z (i,true))≤gap)
  let MA:=fun i=>1024*exp (((d+3:ℕ):ℝ)*log (Nat.card K)-u i)
  let MB:=fun i=>1024*exp (u i)
  let L:=((d+2:ℕ):ℝ)*log (Nat.card K)
  let GA:=fun i=>univ.filter (goodFirst ((q).marginal i) (MA i) L κ (1/50))
  let GB:=fun i=>univ.filter (goodSecond ((q).marginal i) (MB i) L κ (1/50))
  have hgood : ∀ i∈live,∀ c,(M).representative z (i,c)∉bad := by
    intro i hi v
    have hh:¬((M).representative z (i,false)∈bad ∨ (M).representative z (i,true)∈bad) := by
      simpa only [mem_sdiff,mem_univ,true_and,badWindows,mem_filter,true_and] using (mem_filter.mp hi).1
    cases v
    · exact fun h=>hh (Or.inl h)
    · exact fun h=>hh (Or.inr h)
  apply good_population_realization w n k p θ G t z hdim book hb hτ hτsmall bad live fallback hgood
    GA GB MA MB (fun _=>κ) (fun _=>κ)
    (fun i hi=>(hsupp i hi).1.some) (fun i hi=>(hsupp i hi).2.1.some)
    (fun i=>by dsimp [MA]; positivity) (fun i=>by dsimp [MB]; positivity)
  · intro i hi
    exact reciprocal_window_product (Nat.card K) (d+3) (by exact_mod_cast Finite.card_pos)
      1024 κ _ _ gap b (by norm_num) (mem_filter.mp hi).2 hbudget
  · intro y hy i
    exact prepared_pair_property n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz (fun _ _ _ x _=>x.1.rep x.2.rep=0)
      (fun ω h i _=>hf ω h i) i i y hy
  · exact mul_nonneg (by positivity) ha
  · intro i j hij hgood
    have hh:=prepared_open_event n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz position hcon i j hij 1024 κ gap (u i) (u j) J D a
      (d+2) r (by simpa [Nat.add_assoc] using hdim) (by norm_num) (by omega)
      (hband i) (hband j) hsmall hκ
    specialize hh (by simpa only [Nat.add_assoc,Nat.cast_add,Nat.cast_ofNat,
      show (d:ℝ)+2+1=(d:ℝ)+3 by ring] using hgood)
    simpa only [goodIncidence,GA,GB,MA,MB,L,mem_filter,mem_univ,true_and,
      Nat.cast_add,Nat.cast_ofNat,show (d:ℝ)+2+1=(d:ℝ)+3 by ring] using hh
  · intro i hi
    have he : univ\GA i=univ.filter (fun x=>¬goodFirst ((q).marginal i) (MA i) L κ (1/50) x) := by
      ext x
      simp only [GA,mem_sdiff,mem_univ,true_and,mem_filter]
    rw [he]
    exact (hsupp i hi).2.2.1
  · intro i hi
    have he : univ\GB i=univ.filter (fun x=>¬goodSecond ((q).marginal i) (MB i) L κ (1/50) x) := by
      ext x
      simp only [GB,mem_sdiff,mem_univ,true_and,mem_filter]
    rw [he]
    exact (hsupp i hi).2.2.2
end
end SharpLogRamsey.Selection.Windows

end

end OAI
