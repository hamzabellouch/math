import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.PreparedMixture
import OAI.Combinatorics.SharpRamsey.Windows.UniformOpen
import OAI.Combinatorics.SharpRamsey.Windows.UniformMovement
import OAI.Combinatorics.SharpRamsey.Selection.FilteredPredeletion
import OAI.Combinatorics.SharpRamsey.Exposure.ZeroExposure

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance openExpBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
local instance openExpFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance openExpSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
local instance openExpBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)

def openBad (J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) :=
  badIndices ((model w n k p θ G t).tupleLaw z.1) ((model w n k p θ G t).embedding z.1)
    ((model w n k p θ G t).owner z.1) (fun _ _=>0) J D a z.2

def openKeep (u : Θ→Slot w (n+k)→ℝ) (gap : ℝ) (z : (model w n k p θ G t).FreshHistory) (i : Fin w) : Prop :=
  u z.1.1 ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,false)))-
    u z.1.1 ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,true)))≤gap

def openLive (u : Θ→Slot w (n+k)→ℝ) (gap J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) :=
  (univ\badWindows ((model w n k p θ G t).representative z) (openBad w n k p θ G t J D a z)).filter
    (openKeep w n k p θ G t u gap z)

def openPop (u : Θ→Slot w (n+k)→ℝ) (gap J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) : ℕ :=
  ∑ i∈openLive w n k p θ G t u gap J D a z,
    (goodMiddle w n k p θ G t z (openBad w n k p θ G t J D a z) i).card

variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (e : ∀ z : PositiveHistory w n k p θ G t hp,
    Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
      (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))

def openTargets (J D a : ℝ) (y : (mixedPrepared w n k p θ G t hp e).Ω) :
    Fin w→List (Projectivization K (Module.Dual K V)×Projectivization K V) := fun i=>
  List.ofFn (fun j=>(e y.1).source y.2
    (goodTarget w n k p θ G t y.1.val (openBad w n k p θ G t J D a y.1.val) i j))

def openTree (u : Θ→Slot w (n+k)→ℝ) (gap J D a : ℝ) (fallback : Fin w)
    (y : (mixedPrepared w n k p θ G t hp e).Ω) :=
  liveTree (openLive w n k p θ G t u gap J D a y.1.val) fallback

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma openPopulation_size (u : Θ→Slot w (n+k)→ℝ) (gap J D a : ℝ) (fallback : Fin w)
    (y : (mixedPrepared w n k p θ G t hp e).Ω) :
    (population (openTargets w n k p θ G t hp e J D a y)
      (openTree w n k p θ G t hp e u gap J D a fallback y)).length≤w*(2*(n+k)) := by
  change (population (fun i=>List.ofFn (fun j=>(e y.1).source y.2
    (goodTarget w n k p θ G t y.1.val (openBad w n k p θ G t J D a y.1.val) i j)))
    (liveTree (openLive w n k p θ G t u gap J D a y.1.val) fallback)).length≤_
  rw [goodPopulation_length]
  exact goodPopulation_size w n k p θ G t y.1.val _ _

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma openPopulation_length (u : Θ→Slot w (n+k)→ℝ) (gap J D a : ℝ) (fallback : Fin w)
    (y : (mixedPrepared w n k p θ G t hp e).Ω) :
    (population (openTargets w n k p θ G t hp e J D a y)
      (openTree w n k p θ G t hp e u gap J D a fallback y)).length=
    openPop w n k p θ G t u gap J D a y.1.val := by
  exact goodPopulation_length w n k p θ G t y.1.val _ _ _ _

theorem eventually_open_experiment (d : ℕ) (η C A c loss : ℝ)
    (hη : 0<η) (hC : 0<C) (hc : 0<c) (hloss : 0<loss) :
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
          5*(budget/(D*σ^beta η)+2*budget/((k:ℝ)*a))+(w*(2*(n+k)):ℝ)*(2*loss) := by
  filter_upwards [eventually_open_decoder d η C A loss hη hC hloss,
    eventually_open_movement d η c loss hη hc hloss,
    eventually_ge_atTop (1:ℝ)] with σ hdec hmove hσ
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hτ hτsmall Ω Θ _ _ w n k p θ G S u r J budget hn hk hkn hw hcw hr hJ hSJ hS hf hcon hcap hband hbudget fallback
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  have hσ0 : 0<σ := by linarith
  have hD : 0<D*σ^beta η := mul_pos ((rpow_pos_of_pos hσ0 _).trans_le hDl) (rpow_pos_of_pos hσ0 _)
  have ha : 0<a := by dsimp [a]; exact div_pos (rpow_pos_of_pos hσ0 _) (by exact_mod_cast Finite.card_pos)
  obtain ⟨t,hbad,hrep,_⟩:=actual_realized_zero n k hn hk J (D*σ^beta η) a budget hD ha p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) (fun _=>embedding_owner w (n+k))
    S hS hSJ hbudget
  let hp:=contextual_positive n k (by omega : 0<n) p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t
  have hh := hdec K V hdim hlog D P H hDl hDu book hτ hτsmall Ω Θ w n k p θ G S u r J
    hw hr hJ hS hf hcon hcap hband t hp
  choose e he using fun z : PositiveHistory w n k p θ G t hp=>hh z.val z.property fallback
  refine ⟨t,e,?_⟩
  let pop:=openPop w n k p θ G t u (scaleKstar σ η D) J (D*σ^beta η) a
  let out:=fun tab (y : (mixedPrepared w n k p θ G t hp e).Ω)=>
    (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
      (fun i=>book.chronoChoose hdim hτ hτsmall ((e y.1).supports y.2 i))
      (fun _=>chronoRead (16*scaleKstar σ η D))
      (openTargets w n k p θ G t hp e J (D*σ^beta η) a y) tab
      (openTree w n k p θ G t hp e u (scaleKstar σ η D) J (D*σ^beta η) a fallback y) (univ,univ)).length
  have hlocal : ∀ z,(∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) (16*scaleKstar σ η D))).mass tab*
      ∑ y,(e z).μ.mass y*((pop z.val:ℝ)-(out tab ⟨z,y⟩:ℝ)))≤(pop z.val:ℝ)*loss := by
    intro z
    dsimp only [pop,out,openPop,openTree,openLive,openKeep,openBad]
    unfold openTargets
    convert he z using 1 <;> simp only [openBad,Nat.cast_sum] <;> rfl
  have hdrop:=hmove K V hdim hlog D hDl hDu Ω Θ w n k p θ G S u r J
    hcw hr hJ hS hf hcon hcap hband t hp
  have hdelete := filtered_predeletion_mean w n k p θ G t hkn hp
    (openBad w n k p θ G t J (D*σ^beta η) a)
    (openKeep w n k p θ G t u (scaleKstar σ η D)) _ loss hbad hrep (by
      intro z hz
      simpa only [openBad,openKeep,not_le] using hdrop z hz)
  have hres := attachedPrepared_loss w n k p θ G t hp e
    (Law.ofPublic (PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) (16*scaleKstar σ η D))))
    (w*(2*(n+k))) pop out loss _ hloss.le
    (fun z=>goodPopulation_size w n k p θ G t z _ _) hlocal
    (by simpa only [pop,openPop,openLive,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hdelete)
  dsimp only [Law.ofPublic,out] at hres
  convert hres using 1 <;> push_cast <;> ring
end
end SharpLogRamsey.Selection.Windows

end

end OAI
