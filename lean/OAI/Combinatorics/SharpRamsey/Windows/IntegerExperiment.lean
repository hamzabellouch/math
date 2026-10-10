import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.UniformInteger
import OAI.Combinatorics.SharpRamsey.Exposure.PreparedMixture

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
local instance experimentBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
local instance experimentFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance experimentSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
local instance experimentBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)

def integerBad (r : ℕ) (J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) :=
  badIndices ((model w n k p θ G t).tupleLaw z.1) ((model w n k p θ G t).embedding z.1)
    ((model w n k p θ G t).owner z.1)
    (reciprocalCharges ((model w n k p θ G t).tupleLaw z.1) Projectivization.rep Projectivization.rep
      (1/(100*((d:ℝ)+3))) r (d+3-r)) J D a z.2

def integerLive (r : ℕ) (J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) :=
  univ\badWindows ((model w n k p θ G t).representative z) (integerBad (d:=d) w n k p θ G t r J D a z)

def integerPop (r : ℕ) (J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) : ℕ :=
  ∑ i∈integerLive (d:=d) w n k p θ G t r J D a z,
    (goodMiddle w n k p θ G t z (integerBad (d:=d) w n k p θ G t r J D a z) i).card

variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (e : ∀ z : PositiveHistory w n k p θ G t hp,
    Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
      (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))

def integerTargets (r : ℕ) (J D a : ℝ) (y : (mixedPrepared w n k p θ G t hp e).Ω) :
    Fin w→List (Projectivization K (Module.Dual K V)×Projectivization K V) := fun i=>
  List.ofFn (fun j=>(e y.1).source y.2
    (goodTarget w n k p θ G t y.1.val (integerBad (d:=d) w n k p θ G t r J D a y.1.val) i j))

def integerTree (r : ℕ) (J D a : ℝ) (fallback : Fin w)
    (y : (mixedPrepared w n k p θ G t hp e).Ω) :=
  liveTree (integerLive (d:=d) w n k p θ G t r J D a y.1.val) fallback

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma integerPopulation_size (r : ℕ) (J D a : ℝ) (fallback : Fin w)
    (y : (mixedPrepared w n k p θ G t hp e).Ω) :
    (population (integerTargets w n k p θ G t hp e r J D a y)
      (integerTree w n k p θ G t hp e r J D a fallback y)).length≤w*(2*(n+k)) := by
  change (population (fun i=>List.ofFn (fun j=>(e y.1).source y.2
    (goodTarget w n k p θ G t y.1.val (integerBad (d:=d) w n k p θ G t r J D a y.1.val) i j)))
    (liveTree (integerLive (d:=d) w n k p θ G t r J D a y.1.val) fallback)).length≤_
  rw [goodPopulation_length]
  exact goodPopulation_size w n k p θ G t y.1.val _ _

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma integerPopulation_length (r : ℕ) (J D a : ℝ) (fallback : Fin w)
    (y : (mixedPrepared w n k p θ G t hp e).Ω) :
    (population (integerTargets w n k p θ G t hp e r J D a y)
      (integerTree w n k p θ G t hp e r J D a fallback y)).length=
    integerPop (d:=d) w n k p θ G t r J D a y.1.val := by
  exact goodPopulation_length w n k p θ G t y.1.val _ _ _ _

theorem eventually_integer_experiment (d : ℕ) (η C A loss : ℝ)
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
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J M budget : ℝ),
        ∀ (hn : 2≤n), 0<k → k≤n → (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J → 0≤M →
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
              (fun _=>chronoRead b) (integerTargets w n k p θ G t hp e r J (D*σ^beta η) a ω.1) tab
              (integerTree w n k p θ G t hp e r J (D*σ^beta η) a fallback ω.1) (univ,univ)).length))≤
          5*(budget/(D*σ^beta η)+2*budget/((k:ℝ)*a)+
            2*Fintype.card (Slot w (n+k))*M/((n:ℝ)*a))+(w*(2*(n+k)):ℝ)*loss := by
  filter_upwards [eventually_integer_decoder d η C A loss hη hC hloss,
    eventually_ge_atTop (1:ℝ)] with σ hdec hσ
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hτ hτsmall Ω Θ _ _ w n k p θ G S u r J M budget hn hk hkn hw hr hJ hM hSJ hS hf hcon hcap hband ho hbudget fallback
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  have hσ0 : 0<σ := by linarith
  have hD : 0<D*σ^beta η := mul_pos ((rpow_pos_of_pos hσ0 _).trans_le hDl) (rpow_pos_of_pos hσ0 _)
  have ha : 0<a := by dsimp [a]; exact div_pos (rpow_pos_of_pos hσ0 _) (by exact_mod_cast Finite.card_pos)
  obtain ⟨t,hbad,hrep,_⟩:=actual_realized_reciprocal Projectivization.rep Projectivization.rep
    (show (0:ℝ)≤1/(100*((d:ℝ)+3)) by positivity)
    (show Module.finrank K V=r+(d+3-r) by omega)
    n k hn hk J (D*σ^beta η) a M budget hD ha hM p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) (fun _=>embedding_owner w (n+k))
    S hS hSJ hf ho hbudget
  let hp:=contextual_positive n k (by omega : 0<n) p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t
  have hh := hdec K V hdim hlog D P H hDl hDu book hτ hτsmall Ω Θ w n k p θ G S u r J
    hw hr hJ hS hf hcon hcap hband t hp
  choose e he using fun z : PositiveHistory w n k p θ G t hp=>hh z.val z.property fallback
  refine ⟨t,e,?_⟩
  let pop:=integerPop (d:=d) w n k p θ G t r J (D*σ^beta η) a
  let out:=fun tab (y : (mixedPrepared w n k p θ G t hp e).Ω)=>
    (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
      (fun i=>book.chronoChoose hdim hτ hτsmall ((e y.1).supports y.2 i))
      (fun _=>chronoRead (16*scaleKstar σ η D))
      (integerTargets w n k p θ G t hp e r J (D*σ^beta η) a y) tab
      (integerTree w n k p θ G t hp e r J (D*σ^beta η) a fallback y) (univ,univ)).length
  have hlocal : ∀ z,(∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) (16*scaleKstar σ η D))).mass tab*
      ∑ y,(e z).μ.mass y*((pop z.val:ℝ)-(out tab ⟨z,y⟩:ℝ)))≤(pop z.val:ℝ)*loss := by
    intro z
    dsimp only [pop,out,integerPop,integerTree,integerLive,integerBad]
    unfold integerTargets
    convert he z using 1 <;> simp only [integerBad,Nat.cast_sum] <;> rfl
  have hdelete := bad_predeletion_five w n k p θ G t hkn hp
    (integerBad (d:=d) w n k p θ G t r J (D*σ^beta η) a) _ hbad hrep
  have hres := attachedPrepared_loss w n k p θ G t hp e
    (Law.ofPublic (PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) (16*scaleKstar σ η D))))
    (w*(2*(n+k))) pop out loss _ hloss.le
    (fun z=>goodPopulation_size w n k p θ G t z _ _) hlocal
    (by simpa only [pop,integerPop,integerLive,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hdelete)
  simpa only [Law.ofPublic,out,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hres
end
end SharpLogRamsey.Selection.Windows

end

end OAI
