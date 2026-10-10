import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.WindowTransport
import OAI.Combinatorics.SharpRamsey.Windows.IntegerOutput
import OAI.Combinatorics.SharpRamsey.Windows.OpenOutput

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section

theorem eventually_reciprocal_ordered (d : ℕ) (η C A C0 c : ℝ)
    (hη : 0<η) (hC : 0<C) (hC0 : 0≤C0) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (_ : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3)),
        0≤b → 0≤H → 4≤P → b+log 1000000≤P → 0≤τ → τ≤1/40000 →
      ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (F : Ω→Fin (w*(4*(n+k)))→ProjectivePair (K:=K) (V:=V))
        (S : Θ→Fin (w*(4*(n+k)))→Finset (ProjectivePair (K:=K) (V:=V)))
        (integer : Bool) (r : Fin (d+3)) (J M budget : ℝ),
        2≤n → 0<k → k≤n → (w:ℝ)≤C*σ^A → ((d+2:ℕ):ℝ)*σ≤J → 0≤M →
        (∀ z i,log (S z i).card≤J) →
        (∀ x,p.mass x≠0→∀ i,F x i∈S (θ x) i) →
        (∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2) →
        (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
        (∀ x,p.mass x≠0→∀ i,ValidSlotClass (d+2) (scaleKstar σ η D) (S (θ x) i) (.inl (integer,r))) →
        (∀ z i,((S z i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∑ z,(p.map θ).mass z*((w*(4*(n+k)):ℕ)*J-entropy ((p.cond θ z).map F)))≤budget →
        budget≤C0*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) →
        c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
        (if integer then
          M≤C0*σ ∧ c*(Nat.card K:ℝ)*σ^(1+η/2)≤n ∧
          ∀ x,p.mass x≠0→∀ W : Submodule K V,
            ((univ.filter (fun i : Slot w (n+k)=>
              (covectorTuple (F x) (finProdFinEquiv i))∈
                orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ)≤M
         else c*σ^(1+η/2)≤(w:ℝ)*D) →
        Nonempty (Fin w) →
        Nonempty (ContextOutput p F (w*(n+k)) (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
          (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H)
            w (Nat.log 2 w+1) (2*(n+k))) 2) := by
  filter_upwards [eventually_integer_output d η C A C0 c hη hC hC0 hc,
    eventually_open_output d η C A C0 c hη hC hC0 hc] with σ hi ho
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hb hH hP haP hτ hτsmall Ω Θ _ _ w n k p θ F S integer r J M budget hn hk hkn hw hJ hM hSJ hS hf hcon hclass hsize hbudget hb0 hk0 hcase hne
  obtain ⟨fallback⟩:=hne
  have hN : 0<w*(4*(n+k)) := by
    have hw : 0<w:=Nat.zero_lt_of_lt fallback.isLt
    positivity
  obtain ⟨hr1,hr,u,hu⟩:=reciprocal_parameters p θ S integer r _ hN hclass
  let G:=fun x=>windowTuple (covectorTuple (F x))
  let T:=fun z (i : Slot w (n+k))=>covectorDomain (S z (finProdFinEquiv i))
  let u':=fun z (i : Slot w (n+k))=>u z (finProdFinEquiv i)
  have hG : ∀ x,p.mass x≠0→∀ i,G x i∈T (θ x) i := by
    intro x hx i
    exact (covectorDomain_mem _ _).mpr (hS x hx _)
  have hT : ∀ z i,log (T z i).card≤J := by
    intro z i
    simpa only [T,covectorDomain_card] using hSJ z (finProdFinEquiv i)
  have hflag : ∀ x,p.mass x≠0→∀ i,(G x i).1.rep (G x i).2.rep=0 := by
    intro x hx i
    exact covectorTuple_flag (F x) (hf x hx) _
  have hchron : ∀ x,p.mass x≠0→∀ i j,position i<position j→
      (G x i).1.rep (G x j).2.rep=0→(G x j).1.rep (G x i).2.rep=0 := by
    intro x hx i j hij
    apply covectorTuple_consistent (F x) (hcon x hx)
    change (finProdFinEquiv i).val<(finProdFinEquiv j).val
    simpa only [finProd_position] using hij
  have hcap : ∀ x,p.mass x≠0→∀ i,
      (((T (θ x) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u' (θ x) i) ∧
      (((T (θ x) i).image Prod.snd).card:ℝ)≤1024*exp (u' (θ x) i) ∧
      ((T (θ x) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2) := by
    intro x hx i
    have huv:=hu x hx (finProdFinEquiv i)
    refine ⟨?_,?_,?_⟩
    · convert huv.1 using 1
      simp only [u',hlog,Nat.cast_add,Nat.cast_ofNat]
      ring_nf
    · simpa only [T,u'] using huv.2.1
    · simpa only [T,covectorDomain_card] using hsize (θ x) (finProdFinEquiv i)
  have hbud : (∑ z,(p.map θ).mass z*((Fintype.card (Slot w (n+k)):ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget := by
    apply le_trans (le_of_eq ?_) hbudget
    apply sum_congr rfl
    intro z _
    dsimp only [G]
    rw [window_entropy]
    simp only [Slot,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    congr 2
    convert covectorTuple_entropy (p.cond θ z) F using 1 <;> congr!
  have hout : Nonempty (ContextOutput p (fun x=>flattenTuple (G x)) (w*(n+k))
      (8000000*(Nat.card K:ℝ)^(d+2)*exp (16*scaleKstar σ η D))
      (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=16*scaleKstar σ η D) (P:=P) (H:=H)
        w (Nat.log 2 w+1) (2*(n+k))) 2) := by
    cases integer
    · simp only [Bool.false_eq_true,ite_false] at hr hu hcase
      exact ho K V hdim hlog D P H hDl hDu book hb hH hP haP hτ hτsmall Ω Θ w n k p θ G T u'
        (d+4-r.val) J budget hn hk hkn hw hcase (by omega) hJ hT hG hflag hchron hcap
        (by intro x hx i;simpa only [u',hlog] using (hu x hx (finProdFinEquiv i)).2.2)
        hbud hb0 hk0 fallback
    · simp only [ite_true] at hr hu hcase
      exact hi K V hdim hlog D P H hDl hDu book hb hH hP haP hτ hτsmall Ω Θ w n k p θ G T u'
        (d+3-r.val) J M budget hn hk hkn hw (by omega) hJ hM hT hG hflag hchron hcap
        (by intro x hx i;simpa only [u',hlog] using (hu x hx (finProdFinEquiv i)).2.2)
        hcase.2.2 hbud hb0 hcase.1 hk0 hcase.2.1 fallback
  obtain ⟨e⟩:=hout
  exact ⟨e.transport (Equiv.prodComm _ _) F (fun _=>(OrderIso.refl _).toOrderEmbedding) (by
    intro x i
    simp only [G,flatten_window,covectorTuple,Equiv.prodComm_apply,Prod.swap_swap,
      OrderIso.coe_toOrderEmbedding,OrderIso.refl_apply])⟩
end
end SharpLogRamsey.Marking

end

end OAI
