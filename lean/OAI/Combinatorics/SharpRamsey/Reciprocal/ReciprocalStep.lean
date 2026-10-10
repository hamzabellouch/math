import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalOrdered
import OAI.Combinatorics.SharpRamsey.Windows.SuppliedBook
import OAI.Combinatorics.SharpRamsey.Exposure.RestrictionGeometry
import OAI.Combinatorics.SharpRamsey.Execution.OutputRebase
import OAI.Combinatorics.SharpRamsey.Marking.StepCost

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section

 theorem eventually_reciprocal_step (i : ℕ) (η c C C0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C) (hC0 : 0 < C0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
      [Fintype (Projectivization (ZMod q) V)]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) V))]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Module.Dual (ZMod q) V)))],
      Module.finrank (ZMod q) V=i+4 →
    ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ] (m : ℕ) (p : Law Ω) (θ : Ω→Θ)
      (F : Ω→Fin m→ProjectivePair (K:=ZMod q) (V:=V))
      (S : Θ→Fin m→Finset (ProjectivePair (K:=ZMod q) (V:=V)))
      (D J M budget : ℝ) (R : ℕ) (integer : Bool) (r : Fin (i+4)),
      Admissible σ η D R → c*(q:ℝ)*σ^(1+η) ≤ m → (m:ℝ) ≤ C*q*σ^(1+η) →
      ((i+3:ℕ):ℝ)*σ ≤ J → 0 ≤ M → M ≤ C0*σ →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (θ x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      (∀ x,p.mass x≠0→∀ j,ValidSlotClass (i+3) (scaleKstar σ η D) (S (θ x) j) (.inl (integer,r))) →
      (∀ z j,((S z j).card:ℝ) ≤ 64*(q:ℝ)^(i+3)) →
      (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map F))) ≤ budget →
      budget ≤ C0*(m:ℝ)*D*σ^(-beta η) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) V,
        ((univ.filter (fun j : Fin m=>covectorTuple (F x) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M) →
      ∃ w m' : ℕ, 1 ≤ w ∧ (w:ℝ)*D ≤ max C 12*σ^(1+η/2) ∧ (m:ℝ)/8 ≤ m' ∧
        Nonempty (ContextOutput p F m' (8000000*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η D))
          (D*σ^(-η/3)*(m:ℝ)) 2) := by
  obtain ⟨H,hH,hbook⟩:=supplied_book i
  let Cw:=max C 12
  let cs:=min (1/2) (c/(2*Cw))
  let a:=1+η/2
  have hCw : 0 < Cw:=hC.trans_le (le_max_left _ _)
  have hcs : 0 < cs:=lt_min (by norm_num) (by dsimp only [Cw]; positivity)
  filter_upwards [hbook η hη,
    eventually_reciprocal_ordered (i+1) η Cw a (4*C0) cs hη hCw (by positivity) hcs,
    eventually_reciprocal_windows η c C hη hηu hc hC,
    eventually_reciprocal_message_cost i η c Cw H hη hc hCw hH,
    eventually_ge_atTop (1:ℝ)] with σ hbk hout hwin hcost hσ
  intro q _ hq he V _ _ _ _ _ _ hdim Ω Θ _ _ m p θ F S D J M budget R integer r
    had hmlo hmhi hJ hM hMup hSJ hS hf hcon hclass hsize hbudget hbud hocc
  have hσ0 : 0 < σ:=by linarith
  have hq0 : 0 < (q:ℝ):=he ▸ exp_pos _
  have hqlog : log (Nat.card (ZMod q):ℝ)=σ:=by rw [Nat.card_zmod,←he,log_exp]
  have hD : 1 ≤ D:=(one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
  have hD0 : 0 < D:=by linarith
  obtain ⟨hb,hP,hbP,hτ,hτsmall,⟨book⟩⟩:=hbk q hq he V hdim D R had
  let x:=if integer then (q:ℝ)*σ^(1+η/2) else (q:ℝ)*D*σ^(η/2)
  let n:=⌈x⌉₊
  let k:=⌊(q:ℝ)*D*σ^(3000*beta η)⌋₊
  let L:=4*(n+k)
  let w:=m/L
  have hwindows:=hwin (q:ℝ) D m integer he had.D_lower had.D_upper hmlo hmhi
  change 2 ≤ n ∧ 0 < k ∧ k ≤ n ∧ 1 ≤ w ∧ w*L ≤ m ∧ (m:ℝ)/2 ≤ (w*L:ℕ) ∧
    (1/2)*(q:ℝ)*D*σ^(3000*beta η) ≤ k ∧
    (w:ℝ)*D ≤ Cw*σ^a ∧ (w:ℝ) ≤ Cw*σ^a ∧
    (if integer then (q:ℝ)*σ^(1+η/2) ≤ (n:ℝ) else (c/(2*Cw))*σ^(1+η/2) ≤ (w:ℝ)*D) ∧
    (L:ℝ) ≤ 12*(q:ℝ)*σ^a at hwindows
  obtain ⟨hn,hk,hkn,hw,hwm,hhalf,hklow,hwD,hwup,hcase,hLup⟩:=hwindows
  let T : Θ→Finset (Fin m):=fun _=>prefixSet hwm
  let e:=chosenOrder T hwm
  let G:=orderedTuple T hwm θ F
  let S':=fun z j=>S z (e z j)
  have hGS : ∀ z j,log (S' z j).card ≤ J:=fun z j=>hSJ z (e z j)
  have hG : ∀ x,p.mass x≠0→∀ j,G x j∈S' (θ x) j:=fun x hx j=>hS x hx (e (θ x) j)
  have hgf : ∀ x,p.mass x≠0→∀ j,Incidence.Incident (G x j).1 (G x j).2:=
    fun x hx j=>hf x hx (e (θ x) j)
  have hgcon : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan):=
    fun x hx=>scanConsistent_ordered (F x) (hcon x hx) (e (θ x))
  have hgclass : ∀ x,p.mass x≠0→∀ j,ValidSlotClass (i+3) (scaleKstar σ η D) (S' (θ x) j)
      (.inl (integer,r)):=fun x hx j=>hclass x hx (e (θ x) j)
  have hgsize : ∀ z j,((S' z j).card:ℝ) ≤ 64*(Nat.card (ZMod q):ℝ)^((i+1)+2):=by
    intro z j
    simpa only [Nat.card_zmod] using hsize z (e z j)
  have hgbud : (∑ z,(p.map θ).mass z*((w*(4*(n+k)):ℕ)*J-
      entropy ((p.cond θ z).map G))) ≤ budget :=
    (prefix_budget hwm p θ F S J hS hSJ).trans hbudget
  have hbb : budget ≤ (4*C0)*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) := by
    have hm : (m:ℝ) ≤ 4*(w*(2*(n+k)):ℕ):=by
      push_cast at hhalf ⊢
      dsimp only [L] at hhalf
      push_cast at hhalf
      linarith
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hC0.le)
      (mul_nonneg hD0.le (rpow_nonneg hσ0.le (-beta η)))
    push_cast at hh ⊢
    nlinarith only [hbud,hh]
  have hkc : cs*(Nat.card (ZMod q):ℝ)*D*σ^(3000*beta η) ≤ k := by
    rw [Nat.card_zmod]
    apply le_trans _ hklow
    dsimp only [cs]
    gcongr
    exact min_le_left _ _
  have hnewcase : if integer then
      M ≤ (4*C0)*σ ∧ cs*(Nat.card (ZMod q):ℝ)*σ^(1+η/2) ≤ n ∧
      ∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) V,
        ((univ.filter (fun j : Slot w (n+k)=>covectorTuple (G x) (finProdFinEquiv j)∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M
      else cs*σ^(1+η/2) ≤ (w:ℝ)*D := by
    cases integer
    · simp only [Bool.false_eq_true,ite_false] at hcase ⊢
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (rpow_nonneg hσ0.le _)).trans hcase
    · simp only [ite_true] at hcase ⊢
      refine ⟨by nlinarith,?_,?_⟩
      · rw [Nat.card_zmod]
        have hc1 : cs ≤ 1:=(min_le_left _ _).trans (by norm_num)
        calc
          _  ≤  (q:ℝ)*σ^(1+η/2) := by
            calc
              _ = cs*((q:ℝ)*σ^(1+η/2)) := by ring
              _ ≤ 1*((q:ℝ)*σ^(1+η/2)) := mul_le_mul_of_nonneg_right hc1 (by positivity)
              _ = _ := one_mul _
          _  ≤  _:=hcase
      · intro z hz W
        let ee : Slot w (n+k)↪Fin m:=finProdFinEquiv.toEmbedding.trans (e (θ z)).toEmbedding
        have hh:=count_injective_restriction ee (fun j=>covectorTuple (F z) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)
        apply le_trans _ (hocc z hz W)
        have heq : ∀ j,covectorTuple (G z) (finProdFinEquiv j)=covectorTuple (F z) (ee j) := fun _=>rfl
        simp_rw [heq]
        convert (Nat.cast_le (α:=ℝ)).mpr hh using 1 <;> congr!
  have hne : Nonempty (Fin w):=⟨⟨0,by omega⟩⟩
  obtain ⟨out⟩:=hout (ZMod q) V hdim hqlog D (scaleP σ η D R) H had.D_lower had.D_upper
    book hb hH hP hbP hτ hτsmall Ω Θ w n k p θ G S' integer r J M budget hn hk hkn hwup
      hJ hM hGS hG hgf hgcon hgclass hgsize hgbud hbb hkc hnewcase hne
  have hfinalcost:=hcost q he V hdim D R w n k m had hw hmlo hwD hwup
    (hLup.trans (by dsimp only [Cw];gcongr;exact le_max_right _ _)) hP hbP
  have out' := out.mono (le_refl _) hfinalcost (le_refl 2)
  have final:=out'.transport (Equiv.refl _) F (fun z=>e (θ z)) (fun _ _=>rfl)
  refine ⟨w,w*(n+k),hw,hwD,?_,?_⟩
  · dsimp only [L] at hhalf
    push_cast at hhalf ⊢
    linarith
  · simpa only [Nat.card_zmod] using Nonempty.intro final
end
end SharpLogRamsey.Marking

end

end OAI
