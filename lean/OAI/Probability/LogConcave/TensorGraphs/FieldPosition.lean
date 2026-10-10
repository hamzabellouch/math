import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.Chain

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval MeasureTheory TensorEnergy
open scoped Classical BigOperators NNReal ENNReal Matrix.Norms.L2Operator

variable {s a b d : ℕ}
local instance cutDecEqDT (β : Fin (2*s+1) → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

def fieldPosition (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (e : ℕ) (x : Point d) (c : (Fin a ⊕ Fin b) ⊕ (Unit ⊕ Fin e) → Fin d) : ℝ :=
  JetCalculus.jet (fun k => v (c (Sum.inr (Sum.inr k)))) (List.finRange e)
    (F (fun t => c (Sum.inl t)) (c (Sum.inr (Sum.inl ())))) x

lemma lift_position_bound (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (i : Primary s) (e : ℕ) (x : Point d) (M : ℝ)
    (hM : AllSplitBound (fieldPosition v F e x) M) :
    AllSplitBound (chainPositionTensor (bundle a b) a v i (liftField F i) e x) M := by
  exact hM.reindex ((slotEquivAt i).sumCongr (Equiv.refl (Unit ⊕ Fin e)))

def scorePosition (H : Point d → ℝ) (v : Fin d → Point d)
    (e : ℕ) (x : Point d) (c : Fin (e+2) → Fin d) : ℝ :=
  JetCalculus.jet (fun k : Fin e => v (c ⟨k.val+2,by omega⟩)) (List.finRange e)
    (directional (v (c ⟨0,by omega⟩)) (directional (v (c ⟨1,by omega⟩)) H)) x

lemma scorePosition_eq (H : Point d → ℝ) (v : Fin d → Point d)
    (h : Hessian (Primary s)) (x : Point d) :
    scorePosition H v h.extra.length x=hessianPositionTensor H v h x := rfl

lemma trace_polySmooth {H : Point d → ℝ} (hH : PolySmooth H)
    (v : Fin d → Point d) (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (hF : ∀c z,PolySmooth (F c z)) :
    PolySmooth (fun x => ((adjointMatrix H v F x*(adjointMatrix H v F x).transpose)^(s+1)).trace) := by
  simp_rw [trace_eq_chain]
  exact PolySmooth.sum Finset.univ (fun c _ => PolySmooth.prod Finset.univ
    (fun i _ => hH.tensorAdjoint (fun z => hF _ z) v))

theorem adjoint_moment_of_branches {H : Point d → ℝ} (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) (hF : ∀c z,PolySmooth (F c z))
    (B : ℝ≥0∞)
    (hB : ∀S∈expand (Fintype.card (Primary s)) initial,
      (∫⁻x,ENNReal.ofReal |chainBranch (bundle (s:=s) a b) a H v (liftField F) S x|
        ∂gibbs H)≤B) :
    (∫⁻x,ENNReal.ofReal ‖adjointMatrix H v F x‖^(2*(s+1)) ∂gibbs H) ≤
      ((3*(2*s+2)+1:ℕ):ℝ≥0∞)^(2*s+2)*B := by
  let T := fun x => ((adjointMatrix H v F x*(adjointMatrix H v F x).transpose)^(s+1)).trace
  have hi : Integrable T (gibbs H) := (trace_polySmooth hH v F hF).integrable hH.smooth.continuous ht
  have hp (x) : ‖adjointMatrix H v F x‖^(2*(s+1))≤T x :=
    TraceMoment.rectangular_trace_moment _ (Nat.succ_pos s)
  have h0 (x) : 0≤T x := (pow_nonneg (norm_nonneg _) _).trans (hp x)
  have hb := integral_chain_bound (bundle (s:=s) a b) a v (liftField F) hH ht hK
    (fun i c z => hF _ z) B hB
  calc
    _ ≤ ∫⁻x,ENNReal.ofReal (T x) ∂gibbs H := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal ‖adjointMatrix H v F x‖ ^ (2*(s+1)) ≤ _
      rw [←ENNReal.ofReal_pow (norm_nonneg _) (2*(s+1))]
      exact ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal (∫x,T x ∂gibbs H) :=
      (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall h0)).symm
    _ = ENNReal.ofReal |∫x,T x ∂gibbs H| := by
      rw [abs_of_nonneg (integral_nonneg h0)]
    _ ≤ _ := by
      simpa only [T,trace_eq_chain,show 2*s+1+1=2*s+2 from by omega] using hb

theorem adjoint_trace_moment {H : Point d → ℝ} (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (ha : 0<a) (hb : 0<b) {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    (hF : ∀c z,PolySmooth (F c z))
    (M N : ℕ → Point d → ℝ)
    (hM0 : ∀e x,0≤M e x) (hN0 : ∀e x,0≤N e x)
    (hM : ∀e x,AllSplitBound (fieldPosition v F e x) (M e x))
    (hN : ∀e x,AllSplitBound (scorePosition H v e x) (N e x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hMm : ∀e,AEMeasurable (fun x => ENNReal.ofReal (M e x)) (gibbs H))
    (hp : ∀e≤2*(s+1),(∫⁻x,ENNReal.ofReal (M e x)^(2*(s+1)) ∂gibbs H) ≤
      (A^(j+e+1)*R^(k+j+e))^(2*(s+1)))
    (hh : ∀e≤2*(s+1),∀x,ENNReal.ofReal (N e x)≤A^(e+1)*R^e) :
    (∫⁻x,ENNReal.ofReal ‖adjointMatrix H v F x‖^(2*(s+1)) ∂gibbs H)≤
      ((3*(2*s+2)+1:ℕ):ℝ≥0∞)^(2*s+2) * (d:ℝ≥0∞)^a *
        (A^(2*(2*s+2)*(j+1))*R^((2*s+2)*(k+j+1))) := by
  have he : 2*s+1+1=2*(s+1) := by omega
  have hβ : ∀t : Fin (2*s+1),0<bundle a b t := by
    intro t
    unfold bundle
    split <;> assumption
  rw [mul_assoc]
  apply adjoint_moment_of_branches v F hH ht hK hF
  intro S hS
  have hpder (i : Primary s) : (S.derivatives i).length≤2*(s+1) := by
    simpa only [Fintype.card_fin,he] using (terminal_moment_budgets hS j k).1 i
  have hhder (h : S.hessians) : (h : Hessian (Primary s)).extra.length≤2*(s+1) := by
    simpa only [Fintype.card_fin,he] using (terminal_moment_budgets hS j k).2.1 h Multiset.coe_mem
  have hbound := chain_branch_bound (gibbs H) hS (bundle a b) hβ a ha H v (liftField F)
    (fun i => M (S.derivatives i).length) (fun h => N (h : Hessian (Primary s)).extra.length)
    (fun i x => hM0 _ x) (fun h x => hN0 _ x)
    (fun i x => lift_position_bound v F i _ x _ (hM _ x))
    (fun h x => hN _ x) j k A R hA hR hAf hRf
    (fun i => hMm _) (fun i => by simpa only [he] using hp _ (hpder i))
    (fun h x => hh _ (hhder h) x)
  simpa only [show 2*s+1+1=2*s+2 from by omega] using hbound

end LogConcaveSampling.CycleTrace

end

end

end

end OAI
