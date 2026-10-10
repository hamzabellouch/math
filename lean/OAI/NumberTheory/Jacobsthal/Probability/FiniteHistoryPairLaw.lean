import OAI.NumberTheory.Jacobsthal.Paths.FiniteHistorySupport

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FiniteHistoryPairLaw
open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
open FiniteHistoryTransport FiniteHistoryOccurrence
variable {X : Type*} [MeasurableSpace X]

def adjacentPair (N : ℕ) (h : Hist X N) (j : Fin N) : X×X :=
  (atIndex N h j.castSucc,atIndex N h j.succ)

theorem adjacentPair_measurable (N : ℕ) (j : Fin N) : Measurable (fun h : Hist X N => adjacentPair N h j) :=
  (measurable_pi_apply _).prodMk (measurable_pi_apply _)

theorem lintegral_adjacent_pair (K : Kernel X X) [IsMarkovKernel K]
    (N : ℕ) (h₀ : Hist X 0) (j : Fin N) {F : X×X → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ h,F (adjacentPair N h j) ∂pathKernel K N h₀)=
      ∫⁻ x,∫⁻ y,F (x,y) ∂K x ∂(K^j.1) (last 0 h₀) := by
  have hk : j.1+1 ≤ N := by have := j.isLt; omega
  let G : Hist X (j.1+1) → ℝ≥0∞ :=
    fun h => F (h ⟨j.1,Finset.mem_Iic.mpr (by omega)⟩,last (j.1+1) h)
  have hG : Measurable G := hF.comp ((measurable_pi_apply _).prodMk (last_measurable _))
  have hprefix : (pathKernel K N h₀).map (frestrictLe₂ (π := fun _ => X) hk)=pathKernel K (j.1+1) h₀ :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => X) (κ := pastKernel K) h₀ hk
  change (∫⁻ h,G (frestrictLe₂ (π := fun _ => X) hk h) ∂pathKernel K N h₀)=_
  rw [← lintegral_map hG (measurable_frestrictLe₂ hk),hprefix,lintegral_pathKernel_succ K j.1 h₀ hG]
  calc
    _ = ∫⁻ h,∫⁻ y,F (last j.1 h,y) ∂K (last j.1 h) ∂pathKernel K j.1 h₀ := by
      apply lintegral_congr
      intro h
      apply lintegral_congr
      intro y
      change F ((extend j.1 h y) ⟨j.1,Finset.mem_Iic.mpr (by omega)⟩,
        last (j.1+1) (extend j.1 h y))=F (last j.1 h,y)
      rw [extend_last,extend_previous j.1 h y ⟨j.1,by simp⟩]
      rfl
    _ = _ := by
      have hcur : Measurable (Function.uncurry (fun x : X => fun y : X => F (x,y))) := hF
      exact lintegral_endpoint K j.1 h₀ (hcur.lintegral_kernel_prod_right (κ := K))

noncomputable def pairProbability (K : Kernel X X) (E : Set (X×X)) (x : X) : ℝ≥0∞ :=
  K x ((Prod.mk x) ⁻¹' E)

theorem pairProbability_integral (K : Kernel X X) {E : Set (X×X)} (hE : MeasurableSet E) (x : X) :
    (∫⁻ y,E.indicator (fun _ => (1:ℝ≥0∞)) (x,y) ∂K x)=pairProbability K E x := by
  change (∫⁻ y,((Prod.mk x) ⁻¹' E).indicator 1 y ∂K x)=_
  exact lintegral_indicator_one (measurable_prodMk_left hE)

theorem pairProbability_measurable (K : Kernel X X) [IsSFiniteKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) : Measurable (pairProbability K E) := by
  have hF : Measurable (E.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hE
  have hcur : Measurable (Function.uncurry (fun x : X => fun y : X => E.indicator (fun _ => (1:ℝ≥0∞)) (x,y))) := hF
  have hh := hcur.lintegral_kernel_prod_right (κ := K)
  simpa only [pairProbability_integral K hE] using hh

theorem adjacent_pair_probability (K : Kernel X X) [IsMarkovKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) (j : Fin N) :
    pathKernel K N h₀ ((fun h => adjacentPair N h j) ⁻¹' E)=
      ∫⁻ h,pairProbability K E (atIndex N h j.castSucc) ∂pathKernel K N h₀ := by
  have hF : Measurable (E.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hE
  have hc : Measurable (fun h : Hist X N => atIndex N h j.castSucc) := measurable_pi_apply _
  have hp := atIndex_law K N h₀ j.castSucc
  simp only [Fin.val_castSucc] at hp
  calc
    _ = ∫⁻ h,E.indicator (fun _ => (1:ℝ≥0∞)) (adjacentPair N h j) ∂pathKernel K N h₀ :=
      (lintegral_indicator_one ((adjacentPair_measurable N j) hE)).symm
    _ = ∫⁻ x,∫⁻ y,E.indicator (fun _ => (1:ℝ≥0∞)) (x,y) ∂K x ∂(K^j.1) (last 0 h₀) :=
      lintegral_adjacent_pair K N h₀ j hF
    _ = ∫⁻ x,pairProbability K E x ∂(K^j.1) (last 0 h₀) := by simp_rw [pairProbability_integral K hE]
    _ = _ := by rw [← hp,lintegral_map (pairProbability_measurable K hE) hc]
end NumberTheoryLean.FiniteHistoryPairLaw

end

end Erdos970

end OAI
