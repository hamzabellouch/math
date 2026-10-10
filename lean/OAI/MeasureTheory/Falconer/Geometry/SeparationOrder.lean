import OAI.MeasureTheory.Falconer.Estimates.SeparatedInverse
import OAI.MeasureTheory.Falconer.Fourier.SymbolOrder

namespace OAI

/-! # The total `2j` derivative budget in the actual finite inverse split -/

namespace Falconer
open scoped ContDiff

variable {X Y V W E H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

namespace SmoothSeparation

def HasOrder (S : SmoothSeparation X Y E) (B : X → V → ℂ) (C : Y → W → ℂ) (N : ℕ) : Prop :=
  ∃ p q : S.index → ℕ, ∀ i, p i+q i ≤ N ∧
    SymbolOrder B (S.left i) (p i) ∧ SymbolOrder C (S.right i) (q i)

theorem HasOrder.mono {S : SmoothSeparation X Y E} {B : X → V → ℂ}
    {C : Y → W → ℂ} {N M : ℕ} (h : S.HasOrder B C N) (hNM : N ≤ M) :
    S.HasOrder B C M := by
  obtain ⟨p,q,h⟩ := h
  exact ⟨p,q,fun i => ⟨(h i).1.trans hNM,(h i).2⟩⟩

theorem product_hasOrder (B : X → E → ℂ) (C : Y → E → ℂ)
    (hB : ∀ x, ContDiff ℝ ∞ (B x)) (hC : ∀ y, ContDiff ℝ ∞ (C y)) :
    (product B C hB hC).HasOrder B C 0 := by
  refine ⟨fun _ => 0,fun _ => 0,?_⟩
  intro i
  exact ⟨by simp,SymbolOrder.base B hB,SymbolOrder.base C hC⟩

theorem HasOrder.mulLeft {S : SmoothSeparation X Y E} {B : X → V → ℂ}
    {C : Y → W → ℂ} {N : ℕ} (h : S.HasOrder B C N)
    (c : E → ℂ) (hc : ContDiff ℝ ∞ c) : (S.mulLeft c hc).HasOrder B C N := by
  obtain ⟨p,q,h⟩ := h
  refine ⟨p,q,fun i => ⟨(h i).1,?_,(h i).2.2⟩⟩
  exact (h i).2.1.mul_fixed c hc

theorem HasOrder.pullback {S : SmoothSeparation X Y E} {B : X → V → ℂ}
    {C : Y → W → ℂ} {N : ℕ} (h : S.HasOrder B C N)
    (g : H → E) (hg : ContDiff ℝ ∞ g) : (S.pullback g hg).HasOrder B C N := by
  obtain ⟨p,q,h⟩ := h
  exact ⟨p,q,fun i => ⟨(h i).1,(h i).2.1.pullback g hg,(h i).2.2.pullback g hg⟩⟩

theorem HasOrder.derivative {S : SmoothSeparation X Y E} {B : X → V → ℂ}
    {C : Y → W → ℂ} {N : ℕ} (h : S.HasOrder B C N) (v : E) :
    (S.derivative v).HasOrder B C (N+1) := by
  obtain ⟨p,q,h⟩ := h
  refine ⟨Sum.elim (fun i => p i+1) p,Sum.elim q (fun i => q i+1),?_⟩
  intro i
  cases i with
  | inl i => exact ⟨by have hi := (h i).1; dsimp; omega,(h i).2.1.derivative v,(h i).2.2⟩
  | inr i => exact ⟨by have hi := (h i).1; dsimp; omega,(h i).2.1,(h i).2.2.derivative v⟩

theorem sum_hasOrder {I : Type} [Fintype I] (S : I → SmoothSeparation X Y E)
    {B : X → V → ℂ} {C : Y → W → ℂ} {N : ℕ} (h : ∀ i, (S i).HasOrder B C N) :
    (sum S).HasOrder B C N := by
  choose p q hp using h
  exact ⟨fun i => p i.1 i.2,fun i => q i.1 i.2,fun i => hp i.1 i.2⟩

theorem HasOrder.laplacian {S : SmoothSeparation X Y E} {B : X → V → ℂ}
    {C : Y → W → ℂ} {N n : ℕ} (h : S.HasOrder B C N) (v : Fin n → E) :
    (S.laplacian v).HasOrder B C (N+2) := by
  exact sum_hasOrder _ (fun i => (h.derivative (v i)).derivative (v i))

theorem HasOrder.iteratedLaplacian {S : SmoothSeparation X Y E} {B : X → V → ℂ}
    {C : Y → W → ℂ} {N n : ℕ} (h : S.HasOrder B C N) (v : Fin n → E) (j : ℕ) :
    (S.iteratedLaplacian v j).HasOrder B C (N+2*j) := by
  induction j with
  | zero => simpa only [SmoothSeparation.iteratedLaplacian,Function.iterate_zero_apply,mul_zero,Nat.add_zero] using h
  | succ j ih =>
    have hh := ih.laplacian v
    rw [show N+2*j+2 = N+2*(j+1) by omega] at hh
    simpa only [SmoothSeparation.iteratedLaplacian,Function.iterate_succ_apply'] using hh

theorem HasOrder.stationaryJet {m j N : ℕ} {S : SmoothSeparation X Y (Space (m+3))}
    {B : X → V → ℂ} {C : Y → W → ℂ} (h : S.HasOrder B C N) :
    (S.stationaryJet m j).HasOrder B C (N+2*j) := by
  unfold SmoothSeparation.stationaryJet
  exact (((h.pullback _ (safeStationaryChart_contDiff m)).mulLeft _
    (stationaryJointDensity_contDiff m)).iteratedLaplacian _ j).pullback _
      (contDiff_id.prodMk contDiff_const) |>.mulLeft _ (stationaryJetMultiplier_contDiff m j)

theorem HasOrder.inverse {m N : ℕ} {S : SmoothSeparation X Y (Space (m+3))}
    {B : X → V → ℂ} {C : Y → W → ℂ} (h : S.HasOrder B C N) (j : ℕ) :
    (S.inverse m j).HasOrder B C (N+2*j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [SmoothSeparation.inverse]
      exact h.mulLeft _ _
    | succ j =>
      rw [SmoothSeparation.inverse]
      apply HasOrder.mulLeft
      apply sum_hasOrder
      intro k
      have hk := (ih (j-k) (by have hi := k.isLt; omega)).stationaryJet (j := (k:ℕ)+1)
      rwa [show N+2*(j-k)+2*((k:ℕ)+1) = N+2*(j+1) by have hi := k.isLt; omega] at hk

end SmoothSeparation

theorem localInverseAmplitude_product_separated_order (m j : ℕ)
    (B : X → Space (m+3) → ℂ) (C : Y → Space (m+3) → ℂ)
    (hB : ∀ x, ContDiff ℝ ∞ (B x)) (hC : ∀ y, ContDiff ℝ ∞ (C y)) :
    ∃ S : SmoothSeparation X Y (Space (m+3)), S.HasOrder B C (2*j) ∧
      ∀ x y e, localInverseAmplitude m (fun w => B x w*C y w) j e = S.value x y e := by
  let P := SmoothSeparation.product B C hB hC
  refine ⟨P.inverse m j,?_,?_⟩
  · simpa only [Nat.zero_add] using (SmoothSeparation.product_hasOrder B C hB hC).inverse j
  · intro x y e
    rw [SmoothSeparation.inverse_value]
    have hp : P.value x y = fun w => B x w*C y w := by
      funext w
      exact SmoothSeparation.product_value B C hB hC x y w
    rw [hp]

end Falconer

end OAI
