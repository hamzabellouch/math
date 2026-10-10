import OAI.MeasureTheory.Falconer.Angular.AngularStateSuccessor
import OAI.MeasureTheory.Falconer.Angular.CommonProfileAngularNear
import OAI.MeasureTheory.Falconer.Estimates.ActualFarSourceEquation24

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace AngularStateData

noncomputable def contribution (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ)
    (rel : (CellPath × CellPath) → (CellPath × CellPath) → Prop) : ℂ :=
  angularCellContribution d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a) d.a d.v Ψ
    (((2:ℝ)^d.N)^(-d.mass d.a)) (((2:ℝ)^d.N)^(-d.mass d.a))
    (((2:ℝ)^d.N)^(-d.mass p)) (((2:ℝ)^d.N)^(-d.mass p))
    (inheritedCircleSymbol (d.retainedList d.a) id (k 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 0))
    (inheritedCircleSymbol (d.retainedList d.a) id (k 1) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 1)) rel

noncomputable def nearContribution (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ) : ℂ :=
  d.contribution k h p Ψ (angularNear d.Q d.Q p)

noncomputable def farContribution (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ) : ℂ :=
  d.contribution k h p Ψ (fun row col => ¬ angularNear d.Q d.Q p row col)

def distanceSuccessor (d : AngularStateData) (b : ℕ) : PositiveDistanceData :=
  ⟨d.Q,d.ρ,d.mass,d.N,d.q,b,d.v,d.lam,d.sig,d.J,d.i+1,[],[]⟩

noncomputable def farDistanceMaximum (d : AngularStateData) (b : ℕ) : ℝ≥0∞ :=
  (d.distanceSuccessor b).separatedMaximum (d.distanceSuccessor b) (d.children b) b

noncomputable def farSum (d : AngularStateData) (p : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc (d.a+9) (p+5),
    ((2:ℝ)^d.N)^(-2*(d.profile b-d.profile d.a)+4000*(d.lam+d.sig)) *
      (d.farDistanceMaximum b).toReal

theorem farDistanceMaximum_finite (d : AngularStateData) [IsFiniteMeasure d.ρ] (b : ℕ) :
    d.farDistanceMaximum b ≠ ⊤ := by
  let : IsFiniteMeasure (d.distanceSuccessor b).ρ := show IsFiniteMeasure d.ρ from inferInstance
  exact PositiveDistanceData.separatedMaximum_ne_top _ _ _ _

theorem farSum_nonneg (d : AngularStateData) (p : ℕ) : 0 ≤ d.farSum p := by
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

theorem uniform_state_near (K : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData, N₀ ≤ d.N → d.Q.side = 1 →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      ∀ p : ℕ, d.a ≤ p → p ≤ d.N →
      ∀ {Ψ : ℝ → ℝ}, ContDiff ℝ ∞ Ψ → (∀ x, 0 ≤ Ψ x) →
      (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
      d.energy k h Ψ ≠ ⊤ ∧ (∀ row, d.childEnergy k h p Ψ row ≠ ⊤) ∧
      ((d.energy k h Ψ).toReal : ℂ) = d.nearContribution k h p Ψ+d.farContribution k h p Ψ ∧
      ‖d.nearContribution k h p Ψ‖ ≤ ((2:ℝ)^d.N)^
        (-2*(d.profile p-d.profile d.a)+12*d.lam+eps)*d.childMaximum k h p Ψ := by
  obtain ⟨N₀,h₀⟩ := uniform_common_profile_angular_near_equation23 K heps
  refine ⟨N₀,?_⟩
  intro d hN hQ hX hY B δ hprof k hk h hh hhb p hap hpN Ψ hΨ hpos hs
  have heq : d.a+(p-d.a) = p := Nat.add_sub_of_le hap
  have heqR : (d.a:ℝ)+((p-d.a:ℕ):ℝ) = (p:ℝ) := by exact_mod_cast heq
  have hn := h₀ d.N hN (fun _ : Fin 2 => d.retainedList d.a) (fun _ => id) k hk
    (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) d.mass B δ d.lam d.sig (fun _ => hprof)
    d.J d.i h hh hhb d.X d.Y d.a (p-d.a) hX hY (by omega) d.v hΨ hpos hs
  dsimp only at hn
  simp only [heqR,heq] at hn
  let := hprof.probability
  have hQp : 0 < d.Q.side := by rw [hQ]; norm_num
  have hk' (l : Fin 2) := d.child_budget hap (k l) (hk l)
  refine ⟨hn.1,fun row => d.cellEnergy_finite hQp (d.retainedList p) k K hk' h hh hhb p hΨ hpos hs row,
    hn.2.2.2.1,?_⟩
  have he := d.remaining_maximum_eq_child hap hX hY k h Ψ
  rw [← he]
  exact hn.2.2.2.2

end AngularStateData

end PlanarFalconer

end OAI
