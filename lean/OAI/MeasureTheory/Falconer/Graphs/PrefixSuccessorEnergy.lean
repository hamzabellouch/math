import OAI.MeasureTheory.Falconer.Shells.HighShellEndpointTerms
import OAI.MeasureTheory.Falconer.Angular.AngularTerminalBound
import OAI.MeasureTheory.Falconer.Angular.AngularCellKernels
import OAI.MeasureTheory.Falconer.Recursion.InheritedPolicyState

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

noncomputable def policyCellEnergy (d : PositiveDistanceData)
    (S : Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ)
    (h : Fin 2 → Plane → ℂ) (p : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    (row : CellPath × CellPath) : ℝ≥0∞ :=
  sourceAngularH p v Ψ
    (fun z => sourceAngularTransform d.ρ (d.Q.descendant row.1).carrier
      (((2:ℝ)^d.N)^(-d.mass p))
      (inheritedCircleSymbol S id (k 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 0)) z.1 z.2)
    (fun z => sourceAngularTransform d.ρ (d.Q.descendant row.2).carrier
      (((2:ℝ)^d.N)^(-d.mass p))
      (inheritedCircleSymbol S id (k 1) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 1)) z.1 z.2)

noncomputable def prefixRemainingList (d : PositiveDistanceData) (p : ℕ) : Finset PolicyDescriptor :=
  remainingPolicyDescriptors (fun n => d.mass n-(n:ℝ)/d.N) d.N d.q d.a d.t p

noncomputable def prefixEnergyBound (d : PositiveDistanceData) (K p : ℕ) (W : ℝ) : ℝ :=
  let C := (symbolDerivativeConstant K^K)*d.ρ.real univ/(((2:ℝ)^d.N)^(-d.mass p))
  (2:ℝ)^(2*((d.t:ℝ)-p))*((C^2*sourceArcLength.real univ)*(C^2*sourceArcLength.real univ))*(4*W)

theorem policyCellEnergy_finite_bound (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (S : Finset PolicyDescriptor)
    (k : Fin 2 → PolicyDescriptor → ℕ) (K : ℕ) (hK : ∀ l, ∑ b ∈ S, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (p : ℕ) (v : ℝ) (hv : v ≤ d.t) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) (row : CellPath × CellPath) :
    d.policyCellEnergy S k h p v Ψ row ≠ ⊤ ∧
      (d.policyCellEnergy S k h p v Ψ row).toReal ≤ d.prefixEnergyBound K p W := by
  let β := fun l => inheritedCircleSymbol S id (k l) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h l)
  let D := symbolDerivativeConstant K^K
  have hD : 0 ≤ D := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ (hh l)
  have hb (l : Fin 2) (x : Plane) (u : UnitCircle) : ‖β l x u‖ ≤ D :=
    inheritedCircleSymbol_norm_le S id (k l) d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i (h l)
      K (hK l) x (hhb l x) u
  have he := sourceAngularH_uniform_bound p v Ψ hW hw hs _ _
    (measurable_sourceAngularTransform _ _ _ _ (hm 0))
    (measurable_sourceAngularTransform _ _ _ _ (hm 1))
    (show 0 ≤ D*d.ρ.real univ/(((2:ℝ)^d.N)^(-d.mass p)) by positivity)
    (show 0 ≤ D*d.ρ.real univ/(((2:ℝ)^d.N)^(-d.mass p)) by positivity)
    (fun z => sourceAngularTransform_global_bound d.ρ (d.Q.descendant row.1).carrier
      (by positivity) (β 0) hD (hb 0) z.1 z.2)
    (fun z => sourceAngularTransform_global_bound d.ρ (d.Q.descendant row.2).carrier
      (by positivity) (β 1) hD (hb 1) z.1 z.2)
  refine ⟨he.1,he.2.trans ?_⟩
  unfold prefixEnergyBound
  dsimp only [D] at *
  gcongr
  norm_num

noncomputable def prefixSuccessorEnergies (d : PositiveDistanceData) (K p : ℕ)
    (Ψ : ℝ → ℝ) : Set ℝ :=
  insert 0 {E | ∃ v ∈ Finset.Ioc d.a d.t, (d.t:ℝ)-d.sig*d.N < (v:ℝ) ∧
    ∃ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
    ∃ k : Fin 2 → PolicyDescriptor → ℕ,
      (∀ l, ∑ b ∈ d.prefixRemainingList p, k l b ≤ K) ∧
    ∃ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) ∧
      (∀ l x, ‖h l x‖ ≤ 1) ∧
      E = (d.policyCellEnergy (d.prefixRemainingList p) k h p v Ψ row).toReal}

noncomputable def prefixSuccessorSupremum (d : PositiveDistanceData) (K p : ℕ)
    (Ψ : ℝ → ℝ) : ℝ := sSup (d.prefixSuccessorEnergies K p Ψ)

theorem prefixSuccessorEnergies_bddAbove (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (K p : ℕ) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) :
    BddAbove (d.prefixSuccessorEnergies K p Ψ) := by
  refine ⟨d.prefixEnergyBound K p W,?_⟩
  intro E hE
  rcases hE with rfl | ⟨v,hv,_,row,_,k,hk,h,hh,hhb,rfl⟩
  · unfold prefixEnergyBound
    positivity
  · exact (d.policyCellEnergy_finite_bound hQ _ k K hk h hh hhb p v
      (by exact_mod_cast (Finset.mem_Ioc.mp hv).2) Ψ hW hw hs row).2

theorem prefixSuccessorSupremum_majorizes (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (K p : ℕ) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) :
    0 ≤ d.prefixSuccessorSupremum K p Ψ ∧
    ∀ v ∈ Finset.Ioc d.a d.t, (d.t:ℝ)-d.sig*d.N < (v:ℝ) →
    ∀ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
    ∀ k : Fin 2 → PolicyDescriptor → ℕ,
      (∀ l, ∑ b ∈ d.prefixRemainingList p, k l b ≤ K) →
    ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      d.policyCellEnergy (d.prefixRemainingList p) k h p v Ψ row ≠ ⊤ ∧
      (d.policyCellEnergy (d.prefixRemainingList p) k h p v Ψ row).toReal ≤
        d.prefixSuccessorSupremum K p Ψ := by
  have hb := d.prefixSuccessorEnergies_bddAbove hQ K p Ψ hW hw hs
  refine ⟨le_csSup hb (Or.inl rfl),?_⟩
  intro v hv hv' row hr k hk h hh hhb
  exact ⟨(d.policyCellEnergy_finite_bound hQ _ k K hk h hh hhb p v
    (by exact_mod_cast (Finset.mem_Ioc.mp hv).2) Ψ hW hw hs row).1,
    le_csSup hb (Or.inr ⟨v,hv,hv',row,hr,k,hk,h,hh,hhb,rfl⟩)⟩

end PositiveDistanceData

end PlanarFalconer

end OAI
