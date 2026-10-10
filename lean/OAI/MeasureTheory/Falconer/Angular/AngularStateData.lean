import OAI.MeasureTheory.Falconer.Angular.AngularDroppedMaximum
import OAI.MeasureTheory.Falconer.Recursion.InheritedPolicyState

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff

structure AngularStateData where
  Q : DyadicSquare
  ρ : Measure Plane
  mass : ℝ → ℝ
  N : ℕ
  q : ℕ
  a₀ : ℕ
  t₀ : ℕ
  a : ℕ
  v : ℕ
  J : ℕ
  i : ℕ
  lam : ℝ
  sig : ℝ
  X : CellPath
  Y : CellPath

namespace AngularStateData

noncomputable def profile (d : AngularStateData) (n : ℕ) : ℝ := d.mass n-(n:ℝ)/d.N

noncomputable def retainedList (d : AngularStateData) (p : ℕ) : Finset PolicyDescriptor :=
  remainingPolicyDescriptors d.profile d.N d.q d.a₀ d.t₀ p

noncomputable def cellEnergy (d : AngularStateData) (S : Finset PolicyDescriptor)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (p : ℕ) (Ψ : ℝ → ℝ) (row : CellPath × CellPath) : ℝ≥0∞ :=
  sourceAngularH p d.v Ψ
    (fun z => sourceAngularTransform d.ρ (d.Q.descendant row.1).carrier
      (((2:ℝ)^d.N)^(-d.mass p))
      (inheritedCircleSymbol S id (k 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 0)) z.1 z.2)
    (fun z => sourceAngularTransform d.ρ (d.Q.descendant row.2).carrier
      (((2:ℝ)^d.N)^(-d.mass p))
      (inheritedCircleSymbol S id (k 1) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 1)) z.1 z.2)

noncomputable def energy (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (Ψ : ℝ → ℝ) : ℝ≥0∞ :=
  d.cellEnergy (d.retainedList d.a) k h d.a Ψ (d.X,d.Y)

noncomputable def childEnergy (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (p : ℕ) (Ψ : ℝ → ℝ) : CellPath × CellPath → ℝ≥0∞ :=
  d.cellEnergy (d.retainedList p) k h p Ψ

noncomputable def children (d : AngularStateData) (p : ℕ) : Finset (CellPath × CellPath) :=
  sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a)

noncomputable def childMaximum (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (p : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  finiteEnergyMaximum (d.children p) (d.childEnergy k h p Ψ)

theorem child_budget (d : AngularStateData) {a p K : ℕ} (hap : a ≤ p)
    (k : PolicyDescriptor → ℕ) (hk : ∑ b ∈ d.retainedList a, k b ≤ K) :
    ∑ b ∈ d.retainedList p, k b ≤ K := by
  exact (Finset.sum_le_sum_of_subset (remainingPolicyDescriptors_mono
    d.profile d.N d.q d.a₀ d.t₀ hap)).trans hk

theorem cellEnergy_finite (d : AngularStateData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (S : Finset PolicyDescriptor)
    (k : Fin 2 → PolicyDescriptor → ℕ) (K : ℕ) (hk : ∀ l, ∑ b ∈ S, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (p : ℕ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) (row : CellPath × CellPath) :
    d.cellEnergy S k h p Ψ row ≠ ⊤ := by
  let : ∀ _l : Fin 2, IsFiniteMeasure d.ρ := fun _ => inferInstance
  exact inherited_product_energy_finite (fun _ : Fin 2 => S) (fun _ => id) k K hk
    (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) (fun _ => d.mass)
    d.N d.lam d.sig d.J d.i h hh hhb
    (d.Q.descendant row.1).carrier (d.Q.descendant row.2).carrier p d.v
    (by positivity) (by positivity) hΨ hpos hs

theorem childMaximum_nonneg (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ) :
    0 ≤ d.childMaximum k h p Ψ := finiteEnergyMaximum_nonneg _ _

theorem childMaximum_empty (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ)
    (he : d.children p = ∅) : d.childMaximum k h p Ψ = 0 := by
  simp only [childMaximum,he,finiteEnergyMaximum_empty]

theorem childMaximum_attained (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ)
    (he : (d.children p).Nonempty) :
    ∃ row ∈ d.children p, d.childMaximum k h p Ψ = (d.childEnergy k h p Ψ row).toReal :=
  finiteEnergyMaximum_attained _ he _

end AngularStateData

end PlanarFalconer

end OAI
