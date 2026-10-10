import OAI.MeasureTheory.Falconer.Angular.AngularStateData

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
namespace AngularStateData

theorem child_drop (d : AngularStateData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (p : ℕ) (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (row : CellPath × CellPath) (hr : row ∈ d.children p)
    (k : Fin 2 → PolicyDescriptor → ℕ) (K : ℕ)
    (hk : ∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    d.childEnergy k h p Ψ row ≠ ⊤ ∧
    (d.cellEnergy (d.retainedList d.a) k h p Ψ row).toReal ≤
      (symbolDerivativeConstant K^K)^4*(d.childEnergy k h p Ψ row).toReal := by
  classical
  have hd := sourceProductVertices_subset d.Q d.Q d.ρ d.ρ d.X d.Y d.a (p-d.a) hX hY hr
  have hl := Finset.mem_product.mp hd
  have h1 : row.1.length = p := by
    simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.1
  have h2 : row.2.length = p := by
    simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.2
  let : ∀ _l : Fin 2, IsFiniteMeasure d.ρ := fun _ => inferInstance
  have hdrop := inherited_product_energy_drop_real (fun _ : Fin 2 => d.retainedList d.a)
    (fun _ => id) k K hk (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) (fun _ => d.mass)
    d.N d.lam d.sig d.J d.i h hh hhb row p d.v
    (by positivity : 0 < ((2:ℝ)^d.N)^(-d.mass p))
    (by positivity : 0 < ((2:ℝ)^d.N)^(-d.mass p)) hΨ hpos hs
  simpa only [remainingAngularEnergy,h1,h2,childEnergy,cellEnergy,retainedList,id_eq,
    remainingPolicyDescriptors_drop d.profile d.N d.q d.a₀ d.t₀ hap] using hdrop

theorem child_maximum_drop (d : AngularStateData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (p : ℕ) (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (k : Fin 2 → PolicyDescriptor → ℕ) (K : ℕ)
    (hk : ∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    finiteEnergyMaximum (d.children p) (d.cellEnergy (d.retainedList d.a) k h p Ψ) ≤
      (symbolDerivativeConstant K^K)^4*d.childMaximum k h p Ψ := by
  apply finiteEnergyMaximum_le_mul _ _ _ (by positivity)
  intro row hr
  exact (d.child_drop hQ p hap hX hY row hr k K hk h hh hhb hΨ hpos hs).2

end AngularStateData

end PlanarFalconer

end OAI
