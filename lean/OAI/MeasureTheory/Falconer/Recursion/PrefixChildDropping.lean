import OAI.MeasureTheory.Falconer.Graphs.PrefixSuccessorEnergy
import OAI.MeasureTheory.Falconer.Angular.AngularDroppedMaximum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace PositiveDistanceData

theorem prefix_child_drop (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (p : ℕ) (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (row : CellPath × CellPath)
    (hr : row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a))
    (k : Fin 2 → PolicyDescriptor → ℕ) (K : ℕ)
    (hk : ∀ l, ∑ b ∈ d.inverseDescriptorList, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    d.policyCellEnergy (d.prefixRemainingList p) k h p v Ψ row ≠ ⊤ ∧
    (d.policyCellEnergy d.inverseDescriptorList k h p v Ψ row).toReal ≤
      (symbolDerivativeConstant K^K)^4 *
        (d.policyCellEnergy (d.prefixRemainingList p) k h p v Ψ row).toReal := by
  classical
  have hd := sourceProductVertices_subset d.Q d.Q d.ρ d.ρ d.X d.Y d.a (p-d.a) hX hY hr
  have hl := Finset.mem_product.mp hd
  have h1 : row.1.length = p := by
    simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.1
  have h2 : row.2.length = p := by
    simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.2
  let : ∀ _l : Fin 2, IsFiniteMeasure d.ρ := fun _ => inferInstance
  have hdrop := inherited_product_energy_drop_real (fun _ : Fin 2 => d.inverseDescriptorList)
    (fun _ => id) k K hk (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) (fun _ => d.mass)
    d.N d.lam d.sig d.J d.i h hh hhb row p v
    (by positivity : 0 < ((2:ℝ)^d.N)^(-d.mass p))
    (by positivity : 0 < ((2:ℝ)^d.N)^(-d.mass p)) hΨ hpos hs
  simpa only [remainingAngularEnergy,h1,h2,policyCellEnergy,prefixRemainingList,
    remainingPolicyDescriptors,inverseDescriptorList,id_eq] using hdrop

theorem prefix_child_maximum_le (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (K p : ℕ) (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (v : ℕ) (hv : v ∈ Finset.Ioc d.a d.t) (hvhigh : (d.t:ℝ)-d.sig*d.N < (v:ℝ))
    (k : Fin 2 → PolicyDescriptor → ℕ) (hk : ∀ l, ∑ b ∈ d.inverseDescriptorList, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    finiteEnergyMaximum (sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a))
      (d.policyCellEnergy d.inverseDescriptorList k h p v Ψ) ≤
      (symbolDerivativeConstant K^K)^4*d.prefixSuccessorSupremum K p Ψ := by
  classical
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hsup := d.prefixSuccessorSupremum_majorizes hQ K p Ψ hW
    (fun x => (le_abs_self _).trans (hWb x)) hsupport
  have hk' (l : Fin 2) : ∑ b ∈ d.prefixRemainingList p, k l b ≤ K :=
    remaining_symbol_budget d.inverseDescriptorList id (k l) p K (hk l)
  let S := sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a)
  by_cases hS : S.Nonempty
  · obtain ⟨row,hr,he⟩ := finiteEnergyMaximum_attained S hS
      (d.policyCellEnergy d.inverseDescriptorList k h p v Ψ)
    rw [he]
    exact (d.prefix_child_drop hQ p hap hX hY row hr k K hk h hh hhb v hΨ hpos hs).2.trans
      (mul_le_mul_of_nonneg_left (hsup.2 v hv hvhigh row hr k hk' h hh hhb).2 (by positivity))
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change finiteEnergyMaximum S _ ≤ _
    rw [he,finiteEnergyMaximum_empty]
    exact mul_nonneg (by positivity) hsup.1

end PositiveDistanceData

end PlanarFalconer

end OAI
