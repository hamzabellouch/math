import OAI.MeasureTheory.Falconer.Angular.AngularStateData
import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace AngularStateData

def successor (d : AngularStateData) (p : ℕ) (row : CellPath × CellPath) : AngularStateData :=
  {d with a := p, X := row.1, Y := row.2}

theorem successor_energy (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (p : ℕ) (Ψ : ℝ → ℝ) (row : CellPath × CellPath) :
    (d.successor p row).energy k h Ψ = d.childEnergy k h p Ψ row := rfl

theorem children_lengths (d : AngularStateData) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    {row : CellPath × CellPath} (hr : row ∈ d.children p) :
    row.1.length = p ∧ row.2.length = p := by
  have hd := sourceProductVertices_subset d.Q d.Q d.ρ d.ρ d.X d.Y d.a (p-d.a) hX hY hr
  have hl := Finset.mem_product.mp hd
  constructor
  · simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.1
  · simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.2

theorem remaining_energy_eq_child (d : AngularStateData) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (Ψ : ℝ → ℝ) {row : CellPath × CellPath} (hr : row ∈ d.children p) :
    remainingAngularEnergy (fun _ : Fin 2 => d.retainedList d.a) (fun _ => id) k
      (fun _ => d.Q) (fun _ => d.ρ) (fun _ => d.mass) d.N d.lam d.sig d.J d.i h
      (((2:ℝ)^d.N)^(-d.mass p)) (((2:ℝ)^d.N)^(-d.mass p)) p d.v Ψ row =
        d.childEnergy k h p Ψ row := by
  have hl := d.children_lengths hap hX hY hr
  simp only [remainingAngularEnergy,hl.1,hl.2,id_eq,childEnergy,cellEnergy,retainedList,
    remainingPolicyDescriptors_drop d.profile d.N d.q d.a₀ d.t₀ hap]

theorem remaining_maximum_eq_child (d : AngularStateData) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (Ψ : ℝ → ℝ) :
    finiteEnergyMaximum (d.children p)
      (remainingAngularEnergy (fun _ : Fin 2 => d.retainedList d.a) (fun _ => id) k
        (fun _ => d.Q) (fun _ => d.ρ) (fun _ => d.mass) d.N d.lam d.sig d.J d.i h
        (((2:ℝ)^d.N)^(-d.mass p)) (((2:ℝ)^d.N)^(-d.mass p)) p d.v Ψ) =
      d.childMaximum k h p Ψ := by
  unfold finiteEnergyMaximum childMaximum
  congr 1
  apply Finset.sup_congr rfl
  intro row hr
  rw [d.remaining_energy_eq_child hap hX hY k h Ψ hr]

theorem retained_length_le_N (d : AngularStateData) (hq : 0 < d.q) (htN : d.t₀ ≤ d.N)
    (a : ℕ) : (d.retainedList a).sup descriptorLength ≤ d.N := by
  apply Finset.sup_le
  intro b hb
  have ht := policyDescriptor_twice_length d.profile hq (Finset.mem_filter.mp hb).1
  omega

end AngularStateData

end PlanarFalconer

end OAI
