import OAI.NumberTheory.Ostmann.Arithmetic.PermutationDiagramComparison

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PermutationDiagramComparison
open scoped BigOperators ComplexConjugate
open Ostmann.FiniteField Ostmann.Tree ResidueHaar
variable {p depth m : ℕ} [Fact p.Prime]

theorem diagramCorrelation_cauchy_sq {b : ℕ} (P Q : LeafPartition depth b)
    (T1 T2 : Diagram (ZMod p) depth) (g : ZMod p → ℂ) :
    ‖diagramCorrelation P Q T1 T2 g‖^2≤
      Density.average (fun M => ‖T1.value g M‖^2)*
      Density.average (fun M => ‖T2.value g M‖^2) := by
  have hh := coupled_cauchy_sq (labelProducts (U:=(ZMod p)ˣ) P.label) (labelProducts Q.label)
    (labelProducts_surjective P.label P.onto) (labelProducts_surjective Q.label Q.onto)
    (T1.value g) (T2.value g)
  have he := average_equiv (coupledLeavesEquiv (p:=p) P Q)
    (fun x : CoupledLeaves (p:=p) P Q => T1.value g x.val.1*conj (T2.value g x.val.2))
  change average (fun x : coupledGroup (labelProducts P.label) (labelProducts Q.label) =>
    T1.value g x.val.1*conj (T2.value g x.val.2))=diagramCorrelation P Q T1 T2 g at he
  rw [he] at hh
  simp only [real_average_fintype_congr _
    (inferInstance : Fintype (Leaves depth → (ZMod p)ˣ))] at hh
  exact hh

theorem slotCorrelation_universal_bound (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (hm : 0 < m) (T1 T2 : Diagram (ZMod p) depth) (hp : 3≤p)
    (g : ZMod p → ℂ) (hg : l2Sq g≤1) :
    ‖slotCorrelation σ T1 T2 g‖≤(3:ℝ)^(2^depth) := by
  rw [slotCorrelation_eq_diagramCorrelation σ hm]
  have hc := diagramCorrelation_cauchy_sq
    (TreePermutationHaar.leftPartition σ) (TreePermutationHaar.rightPartition σ hm) T1 T2 g
  have h1 := Density.diagram_l2_bound T1 hp g hg
  have h2 := Density.diagram_l2_bound T2 hp g hg
  have hn2 : 0≤Density.average (fun M => ‖T2.value g M‖^2) := by
    unfold Density.average
    positivity
  have hh := mul_le_mul h1 h2 hn2 (by positivity : (0:ℝ)≤3^(2^depth))
  have hsq : ‖diagramCorrelation (TreePermutationHaar.leftPartition σ)
      (TreePermutationHaar.rightPartition σ hm) T1 T2 g‖^2≤((3:ℝ)^(2^depth))^2 := by
    simpa only [pow_two] using hc.trans hh
  have hn := norm_nonneg (diagramCorrelation (TreePermutationHaar.leftPartition σ)
      (TreePermutationHaar.rightPartition σ hm) T1 T2 g)
  have hb : (0:ℝ)≤3^(2^depth) := by positivity
  nlinarith

end Ostmann.Arithmetic.PermutationDiagramComparison

end

end OAI
