import OAI.Geometry.NodalSets.Elliptic.RealTransportDerivatives
import OAI.Geometry.NodalSets.Elliptic.RealWeightedElliptic

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

lemma realMatrixEnergy_derivative (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (v : Yau.Jets.Coord → ℝ) (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hs : ∀ x i j, B x i j = B x j i) (hv : ContDiff ℝ ∞ v)
    (x : Yau.Jets.Coord) (k : Fin 4) :
    Yau.coordPartial (realMatrixEnergy B v v) x k =
      (∑ i, ∑ j, Yau.coordPartial (fun y ↦ B y i j) x k *
        Yau.coordPartial v x i*Yau.coordPartial v x j) +
      2*(∑ i, ∑ j, B x i j*Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k*
        Yau.coordPartial v x j) := by
  have hvd := Yau.real_coordPartial_smooth v hv
  have he : realMatrixEnergy B v v = fun y ↦ ∑ i, ∑ j,
      Yau.coordPartial v y i*B y i j*Yau.coordPartial v y j :=
    funext (realMatrixEnergy_apply B v v)
  rw [he,Yau.real_coordPartial_sum _ (fun i ↦
    ContDiff.sum (fun j _ ↦ ((hvd i).mul (hB i j)).mul (hvd j)))]
  simp_rw [Yau.real_coordPartial_sum _ (fun j ↦ ((hvd _).mul (hB _ j)).mul (hvd j)),
    Yau.real_coordPartial_mul _ _ ((hvd _).mul (hB _ _)) (hvd _),
    Yau.real_coordPartial_mul _ _ (hvd _) (hB _ _)]
  have hswap : (∑ i, ∑ j, Yau.coordPartial v x i*B x i j*
      Yau.coordPartial (fun y ↦ Yau.coordPartial v y j) x k) =
      (∑ i, ∑ j, B x i j*Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k*
        Yau.coordPartial v x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs x j i]
    ring
  simp only [add_mul,Finset.sum_add_distrib]
  rw [hswap]
  have ha : (∑ i, ∑ j, Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k * B x i j *
      Yau.coordPartial v x j) =
      (∑ i, ∑ j, B x i j*Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k*
        Yau.coordPartial v x j) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  have hb : (∑ i, ∑ j, Yau.coordPartial v x i*Yau.coordPartial (fun y ↦ B y i j) x k*
      Yau.coordPartial v x j) =
      (∑ i, ∑ j, Yau.coordPartial (fun y ↦ B y i j) x k *
        Yau.coordPartial v x i*Yau.coordPartial v x j) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [ha,hb]
  ring

lemma real_sum_rotate (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ k, ∑ i, ∑ j, f k i j) = ∑ i, ∑ j, ∑ k, f k i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

def realTransportDeformation (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  ∑ i, ∑ j, ∑ k,
    (2*B x i j*Yau.coordPartial (fun y ↦ V y k) x i*Yau.coordPartial v x k*Yau.coordPartial v x j -
      V x k*Yau.coordPartial (fun y ↦ B y i j) x k*Yau.coordPartial v x i*Yau.coordPartial v x j)

theorem realMatrixEnergy_transport (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ k, ContDiff ℝ ∞ (fun x ↦ V x k)) (hv : ContDiff ℝ ∞ v) (x : Yau.Jets.Coord) :
    2*realMatrixEnergy B (Yau.pairing v V) v x =
      Yau.pairing (realMatrixEnergy B v v) V x + realTransportDeformation B V v x := by
  have he : Yau.pairing (realMatrixEnergy B v v) V x =
      (∑ i, ∑ j, ∑ k, (Yau.coordPartial (fun y ↦ B y i j) x k *
        Yau.coordPartial v x i*Yau.coordPartial v x j)*V x k) +
      (∑ i, ∑ j, ∑ k, (2*(B x i j*Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k*
        Yau.coordPartial v x j))*V x k) := by
    simp only [Yau.pairing,realMatrixEnergy_derivative B v hB hs hv,add_mul,
      Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
    congr 1 <;> exact real_sum_rotate _
  rw [realMatrixEnergy_apply,he]
  simp_rw [Yau.real_coordPartial_pairing v V hv hV]
  simp only [add_mul,
    Finset.sum_add_distrib,Finset.sum_mul,realTransportDeformation,
    Finset.sum_sub_distrib]
  simp_rw [Yau.real_coordPartial_commute v hv x]
  simp only [mul_assoc,mul_left_comm,mul_comm]
  ring_nf
  simp only [← Finset.sum_mul]

end
end Yau.Geometry

end OAI
