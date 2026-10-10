import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactSourceGrid
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalCellVolume
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedFarQuadrature

namespace OAI

/-! The exceptional cells for a compact orbital source consist of the
manufactured well support together with one neighborhood of the orbital. -/

noncomputable section
open MeasureTheory
open scoped Classical
namespace ContinuumCoulomb

theorem source_exceptional_volume {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h R S : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hR : 0 ≤ R) (hS : 1 ≤ S)
    (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (v : PlanarPosition) :
    (Fintype.card {i // sourceExceptionalCell (tsupport (manufacturedWellField freq scale S u))
      v R (gaussCellCenter h (index i)) h}:ℝ)*h^3 ≤
      216*m*S+8*(4*R+2*h)^3 := by
  let a : ι → Prop := fun i => ∃ z ∈ positionCube (gaussCellCenter h (index i)) h,
    z ∈ tsupport (manufacturedWellField freq scale S u)
  let b : ι → Prop := fun i => ‖planarCenter v-gaussCellCenter h (index i)‖ ≤ 4*R
  have ha := exceptional_cell_volume_bound (fun i : {i // a i} => index i.val)
    (fun i j he => Subtype.ext (hindex he)) hh hh1 hS freq scale u (fun i => i.property)
  have hb := orbital_near_cell_volume (fun i : {i // b i} => index i.val)
    (fun i j he => Subtype.ext (hindex he)) (R := 4*R) hh (mul_nonneg (by norm_num) hR) v
    (fun i => by simpa only [b,norm_sub_rev] using i.property)
  have hcard : Fintype.card {i // a i ∨ b i} ≤
      Fintype.card {i // a i}+Fintype.card {i // b i} := by
    simp only [Fintype.card_subtype]
    have he : (Finset.univ.filter (fun i => a i ∨ b i)) =
        (Finset.univ.filter a) ∪ (Finset.univ.filter b) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    rw [he]
    exact Finset.card_union_le _ _
  have hcardR : (Fintype.card {i // a i ∨ b i}:ℝ) ≤
      (Fintype.card {i // a i}:ℝ)+(Fintype.card {i // b i}:ℝ) := by exact_mod_cast hcard
  have hs := mul_le_mul_of_nonneg_right hcardR (pow_nonneg hh.le 3)
  have he : Fintype.card {i // sourceExceptionalCell (tsupport (manufacturedWellField freq scale S u))
      v R (gaussCellCenter h (index i)) h} = Fintype.card {i // a i ∨ b i} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [he]
  nlinarith only [hs,ha,hb]

end ContinuumCoulomb

end

end OAI
