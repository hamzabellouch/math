import OAI.Analysis.LipschitzHilbert.Packets.PacketConvolution
import OAI.Analysis.LipschitzHilbert.Estimates.SlicedIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! Exact periodization over the translated sheared box lattice used
in the continuous packet representation. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace LipschitzHilbert.PacketRepresentation

def latticeHom (l W theta : ℝ) : (ℤ × ℤ) →+ (ℝ × ℝ) where
  toFun n := ((n.1:ℝ)*l, theta*(n.1:ℝ)*l+(n.2:ℝ)*W)
  map_zero' := by simp
  map_add' n m := by ext <;> simp <;> ring

def latticeCell (l W theta : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc 0 l ∧ x.2-theta*x.1 ∈ Ioc 0 W}

theorem latticeHom_injective {l W theta : ℝ} (hl : l ≠ 0) (hW : W ≠ 0) :
    Function.Injective (latticeHom l W theta) := by
  intro n m h
  have h1 : (n.1:ℝ)*l=(m.1:ℝ)*l := congrArg Prod.fst h
  have h2 : theta*(n.1:ℝ)*l+(n.2:ℝ)*W=theta*(m.1:ℝ)*l+(m.2:ℝ)*W :=
    congrArg Prod.snd h
  have hn : n.1=m.1 := by exact_mod_cast (mul_right_cancel₀ hl h1)
  have hk : n.2=m.2 := by
    rw [hn] at h2
    exact_mod_cast (mul_right_cancel₀ hW (add_left_cancel h2))
  exact Prod.ext hn hk

theorem latticeCell_measurable (l W theta : ℝ) : MeasurableSet (latticeCell l W theta) :=
  (measurable_fst measurableSet_Ioc).inter
    ((measurable_snd.sub (measurable_const.mul measurable_fst)) measurableSet_Ioc)

theorem latticeCell_unique {l W theta : ℝ} (hl : 0<l) (hW : 0<W) (x : ℝ × ℝ) :
    ∃! n : ℤ × ℤ, latticeHom l W theta n + x ∈ latticeCell l W theta := by
  obtain ⟨i,hi,hui⟩ := existsUnique_add_zsmul_mem_Ioc hl x.1 0
  obtain ⟨j,hj,huj⟩ := existsUnique_add_zsmul_mem_Ioc hW (x.2-theta*x.1) 0
  have hcoord (n : ℤ × ℤ) :
      (latticeHom l W theta n+x).2-theta*(latticeHom l W theta n+x).1 =
        x.2-theta*x.1+(n.2:ℝ)*W := by
    simp only [latticeHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_add, Prod.snd_add]
    ring
  have hmem (n : ℤ × ℤ) : latticeHom l W theta n+x ∈ latticeCell l W theta ↔
      x.1+n.1 • l ∈ Ioc 0 (0+l) ∧ (x.2-theta*x.1)+n.2 • W ∈ Ioc 0 (0+W) := by
    change (_ ∈ Ioc 0 l ∧ _ ∈ Ioc 0 W) ↔ _
    rw [hcoord]
    simp only [latticeHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_add, zero_add,
      zsmul_eq_mul, add_comm ((n.1:ℝ)*l)]
  refine ⟨(i,j), (hmem _).2 ⟨hi,hj⟩, ?_⟩
  intro n hn
  exact Prod.ext (hui _ ((hmem n).1 hn).1) (huj _ ((hmem n).1 hn).2)

theorem latticeCell_fundamental {l W theta : ℝ} (hl : 0<l) (hW : 0<W) :
    IsAddFundamentalDomain (latticeHom l W theta).range (latticeCell l W theta) planeMeasure := by
  let e := AddMonoidHom.ofInjective (latticeHom_injective (theta := theta) hl.ne' hW.ne')
  apply IsAddFundamentalDomain.mk' (latticeCell_measurable l W theta).nullMeasurableSet
  intro x
  obtain ⟨n,hn,hun⟩ := latticeCell_unique (theta := theta) hl hW x
  refine ⟨e n,hn,?_⟩
  intro g hg
  change (g : ℝ × ℝ)+x ∈ latticeCell l W theta at hg
  have hs : e.symm g=n := hun (e.symm g) (by
    change (e (e.symm g) : ℝ × ℝ)+x ∈ latticeCell l W theta
    simpa only [e.apply_symm_apply] using hg)
  calc
    g = e (e.symm g) := (e.apply_symm_apply g).symm
    _ = e n := congrArg e hs

theorem sheared_lattice_periodization {l W theta : ℝ} (hl : 0<l) (hW : 0<W)
    (F : ℝ × ℝ → ℂ) (hF : Integrable F planeMeasure) :
    (∫ x, F x ∂planeMeasure) =
      ∫ z in latticeCell l W theta, ∑' n : ℤ × ℤ, F (latticeHom l W theta n+z) ∂planeMeasure := by
  let G := (latticeHom l W theta).range
  let e : (ℤ × ℤ) ≃+ G :=
    AddMonoidHom.ofInjective (latticeHom_injective (theta := theta) hl.ne' hW.ne')
  let : Countable G := Countable.of_equiv (ℤ × ℤ) e.toEquiv
  have hs := latticeCell_fundamental (theta := theta) hl hW
  have hm (g : G) : AEStronglyMeasurable (fun z => F (g+ᵥz))
      (planeMeasure.restrict (latticeCell l W theta)) :=
    (hF.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_left planeMeasure (g:ℝ×ℝ))).restrict
  have hsum : (∑' g : G, ∫⁻ z in latticeCell l W theta, ‖F (g+ᵥz)‖ₑ ∂planeMeasure) ≠ ∞ := by
    rw [← hs.lintegral_eq_tsum'' (fun z => ‖F z‖ₑ)]
    exact hF.hasFiniteIntegral.ne
  calc
    _ = ∑' g : G, ∫ z in latticeCell l W theta, F (g+ᵥz) ∂planeMeasure :=
      hs.integral_eq_tsum'' F hF
    _ = ∫ z in latticeCell l W theta, ∑' g : G, F (g+ᵥz) ∂planeMeasure :=
      (integral_tsum hm hsum).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (e.toEquiv.tsum_eq (fun g : G => F (g+ᵥz))).symm


theorem latticeCell_volume {l W theta : ℝ} (hl : 0<l) (_hW : 0<W) :
    planeMeasure (latticeCell l W theta) = ENNReal.ofReal (l*W) := by
  have heq : latticeCell l W theta =
      (slopeShear (-theta)) ⁻¹' ((Ioc 0 l) ×ˢ (Ioc 0 W)) := by
    ext x
    change (x.1 ∈ Ioc 0 l ∧ x.2-theta*x.1 ∈ Ioc 0 W) ↔
      (x.1 ∈ Ioc 0 l ∧ x.2+(-theta)*x.1 ∈ Ioc 0 W)
    simp only [neg_mul, sub_eq_add_neg]
  rw [heq, (slopeShear_measurePreserving (-theta)).measure_preimage_equiv,
    Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc, sub_zero, sub_zero,
    ← ENNReal.ofReal_mul hl.le]

def latticeAverage (l W theta : ℝ) : Measure (ℝ × ℝ) :=
  (ENNReal.ofReal (l*W))⁻¹ • planeMeasure.restrict (latticeCell l W theta)

theorem latticeAverage_probability {l W theta : ℝ} (hl : 0<l) (hW : 0<W) :
    IsProbabilityMeasure (latticeAverage l W theta) where
  measure_univ := by
    rw [latticeAverage, Measure.smul_apply, Measure.restrict_apply_univ, latticeCell_volume hl hW,
      smul_eq_mul, ENNReal.inv_mul_cancel]
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hl hW))
    · exact ENNReal.ofReal_ne_top

theorem integral_latticeAverage {l W theta : ℝ} (hl : 0<l) (hW : 0<W)
    (F : ℝ × ℝ → ℂ) :
    (∫ z, F z ∂latticeAverage l W theta) =
      ((l*W)⁻¹ : ℝ) • ∫ z in latticeCell l W theta, F z ∂planeMeasure := by
  rw [latticeAverage, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (mul_pos hl hW).le]

theorem sheared_lattice_summable {l W theta : ℝ} (hl : 0<l) (hW : 0<W)
    (F : ℝ × ℝ → ℂ) (hF : Integrable F planeMeasure) :
    ∀ᵐ z ∂latticeAverage l W theta,
      Summable (fun n : ℤ×ℤ => ‖F (latticeHom l W theta n+z)‖) := by
  let G := (latticeHom l W theta).range
  let e : (ℤ×ℤ) ≃+ G :=
    AddMonoidHom.ofInjective (latticeHom_injective (theta := theta) hl.ne' hW.ne')
  let : Countable G := Countable.of_equiv (ℤ×ℤ) e.toEquiv
  have hs := latticeCell_fundamental (theta := theta) hl hW
  have hm (g : G) : AEMeasurable (fun z => ‖F (g+ᵥz)‖ₑ)
      (planeMeasure.restrict (latticeCell l W theta)) :=
    ((hF.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left planeMeasure (g:ℝ×ℝ))).restrict).enorm
  have hi : (∫⁻ z in latticeCell l W theta, ∑' g : G, ‖F (g+ᵥz)‖ₑ ∂planeMeasure) ≠ ∞ := by
    rw [lintegral_tsum hm, ← hs.lintegral_eq_tsum'' (fun z => ‖F z‖ₑ)]
    exact hF.hasFiniteIntegral.ne
  have ha := ae_lt_top' (AEMeasurable.tsum hm) hi
  apply Measure.ae_smul_measure _ ((ENNReal.ofReal (l*W))⁻¹)
  filter_upwards [ha] with z hz
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  have he : (∑' n : ℤ×ℤ, ‖F (latticeHom l W theta n+z)‖ₑ) =
      ∑' g : G, ‖F (g+ᵥz)‖ₑ := e.toEquiv.tsum_eq (fun g : G => ‖F (g+ᵥz)‖ₑ)
  rw [he]
  exact hz.ne

end LipschitzHilbert.PacketRepresentation

end

end OAI
