import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedGrid
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedHybrid
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.GaussGrid
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ExceptionalCellVolume

namespace OAI

/-! Local fourth-order error with the nondecaying transport correction
charged only to cells meeting the compact well support. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb

def cellHits (E : Set Position) (b : Position) (h : ℝ) : ℝ :=
  if ∃ z ∈ positionCube b h, z ∈ E then 1 else 0

theorem cellHits_nonneg (E : Set Position) (b : Position) (h : ℝ) : 0 ≤ cellHits E b h := by
  unfold cellHits
  split_ifs <;> norm_num

theorem cellHits_indicator_le (E : Set Position) (b : Position) (h : ℝ)
    {x : Position} (hx : x ∈ positionCube b h) :
    (if x ∈ E then (1:ℝ) else 0) ≤ cellHits E b h := by
  by_cases hE : x ∈ E
  · simp [hE,cellHits,show ∃ z ∈ positionCube b h, z ∈ E from ⟨x,hx,hE⟩]
  · simpa only [ite_eq_right hE] using cellHits_nonneg E b h

theorem manufactured_cellHits_volume_bound {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h S : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hS : 1 ≤ S)
    (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) :
    (∑ i, cellHits (tsupport (manufacturedWellField freq scale S u))
      (gaussCellCenter h (index i)) h*h^3) ≤ 216*m*S := by
  let s := Finset.univ.filter (fun i => ∃ z ∈ positionCube (gaussCellCenter h (index i)) h,
    z ∈ tsupport (manufacturedWellField freq scale S u))
  have hi : Function.Injective (fun i : {i // i ∈ s} => index i.val) := by
    intro i j hij
    exact Subtype.ext (hindex hij)
  have he := exceptional_cell_volume_bound (fun i : {i // i ∈ s} => index i.val) hi
    hh hh1 hS freq scale u (fun i => (Finset.mem_filter.mp i.property).2)
  simpa only [Fintype.card_coe,s,cellHits,ite_mul,one_mul,zero_mul,← Finset.sum_filter,
    Finset.sum_const,nsmul_eq_mul] using he

theorem transportedCoulomb_far_cell_hybrid_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (E : Set Position), IsClosed E → (∀ x, x ∉ E → G x = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ (L : ℝ≥0), 0 < L → LipschitzWith L G →
      ∀ (y b : Position) (h : ℝ), 0 < h → 4*(L:ℝ)*h ≤ ‖y-G b‖ →
      |positionCellGauss b h (fun x => Coulomb.coulombKernel (y-G x))-
        positionCellIntegral b h (fun x => Coulomb.coulombKernel (y-G x))| ≤
        (24*C*D^4)*(32/‖y-G b‖^5+cellHits E b h)*h^7 := by
  obtain ⟨C,hC,hbound⟩ := transportedCoulomb_hybrid_fourth_bound
  refine ⟨C,hC,fun G hG E hE hfix D hD hGD L hL hLip y b h hh hfar => ?_⟩
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  have hd : 0 < ‖y-G b‖ := lt_of_lt_of_le (by positivity) hfar
  have hf (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (v : ℝ) (hv : v ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ContDiffAt ℝ 4 (fun a => Coulomb.coulombKernel (y-G a)) (cubePoint b (h/2) x v z) := by
    have hc := cubePoint_mem_positionCube b hh.le hx hv hz
    have hn := (transported_far_cube_distances hh G hL hLip hfar hc).1
    have hne : y-G (cubePoint b (h/2) x v z) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity : (0:ℝ) < (L:ℝ)*h) hn.le)
    exact ContDiffAt.comp (g := Coulomb.coulombKernel) (f := fun a : Position => y-G a)
      _ ((coulombKernel_contDiffAt hne).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)) (contDiffAt_const.sub hG.contDiffAt)
  apply positionCellGauss_error_local _ b hh.le
    (mul_nonneg (by positivity) (add_nonneg (by positivity) (cellHits_nonneg E b h))) hf
  intro x hx v hv z hz
  let a := cubePoint b (h/2) x v z
  have hc : a ∈ positionCube b h := cubePoint_mem_positionCube b hh.le hx hv hz
  have ha := transported_far_cube_distances hh G hL hLip hfar hc
  have hapos : 0 < ‖y-G a‖ := lt_of_lt_of_le (by positivity : (0:ℝ) < (L:ℝ)*h) ha.1.le
  have hp : 1/‖y-G a‖^5 ≤ 32/‖y-G b‖^5 := by
    have he := one_div_le_one_div_of_le (pow_pos (by positivity : 0 < ‖y-G b‖/2) 5)
      (pow_le_pow_left₀ (by positivity : 0 ≤ ‖y-G b‖/2) ha.2.1 5)
    apply he.trans_eq
    field_simp
    norm_num
  apply (hbound G hG E hE hfix D hD hGD y a (norm_pos_iff.mp hapos)).trans
  exact mul_le_mul_of_nonneg_left (add_le_add hp (cellHits_indicator_le E b h hc)) (by positivity)

theorem transportedCoulomb_far_grid_hybrid_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (E : Set Position), IsClosed E → (∀ x, x ∉ E → G x = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ (L : ℝ≥0), 0 < L → LipschitzWith L G →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ)
        (y : Position) (h : ℝ), 0 < h →
      (∀ i, 4*(L:ℝ)*h ≤ ‖y-G (gaussCellCenter h (index i))‖) →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => Coulomb.coulombKernel (y-G x)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => Coulomb.coulombKernel (y-G x)))| ≤
        24*C*D^4*h^4*(32*(∑ i, h^3/‖y-G (gaussCellCenter h (index i))‖^5)+
          ∑ i, cellHits E (gaussCellCenter h (index i)) h*h^3) := by
  obtain ⟨C,hC,hbound⟩ := transportedCoulomb_far_cell_hybrid_error
  refine ⟨C,hC,?_⟩
  intro G hG E hE hfix D hD hGD L hL hLip ι _ index y h hh hfar
  have he := weighted_cubature_error h 1
    (fun i => positionCellGauss (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x)))
    (fun i => positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x)))
    (fun i => 24*C*D^4*(32/‖y-G (gaussCellCenter h (index i))‖^5+
      cellHits E (gaussCellCenter h (index i)) h))
    zero_le_one (fun i => hbound G hG E hE hfix D hD hGD L hL hLip y _ h hh (hfar i))
  simp only [one_mul] at he
  apply he.trans_eq
  have hs : (∑ i, (24*C*D^4*(32/‖y-G (gaussCellCenter h (index i))‖^5+
      cellHits E (gaussCellCenter h (index i)) h))*h^3) =
      (24*C*D^4)*(32*(∑ i, h^3/‖y-G (gaussCellCenter h (index i))‖^5)+
        ∑ i, cellHits E (gaussCellCenter h (index i)) h*h^3) := by
    calc
      _ = ∑ i, (24*C*D^4)*(32*(h^3/‖y-G (gaussCellCenter h (index i))‖^5)+
          cellHits E (gaussCellCenter h (index i)) h*h^3) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hs]
  ring

end ContinuumCoulomb

end

end OAI
