import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedFarGrid
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedNearGrid

namespace OAI

/-! Pointwise nuclear replacement on any finite grid: the smooth error is
quadratic in the mesh, and the only singular remainder is an explicit sum of
near-node kernels, suitable for the proved weak-H1 estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb

theorem gaussLatticePoint_mem_cube (h : ℝ) (hh : 0 ≤ h)
    (k : Fin 3 → ℤ) (v : Fin 3 → Fin 2) :
    gaussLatticePoint h (k,v) ∈ positionCube (gaussCellCenter h k) h := by
  rw [← cubePoint_gaussLatticePoint]
  have hb (i : Fin 3) : gaussNode (v i) ∈ Set.Icc (-1:ℝ) 1 := by
    have hg := gaussNode_bounds (v i)
    have ha := gaussAbscissa_bounds
    constructor <;> linarith
  exact cubePoint_mem_positionCube _ hh (hb 0) (hb 1) (hb 2)

theorem near_cell_gauss_truncated {h : ℝ} (hh : 0 < h)
    (G : Position → Position) {L : ℝ≥0} (hL : 0 < L) (hG : LipschitzWith L G)
    (y : Position) (k : Fin 3 → ℤ)
    (hnear : ‖y-G (gaussCellCenter h k)‖ ≤ 4*(L:ℝ)*h) :
    positionCellGauss (gaussCellCenter h k) h (fun x => Coulomb.coulombKernel (y-G x)) =
      (h^3/8)*∑ v : Fin 3 → Fin 2,
        Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G (gaussLatticePoint h (k,v))) := by
  rw [gaussCell_quadrature_lattice]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact transported_near_kernel_eq hh G hL hG hnear (gaussLatticePoint_mem_cube h hh.le k v)

theorem manufactured_moser_grid_error (hpublished : PublishedC4FlowInput) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (rho H S freq scale : ℝ) (m : ℕ) (u : Fin m → PlanarPosition),
      0 < rho → 0 ≤ H → 1 ≤ S →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ rho/2) →
      tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ (G : Position → ℝ → Position),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
      Function.Bijective (fun x => G x 1) →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k) →
      ∀ (L : ℝ≥0), 0 < L → LipschitzWith L (fun x => G x 1) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (y : Position) (h : ℝ), 0 < h → h ≤ 1 →
      (∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S) →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => Coulomb.coulombKernel (y-G x 1)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => Coulomb.coulombKernel (y-G x 1)))| ≤
        24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+108*Real.pi*(L:ℝ)^2*h^2+
        (h^3/8)*∑ i, ∑ v : Fin 3 → Fin 2,
          Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G (gaussLatticePoint h (index i,v)) 1) := by
  obtain ⟨C,hC,hfar⟩ := manufactured_moser_far_grid_error hpublished
  refine ⟨C,hC,?_⟩
  intro rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD L hL hLip
    ι _ index hindex y h hh hh1 hsub
  let V := manufacturedWellField freq scale S u
  let p : ι → Prop := fun i => 4*(L:ℝ)*h ≤ ‖y-G (gaussCellCenter h (index i)) 1‖
  let Q : ι → ℝ := fun i => positionCellGauss (gaussCellCenter h (index i)) h
    (fun x => Coulomb.coulombKernel (y-G x 1))
  let I : ι → ℝ := fun i => positionCellIntegral (gaussCellCenter h (index i)) h
    (fun x => Coulomb.coulombKernel (y-G x 1))
  let T : ι → ℝ := fun i => ∑ v : Fin 3 → Fin 2,
    Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G (gaussLatticePoint h (index i,v)) 1)
  have hfi : Function.Injective (fun i : {i // p i} => index i.val) :=
    fun i j hij => Subtype.ext (hindex hij)
  have hni : Function.Injective (fun i : {i // ¬p i} => index i.val) :=
    fun i j hij => Subtype.ext (hindex hij)
  have hn (i : {i // ¬p i}) : ‖y-G (gaussCellCenter h (index i.val)) 1‖ ≤ 4*(L:ℝ)*h :=
    (lt_of_not_ge i.property).le
  have hf := hfar rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD
    L hL hLip (fun i : {i // p i} => index i.val) hfi y h hh hh1
    (fun i => hsub i.val) (fun i => i.property)
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 freq scale S u).of_le (by norm_num)
  have hnear := moser_near_grid_integral_bound hpublished hrho hH (by linarith) V hV hcharge hsupp
    G hflow hbij hfix hL hLip (fun i : {i // ¬p i} => index i.val) hni hh
    (fun i => hsub i.val) y hn
  have hQn : (∑ i : {i // ¬p i}, Q i.val) ≤ (h^3/8)*∑ i, T i := by
    calc
      _ = (h^3/8)*∑ i : {i // ¬p i}, T i.val := by
        simp only [Q,T,near_cell_gauss_truncated hh (fun x => G x 1) hL hLip y _ (hn _),
          Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have he := Fintype.sum_subtype_add_sum_subtype p T
        have hp : 0 ≤ ∑ i : {i // p i}, T i.val :=
          Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
            (fun v _ => Coulomb.truncatedCoulomb_nonneg _ _))
        linarith
  have hIp : 0 ≤ ∑ i : {i // ¬p i}, I i.val := by
    apply Finset.sum_nonneg
    intro i _
    have hi := moser_coulomb_integrableOn hpublished hrho hH (by linarith) V hV hcharge hsupp
      G hflow hbij hfix y
    rw [show I i.val = ∫ x in positionCube (gaussCellCenter h (index i.val)) h,
        Coulomb.coulombKernel (y-G x 1) from
      positionCellIntegral_eq_setIntegral _ hh.le _ (hi.mono_set (hsub i.val))]
    exact setIntegral_nonneg (positionCube_isClosed _ _).measurableSet
      (fun x _ => Coulomb.coulombKernel_nonneg _)
  have hQp : 0 ≤ ∑ i : {i // ¬p i}, Q i.val := by
    apply Finset.sum_nonneg
    intro i _
    rw [show Q i.val = (h^3/8)*T i.val from
      near_cell_gauss_truncated hh (fun x => G x 1) hL hLip y _ (hn i)]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg
      (fun v _ => Coulomb.truncatedCoulomb_nonneg _ _))
  have heQ := Fintype.sum_subtype_add_sum_subtype p Q
  have heI := Fintype.sum_subtype_add_sum_subtype p I
  change |(∑ i, Q i)-(∑ i, I i)| ≤ _
  rw [← heQ,← heI]
  calc
    _ = |((∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val))+
        ((∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val))| := by congr 1; ring
    _ ≤ |(∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val)|+
        |(∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val)| := abs_add_le _ _
    _ ≤ _ := by
      have hnabs := abs_add_le (∑ i : {i // ¬p i}, Q i.val) (-(∑ i : {i // ¬p i}, I i.val))
      simp only [← sub_eq_add_neg,abs_neg,abs_of_nonneg hQp,abs_of_nonneg hIp] at hnabs
      change |(∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val)| ≤ _ at hf
      change (∑ i : {i // ¬p i}, I i.val) ≤ _ at hnear
      change _ ≤ _ + _ + (h^3/8)*∑ i, T i
      linarith

end ContinuumCoulomb

end

end OAI
