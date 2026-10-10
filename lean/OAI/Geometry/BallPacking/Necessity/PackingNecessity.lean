import Mathlib
import OAI.Geometry.BallPacking.Necessity.DensityExistence

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap _root_.OAI.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking
section
open Rigidity

theorem normalized_two_ball_obstruction (n : ℕ) (hn : 3 ≤ n)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hp : HasPacking n 2 1 ![a,b]) : a+b ≤ 1 := by
  obtain ⟨J,p,q,hJs,hJ,hJc,hJinside,hpq,harea⟩ := packing_two_line_reduction ha hb hp
  obtain ⟨u,hu⟩ := actual_affine_line_exists n hn J hJs hJ hJc hJinside p q hpq
  exact harea u hu

end

 

 

 

open scoped ENNReal NNReal Topology ContDiff Pointwise
open Set MeasureTheory
namespace Rigidity

private def symplecticBilin (n : ℕ) : LinearMap.BilinForm ℝ (Phase n) where
  toFun u :=
    { toFun := standardForm u
      map_add' := by
        intro v w
        simp only [standardForm, Pi.add_apply, Complex.add_re, Complex.add_im]
        simp only [mul_add, ← Finset.sum_add_distrib]
        congr 1
        funext i
        ring
      map_smul' := by
        intro c v
        simp [standardForm, Finset.mul_sum, mul_sub, mul_left_comm] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change standardForm (u + v) w = standardForm u w + standardForm v w
    simp only [standardForm, Pi.add_apply, Complex.add_re, Complex.add_im]
    simp only [add_mul, ← Finset.sum_add_distrib]
    congr 1
    funext i
    ring
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    change standardForm (c • u) v = c * standardForm u v
    simp [standardForm, Finset.mul_sum, mul_sub, mul_assoc]

private theorem symplecticBilin_nondegenerate (n : ℕ) :
    (symplecticBilin n).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro v hv
  by_contra hn
  have hp := standardForm_J_pos hn
  have he := hv (standardJ n v)
  change standardForm v (standardJ n v) = 0 at he
  linarith

 

theorem abs_det_of_standardForm {n : ℕ} (L : Phase n →L[ℝ] Phase n)
    (hL : ∀u v, standardForm (L u) (L v) = standardForm u v) :
    |L.det| = 1 := by
  let b := Module.Free.chooseBasis ℝ (Phase n)
  have hB : (symplecticBilin n).comp L.toLinearMap L.toLinearMap = symplecticBilin n := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    exact hL u v
  have hdet := congrArg Matrix.det
    (LinearMap.BilinForm.toMatrix_comp b b (symplecticBilin n) L.toLinearMap L.toLinearMap)
  rw [hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix] at hdet
  have hn := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    (symplecticBilin_nondegenerate n)
  have hs : L.det ^ 2 = 1 := by
    change (L.toLinearMap.det) ^ 2 = 1
    apply mul_right_cancel₀ hn
    nlinarith [hdet]
  nlinarith [sq_abs L.det, abs_nonneg L.det]

 
theorem symplecticOn_volume_closedBall {n : ℕ} {r : ℝ}
    {U : Set (Phase n)} {f : Phase n → Phase n}
    (hf : SymplecticOn U f) (hU : closedBall n r ⊆ U) :
    volume (f '' closedBall n r) = volume (closedBall n r) := by
  have hd : ∀ x ∈ closedBall n r, HasFDerivWithinAt f (fderiv ℝ f x)
      (closedBall n r) x := by
    intro x hx
    exact ((hf.2.1.contDiffAt (hf.1.mem_nhds (hU hx))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hi : InjOn f (closedBall n r) := by
    intro x hx y hy hxy
    have he := hf.2.2.1.injective (a₁ := ⟨x, hU hx⟩) (a₂ := ⟨y, hU hy⟩) hxy
    exact congrArg Subtype.val he
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume
    (closedBall_isClosed n r).measurableSet hd hi]
  calc
    (∫⁻ x in closedBall n r, ENNReal.ofReal |(fderiv ℝ f x).det|) =
        ∫⁻ _ in closedBall n r, (1 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun (closedBall_isClosed n r).measurableSet
      intro x hx
      change ENNReal.ofReal |(fderiv ℝ f x).det| = 1
      rw [abs_det_of_standardForm _ (hf.2.2.2 x (hU hx)), ENNReal.ofReal_one]
    _ = volume (closedBall n r) := by simp

private theorem capacity_real_smul {n : ℕ} (c : ℝ) (z : Phase n) :
    capacity (c • z) = c ^ 2 * capacity z := by
  rw [show c • z = (c : ℂ) • z by ext i; simp]
  rw [capacity_smul_complex]
  simp [Complex.normSq_ofReal, pow_two]

private theorem closedBall_eq_smul_unit (n : ℕ) {r : ℝ} (hr : 0 < r) :
    closedBall n r = Real.sqrt r • closedBall n 1 := by
  ext z
  constructor
  · intro hz
    refine ⟨(Real.sqrt r)⁻¹ • z, ?_, ?_⟩
    · change capacity ((Real.sqrt r)⁻¹ • z) ≤ 1
      rw [capacity_real_smul, inv_pow, Real.sq_sqrt hr.le]
      change capacity z ≤ r at hz
      exact (inv_mul_le_iff₀ hr).mpr (by simpa using hz)
    · exact smul_inv_smul₀ (ne_of_gt (Real.sqrt_pos.mpr hr)) z
  · rintro ⟨y, hy, rfl⟩
    change capacity (Real.sqrt r • y) ≤ r
    rw [capacity_real_smul, Real.sq_sqrt hr.le]
    change capacity y ≤ 1 at hy
    nlinarith

theorem volume_closedBall_capacity (n : ℕ) {r : ℝ} (hr : 0 < r) :
    volume (closedBall n r) = ENNReal.ofReal (r ^ n) * volume (closedBall n 1) := by
  rw [closedBall_eq_smul_unit n hr,
    Measure.addHaar_smul_of_nonneg volume (Real.sqrt_nonneg r)]
  have hd : Module.finrank ℝ (Phase n) = 2 * n := by
    simp [Phase, Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]
  rw [hd, pow_mul, Real.sq_sqrt hr.le]

private theorem unit_capacity_volume_pos (n : ℕ) : 0 < volume (closedBall n 1) := by
  apply lt_of_lt_of_le ((openBall_isOpen n 1).measure_pos volume ?_)
    (measure_mono (show openBall n 1 ⊆ closedBall n 1 from fun _ hz => (show capacity _ ≤ 1 from le_of_lt hz)))
  exact ⟨0, by simp [openBall, capacity]⟩

 
theorem packing_exists_smaller_capacity {n k : ℕ} (hk : 1 ≤ k)
    {R : ℝ} {r : Fin k → ℝ} (hr : ∀ i, 0 < r i)
    {U : Fin k → Set (Phase n)} {f : Fin k → Phase n → Phase n}
    (hf : ∀ i, closedBall n (r i) ⊆ U i ∧ SymplecticOn (U i) (f i) ∧
      MapsTo (f i) (closedBall n (r i)) (openBall n R)) :
    ∃ σ, 0 < σ ∧ σ < R ∧ (⋃ i, f i '' closedBall n (r i)) ⊆ closedBall n σ := by
  let K := ⋃ i, f i '' closedBall n (r i)
  have hK : IsCompact K := isCompact_iUnion fun i =>
    (closedBall_isCompact n (r i)).image_of_continuousOn
      ((hf i).2.1.2.1.continuousOn.mono (hf i).1)
  have hne : K.Nonempty := by
    let i : Fin k := ⟨0, by omega⟩
    refine ⟨f i 0, mem_iUnion.mpr ⟨i, ⟨0, ?_, rfl⟩⟩⟩
    simp only [closedBall, mem_ofPred_eq, capacity, Pi.zero_apply,
      map_zero, Finset.sum_const_zero, mul_zero]
    exact (hr i).le
  obtain ⟨x, hx, hm⟩ := hK.exists_isMaxOn hne (capacity_smooth n).continuous.continuousOn
  have hxR : capacity x < R := by
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact (hf i).2.2 hy
  have hx0 : 0 ≤ capacity x := mul_nonneg Real.pi_pos.le
    (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
  refine ⟨(capacity x + R) / 2, by linarith, by linarith, ?_⟩
  intro y hy
  have hxy : capacity y ≤ capacity x := hm hy
  change capacity y ≤ (capacity x + R) / 2
  linarith

end Rigidity

 

theorem packing_volume_obstruction (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (R : ℝ) (r : Fin k → ℝ) (_hR : 0 < R) (hr : ∀ i, 0 < r i)
    (hp : HasPacking n k R r) : (∑ i, r i ^ n) < R ^ n := by
  classical
  obtain ⟨U, f, hf, hdisj⟩ := hp
  obtain ⟨σ, hσ, hσR, hsub⟩ := Rigidity.packing_exists_smaller_capacity hk hr hf
  have hmeas : ∀ i, MeasurableSet (f i '' closedBall n (r i)) := by
    intro i
    exact ((Rigidity.closedBall_isCompact n (r i)).image_of_continuousOn
      ((hf i).2.1.2.1.continuousOn.mono (hf i).1)).measurableSet
  have hvol : (∑ i, ENNReal.ofReal (r i ^ n)) * volume (closedBall n 1) ≤
      ENNReal.ofReal (σ ^ n) * volume (closedBall n 1) := by
    calc
      _ = ∑ i, volume (f i '' closedBall n (r i)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Rigidity.symplecticOn_volume_closedBall (hf i).2.1 (hf i).1,
          Rigidity.volume_closedBall_capacity n (hr i)]
      _ = volume (⋃ i, f i '' closedBall n (r i)) := by
        rw [measure_iUnion hdisj hmeas, tsum_fintype]
      _ ≤ volume (closedBall n σ) := measure_mono hsub
      _ = _ := Rigidity.volume_closedBall_capacity n hσ
  have hV0 := ne_of_gt (Rigidity.unit_capacity_volume_pos n)
  have hVtop := (Rigidity.closedBall_isCompact n 1).measure_ne_top (μ := volume)
  rw [mul_comm _ (volume (closedBall n 1)), mul_comm _ (volume (closedBall n 1))] at hvol
  have hsum := (ENNReal.mul_le_mul_iff_right hV0 hVtop).mp hvol
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (hr i).le n)] at hsum
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  simp only [ENNReal.toReal_ofReal (pow_nonneg hσ.le n),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => pow_nonneg (hr i).le n))] at hreal
  exact hreal.trans_lt (pow_lt_pow_left₀ hσR hσ.le (by omega))


 

 

 

open scoped ContDiff Topology
open Set Function
section
namespace Rigidity

def packingDilation (n : ℕ) (c : ℝ) (hc : c≠0) : Phase n ≃L[ℝ] Phase n :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Phase n) (Units.mk0 c hc)

@[simp] theorem packingDilation_apply (n : ℕ) (c : ℝ) (hc : c≠0) (x : Phase n) :
    packingDilation n c hc x=c • x := rfl
@[simp] theorem packingDilation_symm_apply (n : ℕ) (c : ℝ) (hc : c≠0) (x : Phase n) :
    (packingDilation n c hc).symm x=c⁻¹ • x := rfl

theorem capacity_smul_real {n : ℕ} (c : ℝ) (x : Phase n) :
    capacity (c • x)=c^2*capacity x := by
  rw [←Complex.coe_smul,capacity_smul_complex,Complex.normSq_ofReal,pow_two]

theorem standardForm_smul_real_same {n : ℕ} (c : ℝ) (x v : Phase n) :
    standardForm (c • x) (c • v)=c^2*standardForm x v := by
  rw [←Complex.coe_smul,←Complex.coe_smul,standardForm_smul_complex_same,Complex.normSq_ofReal,pow_two]

theorem symplecticOn_dilation {n : ℕ} {U : Set (Phase n)} {f : Phase n → Phase n}
    (hf : SymplecticOn U f) (c : ℝ) (hc : c≠0) :
    SymplecticOn ((packingDilation n c hc) ⁻¹' U)
      (fun x => (packingDilation n c hc).symm (f (packingDilation n c hc x))) := by
  let D := packingDilation n c hc
  have ho : IsOpen (D ⁻¹' U) := hf.1.preimage D.continuous
  refine ⟨ho,?_,?_,?_⟩
  · apply ho.contDiffOn_iff.mpr
    intro x hx
    exact D.symm.contDiff.contDiffAt.comp x
      ((hf.2.1.contDiffAt (hf.1.mem_nhds hx)).comp x D.contDiff.contDiffAt)
  · let e : (D ⁻¹' U) ≃ₜ U := D.toHomeomorph.sets rfl
    exact D.symm.toHomeomorph.isEmbedding.comp (hf.2.2.1.comp e.isEmbedding)
  · intro x hx v w
    have hdf : HasFDerivAt f (fderiv ℝ f (D x)) (D x) :=
      (hf.2.1.contDiffAt (hf.1.mem_nhds hx)).differentiableAt (by simp) |>.hasFDerivAt
    have hd := D.symm.hasFDerivAt.comp x (hdf.comp x D.hasFDerivAt)
    change standardForm (fderiv ℝ (D.symm ∘ f ∘ D) x v) (fderiv ℝ (D.symm ∘ f ∘ D) x w)=standardForm v w
    rw [hd.fderiv]
    change standardForm (c⁻¹ • fderiv ℝ f (D x) (c • v))
      (c⁻¹ • fderiv ℝ f (D x) (c • w))=standardForm v w
    rw [standardForm_smul_real_same,hf.2.2.2 (D x) hx,standardForm_smul_real_same]
    field_simp

end Rigidity
open Rigidity

theorem packing_dilation {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (c : ℝ) (hc : c≠0) :
    HasPacking n k (R/c^2) (fun i => r i/c^2) := by
  obtain ⟨U,f,hf,hd⟩ := hp
  let D := packingDilation n c hc
  have hc2 : 0<c^2 := sq_pos_of_ne_zero hc
  refine ⟨(fun i => D ⁻¹' U i),(fun i x => D.symm (f i (D x))),?_,?_⟩
  · intro i
    have hmem (x : Phase n) (hx : x∈closedBall n (r i/c^2)) : D x∈closedBall n (r i) := by
      change capacity (c • x)≤r i
      rw [capacity_smul_real]
      simpa only [mul_comm] using (le_div_iff₀ hc2).mp hx
    refine ⟨fun x hx => (hf i).1 (hmem x hx),symplecticOn_dilation (hf i).2.1 c hc,?_⟩
    intro x hx
    have hcap := (hf i).2.2 (hmem x hx)
    change capacity (c⁻¹ • f i (D x))<R/c^2
    rw [capacity_smul_real]
    simpa only [inv_pow,div_eq_mul_inv,mul_comm] using mul_lt_mul_of_pos_left hcap (inv_pos.mpr hc2)
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro y ⟨x,hx,rfl⟩ ⟨z,hz,he⟩
    have hx' : D x∈closedBall n (r i) := by
      change capacity (c • x)≤r i
      rw [capacity_smul_real,mul_comm]
      exact (le_div_iff₀ hc2).mp hx
    have hz' : D z∈closedBall n (r j) := by
      change capacity (c • z)≤r j
      rw [capacity_smul_real,mul_comm]
      exact (le_div_iff₀ hc2).mp hz
    exact Set.disjoint_left.mp (hd i j hij) (mem_image_of_mem _ hx')
      ⟨D z,hz',D.symm.injective he⟩

end

 

 

 

open scoped ContDiff Topology
open Set Function
open Rigidity

theorem packing_reindex {n k l : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (e : Fin l → Fin k) (he : Injective e) :
    HasPacking n l R (r ∘ e) := by
  obtain ⟨U,f,hf,hd⟩ := hp
  exact ⟨U ∘ e,f ∘ e,fun i => hf (e i),fun i j hij => hd (e i) (e j) (he.ne hij)⟩

theorem packing_two_of_pair {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (i j : Fin k) (hij : i≠j) :
    HasPacking n 2 R ![r i,r j] := by
  have he : Injective (![i,j] : Fin 2 → Fin k) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have hr : (r ∘ (![i,j] : Fin 2 → Fin k))=![r i,r j] := by
    funext x
    fin_cases x <;> rfl
  simpa only [hr] using packing_reindex hp (![i,j] : Fin 2 → Fin k) he

theorem two_ball_obstruction (n : ℕ) (hn : 3≤n) (R a b : ℝ)
    (hR : 0<R) (ha : 0<a) (hb : 0<b) (hp : HasPacking n 2 R ![a,b]) :
    a+b≤R := by
  have hsq := Real.sq_sqrt hR.le
  have hc : Real.sqrt R≠0 := (Real.sqrt_pos.mpr hR).ne'
  have hp' := packing_dilation hp (Real.sqrt R) hc
  rw [hsq,div_self hR.ne'] at hp'
  have hr : (fun i : Fin 2 => ![a,b] i/R)=![a/R,b/R] := by
    funext i
    fin_cases i <;> rfl
  rw [hr] at hp'
  have h := normalized_two_ball_obstruction n hn (a/R) (b/R) (div_pos ha hR) (div_pos hb hR) hp'
  rw [←add_div] at h
  exact (div_le_one hR).mp h

theorem packing_pair_obstruction (n k : ℕ) (hn : 3≤n) (hk : 1≤k)
    (R : ℝ) (r : Fin k → ℝ) (hr : ∀ i,0<r i) (hp : HasPacking n k R r) :
    ∀ i j, i≠j → r i+r j<R := by
  obtain ⟨U,f,hf,hd⟩ := hp
  obtain ⟨σ,hσ,hσR,hσbound⟩ := packing_exists_smaller_capacity hk hr hf
  let τ : ℝ := (σ+R)/2
  have hστ : σ<τ := by dsimp [τ]; linarith
  have hτR : τ<R := by dsimp [τ]; linarith
  have hτ : 0<τ := hσ.trans hστ
  have hpτ : HasPacking n k τ r := by
    refine ⟨U,f,?_,hd⟩
    intro i
    refine ⟨(hf i).1,(hf i).2.1,?_⟩
    intro x hx
    have hb := hσbound (mem_iUnion.mpr ⟨i,mem_image_of_mem (f i) hx⟩)
    exact hb.trans_lt hστ
  intro i j hij
  exact (two_ball_obstruction n hn τ (r i) (r j) hτ (hr i) (hr j)
    (packing_two_of_pair hpτ i j hij)).trans_lt hτR

 
theorem packing_necessity (n k : ℕ) (hn : 3≤n) (hk : 1≤k)
    (R : ℝ) (r : Fin k → ℝ) (hR : 0<R) (hr : ∀ i,0<r i)
    (hp : HasPacking n k R r) : PackingInequalities n k R r :=
  ⟨packing_volume_obstruction n k hn hk R r hR hr hp,
    packing_pair_obstruction n k hn hk R r hr hp⟩

end HigherDimensionalBallPacking

end

end OAI
