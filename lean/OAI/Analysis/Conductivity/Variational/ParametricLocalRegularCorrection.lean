import Mathlib
import OAI.Analysis.Conductivity.Geometry.MatrixPerturbInverse
import OAI.Analysis.Conductivity.Variational.QuantitativePhysicalMoments
import OAI.Analysis.Conductivity.Variational.ParametricSpatialDerivative
import OAI.Analysis.Conductivity.Sobolev.UniformLocalPhysicalCorrection

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

lemma exists_open_product_inside {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]
    {O : Set (P×E)} (hO : IsOpen O) {p : P} {x : E} (hx : (p,x)∈O) :
    ∃ V W,IsOpen V ∧ IsOpen W ∧ p∈V ∧ x∈W ∧ V×ˢW⊆O := by
  obtain ⟨V,W,hV,hW,hp,hx',hs⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p)) (isCompact_singleton (x := x)) hO
    (show ({p} : Set P)×ˢ{ x }⊆O from by
      rintro ⟨q,y⟩ ⟨hq,hy⟩
      rcases hq with rfl
      rcases hy with rfl
      exact hx)
  exact ⟨V,W,hV,hW,hp (mem_singleton p),hx' (mem_singleton x),hs⟩

lemma BoundedPhysicallyCorrectable.region_mono
    {u : Coord3 → Fin 2 → ℝ} {U V : Set Coord3} {r : PhysicalSourcePair} {N : ℝ}
    (h : BoundedPhysicallyCorrectable u U r N) (hUV : U⊆V) :
    BoundedPhysicallyCorrectable u V r N := by
  obtain ⟨H,hH,hc,hs,hsy,hr,hb⟩ := h
  exact ⟨H,hH,hc,hs.trans hUV,hsy,hr,hb⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_uniform_local_regular_correction
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (p : P) {x : Coord3} (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    ∃ V : Set P,∃ W : Set Coord3,∃ L : ℝ,
      IsOpen V ∧ p∈V ∧ IsOpen W ∧ x∈W ∧ W⊆U ∧ Bornology.IsBounded W ∧ 0<L ∧
      ∀ q∈V,∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r W →
        physicalSourceMoment (fun y => u (q,y)) r=0 → ∀ M : ℝ,0≤M →
        (∀ j,UniformC1Bound (r j) M) →
        BoundedPhysicallyCorrectable (fun y => u (q,y)) U r (L*M) := by
  obtain ⟨Y,hpY,hYU,hY,hpot,hsm,hinv⟩ := exists_parametric_potential_coordinates hu p x hD
    (isOpen_univ.prod hU) ⟨mem_univ p,hx⟩
  let z := (Y (p,x)).2
  have hpz : (p,z)∈Y.target := by
    have he : (p,z)=Y (p,x) := Prod.ext (hY p x).symm rfl
    rw [he]
    exact Y.map_source hpY
  obtain ⟨V₀,W₀,hV₀,hW₀,hp₀,hz₀,hprod₀⟩ := exists_open_product_inside Y.open_target hpz
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hW₀ z hz₀
  let a : Coord3 := fun i => z i-ε/3
  let b : Coord3 := fun i => z i+ε/3
  let c : Coord3 := fun i => z i-2*ε/3
  let d : Coord3 := fun i => z i+2*ε/3
  have hc : closedCorrectionBox c d⊆W₀ := by
    intro y hy
    apply hball
    rw [Metric.mem_ball,dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq,abs_lt]
    have hi : c i≤y i ∧ y i≤d i := by
      fin_cases i
      · exact hy.1.1
      · exact hy.1.2
      · exact hy.2
    dsimp [c,d] at hi
    constructor <;> linarith
  have hab : ∀ i,a i<b i := fun i => by dsimp [a,b]; linarith
  have hca : ∀ i,c i<a i := fun i => by dsimp [c,a]; linarith
  have hbd : ∀ i,b i<d i := fun i => by dsimp [b,d]; linarith
  obtain ⟨δ,hδ,hδball⟩ := Metric.isOpen_iff.mp hV₀ p hp₀
  let Kp := Metric.closedBall p (δ/2)
  have hKp : IsCompact Kp := isCompact_closedBall _ _
  have hpK : Kp⊆V₀ := fun q hq => hδball
    (lt_of_le_of_lt hq (by linarith : δ/2<δ))
  have hjoint : Kp×ˢclosedCorrectionBox c d⊆Y.target :=
    fun q hq => hprod₀ ⟨hpK hq.1,hc hq.2⟩
  obtain ⟨B,hB,hbound⟩ := parametric_chart_compact_bounds Y hY hsm hinv
    (hKp.prod (closedCorrectionBox_compact c d)) hjoint
  let O : Set (P×Coord3) := Y.source∩{q | (Y q).2∈correctionBox a b}
  have hO : IsOpen O := Y.open_source.inter
    ((correctionBox_isOpen a b).preimage (continuous_snd.comp hsm.continuous))
  have hpxO : (p,x)∈O := ⟨hpY,mem_correctionBox.mpr (fun i => by dsimp [a,b,z]; constructor <;> linarith)⟩
  obtain ⟨V₁,W₁,hV₁,hW₁,hp₁,hx₁,hprod₁⟩ := exists_open_product_inside hO hpxO
  let V := Metric.ball p (δ/2)∩V₁
  let W := W₁∩Metric.ball x 1
  have hVp : p∈V := ⟨Metric.mem_ball_self (by positivity),hp₁⟩
  have hWx : x∈W := ⟨hx₁,Metric.mem_ball_self zero_lt_one⟩
  have hWU : W⊆U := fun y hy => (hYU (hprod₁ (show (p,y)∈V₁×ˢW₁ from ⟨hp₁,hy.1⟩)).1).2
  let Xs : V → OpenPartialHomeomorph Coord3 Coord3 := fun q => (fiberSlice Y hY q.1).symm
  have hXs (q : V) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs q) (Xs q).source :=
    (fiberSlice_smooth Y hY hsm hinv q.1).2
  have hXis (q : V) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs q).symm (Xs q).target :=
    (fiberSlice_smooth Y hY hsm hinv q.1).1.contDiffOn
  have hboxes (q : V) : closedCorrectionBox c d⊆(Xs q).source :=
    fun y hy => hjoint ⟨Metric.ball_subset_closedBall q.2.1,hy⟩
  let us : V → Coord3 → Fin 2 → ℝ := fun q y => u (q.1,y)
  have hus (q : V) : ContDiff ℝ (↑(⊤:ℕ∞)) (us q) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hpot' (q : V) : EqOn (us q) (coordinatePair∘(Xs q).symm) (Xs q).target :=
    fun y _ => (hpot q.1 y).symm
  obtain ⟨L,hL,solve⟩ := uniform_local_physical_symmetric_correction_C0 Xs hXs hXis hab hca hbd hboxes hB
    (fun q y hy => hbound (q.1,y) ⟨Metric.ball_subset_closedBall q.2.1,hy⟩) us hus hpot'
  refine ⟨V,W,L,Metric.isOpen_ball.inter hV₁,hVp,hW₁.inter Metric.isOpen_ball,hWx,hWU,
    Metric.isBounded_ball.subset inter_subset_right,hL,?_⟩
  intro q hq r hr hs hm M hM hb
  let i : V := ⟨q,hq⟩
  have hWbox : W⊆(Xs i) '' correctionBox a b := by
    intro y hy
    have hh := hprod₁ (show (q,y)∈V₁×ˢW₁ from ⟨hq.2,hy.1⟩)
    refine ⟨(Y (q,y)).2,hh.2,?_⟩
    exact (fiberSlice Y hY q).left_inv hh.1
  have hXt : (Xs i).target⊆U := fun y hy => (hYU hy).2
  exact (solve i r hr (fun j => (hs j).trans hWbox) hm M hM hb).region_mono hXt

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma physicalSourceMoment_parametric_continuous
    {u : P×Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) :
    Continuous (fun p => physicalSourceMoment (fun x => u (p,x)) r) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_const
  · let K := tsupport (r 0)∪tsupport (r 1)
    have hK : IsCompact K := (hr 0).2.isCompact.union (hr 1).2.isCompact
    have hcont : Continuous (fun q : P×Coord3 => u q 1*r 0 q.2-u q 0*r 1 q.2) :=
      ((continuous_apply 1|>.comp hu).mul ((hr 0).1.continuous.comp continuous_snd)).sub
        ((continuous_apply 0|>.comp hu).mul ((hr 1).1.continuous.comp continuous_snd))
    have he (p : P) : physicalSourceMoment (fun x => u (p,x)) r 2=
        ∫ x in K,u (p,x) 1*r 0 x-u (p,x) 0*r 1 x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have h0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
      have h1 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
      simp [h0,h1]
    change Continuous (fun p => physicalSourceMoment (fun x => u (p,x)) r 2)
    simp_rw [he]
    exact continuous_parametric_integral_of_continuous hcont hK

theorem parametric_bounded_physical_moments
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {U O : Set Coord3} (hO : IsOpen O) (hne : O.Nonempty) (hOU : O⊆U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) :
    ∃ (Q : P → Coord3 → PhysicalSourcePair) (L : ℝ),0<L ∧
      (∀ q m,CompactSmoothPair (Q q m)) ∧ (∀ q m,PairSupported (Q q m) O) ∧
      ∀ᶠ q in 𝓝 p, (∀ m,physicalSourceMoment (fun x => u (q,x)) (Q q m)=m) ∧
        ∀ m j,UniformC1Bound (Q q m j) (L*‖m‖) := by
  classical
  have hup : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (p,x)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  choose g hg hs hm using fun i : Fin 3 =>
    exists_physical_moments_in_open hup hO hne hOU hD (Pi.single i 1)
  let A : P → Matrix (Fin 3) (Fin 3) ℝ := fun q i j =>
    physicalSourceMoment (fun x => u (q,x)) (g j) i
  have hA : Continuous A := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (physicalSourceMoment_parametric_continuous hu.continuous (hg j))
  have hAp : A p=1 := by
    ext i j
    simp [A,hm,Pi.single_apply,Matrix.one_apply]
  obtain ⟨C,hC,hnear⟩ := matrix_inverse_locally_bounded hA.continuousAt
    (show IsUnit (A p) by rw [hAp]; exact isUnit_one)
  let Q : P → Coord3 → PhysicalSourcePair := fun q m => ∑ i,((A q)⁻¹*ᵥm) i • g i
  have hQ (q m) : CompactSmoothPair (Q q m) :=
    CompactSmoothPair.sum _ _ (fun i _ => (hg i).smul _)
  have hQs (q m) : PairSupported (Q q m) O :=
    PairSupported.sum _ _ (fun i _ => (hs i).smul _)
  choose B hB hb using fun j : Fin 2 => fun n : Fin 2 =>
    fixed_smooth_tests_bound (fun i : Fin 3 => g i j) (fun i => (hg i j).1) (fun i => (hg i j).2) n.val
  let D := ∑ j : Fin 2,∑ n : Fin 2,B j n
  have hDpos : 0<D := Finset.sum_pos (fun j _ => Finset.sum_pos (fun n _ => hB j n) Finset.univ_nonempty)
    Finset.univ_nonempty
  have hBD (j n) : B j n≤D :=
    (Finset.single_le_sum (fun k _ => (hB j k).le) (Finset.mem_univ n)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => (hB k l).le)) (Finset.mem_univ j))
  refine ⟨Q,D*C,mul_pos hDpos hC,hQ,hQs,?_⟩
  filter_upwards [hnear] with q hq
  constructor
  · intro m
    have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (q,x)) :=
      hu.comp (contDiff_const.prodMk contDiff_id)
    change physicalSourceMoment (fun x => u (q,x)) (∑ i,((A q)⁻¹*ᵥm) i • g i)=m
    rw [physicalSourceMoment_sum _ _ huq.continuous (fun i _ => (hg i).smul _)]
    simp_rw [physicalSourceMoment_smul]
    have he := (hq.2 m).1
    ext i
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm,Matrix.mulVec,dotProduct,A] using congrFun he i
  · intro m j x
    have hcoef := (hq.2 m).2
    have h0 := hb j 0 ((A q)⁻¹*ᵥm) (C*‖m‖) (mul_nonneg hC.le (norm_nonneg _)) hcoef x
    have h1 := hb j 1 ((A q)⁻¹*ᵥm) (C*‖m‖) (mul_nonneg hC.le (norm_nonneg _)) hcoef x
    simp only [Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h0
    simp only [Fin.val_one,norm_iteratedFDeriv_one] at h1
    have he : Q q m j=(fun x => ∑ i,((A q)⁻¹*ᵥm) i • g i j x) := by
      funext x; simp [Q,Finset.sum_apply]
    rw [he]
    have hmul (n) : B j n*(C*‖m‖)≤(D*C)*‖m‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hBD j n) (mul_nonneg hC.le (norm_nonneg _))
    exact ⟨h0.trans (hmul 0),h1.trans (hmul 1)⟩

end ScalarConductivity

end
end

end OAI
