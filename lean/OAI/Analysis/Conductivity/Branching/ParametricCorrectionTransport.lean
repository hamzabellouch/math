import Mathlib
import OAI.Analysis.Conductivity.Variational.ParametricLocalRegularCorrection

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma parametric_physical_source_moment_bound
    {u : P×Coord3 → Fin 2 → ℝ} (hu : Continuous u) (p : P) {V : Set Coord3}
    (hV : Bornology.IsBounded V) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ q in 𝓝 p,∀ r : PhysicalSourcePair,PairSupported r V →
      ∀ M : ℝ,0≤M → (∀ j x,|r j x|≤M) →
      ‖physicalSourceMoment (fun x => u (q,x)) r‖≤L*M := by
  let K := closure V
  have hK : IsCompact K := hV.isCompact_closure
  obtain ⟨B,hB⟩ := ((isCompact_closedBall p 1).prod hK).exists_bound_of_continuousOn hu.continuousOn
  let A := |B|+1
  let W := volume.real K
  have hA : 0<A := by dsimp [A]; positivity
  have hW : 0≤W := ENNReal.toReal_nonneg
  refine ⟨(1+2*A)*(W+1),by positivity,?_⟩
  filter_upwards [Metric.ball_mem_nhds p zero_lt_one] with q hq
  intro r hs M hM hb
  have huB (x) (hx : x∈K) (j : Fin 2) : |u (q,x) j|≤A :=
    (norm_le_pi_norm (u (q,x)) j).trans
      ((hB (q,x) ⟨Metric.ball_subset_closedBall hq,hx⟩).trans (by dsimp [A]; linarith [le_abs_self B]))
  have hrK (j) : tsupport (r j)⊆K := (hs j).trans subset_closure
  have hi (j) : |∫ x,r j x|≤M*W :=
    integral_bound_on_compact hK ((subset_tsupport _).trans (hrK j)) (fun x _ => hb j x)
  have htK : Function.support (fun x => u (q,x) 1*r 0 x-u (q,x) 0*r 1 x)⊆K := by
    intro x hx
    by_contra hn
    have h0 := image_eq_zero_of_notMem_tsupport (fun h => hn (hrK 0 h))
    have h1 := image_eq_zero_of_notMem_tsupport (fun h => hn (hrK 1 h))
    exact hx (by simp [h0,h1])
  have ht : |∫ x,u (q,x) 1*r 0 x-u (q,x) 0*r 1 x|≤(2*A*M)*W := by
    apply integral_bound_on_compact hK htK
    intro x hx
    calc
      _ ≤ |u (q,x) 1*r 0 x|+|u (q,x) 0*r 1 x| := abs_sub _ _
      _ ≤ A*M+A*M := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul (huB x hx 1) (hb 0 x) (abs_nonneg _) hA.le)
          (mul_le_mul (huB x hx 0) (hb 1 x) (abs_nonneg _) hA.le)
      _ = _ := by ring
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro j
  have hmass : M*W≤((1+2*A)*(W+1))*M := by
    nlinarith [mul_nonneg hM hW,mul_nonneg hA.le (mul_nonneg hM hW),mul_nonneg hA.le hM]
  have htorque : (2*A*M)*W≤((1+2*A)*(W+1))*M := by
    nlinarith [mul_nonneg hM hW,mul_nonneg hA.le hM]
  fin_cases j
  · exact (hi 0).trans hmass
  · exact (hi 1).trans hmass
  · exact ht.trans htorque

structure ParametricCorrectionBox (u : P×Coord3 → Fin 2 → ℝ) (p : P) (U : Set Coord3) where
  region : Set Coord3
  region_open : IsOpen region
  region_nonempty : region.Nonempty
  region_subset : region⊆U
  region_bounded : Bornology.IsBounded region
  bounded_solver : ∃ L : ℝ,0<L ∧ ∀ᶠ q in 𝓝 p,
    ∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r region →
      physicalSourceMoment (fun x => u (q,x)) r=0 → ∀ M : ℝ,0≤M →
      (∀ j,UniformC1Bound (r j) M) →
      BoundedPhysicallyCorrectable (fun x => u (q,x)) U r (L*M)

lemma exists_parametric_correction_box
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {U : Set Coord3} (hU : IsOpen U) {x : Coord3} (hx : x∈U)
    (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) :
    ∃ B : ParametricCorrectionBox u p U,x∈B.region := by
  obtain ⟨V,W,L,hV,hp,hW,hxW,hWU,hWb,hL,solve⟩ :=
    exists_uniform_local_regular_correction hu p hD hU hx
  refine ⟨⟨W,hW,⟨x,hxW⟩,hWU,hWb,L,hL,?_⟩,hxW⟩
  exact Filter.eventually_of_mem (hV.mem_nhds hp) solve

lemma parametric_correction_boxes_cover
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) :
    (⋃ B : ParametricCorrectionBox u p U,B.region)=U := by
  apply Subset.antisymm
  · exact iUnion_subset fun B => B.region_subset
  · intro x hx
    obtain ⟨B,hB⟩ := exists_parametric_correction_box hu p hU hx (hD x hx)
    exact mem_iUnion.mpr ⟨B,hB⟩

lemma ParametricCorrectionBox.bounded_transfer
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    (B C : ParametricCorrectionBox u p U) (hBC : (B.region∩C.region).Nonempty) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ t in 𝓝 p,∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r B.region →
      ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      ∃ q : PhysicalSourcePair,CompactSmoothPair q ∧ PairSupported q C.region ∧
        physicalSourceMoment (fun x => u (t,x)) q=physicalSourceMoment (fun x => u (t,x)) r ∧
        (∀ j,UniformC1Bound (q j) (L*M)) ∧
        BoundedPhysicallyCorrectable (fun x => u (t,x)) U (r-q) (L*M) := by
  obtain ⟨Q,R,hR,hQ,hQs,hQnear⟩ := parametric_bounded_physical_moments hu p
    (B.region_open.inter C.region_open) hBC (inter_subset_left.trans B.region_subset) hD
  obtain ⟨Z,hZ,hZnear⟩ := parametric_physical_source_moment_bound hu.continuous p B.region_bounded
  obtain ⟨D,hDpos,hsolve⟩ := B.bounded_solver
  let L := (D+1)*(1+R*Z)
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  filter_upwards [hQnear,hZnear,hsolve] with t ht hZb solve
  intro r hr hs M hM hb
  let v := fun x => u (t,x)
  have hv : ContDiff ℝ (↑(⊤:ℕ∞)) v := hu.comp (contDiff_const.prodMk contDiff_id)
  let q := Q t (physicalSourceMoment v r)
  have hq : CompactSmoothPair q := hQ _ _
  have hqm : physicalSourceMoment v q=physicalSourceMoment v r := ht.1 _
  have hqb (j) : UniformC1Bound (q j) ((R*Z)*M) := (ht.2 _ j).mono
    ((mul_le_mul_of_nonneg_left (hZb r hs M hM (fun j x => (hb j x).1)) hR.le).trans_eq (by ring))
  have hsmall : (R*Z)*M≤L*M := by
    dsimp [L]
    nlinarith [mul_nonneg hR.le hZ.le,mul_nonneg hDpos.le (mul_nonneg hR.le hZ.le)]
  have hrq : CompactSmoothPair (r-q) := hr.sub hq
  have hsrc : physicalSourceMoment v (r-q)=0 := by
    rw [physicalSourceMoment_sub hv.continuous hr hq,hqm,sub_self]
  have hdif (j) : UniformC1Bound ((r-q) j) ((1+R*Z)*M) := by
    change UniformC1Bound (fun x => r j x-q j x) ((1+R*Z)*M)
    convert (hb j).sub ((hr j).1.differentiable (by simp)) ((hq j).1.differentiable (by simp)) (hqb j) using 1; ring
  have hc := solve (r-q) hrq (hs.sub ((hQs t _).mono inter_subset_left)) hsrc
    ((1+R*Z)*M) (by positivity) hdif
  refine ⟨q,hq,(hQs t _).mono inter_subset_right,hqm,fun j => (hqb j).mono hsmall,hc.mono ?_⟩
  dsimp [L]
  nlinarith [mul_nonneg hR.le hZ.le,mul_nonneg (add_nonneg zero_le_one (mul_nonneg hR.le hZ.le)) hM]

lemma parametric_correction_boxes_chain
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    (B C : ParametricCorrectionBox u p U) :
    Relation.TransGen (fun B C : ParametricCorrectionBox u p U => (B.region∩C.region).Nonempty) B C := by
  have hc : IsPreconnected (⋃ B : ParametricCorrectionBox u p U,B.region) := by
    rwa [parametric_correction_boxes_cover hu p hU hD]
  exact hc.transGen_of_iUnion (fun B => B.region_open) B C B.region_nonempty C.region_nonempty

theorem parametric_controlled_source_transport
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    (B C : ParametricCorrectionBox u p U) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ t in 𝓝 p,∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r B.region →
      ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      ∃ q : PhysicalSourcePair,CompactSmoothPair q ∧ PairSupported q C.region ∧
        physicalSourceMoment (fun x => u (t,x)) q=physicalSourceMoment (fun x => u (t,x)) r ∧
        (∀ j,UniformC1Bound (q j) (L*M)) ∧
        BoundedPhysicallyCorrectable (fun x => u (t,x)) U (r-q) (L*M) := by
  have hp := parametric_correction_boxes_chain hu p hU hUc hD B C
  induction hp with
  | single h => exact B.bounded_transfer hu p hD _ h
  | @tail C D hpath hCD ih =>
    obtain ⟨L,hL,hsolve⟩ := ih
    obtain ⟨R,hR,hstep⟩ := C.bounded_transfer hu p hD D hCD
    refine ⟨L+R*L,by positivity,?_⟩
    filter_upwards [hsolve,hstep] with t solve step
    intro r hr hs M hM hb
    obtain ⟨q,hq,hqs,hqm,hqb,hqc⟩ := solve r hr hs M hM hb
    obtain ⟨s,hss,hssup,hsm,hsb,hsc⟩ := step q hq hqs (L*M) (mul_nonneg hL.le hM) hqb
    refine ⟨s,hss,hssup,hsm.trans hqm,fun j => (hsb j).mono ?_,?_⟩
    · nlinarith [mul_nonneg hL.le hM]
    · have hut : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (t,x)) :=
        hu.comp (contDiff_const.prodMk contDiff_id)
      have he := hqc.add hut hsc
      rw [sub_add_sub_cancel] at he
      exact he.mono (by ring_nf; rfl)

end ScalarConductivity

end

end OAI
