import OAI.Analysis.Steinitz.Adaptive

namespace OAI

/-! Filtered-body energy and the predictor slab budget. -/

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Pointwise NNReal
namespace GaussianEvents
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]
noncomputable def openConstraints (A : I → E →L[ℝ] F) (R : I → ℝ) : Set E :=
  {x | ∀ i,‖A i x‖ < R i}
lemma openConstraints_open (A : I → E →L[ℝ] F) (R : I → ℝ) : IsOpen (openConstraints A R) := by
  simp only [openConstraints,Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (A i).continuous.norm continuous_const
omit [Fintype I] in
lemma openConstraints_convex (A : I → E →L[ℝ] F) (R : I → ℝ) : Convex ℝ (openConstraints A R) := by
  have he : openConstraints A R = ⋂ i,(A i) ⁻¹' Metric.ball 0 (R i) := by
    ext x; simp [openConstraints,Metric.mem_ball,dist_zero_right]
  rw [he]
  exact convex_iInter fun i => (convex_ball (0:F) (R i)).linear_preimage (A i).toLinearMap
omit [Fintype I] in
lemma openConstraints_symmetric (A : I → E →L[ℝ] F) (R : I → ℝ) :
    ∀ x∈openConstraints A R,-x∈openConstraints A R := by
  intro x hx i
  simpa only [map_neg,norm_neg] using hx i
omit [Fintype I] in
lemma openConstraints_zero (A : I → E →L[ℝ] F) {R : I → ℝ} (hR : ∀ i,0<R i) :
    (0:E)∈openConstraints A R := by intro i; simpa only [map_zero,norm_zero] using hR i
end GaussianEvents

namespace EuclideanSteinitz.Filter
open GaussianAR GaussianEvents Coefficient
variable {ι κ T J : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype T] [Fintype J] [Nonempty ι] [Nonempty κ]

noncomputable def bodyRate : ℝ := 2*stateRate+1
lemma bodyRate_nonneg : 0≤bodyRate := by unfold bodyRate; linarith [stateRate_nonneg]
noncomputable def applicationDomain (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) : Set (EuclideanSpace ℝ κ) :=
  openConstraints (fun t => matrixMap (Rt t)) (fun _ => 2*stateRadius*Real.sqrt (Fintype.card ι)) ∩
  Metric.ball 0 (2*stateRadius*Real.sqrt (Fintype.card κ)) ∩
  openConstraints (fun j => matrixMap (H j)) (fun _ => 2*slabRadius)

omit [DecidableEq ι] [Nonempty ι] [Nonempty κ] in
lemma applicationDomain_open (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    IsOpen (applicationDomain Rt H) :=
  ((openConstraints_open _ _).inter Metric.isOpen_ball).inter (openConstraints_open _ _)
omit [DecidableEq ι] [Nonempty ι] [Nonempty κ] [Fintype T] [Fintype J] in
lemma applicationDomain_convex (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    Convex ℝ (applicationDomain Rt H) :=
  ((openConstraints_convex _ _).inter (convex_ball _ _)).inter (openConstraints_convex _ _)
omit [DecidableEq ι] [Fintype T] [Fintype J] [Nonempty ι] [Nonempty κ] in
lemma applicationDomain_bounded (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    Bornology.IsBounded (applicationDomain Rt H) :=
  (Metric.isBounded_ball (x := (0:EuclideanSpace ℝ κ)) (r := _)).subset (fun _ hx => hx.1.2)
omit [DecidableEq ι] [Nonempty ι] [Nonempty κ] [Fintype T] [Fintype J] in
lemma applicationDomain_symmetric (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    ∀ x∈applicationDomain Rt H,-x∈applicationDomain Rt H := by
  intro x hx
  refine ⟨⟨openConstraints_symmetric _ _ x hx.1.1,?_⟩,openConstraints_symmetric _ _ x hx.2⟩
  simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hx.1.2
omit [DecidableEq ι] [Fintype T] [Fintype J] in
lemma applicationDomain_zero (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    (0:EuclideanSpace ℝ κ)∈applicationDomain Rt H := by
  have hι : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hκ : (0:ℝ)<Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨⟨openConstraints_zero _ (fun _ => mul_pos (mul_pos (by norm_num) stateRadius_pos) (Real.sqrt_pos.mpr hι)),?_⟩,openConstraints_zero _ (fun _ => mul_pos (by norm_num) slabRadius_pos)⟩
  simp only [Metric.mem_ball,dist_self]
  exact mul_pos (mul_pos (by norm_num) stateRadius_pos) (Real.sqrt_pos.mpr hκ)

omit [Nonempty κ] in
lemma slabs_rate (H : J → Matrix Unit κ ℝ) (hH : ∀ i,∑ j, (H j () i)^2 ≤ 1)
    {q : κ → ℝ} (hq : ∀ i,0≤q i) :
    (∑ j,weightedSq (H j) (diagonal q)) ≤ ∑ i,q i := by
  simp only [weighted_diagonal_eq,Fintype.sum_unique]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hH i) (hq i)

lemma applicationDomain_survival {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (ps : T → List (Step ι κ)) (hps : ∀ t,ps t <+: L)
    (H : J → Matrix Unit κ ℝ) (hH : ∀ j,squareMass (H j)≤1) (hcol : ∀ i,∑ j,(H j () i)^2≤1)
    {q : κ → ℝ} (hq : ∀ i,0<q i) :
    ∃ a : ℝ,∀ n : ℕ,Real.exp (-a-bodyRate*(∑ i,q i)*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×κ))).real
        {x | ∀ u : Fin (n+1),matrixMap (evaluation (fun i => (1+q i)⁻¹) n u) x ∈
          applicationDomain (fun t => run R (ps t)) H} := by
  let r : κ → ℝ := fun i => (1+q i)⁻¹
  have hr i : 0≤r i := inv_nonneg.mpr (by linarith [hq i])
  have hr1 i : r i≤1 := (inv_le_one₀ (by linarith [hq i])).mpr (by linarith [hq i])
  have hrq i : 1-r i≤q i := by
    dsimp [r]
    have hh : 1-q i≤1/(1+q i) := (le_div_iff₀ (by linarith [hq i])).mpr (by nlinarith [sq_nonneg (q i)])
    rw [one_div] at hh
    linarith
  obtain ⟨a,ha⟩ := state_survival hR hp hf hd ps hps hq r hr hr1 hrq
  obtain ⟨b,hb⟩ := state_survival (ι := κ) (R := 1) (by simp) (L := []) (by simp)
    (by simp [Fresh]) (by simp) (fun _ : Unit => []) (by simp) hq r hr hr1 hrq
  let w := ∑ j,weightedSq (H j) (diagonal q)
  have hw : w≤∑ i,q i := slabs_rate H hcol (fun i => (hq i).le)
  refine ⟨a+b+Fintype.card J,fun n => ?_⟩
  let A := constraints (fun p : T×Fin (n+1) => matrixMap (run R (ps p.1)*evaluation r n p.2))
    (fun _ => stateRadius*Real.sqrt (Fintype.card ι))
  let B := constraints (fun u : Fin (n+1) => matrixMap (evaluation r n u))
    (fun _ => stateRadius*Real.sqrt (Fintype.card κ))
  let C := constraints (fun p : J×Fin (n+1) => matrixMap (H p.1*evaluation r n p.2)) (fun _ => slabRadius)
  have hpa : Real.exp (-a-stateRate*(∑ i,q i)*n)≤(stdGaussian _).real A := by
    simpa only [A,constraints,Prod.forall] using ha n
  have hpb : Real.exp (-b-stateRate*(∑ i,q i)*n)≤(stdGaussian _).real B := by
    simpa only [B,constraints,run,Matrix.one_mul,forall_const] using hb n
  have hpc : Real.exp (-(Fintype.card J:ℝ)-w*n)≤(stdGaussian _).real C := by
    simpa only [C,constraints,Prod.forall,w] using slabs_survival H hH r hr hr1 q (fun i => (hq i).le) hrq n
  have hab := GaussianCorrelation.stdGaussian_closed_convex_correlation
    (constraints_closed _ _) (constraints_closed _ _) (constraints_convex _ _) (constraints_convex _ _)
    (constraints_symmetric _ _) (constraints_symmetric _ _) (K := A) (L := B)
  have habc := GaussianCorrelation.stdGaussian_closed_convex_correlation
    ((constraints_closed _ _).inter (constraints_closed _ _)) (constraints_closed _ _)
    ((constraints_convex _ _).inter (constraints_convex _ _)) (constraints_convex _ _)
    (fun x hx => ⟨constraints_symmetric _ _ x hx.1,constraints_symmetric _ _ x hx.2⟩)
    (constraints_symmetric _ _) (K := A∩B) (L := C)
  have hlow : Real.exp (-(a+b+Fintype.card J)-bodyRate*(∑ i,q i)*n) ≤
      Real.exp (-a-stateRate*(∑ i,q i)*n)*Real.exp (-b-stateRate*(∑ i,q i)*n)*Real.exp (-(Fintype.card J:ℝ)-w*n) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold bodyRate
    nlinarith [mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg n : (0:ℝ)≤n)]
  apply hlow.trans
  apply le_trans (mul_le_mul (mul_le_mul hpa hpb (Real.exp_pos _).le (measureReal_nonneg)) hpc (Real.exp_pos _).le (mul_nonneg measureReal_nonneg measureReal_nonneg))
  apply le_trans (mul_le_mul_of_nonneg_right hab measureReal_nonneg)
  apply habc.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx u
  have hι : 0<stateRadius*Real.sqrt (Fintype.card ι) := mul_pos stateRadius_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  have hκ : 0<stateRadius*Real.sqrt (Fintype.card κ) := mul_pos stateRadius_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro t
    have hh := hx.1.1 (t,u)
    change ‖matrixMap (run R (ps t)*evaluation r n u) x‖≤_ at hh
    rw [matrixMap_mul_apply] at hh
    change ‖matrixMap (run R (ps t)) (matrixMap (evaluation r n u) x)‖< _
    linarith
  · have hh := hx.1.2 u
    change ‖matrixMap (evaluation r n u) x‖≤_ at hh
    simp only [Metric.mem_ball,dist_zero_right]
    linarith
  · intro j
    have hh := hx.2 (j,u)
    change ‖matrixMap (H j*evaluation r n u) x‖≤_ at hh
    rw [matrixMap_mul_apply] at hh
    change ‖matrixMap (H j) (matrixMap (evaluation r n u) x)‖< _
    linarith [slabRadius_pos]

noncomputable def bodyScale : ℝ := 1000*(2*bodyRate+1)
lemma bodyScale_pos : 0 < bodyScale := by unfold bodyScale; linarith [bodyRate_nonneg]
lemma bodyScale_ge_one : 1 ≤ bodyScale := by unfold bodyScale; linarith [bodyRate_nonneg]
lemma bodyScale_bound : (2*bodyRate+1)/bodyScale^2 ≤ 1/10000 := by
  apply (div_le_iff₀ (sq_pos_of_pos bodyScale_pos)).mpr
  unfold bodyScale
  nlinarith [bodyRate_nonneg,sq_nonneg bodyRate]

lemma applicationDomain_good {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (ps : T → List (Step ι κ)) (hps : ∀ t,ps t <+: L)
    (H : J → Matrix Unit κ ℝ) (hH : ∀ j,squareMass (H j)≤1) (hcol : ∀ i,∑ j,(H j () i)^2≤1) :
    ShiftedSections.Good (bodyScale • applicationDomain (fun t => run R (ps t)) H) := by
  let D := applicationDomain (fun t => run R (ps t)) H
  let s : ℝ≥0 := ⟨bodyScale,bodyScale_pos.le⟩
  have ho := applicationDomain_open (fun t => run R (ps t)) H
  have hb := applicationDomain_bounded (fun t => run R (ps t)) H
  have hso := ho.smul₀ bodyScale_pos.ne'
  have hsb := hb.smul₀ bodyScale
  let : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict ((s:ℝ) • D)) := isFiniteMeasure_restrict.mpr hsb.measure_lt_top.ne
  refine ⟨?_,hso,hsb,(applicationDomain_convex _ _).smul bodyScale,?_,?_⟩
  · exact ⟨0,Set.mem_smul_set.mpr ⟨0,applicationDomain_zero _ _,smul_zero _⟩⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Set.mem_smul_set.mp hx
    exact Set.mem_smul_set.mpr ⟨-y,applicationDomain_symmetric _ _ y hy,smul_neg _ _⟩
  · have hh := dilated_bound_of_survival (s := s) bodyScale_pos D
      ho.measurableSet hso.measurableSet bodyRate
      (fun q hq => applicationDomain_survival hR hp hf hd ps hps H hH hcol hq)
    exact hh.mono_const bodyScale_bound

end EuclideanSteinitz.Filter

end

end OAI
