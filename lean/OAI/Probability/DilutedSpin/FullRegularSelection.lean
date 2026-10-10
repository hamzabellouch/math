import OAI.Probability.DilutedSpin.RegularCovarianceConvergence

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance fullRegularSelectionDecidableEq (β : Type) :
    DecidableEq β := Classical.decEq β
variable {p L : ℕ}

lemma gridExponents_pos (L : ℕ) (j : Fin (L+1)) :
    0 < gridExponents L j :=
  (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))).trans_le (gridExponents_lower L j)

/-- The full signed identity, retained for marker anchors as well as spin
anchors. This is the literal output of the analytic perturbation selector. -/
structure FullShapeControl (M : Model p) (C H : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) : Prop where
  shape : ∀ (S : PrescribedTree (L+1)) (a : S.Leaf)
    (f : (n : ℕ) → (S.Leaf → FinitePath (Fin (Ns n+1) → Spin) (L+1)) → ℝ)
    (B : ℝ), 0≤B → (∀ n x, |f n x|≤B) →
    ∀ (k : ℕ) (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool),
    Tendsto (fun n => physicalShapeCovariance (gridExponents L) S a M C H
      (Ns n+1) (us n) F spinAnchor (f n)) atTop (𝓝 0)

lemma FullShapeControl.matrix {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (k : ℕ) (hk : 0<k)
    (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) :
    Tendsto (fun n => physicalTreeMatrixCovariance (gridExponents L) S a M C H
      (Ns n+1) (us n) T q) atTop (𝓝 0) := by
  let F := fun n => spatialProduct (fun _ : S.Leaf =>
    readVector (fun v x => readSpin (KernelTower.terminalState L x) v) (N := Ns n+1))
  have hF : ∀ n x, |F n x|≤1 := fun n x => spatialProduct_bound _
    (fun _ y i => readVector_bound _ y i) x
  have hs := h.shape S a F 1 (by norm_num) hF k (matrixSplitTest T q) true
  have he (n : ℕ) :
      physicalShapeCovariance (gridExponents L) S a M C H (Ns n+1) (us n)
        (matrixSplitTest T q) true (F n) =
        physicalTreeMatrixCovariance (gridExponents L) S a M C H (Ns n+1) (us n) T q := by
    rw [physicalShape_matrix hk (gridExponents L) (gridExponents_pos L)
      (gridExponents_mono L) (gridExponents_last L) S a M C H _ _ T q _
      (by norm_num : (0:ℝ)≤1) (hF n)]
    exact (physicalTreeMatrixCovariance_eq (gridExponents L) S a M C H _ _ T q).symm
  simpa only [he] using hs

lemma FullShapeControl.singleton_energy {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (d : ℕ) (hd : d<L+1) {t : ℝ} (ht : 0<t) :
    ∀ᶠ n in atTop,
      (2*(Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-
        (Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) ⟨d,by omega⟩) *
        physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d ≤
      ((Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-
        (Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) ⟨d,by omega⟩)+t := by
  have hlim := h.shape (forkAt (L+1) d hd) (forkAtLeaf (L+1) d hd 0)
    (fun n => singletonOldTest d hd (Ns n+1)) 1 (by norm_num)
    (fun n x => singletonOldTest_bound d hd (Ns n+1) x) 1 (pairSplitTest d) true
  have hsmall : ∀ᶠ n in atTop, physicalShapeCovariance (gridExponents L) (forkAt (L+1) d hd)
      (forkAtLeaf (L+1) d hd 0) M C H (Ns n+1) (us n) (pairSplitTest d) true
      (singletonOldTest d hd (Ns n+1)) < t := (tendsto_order.1 hlim).2 t ht
  filter_upwards [hsmall] with n hn
  exact (physical_singleton_bound (gridExponents L) (fun j => (gridExponents_pos L j).le)
    (gridExponents_mono L) (gridExponents_last L) M C H (Ns n+1) (us n) d hd).trans
    (add_le_add le_rfl hn.le)

lemma FullShapeControl.singleton_regular {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    {η t : ℝ} (hη : 0<η) (ht : 0<t) : ∀ᶠ n in atTop,
    ∀ d ∈ regularSingletonDepths L η,
      physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d≤((L+1:ℕ):ℝ)⁻¹/η+t := by
  apply (Filter.eventually_all_finset _).mpr
  intro d hd
  have hreg := (Finset.mem_filter.mp hd).2.1
  have hs := h.singleton_energy d d.isLt (mul_pos hη ht)
  filter_upwards [hs] with n hn
  rw [gridExponents_cons] at hn
  have hcoef : η≤2*grid (L+1) 0 (L+1) ⟨d.val+1,by omega⟩-
      grid (L+1) 0 (L+1) ⟨d.val,by omega⟩ := by
    simp only [grid,Nat.zero_add,Nat.cast_add,Nat.cast_one,add_div]
    have hx : 0≤(1:ℝ)/((L+1:ℕ):ℝ) := by positivity
    change η<(d.val:ℝ)/((L+1:ℕ):ℝ) at hreg
    simp only [Nat.cast_add,Nat.cast_one] at hreg hx
    linarith
  have hstep : grid (L+1) 0 (L+1) ⟨d.val+1,by omega⟩-
      grid (L+1) 0 (L+1) ⟨d.val,by omega⟩=((L+1:ℕ):ℝ)⁻¹ := by
    simp [grid,Nat.cast_add,add_div]
  rw [hstep] at hn
  have hen := physicalSingletonEnergy_nonneg (gridExponents L) M C H (Ns n+1) (us n) d
  have hx : η*physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d≤
      ((L+1:ℕ):ℝ)⁻¹+η*t := (mul_le_mul_of_nonneg_right hcoef hen).trans hn
  calc
    _ ≤ (((L+1:ℕ):ℝ)⁻¹+η*t)/η := (le_div_iff₀ hη).mpr (by nlinarith [hx])
    _ = _ := by rw [add_div,mul_div_cancel_left₀ t (ne_of_gt hη)]

lemma physicalShapeAverage_le_of_pointwise (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (η b : ℝ) (hb : 0≤b)
    (h : ∀ Q, regularShapeDomain S (L+1) η Q → physicalScheduledEnergy M C H N L u S Q≤b) :
    physicalShapeAverage M C H N L u S η≤b :=
  DepthAverage.average_le_const _ _ hb h

lemma FullShapeControl.scheduled {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us) :
    ScheduledControl M C H L Ns us := by
  constructor
  · intro η hη t ht
    filter_upwards [h.singleton_regular hη ht] with n hn
    apply physicalShapeAverage_le_of_pointwise M C H (Ns n+1) L (us n) .leaf η _ (by positivity)
    intro Q hQ
    rw [physicalScheduledEnergy_leaf]
    exact hn (Q none) (by
      simp only [regularSingletonDepths,Finset.mem_filter,Finset.mem_univ,true_and]
      exact hQ.1.1 none)
  · intro α _ _ D S T a k hk q denom
    apply DepthAverage.tendsto_average_zero
    intro Q
    have hh := (h.matrix (S Q) (a Q) (k Q) (hk Q) (T Q) (q Q)).abs.div_const |denom Q|
    simpa only [abs_zero,zero_div] using hh

/-- The stronger model-produced selection keeps all marker identities needed
for the subsequent overlap concentration, without changing the sequence in
the covariance induction. -/
theorem full_regular_covariance_selection (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ|≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h|≤H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ),
      (∀ L, StrictMono (Ns L)) ∧
      (∀ L n i, us L n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ L n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns L n) (us L n)≤
        liminf (pressure M) atTop+ε) ∧
      (∀ L, FullShapeControl M C H L (Ns L) (us L)) ∧
      (∀ S η, 0<η → Tendsto (fun L => physicalShapeLimsup M C H L (Ns L) (us L) S η) atTop (𝓝 0)) := by
  classical
  have hx (L : ℕ) := complete_shape_selection (gridExponents L) M hC hH
    (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))) hθ hh hθi hhi
    (gridExponents_lower L) (gridExponents_mono L) (gridExponents_last L) hε
  choose Ns us hNs hus hinc hshape using hx
  have hcontrol (L : ℕ) : FullShapeControl M C H L (Ns L) (us L) := ⟨hshape L⟩
  exact ⟨Ns,us,hNs,hus,hinc,hcontrol,fun S η hη =>
    physicalShapeLimsup_tendsto M C H Ns us (fun L => (hcontrol L).scheduled) S hη⟩

end DilutedSpinGlass.UniversalDictionary

end

end OAI
