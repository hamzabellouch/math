import Mathlib
import OAI.Analysis.Conductivity.Variational.QuantitativeGlobalCorrection
import OAI.Analysis.Conductivity.Branching.ParametricCorrectionTransport

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem parametric_source_finite_split
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U) :
    ∃ (s : Finset (ParametricCorrectionBox u p U)) (ρ : s → Coord3 → ℝ) (C : s → ℝ),
      (∀ i,0<C i) ∧ ∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r K →
      ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      let p : s → PhysicalSourcePair := fun i j x => ρ i x*r j x
      (∀ i,CompactSmoothPair (p i)) ∧ (∀ i,PairSupported (p i) i.val.region) ∧
      (∑ i,p i)=r ∧ ∀ i j,UniformC1Bound (p i j) (C i*M) := by
  classical
  have hcov : K⊆⋃ B : ParametricCorrectionBox u p U,B.region := by
    rwa [parametric_correction_boxes_cover hu p hU hD]
  obtain ⟨s,hsc⟩ := hK.elim_finite_subcover (fun B : ParametricCorrectionBox u p U => B.region)
    (fun B => B.region_open) hcov
  have hsc' : K⊆⋃ B : s,B.val.region := by
    intro x hx
    obtain ⟨B,hB,hxB⟩ := mem_iUnion₂.mp (hsc hx)
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hxB⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ Coord3) hK.isClosed (fun B : s => B.val.region)
    (fun B => B.val.region_open) hsc'
  have hsρ (i : s) : HasCompactSupport (ρ i) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _,i.val.region_bounded.subset (hρ i)⟩
  choose C hC hbC using fun i : s => exists_uniformC1Bound (ρ i).contMDiff.contDiff (hsρ i)
  refine ⟨s,fun i => ρ i,fun i => 2*C i,fun i => mul_pos (by norm_num) (hC i),?_⟩
  intro r hr hs M hM hb
  dsimp only
  refine ⟨fun i j => ⟨(ρ i).contMDiff.contDiff.mul (hr j).1,(hr j).2.mul_left⟩,
    fun i j => tsupport_mul_subset_left.trans (hρ i),?_,?_⟩
  · funext j x
    simp only [Finset.sum_apply]
    rw [←Finset.sum_mul]
    by_cases hx : x∈K
    · have he := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at he
      rw [he,one_mul]
    · have hz : r j x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs j h))
      simp [hz]
  · intro i j
    exact (hbC i).mul ((ρ i).contMDiff.contDiff.differentiable (by simp))
      ((hr j).1.differentiable (by simp)) (hC i).le hM (hb j)

theorem parametric_global_regular_symmetric_correction_C0
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ t in 𝓝 p,∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r K →
      physicalSourceMoment (fun x => u (t,x)) r=0 → ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      BoundedPhysicallyCorrectable (fun x => u (t,x)) U r (L*M) := by
  classical
  by_cases hne : U.Nonempty
  · obtain ⟨x,hx⟩ := hne
    obtain ⟨B,_⟩ := exists_parametric_correction_box hu p hU hx (hD x hx)
    obtain ⟨s,ρ,C,hC,split⟩ := parametric_source_finite_split hu p hU hD hK hKU
    choose D hDpos htransport using fun i : s => parametric_controlled_source_transport hu p hU hUc hD i.val B
    obtain ⟨R,hR,hsolve⟩ := B.bounded_solver
    let S : ℝ := (∑ i,D i*C i)+1
    have hS : 0<S := by
      have hn : 0≤∑ i,D i*C i := Finset.sum_nonneg (fun i _ => mul_nonneg (hDpos i).le (hC i).le)
      change 0<(∑ i : s,D i*C i)+1
      linarith
    refine ⟨(1+R)*S,by positivity,?_⟩
    have ht := Filter.eventually_all.mpr htransport
    filter_upwards [ht,hsolve] with t transport solve
    have hut : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (t,x)) := hu.comp (contDiff_const.prodMk contDiff_id)
    intro r hr hs hm M hM hb
    let p : s → PhysicalSourcePair := fun i j x => ρ i x*r j x
    obtain ⟨hp,hps,hpe,hpb⟩ := split r hr hs M hM hb
    change (∀ i,CompactSmoothPair (p i)) at hp
    change (∀ i,PairSupported (p i) i.val.region) at hps
    change (∑ i,p i)=r at hpe
    change (∀ i j,UniformC1Bound (p i j) (C i*M)) at hpb
    choose q hq hqs hqm hqb hqc using fun i : s =>
      transport i (p i) (hp i) (hps i) (C i*M) (mul_nonneg (hC i).le hM) (hpb i)
    have hN : (∑ i,D i*(C i*M))≤S*M := by
      have he : (∑ i,D i*(C i*M))=(∑ i,D i*C i)*M := by
        simp_rw [←mul_assoc]; exact (Finset.sum_mul _ _ _).symm
      rw [he]; dsimp [S]; nlinarith
    have hQ : CompactSmoothPair (∑ i,q i) := CompactSmoothPair.sum _ q (fun i _ => hq i)
    have hQs : PairSupported (∑ i,q i) B.region := PairSupported.sum _ q (fun i _ => hqs i)
    have hQm : physicalSourceMoment (fun x => u (t,x)) (∑ i,q i)=0 := by
      rw [physicalSourceMoment_sum _ q hut.continuous (fun i _ => hq i)]
      simp_rw [hqm]
      rw [←physicalSourceMoment_sum _ p hut.continuous (fun i _ => hp i),hpe,hm]
    have hQb (j) : UniformC1Bound ((∑ i,q i) j) (S*M) := by
      have he : ((∑ i,q i) j)=(∑ i,q i j) := by funext x; simp only [Finset.sum_apply]
      rw [he]
      exact (UniformC1Bound.sum _ _ _ (fun i _ => (hq i j).1.differentiable (by simp))
        (fun i _ => hqb i j)).mono hN
    have hbase := solve (∑ i,q i) hQ hQs hQm (S*M) (mul_nonneg hS.le hM) hQb
    have hall := ((BoundedPhysicallyCorrectable.sum Finset.univ (fun i => p i-q i)
      (fun i => D i*(C i*M)) hut (fun i _ => hqc i)).mono hN).add hut hbase
    rw [Finset.sum_sub_distrib,sub_add_cancel,hpe] at hall
    exact hall.mono (by ring_nf; rfl)
  · refine ⟨1,zero_lt_one,?_⟩
    apply Filter.Eventually.of_forall
    intro t r hr hs hm M hM hb
    have he : r=0 := by
      funext j x
      exact Function.notMem_support.mp (fun h => hne ⟨x,hKU (hs j (subset_tsupport (r j) h))⟩)
    rw [he]
    exact BoundedPhysicallyCorrectable.zero (by simpa using hM)

end ScalarConductivity

end
end

end OAI
