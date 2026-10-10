import OAI.NumberTheory.DukePrimeDegree.Dynamics.NeutralLeafFlow
import OAI.NumberTheory.DukePrimeDegree.Dynamics.LusinFlowReturns
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitRebase
import OAI.NumberTheory.DukePrimeDegree.Geometry.CompactLimitData
import OAI.NumberTheory.DukePrimeDegree.Dynamics.DiagonalFlowMaximal

namespace OAI

/-!
# Pointwise root holonomy under a neutral diagonal flow

This is the consequence of Einsiedler–Katok (2003), Proposition 5.1,
needed by the high-entropy commutator argument. One null set works for
all pairs and all relative matrices whose conjugates approach a root
translation. Lusin compactness and strict neutral invariance identify
both limiting root conditionals; pointwise rebasing supplies holonomy.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_neutral_root_holonomy
    (d : ℕ) {a b : Fin (d + 1)} (hab : a ≠ b)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ y ∉ N, ∀ g : G (d + 1), rightAction x g = y → ∀ c : ℝ,
        Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
          diagonalOneParameter ell hell (-t)) atTop
          (𝓝 (Matrix.SpecialLinearGroup.transvection hab c)) →
        intrinsicRootLeaf hab μ y = basedRealMeasure (intrinsicRootLeaf hab μ x) c := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hab t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx a b hab
  let F := intrinsicLeafData hab μ hfree
  obtain ⟨V, hVF, _, hV⟩ := exists_strictly_neutral_flow_invariant_leafData d hab μ hA hfree
  obtain ⟨R, hR, hRzero, hrebase⟩ := exists_nullset_root_orbit_rebase d hab μ hA
  have hspec : ∀ᵐ x ∂μ, intrinsicRootKernel hab μ hfree x = intrinsicRootLeaf hab μ x ∧ V x = F x :=
    (ae_intrinsicRootKernel_eq hab μ hfree).and hVF
  obtain ⟨S, hbad, hS, hSzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hspec)
  let E := R ∪ S
  have hE : MeasurableSet E := hR.union hS
  have hEzero : μ E = 0 := measure_union_null hRzero hSzero
  have hgood (x : X (d + 1)) (hx : x ∉ E) :
      intrinsicRootKernel hab μ hfree x = intrinsicRootLeaf hab μ x ∧ V x = F x := by
    by_contra h
    exact hx (Or.inr (hbad h))
  let Φ : ℝ → X (d + 1) → X (d + 1) :=
    fun t x => rightAction x (diagonalOneParameter ell hell (-t))
  have hcont : Continuous (fun p : X (d + 1) × ℝ => Φ p.2 p.1) :=
    (continuous_rightAction_uncurry (d + 1)).comp
      (continuous_fst.prodMk ((continuous_diagonalOneParameter ell hell).comp continuous_snd.neg))
  have hzero (x : X (d + 1)) : Φ 0 x = x := by simp [Φ, diagonalOneParameter_zero]
  have hadd (s t : ℝ) (x : X (d + 1)) : Φ (s + t) x = Φ s (Φ t x) := by
    dsimp [Φ]
    rw [rightAction_mul, ← diagonalOneParameter_add]
    congr 2
    ring
  have hpres (t : ℝ) : MeasurePreserving (Φ t) μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp only [Φ]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨M, hM, hMzero, hreturns⟩ := exists_conull_lusin_flow_returns μ hcont.measurable
    hzero hadd hpres F (measurable_intrinsicLeafData hab μ hfree) E hE hEzero
  refine ⟨E ∪ M, hE.union hM, measure_union_null hEzero hMzero, ?_⟩
  intro x hx y hy g hxy c hlim
  have hxE : x ∉ E := fun h => hx (Or.inl h)
  have hyE : y ∉ E := fun h => hy (Or.inl h)
  obtain ⟨K, hK, hKE, hFK, hret⟩ := hreturns x (fun h => hx (Or.inr h)) y (fun h => hy (Or.inr h))
  have hseq (m : ℕ) : ∃ t : ℝ, (m : ℝ) < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := hret m
  choose t ht htx hty using hseq
  have htop : Tendsto t atTop atTop :=
    tendsto_atTop_mono (fun m => (ht m).le) tendsto_natCast_atTop_atTop
  let H : ℕ → G (d + 1) := fun m => diagonalOneParameter ell hell (t m) * g *
    diagonalOneParameter ell hell (-t m)
  have hpair (m : ℕ) : rightAction (Φ (t m) x) (H m) = Φ (t m) y := by
    rw [← hxy]
    dsimp only [Φ, H]
    rw [rightAction_mul, rightAction_mul]
    congr 1
    rw [diagonalOneParameter_neg]
    group
  have hdata (w : X (d + 1)) (m : ℕ) (hw : Φ (t m) w ∈ K) : F (Φ (t m) w) = V w :=
    (hgood _ (hKE hw)).2.symm.trans (hV ell hell hneut (-t m) w)
  obtain ⟨z, hz, hzc, hFz, hFzc⟩ := compact_orbit_limit_with_data K hK F hFK
    (fun m => Φ (t m) x) H (Matrix.SpecialLinearGroup.transvection hab c) htx
    (fun m => by rw [hpair]; exact hty m) (V x) (V y)
    (fun m => hdata x m (htx m))
    (fun m => by rw [hpair]; exact hdata y m (hty m)) (hlim.comp htop)
  have hleaf (w u : X (d + 1)) (hw : w ∉ E) (hu : u ∉ E) (hFwu : F w = V u) :
      intrinsicRootLeaf hab μ w = intrinsicRootLeaf hab μ u := by
    have he : F w = F u := hFwu.trans (hgood u hu).2
    have hk := (intrinsicLeafData_eq_iff hab μ hfree w u).mp he
    exact (hgood w hw).1.symm.trans (hk.trans (hgood u hu).1)
  have hxz := hleaf z x (hKE hz) hxE hFz
  have hyz := hleaf _ y (hKE hzc) hyE hFzc
  have hr := hrebase z (fun h => hKE hz (Or.inl h)) c (fun h => hKE hzc (Or.inl h))
  rw [hxz, hyz] at hr
  exact hr

end DukePrimeDegree

end

end OAI
