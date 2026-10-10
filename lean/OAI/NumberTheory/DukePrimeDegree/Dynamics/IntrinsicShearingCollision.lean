import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingSelection
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafLusin

namespace OAI

/-!
# Two annular equal-leaf sequences force a horospherical collision

The compactness argument is expressed directly in terms of the actual
intrinsic leaves. Countable determining data allow passage to the
limit on a Lusin compact set. Arithmetic freeness ensures that the
nonidentity limiting matrix moves the limiting point.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem two_annular_equal_leaves_force_collision
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0)
    (K : Set (X n)) (hK : IsCompact K)
    (hF : ContinuousOn (intrinsicLeafData hij μ hfree) K)
    (hkernel : ∀ x ∈ K, intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x)
    (hcoords : ∀ z ∈ K, ∀ v ∈ pointLattice z, v ≠ 0 → ∀ k, v k ≠ 0)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hkpos : ∀ m, 0 < rootShearingKappa i j (g m))
    (hksmall : ∀ m, rootShearingKappa i j (g m) ≤ 1)
    (x : ℕ → Fin 2 → X n) (t : ℕ → Fin 2 → ℝ)
    (ρ C : ℝ) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hlo : ∀ m q, ρ ≤ |rootShearingKappa i j (g m) * t m q|)
    (hfirst : ∀ m, |rootShearingKappa i j (g m) * t m 0| ≤ 1)
    (hsecond : ∀ m, 16 / ρ ≤ |rootShearingKappa i j (g m) * t m 1|)
    (hupp : ∀ m q, |rootShearingKappa i j (g m) * t m q| ≤ C)
    (hx : ∀ m q, x m q ∈ K)
    (hy : ∀ m q, rightAction (x m q)
      (Matrix.SpecialLinearGroup.transvection hij (t m q) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m q)) ∈ K)
    (heq : ∀ m q, intrinsicRootLeaf hij μ (x m q) = intrinsicRootLeaf hij μ
      (rightAction (x m q) (Matrix.SpecialLinearGroup.transvection hij (t m q) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m q)))) :
    ∃ z ∈ K, ∃ h : G n, RootHorosphereShape i j h ∧ rightAction z h ∈ K ∧
      rightAction z h ≠ z ∧ intrinsicRootLeaf hij μ z =
        intrinsicRootLeaf hij μ (rightAction z h) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Fin.pos i
  let a : ℝ := ρ / (16 * (n : ℝ))
  have ha : 0 < a := div_pos hρ (by positivity)
  have hchoice (m : ℕ) : ∃ q : Fin 2, a ≤ rootShearSize hij (g m) (t m q) := by
    rcases rootShearSize_two_scales_lower hij (g m) (hkpos m)
      (t m 0) (t m 1) ρ hρ hρone (hlo m 0) (hfirst m) (hsecond m) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  choose q hq using hchoice
  have hk : Tendsto (fun m => rootShearingKappa i j (g m)) atTop (𝓝 0) := by
    change Tendsto (rootShearingKappa i j ∘ g) atTop (𝓝 0)
    simpa only [rootShearingKappa_one hij] using
      ((continuous_rootShearingKappa i j).tendsto 1).comp hg
  have hnorm (m : ℕ) : ρ ≤ rootShearingKappa i j (g m) * |t m (q m)| := by
    simpa only [abs_mul, abs_of_pos (hkpos m)] using hlo m (q m)
  have ht (m : ℕ) : t m (q m) ≠ 0 := by
    intro he
    have h := hnorm m
    rw [he, abs_zero, mul_zero] at h
    exact hρ.not_ge h
  have hdata (m : ℕ) : intrinsicLeafData hij μ hfree (x m (q m)) =
      intrinsicLeafData hij μ hfree (rightAction (x m (q m))
        (Matrix.SpecialLinearGroup.transvection hij (t m (q m)) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m (q m)))) := by
    apply (intrinsicLeafData_eq_iff hij μ hfree _ _).mpr
    rw [hkernel _ (hx m (q m)), hkernel _ (hy m (q m)), heq m (q m)]
  obtain ⟨h, hne, hshape, _, _, z, hz, hzh, he⟩ :=
    signed_shearing_forces_horospherical_collision hij K hK (intrinsicLeafData hij μ hfree) hF
      (fun m => x m (q m)) g hg (fun m => t m (q m)) ht
      (abs_tendsto_atTop_of_vanishing_scale _ _ hk (fun m => (hkpos m).le) ρ hρ hnorm)
      a ((n : ℝ) * n * (2 * C + C ^ 2)) ha hq
      (fun m u hu => rootShearSize_bound_on_symmetric_interval hij (g m) (hksmall m)
        (t m (q m)) C (by
          simpa only [abs_mul, abs_of_pos (hkpos m), mul_comm] using hupp m (q m)) u hu)
      (fun m => hx m (q m)) (fun m => hy m (q m)) hdata
  refine ⟨z, hz, h, hshape, hzh, ?_, ?_⟩
  · exact fun hfix => hne (rootHorosphere_stabilizer_eq_one hij z (hcoords z hz) h hshape hfix)
  · have he' := (intrinsicLeafData_eq_iff hij μ hfree _ _).mp he
    rwa [hkernel z hz, hkernel _ hzh] at he'

end DukePrimeDegree

end

end OAI
