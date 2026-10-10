import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingSignedLimit

namespace OAI

/-!
# Compact collisions at signed annular return times

Equal leaf data on compact simultaneous returns survive the signed
bounded shearing limit. A uniform horospherical separation property then
excludes such sequences.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem signed_shearing_forces_horospherical_collision
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (x : ℕ → X n) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop)
    (a B : ℝ) (ha : 0 < a)
    (hsize : ∀ m, a ≤ rootShearSize hij (g m) (t m))
    (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ B)
    (hx : ∀ m, x m ∈ K)
    (hy : ∀ m, rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)) ∈ K)
    (heq : ∀ m, F (x m) = F (rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)))) :
    ∃ h : G n, h ≠ 1 ∧ RootHorosphereShape i j h ∧
      a ≤ slMatrixDifference h 1 ∧ slMatrixDifference h 1 ≤ B ∧
      ∃ z ∈ K, rightAction z h ∈ K ∧ F z = F (rightAction z h) := by
  obtain ⟨h, hne, hshape, hlow, hupp, φ, hφ, hlim⟩ :=
    exists_signed_bounded_horospherical_rootShearLimit hij g hg t ht htop a B ha hsize hsmall
  obtain ⟨z, hz, hzh, heqz⟩ := compact_equal_data_orbit_limit K hK F hF (x ∘ φ)
    (fun m => Matrix.SpecialLinearGroup.transvection hij (t (φ m)) * g (φ m) *
      Matrix.SpecialLinearGroup.transvection hij (-t (φ m))) h
    (fun m => hx (φ m)) (fun m => hy (φ m)) (fun m => heq (φ m)) hlim
  exact ⟨h, hne, hshape, hlow, hupp, z, hz, hzh, heqz⟩

theorem no_small_signed_shearing_pairs
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (r : ℝ) (hr : 0 < r)
    (hinj : ∀ z ∈ K, InjOn (fun g => rightAction z g) (matrixBall n r))
    (hsep : ∀ z ∈ K, ∀ h : G n, RootHorosphereShape i j h → rightAction z h ∈ K →
      F z = F (rightAction z h) → rightAction z h = z)
    (x : ℕ → X n) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop)
    (a B : ℝ) (ha : 0 < a) (hBr : B < r)
    (hsize : ∀ m, a ≤ rootShearSize hij (g m) (t m))
    (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ B)
    (hx : ∀ m, x m ∈ K)
    (hy : ∀ m, rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)) ∈ K)
    (heq : ∀ m, F (x m) = F (rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)))) : False := by
  obtain ⟨h, hne, hshape, _, hupp, z, hz, hzh, heqz⟩ :=
    signed_shearing_forces_horospherical_collision hij K hK F hF x g hg t ht htop
      a B ha hsize hsmall hx hy heq
  have hhball : h ∈ matrixBall n r := fun u v =>
    (slMatrixDifference_entry_le h 1 u v).trans_lt (hupp.trans_lt hBr)
  exact hne (hinj z hz hhball (one_mem_matrixBall n hr)
    ((hsep z hz h hshape hzh heqz).trans (rightAction_one z).symm))

end DukePrimeDegree

end

end OAI
