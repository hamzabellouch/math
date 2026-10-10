import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereFreeness

namespace OAI

/-!
# Excluding bounded shearing collisions on a compact Lusin set

The arithmetic no-coordinate-zero property excludes every nonidentity
horospherical stabilizer. Hence a compact leaf-data separation property
rules out the selected shearing sequences at any fixed bounded size.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem no_signed_shearing_pairs_on_free_compact
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (hfree : ∀ z ∈ K, ∀ v ∈ pointLattice z, v ≠ 0 → ∀ k, v k ≠ 0)
    (hsep : ∀ z ∈ K, ∀ h : G n, RootHorosphereShape i j h → rightAction z h ∈ K →
      F z = F (rightAction z h) → rightAction z h = z)
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
        Matrix.SpecialLinearGroup.transvection hij (-t m)))) : False := by
  obtain ⟨h, hne, hshape, _, _, z, hz, hzh, heqz⟩ :=
    signed_shearing_forces_horospherical_collision hij K hK F hF x g hg t ht htop
      a B ha hsize hsmall hx hy heq
  exact hne (rootHorosphere_stabilizer_eq_one hij z (hfree z hz) h hshape
    (hsep z hz h hshape hzh heqz))

end DukePrimeDegree

end

end OAI
