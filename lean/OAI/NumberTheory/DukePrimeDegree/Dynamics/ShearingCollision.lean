import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingHorosphere

namespace OAI

/-!
# Compactness for pairs with equal leaf data

The last limiting step of the low-entropy argument: equal continuous
leaf data on a compact set survive a normalized shearing limit. This
isolates the compactness step from the return-time selection and the
horospherical separation argument in EKL (2006), Section 4.2.
-/

noncomputable section
open Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixDifference_entry_le {n : ℕ} (g h : G n) (r s : Fin n) :
    |g.val r s - h.val r s| ≤ slMatrixDifference g h := by
  apply (Finset.single_le_sum (f := fun u : Fin n => |g.val r u - h.val r u|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ s)).trans
  exact Finset.single_le_sum (f := fun u : Fin n =>
    ∑ v, |g.val u v - h.val u v|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ r)

lemma rootShearLimit_size {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) (t : ℕ → ℝ)
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-t m)) atTop (𝓝 h))
    (a : ℝ) (hsize : ∀ m, rootShearSize hij (g m) (t m) = a) :
    slMatrixDifference h 1 = a := by
  have hd := continuous_slMatrixDifference.continuousAt.tendsto.comp (hlim.prodMk_nhds hg)
  have hc : Tendsto (fun m => slMatrixDifference
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)) (g m)) atTop (𝓝 a) := by
    change Tendsto (fun m => rootShearSize hij (g m) (t m)) atTop (𝓝 a)
    simpa only [hsize] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  exact tendsto_nhds_unique hd hc

theorem compact_equal_data_orbit_limit
    {n : ℕ} {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (x : ℕ → X n) (H : ℕ → G n) (h : G n)
    (hx : ∀ m, x m ∈ K) (hy : ∀ m, rightAction (x m) (H m) ∈ K)
    (heq : ∀ m, F (x m) = F (rightAction (x m) (H m)))
    (hH : Tendsto H atTop (𝓝 h)) :
    ∃ z ∈ K, rightAction z h ∈ K ∧ F z = F (rightAction z h) := by
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hK.isSeqCompact hx
  have hxlim : Tendsto (x ∘ φ) atTop (𝓝 z) := hlim
  have hylim : Tendsto (fun m => rightAction (x (φ m)) (H (φ m)))
      atTop (𝓝 (rightAction z h)) :=
    (continuous_rightAction_uncurry n).continuousAt.tendsto.comp
      (hxlim.prodMk_nhds (hH.comp hφ.tendsto_atTop))
  have hzy : rightAction z h ∈ K := hK.isClosed.mem_of_tendsto hylim
    (Eventually.of_forall fun m => hy (φ m))
  have hFx : Tendsto (fun m => F (x (φ m))) atTop (𝓝 (F z)) :=
    (hF z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxlim, Eventually.of_forall fun m => hx (φ m)⟩)
  have hFy : Tendsto (fun m => F (rightAction (x (φ m)) (H (φ m))))
      atTop (𝓝 (F (rightAction z h))) :=
    (hF _ hzy).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hylim, Eventually.of_forall fun m => hy (φ m)⟩)
  have heq' : (fun m => F (x (φ m))) =
      (fun m => F (rightAction (x (φ m)) (H (φ m)))) := funext fun m => heq (φ m)
  exact ⟨z, hz, hzy, tendsto_nhds_unique hFx (heq' ▸ hFy)⟩

/-- Equal compact leaf data on normalized shearing pairs force a
nonidentity horospherical collision. The measure-theoretic selection of
these pairs is a separate step. -/
theorem normalized_shearing_forces_horospherical_collision
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (x : ℕ → X n) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, 0 < t m) (htop : Tendsto t atTop atTop)
    {a : ℝ} (ha : 0 < a)
    (hsize : ∀ m, rootShearSize hij (g m) (t m) = a)
    (hsmall : ∀ m, ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a)
    (hx : ∀ m, x m ∈ K)
    (hy : ∀ m, rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)) ∈ K)
    (heq : ∀ m, F (x m) = F (rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)))) :
    ∃ h : G n, h ≠ 1 ∧ RootHorosphereShape i j h ∧ slMatrixDifference h 1 = a ∧
      ∃ z ∈ K, rightAction z h ∈ K ∧ F z = F (rightAction z h) := by
  obtain ⟨h, hne, hshape, _, φ, hφ, hlim⟩ :=
    exists_nontrivial_horospherical_rootShearLimit hij g hg t ht htop ha hsize hsmall
  obtain ⟨z, hz, hzh, heqz⟩ := compact_equal_data_orbit_limit K hK F hF (x ∘ φ)
    (fun m => Matrix.SpecialLinearGroup.transvection hij (t (φ m)) * g (φ m) *
      Matrix.SpecialLinearGroup.transvection hij (-t (φ m))) h
    (fun m => hx (φ m)) (fun m => hy (φ m)) (fun m => heq (φ m)) hlim
  have hsizeh := rootShearLimit_size hij (g ∘ φ) (hg.comp hφ.tendsto_atTop)
    (t ∘ φ) h hlim a (fun m => hsize (φ m))
  exact ⟨h, hne, hshape, hsizeh, z, hz, hzh, heqz⟩

/-- Continuous data that separate horospherical points rule out small
normalized shearing pairs in one compact injectivity region. -/
theorem no_small_normalized_shearing_pairs
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (r : ℝ) (hr : 0 < r)
    (hinj : ∀ z ∈ K, Set.InjOn (fun g => rightAction z g) (matrixBall n r))
    (hsep : ∀ z ∈ K, ∀ h : G n, RootHorosphereShape i j h → rightAction z h ∈ K →
      F z = F (rightAction z h) → rightAction z h = z)
    (x : ℕ → X n) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, 0 < t m) (htop : Tendsto t atTop atTop)
    {a : ℝ} (ha : 0 < a) (har : a < r)
    (hsize : ∀ m, rootShearSize hij (g m) (t m) = a)
    (hsmall : ∀ m, ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a)
    (hx : ∀ m, x m ∈ K)
    (hy : ∀ m, rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)) ∈ K)
    (heq : ∀ m, F (x m) = F (rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)))) : False := by
  obtain ⟨h, hne, hshape, hsizeh, z, hz, hzh, heqz⟩ :=
    normalized_shearing_forces_horospherical_collision hij K hK F hF x g hg t ht htop
      ha hsize hsmall hx hy heq
  have hhball : h ∈ matrixBall n r := fun u v =>
    (slMatrixDifference_entry_le h 1 u v).trans_lt (hsizeh ▸ har)
  exact hne (hinj z hz hhball (one_mem_matrixBall n hr)
    ((hsep z hz h hshape hzh heqz).trans (rightAction_one z).symm))

end DukePrimeDegree

end

end OAI
