import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm

namespace OAI

/-! Finite tuples of supported linear operators, with actual weighted
seminorm bounds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A F E ι : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup E] [Module ℝ E]
  [Fintype ι]

lemma supportedWeightedSeminorm_mono {K : Compacts A} (s : ℝ≥0) {m r : ℕ} (hmr : m ≤ r)
    (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm K s m f ≤ supportedWeightedSeminorm K s r f := by
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact supportedWeightedSeminorm_component s r j (hjm.trans hmr) f

def tupleSupportedLM (K : Compacts A) (L : ι → E →ₗ[ℝ] SupportedField (F := F) K) :
    E →ₗ[ℝ] SupportedField (F := ι → F) K where
  toFun z := ⟨fun p i => L i z p,
    contDiff_pi.mpr (fun i => (L i z).contDiff), fun p hp => by
      funext i
      exact (L i z).zero_on_compl hp⟩
  map_add' z w := by
    apply DFunLike.ext
    intro p
    funext i
    exact congrArg (fun f : SupportedField (F := F) K => f p) ((L i).map_add z w)
  map_smul' c z := by
    apply DFunLike.ext
    intro p
    funext i
    exact congrArg (fun f : SupportedField (F := F) K => f p) ((L i).map_smul c z)

lemma tupleSupportedLM_apply (K : Compacts A) (L : ι → E →ₗ[ℝ] SupportedField (F := F) K)
    (z : E) (p : A) (i : ι) : tupleSupportedLM K L z p i = L i z p := rfl

lemma tupleSupportedLM_bound (K : Compacts A) (L : ι → E →ₗ[ℝ] SupportedField (F := F) K)
    {s : ℝ≥0} (hs : 0 < (s : ℝ)) (m : ℕ) (z : E) :
    supportedWeightedSeminorm K s m (tupleSupportedLM K L z) ≤
      ∑ i, supportedWeightedSeminorm K s m (L i z) := by
  have hn : 0 ≤ ∑ i, supportedWeightedSeminorm K s m (L i z) :=
    Finset.sum_nonneg fun i _ => apply_nonneg _ _
  apply supportedSeminorm_le_of_weightedBound hs hn
  apply WeightedBound.pi uniqueDiffOn_univ hs hn
  · intro i
    exact (L i z).contDiff.contDiffOn
  · intro i
    exact (weightedBound_of_supportedSeminorm s m (L i z)).mono_const
      (Finset.single_le_sum (f := fun j => supportedWeightedSeminorm K s m (L j z))
        (fun j _ => apply_nonneg _ _) (Finset.mem_univ i))

end ClosedSurfaceR4.JetPolynomial

end

end OAI
