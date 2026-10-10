import OAI.Probability.RadialTransition.CellIntegral

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

def freeCoverWeight (L t α : ℝ) : Multiset Position → ℝ≥0∞ :=
  indexedClusterProduct (fun k : cubeCells L =>
    cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k.val)

lemma measurable_freeCoverWeight (L t α : ℝ) : MeasurableConfiguration (freeCoverWeight L t α) :=
  measurable_indexedClusterProduct _ (fun _ => measurable_cellClusterWeight _ _ _ _)

lemma core_boltzmann_cover {ι : Type} [Fintype ι] {t α L β : ℝ} {x : ι → Position}
    (ht0 : 0 ≤ t) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hβ : 0 ≤ β) (hbox : ∀ i, x i ∈ cube L) (hta : 0 ≤ t*α) :
    ENNReal.ofReal (Real.exp (-β*orderedEnergy (corePotential t) x)) ≤
    ENNReal.ofReal (Real.exp (t*α*packingNumber L))*
      clusterConvolution (freeCoverWeight L t α) (removalWeight t β) (configurationMultiset x) := by
  classical
  let B := badLabels t x
  let good := configurationMultiset (fun i : {i // i ∉ B} => x i)
  let bad := configurationMultiset (fun i : B => x i)
  have hfree : ENNReal.ofReal (Real.exp (-t*α*packingNumber L)) ≤ freeCoverWeight L t α good :=
    coreFree_cell_cover (after_removal_free t x) ht (fun i => hbox i.val) hta
  have hsum : freeCoverWeight L t α good*removalWeight t β bad ≤
      clusterConvolution (freeCoverWeight L t α) (removalWeight t β) (configurationMultiset x) := by
    rw [clusterConvolution_configuration]
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Finset ι)))
      (f := fun T : Finset ι => freeCoverWeight L t α (configurationMultiset (fun i : {i // i ∉ T} => x i)) *
        removalWeight t β (configurationMultiset (fun i : T => x i)))
      (fun _ _ => (bot_le : (0:ℝ≥0∞) ≤ _)) (Finset.mem_univ B)
    convert hh using 1

  have hb : ENNReal.ofReal (Real.exp (-β*orderedEnergy (corePotential t) x)) ≤
      removalWeight t β bad := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    change -β*orderedEnergy (corePotential t) x ≤ -β*t^2*(configurationMultiset (fun i : B => x i)).card/2
    rw [configurationMultiset_card, Fintype.card_coe]
    have he := mul_le_mul_of_nonneg_left (badLabels_energy ht0 x) hβ
    dsimp [B]
    nlinarith
  have hc : ENNReal.ofReal (Real.exp (t*α*packingNumber L))*
      ENNReal.ofReal (Real.exp (-t*α*packingNumber L)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    convert (by norm_num : ENNReal.ofReal (Real.exp 0) = 1) using 2; ring_nf
  calc
    _ ≤ removalWeight t β bad := hb
    _ = ENNReal.ofReal (Real.exp (t*α*packingNumber L))*
      (ENNReal.ofReal (Real.exp (-t*α*packingNumber L))*removalWeight t β bad) := by rw [← mul_assoc, hc, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl ((mul_le_mul' hfree le_rfl).trans hsum)

lemma particleBase_ae_cube (L z : ℝ) :
    ∀ᵐ s : ParticleState Position ∂particleBase (volume.restrict (cube L)) z,
      ∀ i, s.2 i ∈ cube L := by
  rw [particleBase, Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure
  rw [(Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding).ae_map_iff]
  rw [← Measure.restrict_pi_pi]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ : Fin n => measurableSet_cube L))] with x hx
  exact fun i => hx i (Set.mem_univ i)

lemma particleBase_restrict_le (A : Set Position) (z : ℝ) (F : Multiset Position → ℝ≥0∞)
    (hF : MeasurableConfiguration F) :
    (∫⁻ x, F (particleMultiset x) ∂particleBase (volume.restrict A) z) ≤
      ∫⁻ x, F (particleMultiset x) ∂particleBase volume z := by
  have hm := measurable_particleObservable F hF 0
  simp only [zero_add] at hm
  rw [lintegral_particleBase _ _ hm, lintegral_particleBase _ _ hm]
  apply ENNReal.tsum_le_tsum
  intro n
  apply mul_le_mul' le_rfl
  rw [← Measure.restrict_pi_pi]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

lemma particleBase_freeCoverWeight_le {t h α : ℝ} (ht : 0 ≤ t)
    (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) (L : ℝ) :
    (∫⁻ x, freeCoverWeight L t α (particleMultiset x)
      ∂particleBase (volume.restrict (cube L)) (t*h)) ≤ (15001:ℝ≥0∞)^(cubeCells L).card := by
  rw [freeCoverWeight, particleBase_indexedClusterProduct _ (fun _ => measurable_cellClusterWeight _ _ _ _)]
  have hh : ∀ k : cubeCells L,
      (∫⁻ x, cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k.val (particleMultiset x)
        ∂particleBase (volume.restrict (cube L)) (t*h)) ≤ 15001 := by
    intro k
    exact (particleBase_restrict_le _ _ _ (measurable_cellClusterWeight _ _ _ _)).trans
      (particleBase_cellClusterWeight_le ht h1 h4 k.val)
  simpa using Finset.prod_le_prod (fun k (_ : k ∈ (Finset.univ : Finset (cubeCells L))) => hh k)

lemma stable_corePotential (t : ℝ) : StableWith (corePotential t) 0 := by
  intro N x
  simp only [zero_mul, neg_zero, energy]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => coreReal_nonneg _ _))

lemma core_grand_upper {t α L β h : ℝ} (hL : 0 ≤ L)
    (ht0 : 0 ≤ t) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hβ : 0 ≤ β) (hta : 0 ≤ t*α) (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) :
    ENNReal.ofReal (grandPartition (corePotential t) t L β h) ≤
      ENNReal.ofReal (Real.exp (t*α*packingNumber L))*
      ((15001:ℝ≥0∞)^(cubeCells L).card *
        ENNReal.ofReal (Real.exp (L^3*Real.exp (t*h-β*t^2/2)))) := by
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; finiteness
  have hmass : (volume.restrict (cube L) univ).toReal = L^3 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_cube,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hL]
  rw [← grandOn_cube]
  rw [← lintegral_grandOn (continuous_corePotential t) (bounded_corePotential t) (stable_corePotential t) hβ hfin]
  have hle := lintegral_mono_ae ((particleBase_ae_cube L (t*h)).mono (fun x hx => core_boltzmann_cover ht0 ht hβ hx hta))
  apply hle.trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change _ * (∫⁻ x, clusterConvolution (freeCoverWeight L t α) (removalWeight t β) (particleMultiset x) ∂particleBase (volume.restrict (cube L)) (t*h)) ≤ _
  rw [particleBase_convolution (measurable_freeCoverWeight _ _ _) (measurable_removalWeight _ _),
    particleBase_removalWeight (by simpa using hfin), hmass]
  exact mul_le_mul' le_rfl (mul_le_mul' (particleBase_freeCoverWeight_le ht0 h1 h4 L) le_rfl)

end RadialTransition
end

end OAI
