import OAI.Geometry.Perimeter.Regularity.HeightCompactness

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace RPISingularHarnack
open RPI.Boundary
variable {n : ℕ}

def compactLpExtension (K : Set (Euc n))
    (g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n))) : Euc n → ℝ :=
  Function.extend (Subtype.val : K → Euc n) g (fun _ ↦ 0)

@[simp] theorem compactLpExtension_coe (K : Set (Euc n))
    (g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n))) (x : K) :
    compactLpExtension K g x = g x :=
  Subtype.val_injective.extend_apply _ _ x

theorem compactLpExtension_zero (K : Set (Euc n))
    (g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n))) {x : Euc n} (hx : x ∉ K) :
    compactLpExtension K g x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y,rfl⟩; exact hx y.property

theorem compactLpExtension_integrable (K : Set (Euc n)) (hK : IsCompact K)
    (g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n))) :
    Integrable (compactLpExtension K g) volume := by
  have hi : IntegrableOn (compactLpExtension K g) K volume := by
    rw [integrableOn_iff_comap_subtypeVal hK.measurableSet]
    simpa only [Function.comp_def,compactLpExtension_coe] using
      (memLp_one_iff_integrable.mp (Lp.memLp g))
  exact hi.integrable_of_forall_notMem_eq_zero (fun _ hx ↦ compactLpExtension_zero K g hx)

theorem compactLpExtension_error (K : Set (Euc n)) (hK : IsCompact K)
    (g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n)))
    (f : Euc n → ℝ) (hi : Integrable f volume) (hs : Function.support f ⊆ K) :
    (∫⁻ x, ‖f x-compactLpExtension K g x‖ₑ) = edist (compactFunctionLp K hK f hi) g := by
  rw [Lp.edist_def,eLpNorm_one_eq_lintegral_enorm
    ((Lp.aestronglyMeasurable (compactFunctionLp K hK f hi)).sub (Lp.aestronglyMeasurable g))]
  have hz : Function.support (fun x ↦ ‖f x-compactLpExtension K g x‖ₑ) ⊆ K := by
    intro x hx
    by_contra hnot
    have hf : f x=0 := Function.notMem_support.mp (fun h ↦ hnot (hs h))
    simp [hf,compactLpExtension_zero K g hnot] at hx
  rw [← setLIntegral_eq_of_support_subset hz,← lintegral_subtype_comap hK.measurableSet]
  apply lintegral_congr_ae
  filter_upwards [compactFunctionLp_ae K hK f hi] with x hx
  simp only [compactLpExtension_coe,Pi.sub_apply,hx]

theorem compactLpExtension_tendsto (K : Set (Euc n)) (hK : IsCompact K)
    (f : ℕ → Euc n → ℝ) (hi : ∀ i, Integrable (f i) volume)
    (hs : ∀ i, Function.support (f i) ⊆ K)
    (g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n)))
    (hlim : Tendsto (fun i ↦ compactFunctionLp K hK (f i) (hi i)) atTop (𝓝 g)) :
    Tendsto (fun i ↦ ∫⁻ x, ‖f i x-compactLpExtension K g x‖ₑ) atTop (𝓝 0) := by
  have he (i : ℕ) := compactLpExtension_error K hK g (f i) (hi i) (hs i)
  simp_rw [he]
  simpa only [edist_self] using hlim.edist (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ g) atTop (𝓝 g))

theorem compact_support_L1_subsequence
    (K : Set (Euc n)) (hK : IsCompact K) (f : ℕ → Euc n → ℝ)
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (f i) volume)
    (hs : ∀ i, Function.support (f i) ⊆ K)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ i, (∫ x, ‖f i x‖) ≤ A)
    (D : ℝ≥0∞) (hD : D ≠ ⊤)
    (ht : ∀ i w, (∫⁻ x, ‖f i (x+w)-f i x‖ₑ) ≤ ‖w‖ₑ * D) :
    ∃ g : Euc n → ℝ, Integrable g volume ∧ Function.support g ⊆ K ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun i ↦ ∫⁻ x, ‖f (σ i) x-g x‖ₑ) atTop (𝓝 0) := by
  obtain ⟨g,σ,hσ,hg⟩ := compactFunctionLp_subsequence_of_translation K hK f hm hi A hA hb D hD ht
  refine ⟨compactLpExtension K g,compactLpExtension_integrable K hK g,?_,σ,hσ,?_⟩
  · intro x hx
    by_contra hnot
    exact hx (compactLpExtension_zero K g hnot)
  · exact compactLpExtension_tendsto K hK (fun i ↦ f (σ i)) (fun i ↦ hi (σ i))
      (fun i ↦ hs (σ i)) g hg

end RPISingularHarnack

end

end OAI
