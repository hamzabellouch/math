import Mathlib.Data.Fintype.Perm
import OAI.NumberTheory.Catalan.Determinants.RealCauchyDeterminant

namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set
open scoped BigOperators

def realListPairMeasure (N : ℕ) :
    Measure ((Fin (n N) → ℝ) × (Fin (n N) → ℝ)) :=
  (Measure.pi (fun _ : Fin (n N) => realPlaceMeasure)).prod
    (Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))

private theorem list_permute_left_preserving (N : ℕ) (σ : Equiv.Perm (Fin (n N))) :
    MeasurePreserving
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin (n N) => ℝ) σ).symm.prodCongr
        (MeasurableEquiv.refl (Fin (n N) → ℝ)))
      (realListPairMeasure N) (realListPairMeasure N) := by
  exact (measurePreserving_piCongrLeft
    (fun _ : Fin (n N) => realPlaceMeasure) σ).symm.prod
      (MeasurePreserving.id _)

private theorem list_permute_right_preserving (N : ℕ) (σ : Equiv.Perm (Fin (n N))) :
    MeasurePreserving
      ((MeasurableEquiv.refl (Fin (n N) → ℝ)).prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (n N) => ℝ) σ).symm)
      (realListPairMeasure N) (realListPairMeasure N) := by
  exact (MeasurePreserving.id _).prod
    (measurePreserving_piCongrLeft
      (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)) σ).symm

private theorem integral_list_permute_left (N : ℕ) (σ : Equiv.Perm (Fin (n N)))
    (F : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) → ℝ) :
    (∫ p, F (p.1 ∘ σ, p.2) ∂realListPairMeasure N) =
      ∫ p, F p ∂realListPairMeasure N :=
  (list_permute_left_preserving N σ).integral_comp' F

private theorem integral_list_permute_right (N : ℕ) (σ : Equiv.Perm (Fin (n N)))
    (F : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) → ℝ) :
    (∫ p, F (p.1, p.2 ∘ σ) ∂realListPairMeasure N) =
      ∫ p, F p ∂realListPairMeasure N :=
  (list_permute_right_preserving N σ).integral_comp' F

private theorem integrable_list_permute_left (N : ℕ) (σ : Equiv.Perm (Fin (n N)))
    {F : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) → ℝ}
    (hF : Integrable F (realListPairMeasure N)) :
    Integrable (fun p => F (p.1 ∘ σ, p.2)) (realListPairMeasure N) :=
  (list_permute_left_preserving N σ).integrable_comp_of_integrable hF

private theorem integrable_list_permute_right (N : ℕ) (σ : Equiv.Perm (Fin (n N)))
    {F : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) → ℝ}
    (hF : Integrable F (realListPairMeasure N)) :
    Integrable (fun p => F (p.1, p.2 ∘ σ)) (realListPairMeasure N) :=
  (list_permute_right_preserving N σ).integrable_comp_of_integrable hF

theorem integrable_rawRealIntegrand (N : ℕ) :
    Integrable (fun p => rawRealIntegrand N p.1 p.2) (realListPairMeasure N) := by
  have hmap := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n N))
    (fun _ => realPlaceMeasure) (fun _ => volume.restrict (Ioo (0 : ℝ) 1))
  apply (hmap.integrable_comp_emb
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (n N))).measurableEmbedding).mp
  apply (integrable_pairedDeterminant N).congr
  filter_upwards with z
  exact pairedDeterminant_factor N z

theorem determinant_eq_rawRealIntegrand (N : ℕ) :
    determinant N = ∫ p, rawRealIntegrand N p.1 p.2 ∂realListPairMeasure N := by
  have hmap := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n N))
    (fun _ => realPlaceMeasure) (fun _ => volume.restrict (Ioo (0 : ℝ) 1))
  unfold realListPairMeasure
  rw [← hmap.integral_comp' (fun p => rawRealIntegrand N p.1 p.2)]
  exact determinant_eq_paired_factored_integral N

theorem integrable_leftRealIntegrand (N : ℕ) :
    Integrable (fun p => leftRealIntegrand N p.1 p.2) (realListPairMeasure N) := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun (σ : Equiv.Perm (Fin (n N))) _ =>
    integrable_list_permute_left N σ (integrable_rawRealIntegrand N))
  apply hi.congr
  filter_upwards with p
  exact sum_rawRealIntegrand_permute_left N p.1 p.2

theorem integral_leftRealIntegrand (N : ℕ) :
    (∫ p, leftRealIntegrand N p.1 p.2 ∂realListPairMeasure N) =
      ((n N).factorial : ℝ) * determinant N := by
  classical
  calc
    _ = ∫ p, ∑ σ : Equiv.Perm (Fin (n N)),
        rawRealIntegrand N (p.1 ∘ σ) p.2 ∂realListPairMeasure N := by
      apply integral_congr_ae
      filter_upwards with p
      exact (sum_rawRealIntegrand_permute_left N p.1 p.2).symm
    _ = ∑ σ : Equiv.Perm (Fin (n N)),
        ∫ p, rawRealIntegrand N (p.1 ∘ σ) p.2 ∂realListPairMeasure N :=
      integral_finsetSum Finset.univ (fun (σ : Equiv.Perm (Fin (n N))) _ =>
        integrable_list_permute_left N σ (integrable_rawRealIntegrand N))
    _ = _ := by
      simp only [integral_list_permute_left N _ (fun p => rawRealIntegrand N p.1 p.2),
        ← determinant_eq_rawRealIntegrand, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem integrable_doubleRealIntegrand (N : ℕ) :
    Integrable (fun p => doubleRealIntegrand N p.1 p.2) (realListPairMeasure N) := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun (σ : Equiv.Perm (Fin (n N))) _ =>
    integrable_list_permute_right N σ (integrable_leftRealIntegrand N))
  apply hi.congr
  filter_upwards with p
  exact sum_leftRealIntegrand_permute_right N p.1 p.2

theorem integral_doubleRealIntegrand (N : ℕ) :
    (∫ p, doubleRealIntegrand N p.1 p.2 ∂realListPairMeasure N) =
      ((n N).factorial : ℝ) ^ 2 * determinant N := by
  classical
  calc
    _ = ∫ p, ∑ σ : Equiv.Perm (Fin (n N)),
        leftRealIntegrand N p.1 (p.2 ∘ σ) ∂realListPairMeasure N := by
      apply integral_congr_ae
      filter_upwards with p
      exact (sum_leftRealIntegrand_permute_right N p.1 p.2).symm
    _ = ∑ σ : Equiv.Perm (Fin (n N)),
        ∫ p, leftRealIntegrand N p.1 (p.2 ∘ σ) ∂realListPairMeasure N :=
      integral_finsetSum Finset.univ (fun (σ : Equiv.Perm (Fin (n N))) _ =>
        integrable_list_permute_right N σ (integrable_leftRealIntegrand N))
    _ = _ := by
      simp only [integral_list_permute_right N _ (fun p => leftRealIntegrand N p.1 p.2),
        integral_leftRealIntegrand, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem determinant_eq_doubleRealIntegral (N : ℕ) :
    determinant N = 1 / (((n N).factorial : ℝ) ^ 2) *
      ∫ t, (∫ s, doubleRealIntegrand N t s
        ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
        ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure) := by
  have h := integral_prod (fun p => doubleRealIntegrand N p.1 p.2)
    (integrable_doubleRealIntegrand N)
  change (∫ p, doubleRealIntegrand N p.1 p.2 ∂realListPairMeasure N) =
    (∫ t, (∫ s, doubleRealIntegrand N t s
      ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
      ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure)) at h
  rw [integral_doubleRealIntegrand] at h
  rw [← h]
  have hn : ((n N).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n N)
  field_simp

open MeasureTheory Set
open scoped BigOperators

theorem ae_realPlace_mem : ∀ᵐ t ∂realPlaceMeasure, t ∈ Ioo (-1 : ℝ) 1 := by
  unfold realPlaceMeasure
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact fun _ => ht

private theorem ae_realPlace_list_mem (N : ℕ) :
    ∀ᵐ t ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure),
      ∀ i, t i ∈ Ioo (-1 : ℝ) 1 :=
  Filter.eventually_all.2 (fun _ => Measure.tendsto_eval_ae_ae.eventually ae_realPlace_mem)

private theorem ae_unit_list_mem (N : ℕ) :
    ∀ᵐ s ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ j, s j ∈ Ioo (0 : ℝ) 1 :=
  Filter.eventually_all.2 (fun _ => Measure.tendsto_eval_ae_ae.eventually
    (ae_restrict_mem measurableSet_Ioo))

theorem ae_realList_rectangle (N : ℕ) :
    ∀ᵐ p ∂realListPairMeasure N,
      p ∈ (Set.univ.pi (fun _ : Fin (n N) => Ioo (-1 : ℝ) 1)) ×ˢ
        (Set.univ.pi (fun _ : Fin (n N) => Ioo (0 : ℝ) 1)) := by
  unfold realListPairMeasure
  apply (Measure.ae_prod_mem_iff_ae_ae_mem
    ((MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).prod
      (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)))).mpr
  filter_upwards [ae_realPlace_list_mem N] with t ht
  filter_upwards [ae_unit_list_mem N] with s hs
  exact ⟨fun i _ => ht i, fun j _ => hs j⟩

def productRealIntegrand (N : ℕ) (t s : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
    (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (t j - t i)) *
    (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)) ^ 2 *
    (∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N) /
    (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - t i * s j))

theorem doubleRealIntegrand_ae_eq_products (N : ℕ) :
    (fun p => doubleRealIntegrand N p.1 p.2) =ᵐ[realListPairMeasure N]
      (fun p => productRealIntegrand N p.1 p.2) := by
  filter_upwards [ae_realList_rectangle N] with p hp
  exact doubleRealIntegrand_eq_products N p.1 p.2
    (fun i => hp.1 i (Set.mem_univ i)) (fun j => hp.2 j (Set.mem_univ j))

theorem integrable_productRealIntegrand (N : ℕ) :
    Integrable (fun p => productRealIntegrand N p.1 p.2) (realListPairMeasure N) :=
  (integrable_doubleRealIntegrand N).congr (doubleRealIntegrand_ae_eq_products N)

theorem determinant_eq_productRealIntegral (N : ℕ) :
    determinant N = 1 / (((n N).factorial : ℝ) ^ 2) *
      ∫ t, (∫ s, productRealIntegrand N t s
        ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
        ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure) := by
  have hproduct : (∫ p, productRealIntegrand N p.1 p.2 ∂realListPairMeasure N) =
      ((n N).factorial : ℝ) ^ 2 * determinant N := by
    rw [← integral_congr_ae (doubleRealIntegrand_ae_eq_products N)]
    exact integral_doubleRealIntegrand N
  have h := integral_prod (fun p => productRealIntegrand N p.1 p.2)
    (integrable_productRealIntegrand N)
  change (∫ p, productRealIntegrand N p.1 p.2 ∂realListPairMeasure N) =
    (∫ t, (∫ s, productRealIntegrand N t s
      ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
      ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure)) at h
  rw [hproduct] at h
  rw [← h]
  have hn : ((n N).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n N)
  field_simp

end InternalCatalan

end

end OAI
