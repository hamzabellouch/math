import Mathlib
import OAI.Analysis.CoulombRadii.Localization.CutRefinement
import OAI.Analysis.CoulombRadii.FormDomain.RecordReindex

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma slice_positive_square_jensen {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ}
    (hB0 : 0≤B) (hB : ∀ x, |W x| ≤ B) :
    mass u*(max (potentialForm W u.normalized) 0)^2 ≤
      sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) := by
  let c := max (potentialForm W u.normalized) 0
  have hc : 0≤c := le_max_right _ _
  have hi (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*
      (2*c*coreConditionalObservable u W s x-c^2)) := by
    have H := (coreConditionalObservable_weight_integrable u W hW hB0 hB s).const_mul (2*c)
    have K := (mass_coreSlice_integrable u s).mul_const (c^2)
    apply (H.sub K).congr
    exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply]; ring)
  have H0 : sliceExpectation u (fun s x => 2*c*coreConditionalObservable u W s x-c^2) ≤
      sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) := by
    apply Finset.sum_le_sum
    intro s hs
    exact integral_mono (hi s) (coreConditionalObservable_positive_weight_integrable u W hW hB0 hB s 2)
      (fun x => mul_le_mul_of_nonneg_left (positive_square_tangent _ c hc) (mass_nonneg _))
  have he (s : Spins m) : (∫ x, mass (u.coreSlice s x)*(2*c*coreConditionalObservable u W s x-c^2))=
      2*c*(∫ x, mass (u.coreSlice s x)*coreConditionalObservable u W s x)-c^2*(∫ x, mass (u.coreSlice s x)) := by
    calc
      _ = ∫ x, 2*c*(mass (u.coreSlice s x)*coreConditionalObservable u W s x)-c^2*mass (u.coreSlice s x) := by congr 1; funext x; ring
      _ = _ := by rw [integral_sub ((coreConditionalObservable_weight_integrable u W hW hB0 hB s).const_mul _)
        ((mass_coreSlice_integrable u s).const_mul _),integral_const_mul,integral_const_mul]
  have hs : sliceExpectation u (fun s x => 2*c*coreConditionalObservable u W s x-c^2)=
      2*c*potentialForm W u-c^2*mass u := by
    unfold sliceExpectation
    simp_rw [he]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,integral_mass_coreSlice]
    rw [show (∑ s, ∫ x, mass (u.coreSlice s x)*coreConditionalObservable u W s x)=potentialForm W u from
      sliceExpectation_coreConditionalObservable u W hW hB]
  rw [hs] at H0
  have hw := potentialForm_normalized_weight W u
  by_cases hp : 0≤potentialForm W u.normalized
  · have hec : c=potentialForm W u.normalized := max_eq_left hp
    rw [hec] at H0
    rw [max_eq_left hp]
    nlinarith
  · have hec : c=0 := max_eq_right (le_of_not_ge hp)
    rw [hec] at H0
    rw [max_eq_right (le_of_not_ge hp)]
    nlinarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma potentialForm_congr_values {k : ℕ} (W : Configuration k → ℝ) (u v : H1Vector k)
    (hv : ∀ t, u.value t =ᵐ[volume] v.value t) : potentialForm W u=potentialForm W v := by
  apply Finset.sum_congr rfl
  intro t ht
  apply integral_congr_ae
  filter_upwards [hv t] with z hz
  rw [hz]

lemma potentialForm_normalized_congr_values {k : ℕ} (W : Configuration k → ℝ)
    (u v : H1Vector k) (hv : ∀ t, u.value t =ᵐ[volume] v.value t) :
    potentialForm W u.normalized=potentialForm W v.normalized := by
  rw [potentialForm_normalized_eq,potentialForm_normalized_eq,
    mass_congr_ae u v hv,potentialForm_congr_values W u v hv]

lemma nested_coreSlice_values {m q k : ℕ} (u : H1Vector (m+(q+k)))
    (s : Spins m) (t : Spins q) :
    ∀ᵐ x : Configuration m, ∀ᵐ y : Configuration q,
      ∀ r : Spins k, ∀ z : Configuration k,
        ((u.coreSlice s x).coreSlice t y).value r z=
          ((u.reindex (recordAssoc m q k)).coreSlice (Fin.append s t)
            (joinConfiguration m q (x,y))).value r z := by
  let v := u.reindex (recordAssoc m q k)
  have hd : ∀ᵐ x : Configuration m, ∀ᵐ y : Configuration q,
      v.CoreSliceRegular (Fin.append s t) (joinConfiguration m q (x,y)) :=
    Measure.ae_ae_of_ae_prod ((joinConfiguration_measurePreserving m q).quasiMeasurePreserving.ae
      (v.coreSliceRegular_ae (Fin.append s t)))
  filter_upwards [u.coreSliceRegular_ae s,hd] with x hx hd
  filter_upwards [(u.coreSlice s x).coreSliceRegular_ae t,hd] with y hy hd
  intro r z
  rw [(u.coreSlice s x).coreSlice_value t hy,u.coreSlice_value s hx,v.coreSlice_value (Fin.append s t) hd]
  simp only [v,H1Vector.reindex_value,append_recordAssoc,reindex_join_recordAssoc]

lemma nested_coreConditional_weight {m q k : ℕ} (u : H1Vector (m+(q+k)))
    (W : Configuration (m+(q+k)) → ℝ) (s : Spins m) (t : Spins q) :
    ∀ᵐ x : Configuration m, ∀ᵐ y : Configuration q,
      mass ((u.coreSlice s x).coreSlice t y)*
        (max (coreConditionalObservable (u.coreSlice s x)
          (fun w => W (joinConfiguration m (q+k) (x,w))) t y) 0)^2 =
      mass ((u.reindex (recordAssoc m q k)).coreSlice (Fin.append s t) (joinConfiguration m q (x,y)))*
        (max (coreConditionalObservable (u.reindex (recordAssoc m q k))
          (W ∘ reindexConfiguration (recordAssoc m q k)) (Fin.append s t) (joinConfiguration m q (x,y))) 0)^2 := by
  filter_upwards [nested_coreSlice_values u s t] with x hx
  filter_upwards [hx] with y hy
  have hv : ∀ r, ((u.coreSlice s x).coreSlice t y).value r =ᵐ[volume]
      ((u.reindex (recordAssoc m q k)).coreSlice (Fin.append s t) (joinConfiguration m q (x,y))).value r :=
    fun r => Eventually.of_forall (hy r)
  rw [mass_congr_ae _ _ hv]
  congr 2
  unfold coreConditionalObservable
  simp only [Function.comp_apply,reindex_join_recordAssoc]
  exact congrArg (fun b : ℝ => max b 0)
    (potentialForm_normalized_congr_values _ _ _ hv)

theorem record_more_positive_jensen {m q k : ℕ} (u : H1Vector (m+(q+k)))
    (W : Configuration (m+(q+k)) → ℝ) (hW : Measurable W) {B : ℝ}
    (hB0 : 0≤B) (hB : ∀ x, |W x| ≤ B) :
    sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) ≤
      sliceExpectation (u.reindex (recordAssoc m q k)) (fun s x =>
        (max (coreConditionalObservable (u.reindex (recordAssoc m q k))
          (W ∘ reindexConfiguration (recordAssoc m q k)) s x) 0)^2) := by
  let v := u.reindex (recordAssoc m q k)
  let V := W ∘ reindexConfiguration (recordAssoc m q k)
  have hV : Measurable V := hW.comp (reindexConfiguration_continuous _).measurable
  let F := fun (s : Spins m) (t : Spins q) (x : Configuration m) (y : Configuration q) =>
    mass (v.coreSlice (Fin.append s t) (joinConfiguration m q (x,y)))*
      (max (coreConditionalObservable v V (Fin.append s t) (joinConfiguration m q (x,y))) 0)^2
  have hi (s : Spins m) (t : Spins q) : Integrable (fun xy : Configuration m × Configuration q => F s t xy.1 xy.2)
      (volume.prod volume) := by
    exact ((joinConfiguration_measurePreserving m q).integrable_comp_emb
      (joinConfiguration m q).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr
      (coreConditionalObservable_positive_weight_integrable v V hV hB0 (fun x => hB _) (Fin.append s t) 2)
  have hstep (s : Spins m) :
      (∫ x, mass (u.coreSlice s x)*(max (coreConditionalObservable u W s x) 0)^2) ≤
        ∑ t : Spins q, ∫ xy, mass (v.coreSlice (Fin.append s t) xy)*
          (max (coreConditionalObservable v V (Fin.append s t) xy) 0)^2 := by
    calc
      _ ≤ ∫ x, ∑ t, ∫ y, F s t x y := by
        apply integral_mono_ae (coreConditionalObservable_positive_weight_integrable u W hW hB0 hB s 2)
          (integrable_finsetSum _ (fun t _ => (hi s t).integral_prod_left))
        have hall : ∀ᵐ x : Configuration m, ∀ t : Spins q,
            ∀ᵐ y : Configuration q,
              mass ((u.coreSlice s x).coreSlice t y)*
                (max (coreConditionalObservable (u.coreSlice s x)
                  (fun w => W (joinConfiguration m (q+k) (x,w))) t y) 0)^2=F s t x y :=
          ae_all_iff.mpr (fun t => nested_coreConditional_weight u W s t)
        filter_upwards [hall] with x hx
        have H := slice_positive_square_jensen (u.coreSlice s x)
          (fun w => W (joinConfiguration m (q+k) (x,w)))
          (hW.comp ((joinConfiguration m (q+k)).continuous.measurable.comp
            (measurable_const.prodMk measurable_id))) hB0 (fun w => hB _)
        change mass (u.coreSlice s x)*(max (coreConditionalObservable u W s x) 0)^2 ≤ _ at H
        apply H.trans_eq
        exact Finset.sum_congr rfl (fun t _ => integral_congr_ae (hx t))
      _ = ∑ t, ∫ xy : Configuration m × Configuration q, F s t xy.1 xy.2 ∂volume.prod volume := by
        rw [integral_finsetSum _ (fun t _ => (hi s t).integral_prod_left)]
        exact Finset.sum_congr rfl (fun t _ => (integral_prod _ (hi s t)).symm)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (joinConfiguration_measurePreserving m q).integral_comp' (fun xy : Configuration (m+q) =>
          mass (v.coreSlice (Fin.append s t) xy)*(max (coreConditionalObservable v V (Fin.append s t) xy) 0)^2)
  calc
    _ ≤ ∑ s : Spins m, ∑ t : Spins q, ∫ x, mass (v.coreSlice (Fin.append s t) x)*
        (max (coreConditionalObservable v V (Fin.append s t) x) 0)^2 :=
      Finset.sum_le_sum (fun s (_ : s∈Finset.univ) => hstep s)
    _ = _ := by
      unfold sliceExpectation
      rw [←Fintype.sum_prod_type (f:=fun st : Spins m × Spins q => ∫ x,
        mass (v.coreSlice (Fin.append st.1 st.2) x)*(max (coreConditionalObservable v V (Fin.append st.1 st.2) x) 0)^2)]
      exact Fintype.sum_equiv (Fin.appendEquiv m q) _ _ (fun _ => rfl)

end Coulomb

end

end OAI
